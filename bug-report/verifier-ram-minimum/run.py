"""Run against the current local Rust checkout: python3 run.py /path/to/jolt."""

import json
from pathlib import Path
import struct
import subprocess
import sys
import tempfile


def make_elf(path, text, entry):
    names = b"\0.text\0.shstrtab\0"
    buf = bytearray(0x1200 + 3 * 64)
    buf[0:16] = b"\x7fELF\x02\x01\x01" + bytes(9)
    struct.pack_into("<HHIQQQIHHHHHH", buf, 16,
                     2, 243, 1, entry, 64, 0x1200, 0, 64, 56, 1, 64, 3, 2)
    struct.pack_into("<IIQQQQQQ", buf, 64,
                     1, 5, 0x1000, 0x80000000, 0x80000000,
                     len(text), len(text), 0x1000)
    buf[0x1000:0x1000 + len(text)] = text
    buf[0x1100:0x1100 + len(names)] = names
    struct.pack_into("<IIQQQQIIQQ", buf, 0x1240,
                     1, 1, 6, 0x80000000, 0x1000, len(text), 0, 0, 4, 0)
    struct.pack_into("<IIQQQQIIQQ", buf, 0x1280,
                     7, 3, 0, 0, 0x1100, len(names), 0, 0, 1, 0)
    path.write_bytes(buf)


def main():
    repo = Path(sys.argv[1]).resolve()
    source = Path(__file__).with_name("repro.rs")
    packages = ["jolt-prover", "jolt-verifier", "tracer", "jolt-program",
                "jolt-riscv", "common", "jolt-field"]
    build = ["cargo", "+1.95", "build", "--message-format=json"]
    for package in packages:
        build += ["-p", package]
    built = subprocess.run(build, cwd=repo, text=True, stdout=subprocess.PIPE, check=True)
    libraries = {}
    for line in built.stdout.splitlines():
        event = json.loads(line)
        if event.get("reason") == "compiler-artifact":
            for filename in event.get("filenames", []):
                if filename.endswith(".rlib"):
                    libraries[event["target"]["name"]] = filename
    with tempfile.TemporaryDirectory(prefix="jolt-ram-minimum-") as directory:
        directory = Path(directory)
        binary = directory / "repro"
        dependency_dir = Path(libraries["jolt_prover"]).parent
        if dependency_dir.name != "deps":
            dependency_dir /= "deps"
        compile_command = ["rustup", "run", "1.95", "rustc", "--edition=2021",
                           str(source), "-L", f"dependency={dependency_dir}"]
        for name in ["common", "jolt_crypto", "jolt_dory", "jolt_field", "jolt_program",
                     "jolt_prover", "jolt_riscv", "jolt_verifier", "tracer"]:
            compile_command += ["--extern", f"{name}={libraries[name]}"]
        subprocess.run(compile_command + ["-o", str(binary)], check=True)
        for name, text, entry in [("empty", b"", 0),
                                  ("self_jump", bytes.fromhex("6f000000"), 0x80000000)]:
            elf = directory / f"{name}.elf"
            make_elf(elf, text, entry)
            print(f"== {name}", flush=True)
            subprocess.run([str(binary), str(elf)], check=True)


if __name__ == "__main__":
    main()
