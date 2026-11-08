#!/usr/bin/env python3
"""Compare the Sail RISC-V model with Jolt's tracer on one ELF, per retired
instruction.

Both simulators run the same ELF from reset. The Sail run uses the C++
emulator `sail_riscv_sim` with the jolt-qed configuration
(sail-import/rv64d_jolt.json); the Jolt run uses `jolt-trace`, which drives the
tracer in trace mode so that every instruction executes its inline sequence.

For each retired instruction the script compares
  * the instruction address and the address of the next instruction,
  * the integer registers x1..x31,
  * the six machine CSRs that Jolt keeps in virtual registers
    (mstatus, mtvec, mscratch, mepc, mcause, mtval); Jolt's mstatus is
    compared as virtual register 39 OR --jolt-mstatus-or, the value a CSR read
    returns,
  * the memory bytes whose value changed.
A difference is reported at the instruction where it first appears or
changes, so a register that stays different is reported once. The comparison
stops at the first control-flow difference, since the two runs no longer
execute the same instructions after it.

It also reports, without counting them as differences: CSR bits that differ
from reset on and have kept differing, Sail privilege-mode changes and traps,
and Jolt RAM writes at instructions where Sail stores nothing.

LR/SC reservations are a spec-legal policy choice. Jolt reserves the exact
address and fails an SC wider than its LR. Sail's emulator may be more
permissive (unpatched sail-riscv reserves an 8-byte granule and does not check
the width). When the first difference of a run is an SC that succeeds in Sail
and fails in Jolt for one of these two reasons, the run is labelled POLICY and
compared no further.

Usage:
  difftest.py --sail SIM --config JSON --jolt JOLT_TRACE ELF [--json OUT]
              [--limit N] [--keep DIR]

Exit status: 0 when the runs agree, 1 when they differ, 2 on a harness error,
3 when they differ only from a reservation-policy SC on.
"""

import argparse
import json
import os
import re
import struct
import subprocess
import sys

# LR/SC as Sail disassembles them, such as "sc.d.aq x23, x6, (x8)".
LRSC_RE = re.compile(r"\b(lr|sc)\.([wd])(?:\.\w+)*\s+x(\d+),\s*(?:x\d+,\s*)?\(x(\d+)\)")
CSRS = ("mstatus", "mtvec", "mscratch", "mepc", "mcause", "mtval")
MASK64 = (1 << 64) - 1


def load_elf(path):
    """Return {address: byte} for the PT_LOAD segments of a 64-bit LE ELF."""
    data = open(path, "rb").read()
    if data[:4] != b"\x7fELF" or data[4] != 2 or data[5] != 1:
        raise SystemExit(f"{path}: not a 64-bit little-endian ELF")
    phoff, = struct.unpack_from("<Q", data, 0x20)
    phentsize, phnum = struct.unpack_from("<HH", data, 0x36)
    mem = {}
    for i in range(phnum):
        p_type, _, p_offset, p_vaddr, _, p_filesz, p_memsz = struct.unpack_from(
            "<IIQQQQQ", data, phoff + i * phentsize)
        if p_type != 1:
            continue
        for k in range(p_memsz):
            mem[p_vaddr + k] = data[p_offset + k] if k < p_filesz else 0
    return mem


class Step:
    def __init__(self, pc, insn="", priv="M"):
        self.pc = pc
        self.next = None
        self.insn = insn
        self.priv = priv
        self.x = {}        # register index -> value written
        self.csr = {}      # CSR name -> value written
        self.writes = []   # (address, width, value) or (address, pre, post)
        self.trap = None
        self.resv = {}


STEP_RE = re.compile(r"^\[(\d+)\] \[(\w+)\]: 0x([0-9A-Fa-f]+) \(0x([0-9A-Fa-f]+)\) (.*?)\s*(\S+\+\d+)?$")
XW_RE = re.compile(r"^x(\d+) <- 0x([0-9A-Fa-f]+)$")
CSRW_RE = re.compile(r"^CSR (\w+) \(0x[0-9A-Fa-f]+\) <- 0x([0-9A-Fa-f]+)$")
MEMW_RE = re.compile(r"^mem\[R?W,0x([0-9A-Fa-f]+)\] <- 0x([0-9A-Fa-f]+)$")
TRAP_RE = re.compile(r"^handling (\S+) at priv (\w+) with tval 0x([0-9A-Fa-f]+)$")


def run_sail(sim, config, elf, limit, log):
    cmd = [sim, "--config", config, "--trace-instr", "--trace-reg", "--trace-mem",
           "--trace-exception", "--inst-limit", str(limit), elf]
    proc = subprocess.run(cmd, capture_output=True, text=True)
    out = proc.stdout + proc.stderr
    if log:
        open(log, "w").write(out)
    steps, end, reset = [], {"kind": "limit"}, {}
    cur = None
    for line in out.splitlines():
        line = line.strip()
        m = STEP_RE.match(line)
        if m:
            if cur is not None:
                cur.next = int(m.group(3), 16)
            cur = Step(int(m.group(3), 16), f"{m.group(4)} {m.group(5).strip()}", m.group(2))
            steps.append(cur)
            continue
        if line == "SUCCESS":
            end = {"kind": "tohost", "code": 0}
            continue
        if line.startswith("FAILURE"):
            code = re.search(r"(\d+)\s*$", line)
            end = {"kind": "tohost", "code": int(code.group(1)) if code else None}
            continue
        if cur is None:
            # Reset writes happen before the first instruction; keep the CSRs.
            if (m := CSRW_RE.match(line)):
                reset[m.group(1)] = int(m.group(2), 16)
            continue
        if (m := XW_RE.match(line)):
            if int(m.group(1)) != 0:
                cur.x[int(m.group(1))] = int(m.group(2), 16)
        elif (m := CSRW_RE.match(line)):
            cur.csr[m.group(1)] = int(m.group(2), 16)
        elif (m := MEMW_RE.match(line)):
            cur.writes.append((int(m.group(1), 16), len(m.group(2)) // 2, int(m.group(2), 16)))
        elif (m := TRAP_RE.match(line)):
            cur.trap = f"{m.group(1)} tval=0x{int(m.group(3), 16):x}"
    if proc.returncode not in (0, 1) and end["kind"] == "limit":
        end = {"kind": "error", "status": proc.returncode, "tail": out.splitlines()[-3:]}
    return steps, end, reset


def run_jolt(binary, elf, limit, log):
    proc = subprocess.run([binary, elf, "--limit", str(limit)], capture_output=True, text=True)
    if log:
        open(log, "w").write(proc.stdout + proc.stderr)
    steps, end = [], {"kind": "error", "status": proc.returncode, "tail": proc.stderr.splitlines()[-3:]}
    for line in proc.stdout.splitlines():
        rec = json.loads(line)
        if "end" in rec:
            end = {"kind": rec["end"]}
            if rec["end"] == "tohost":
                value = int(rec["value"], 16)
                end["code"] = value >> 1 if value & 1 else None
                end["value"] = value
            if rec["end"] == "panic":
                end["msg"] = rec["msg"]
                end["pc"] = int(rec["pc"], 16)
            continue
        s = Step(int(rec["pc"], 16))
        s.next = int(rec["next"], 16)
        s.x = {int(k): int(v, 16) for k, v in rec["x"].items()}
        s.csr = {k: int(v, 16) for k, v in rec["csr"].items()}
        s.writes = [tuple(int(v, 16) for v in w) for w in rec["mem"]]
        s.resv = {int(k): int(v, 16) for k, v in rec["resv"].items()}
        steps.append(s)
    return steps, end, {}


def sail_bytes(writes):
    out = {}
    for addr, width, value in writes:
        for k in range(width):
            out[addr + k] = (value >> (8 * k)) & 0xFF
    return out


def jolt_bytes(writes):
    out = {}
    for addr, _pre, post in writes:
        for k in range(8):
            out[addr + k] = (post >> (8 * k)) & 0xFF
    return out


def compare(elf, sail, jolt, mstatus_or=0, ignore=None):
    ignore = ignore or {}
    s_steps, s_end, s_reset = sail
    j_steps, j_end, _ = jolt
    mem_s = load_elf(elf)
    mem_j = dict(mem_s)
    xs, xj = [0] * 32, [0] * 32
    # Sail traces the CSRs its reset sets; the others reset to zero. Jolt's
    # virtual registers start at zero.
    cs, cj = {c: s_reset.get(c, 0) for c in CSRS}, {c: 0 for c in CSRS}
    reported = {}
    diffs, notes = [], []

    def report(key, pair, text):
        if reported.get(key) != pair:
            reported[key] = pair
            if pair is not None:
                diffs.append(text)

    # CSR bits that differ at reset are a note, not a difference, for as long
    # as they keep differing: a guest sees them only by reading the CSR (and
    # the register it reads into is compared) or through control flow (also
    # compared). Once such a bit agrees it is compared like any other.
    view0 = dict(cj, mstatus=cj["mstatus"] | mstatus_or)
    since_reset = {}
    for c in CSRS:
        since_reset[c] = (cs[c] ^ view0[c]) & ~ignore.get(c, 0)
        if since_reset[c]:
            notes.append(f"reset: {c} Sail 0x{cs[c]:x}, Jolt 0x{view0[c]:x} "
                         f"(differ in 0x{since_reset[c]:x})")

    n = min(len(s_steps), len(j_steps))
    stopped = None
    policy = None
    resv = None     # (address, width) of the last LR, while no SC has followed
    for i in range(n):
        s, j = s_steps[i], j_steps[i]
        where = f"step {i} pc=0x{s.pc:x} [{s.insn}]"
        before = len(diffs)
        lrsc = LRSC_RE.search(s.insn)
        if lrsc:
            addr, width = xs[int(lrsc[4])], 4 if lrsc[2] == "w" else 8
        if s.pc != j.pc:
            stopped = f"{where}: Sail pc 0x{s.pc:x}, Jolt pc 0x{j.pc:x}"
            diffs.append("control flow: " + stopped)
            n = i
            break
        if s.priv != "M":
            notes.append(f"{where}: Sail runs in privilege {s.priv}")
        if s.trap:
            notes.append(f"{where}: Sail trap {s.trap}")
        for r, v in s.x.items():
            xs[r] = v
        for r, v in j.x.items():
            xj[r] = v
        for r in range(1, 32):
            pair = (xs[r], xj[r]) if xs[r] != xj[r] else None
            report(("x", r), pair, f"{where}: x{r} Sail 0x{xs[r]:x}, Jolt 0x{xj[r]:x}")
        for c, v in s.csr.items():
            if c in cs:
                cs[c] = v
        for c, v in j.csr.items():
            cj[c] = v
        view = dict(cj, mstatus=cj["mstatus"] | mstatus_or)
        for c in CSRS:
            # Keyed on the differing bits, so a constant difference (such as
            # the read-only mstatus.UXL/SXL fields) is reported once.
            xor = (cs[c] ^ view[c]) & ~ignore.get(c, 0)
            since_reset[c] &= xor
            xor &= ~since_reset[c]
            report(("csr", c), xor or None,
                   f"{where}: {c} Sail 0x{cs[c]:x}, Jolt 0x{view[c]:x} (differ in 0x{xor:x})")
        changed_s = {a: b for a, b in sail_bytes(s.writes).items() if mem_s.get(a, 0) != b}
        changed_j = {a: b for a, b in jolt_bytes(j.writes).items() if mem_j.get(a, 0) != b}
        mem_s.update(changed_s)
        mem_j.update(changed_j)
        if changed_s != changed_j:
            diffs.append(f"{where}: memory Sail {fmt_bytes(changed_s)}, Jolt {fmt_bytes(changed_j)}")
        if j.writes and not s.writes:
            ws = ", ".join(f"0x{a:x}: 0x{pre:x} -> 0x{post:x}" for a, pre, post in j.writes)
            notes.append(f"{where}: Jolt RAM write with no Sail store ({ws})")
        if lrsc and lrsc[1] == "lr":
            resv = (addr, width)
        elif lrsc:
            rd = int(lrsc[3])
            # Jolt's reservation needs the same address and an SC no wider
            # than the LR. The spec also lets an implementation accept an SC
            # elsewhere in the reserved granule, or wider than the LR, as
            # unpatched sail-riscv does (8-byte granule, no width check).
            # With rd = x0 the outcome shows only as Sail's store.
            sail_only = (xs[rd] == 0 and xj[rd] == 1) if rd else (changed_s and not changed_j)
            if (before == 0 and len(diffs) > 0 and resv and sail_only
                    and resv[0] // 8 == addr // 8
                    and (resv[0] != addr or resv[1] < width)):
                policy = (f"{where}: SC succeeds in Sail and fails in Jolt after an LR "
                          f"of {resv[1]} bytes at 0x{resv[0]:x} (spec-legal reservation "
                          "policy, compared no further)")
                del diffs[before:]
                stopped = policy
                n = i + 1
                break
            resv = None
        if s.next is not None and s.next != j.next:
            stopped = f"{where}: next pc Sail 0x{s.next:x}, Jolt 0x{j.next:x}"
            diffs.append("control flow: " + stopped)
            n = i + 1
            break
    same_exit = end_key(s_end) == end_key(j_end) and s_end["kind"] == "tohost"
    if stopped is None and same_exit and len(s_steps) != len(j_steps):
        # Both wrote the same exit code to tohost. Jolt stops at the first
        # store to tohost; Sail can retire a few more instructions before its
        # HTIF device acts (riscv-tests store the high half separately).
        notes.append(f"Sail retired {len(s_steps)} instructions, Jolt {len(j_steps)}, "
                     "before the same tohost exit")
    elif stopped is None and len(s_steps) != len(j_steps):
        diffs.append(f"length: Sail retired {len(s_steps)} instructions, Jolt {len(j_steps)}")
        if len(s_steps) > n:
            s = s_steps[n]
            notes.append(f"step {n} pc=0x{s.pc:x} [{s.insn}]: Sail continues"
                         + (f" with trap {s.trap}" if s.trap else "")
                         + (f", writes {', '.join(f'{k}=0x{v:x}' for k, v in s.csr.items())}" if s.csr else ""))
    if stopped is None and end_key(s_end) != end_key(j_end):
        diffs.append(f"end: Sail {s_end}, Jolt {j_end}")
    return diffs, notes, s_end, j_end, n, policy


def end_key(end):
    return (end["kind"], end.get("code"))


def fmt_bytes(b):
    if not b:
        return "{}"
    return "{" + ", ".join(f"0x{a:x}=0x{v:02x}" for a, v in sorted(b.items())) + "}"


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("elf")
    ap.add_argument("--sail", required=True, help="sail_riscv_sim binary")
    ap.add_argument("--config", required=True, help="Sail configuration JSON")
    ap.add_argument("--jolt", required=True, help="jolt-trace binary")
    ap.add_argument("--limit", type=int, default=100000, help="instruction limit")
    ap.add_argument("--json", help="write the result as JSON to this file")
    ap.add_argument("--ignore-bits", action="append", default=[], metavar="CSR=MASK",
                    help="leave these bits of CSR out of the comparison (repeatable)")
    ap.add_argument("--jolt-mstatus-or", type=lambda v: int(v, 0), default=0,
                    help="bits Jolt ORs into virtual register 39 when it reads mstatus "
                         "(0x1800 on Jolt versions that keep only MIE and MPIE there)")
    ap.add_argument("--keep", help="keep both raw traces in this directory")
    a = ap.parse_args()
    logs = (None, None)
    if a.keep:
        os.makedirs(a.keep, exist_ok=True)
        base = os.path.join(a.keep, os.path.splitext(os.path.basename(a.elf))[0])
        logs = (base + ".sail.log", base + ".jolt.jsonl")
    try:
        sail = run_sail(a.sail, a.config, a.elf, a.limit, logs[0])
        jolt = run_jolt(a.jolt, a.elf, a.limit, logs[1])
    except (OSError, json.JSONDecodeError) as e:
        print(f"difftest: {e}", file=sys.stderr)
        return 2
    diffs, notes, s_end, j_end, n, policy = compare(a.elf, sail, jolt, a.jolt_mstatus_or,
                                                {c: int(m, 0) for c, m in (i.split("=") for i in a.ignore_bits)})
    name = os.path.basename(a.elf)
    verdict = "DIFFER" if diffs else "POLICY" if policy else "AGREE"
    print(f"== {name}: {verdict} ({n} instructions compared)")
    print(f"   end: Sail {s_end}; Jolt {j_end}")
    if policy:
        print(f"   policy  {policy}")
    for d in diffs:
        print(f"   diff  {d}")
    for t in notes:
        print(f"   note  {t}")
    if a.json:
        json.dump({"elf": name, "verdict": verdict, "compared": n, "policy": policy, "diffs": diffs,
                   "notes": notes, "sail_end": s_end, "jolt_end": j_end},
                  open(a.json, "w"), indent=2)
    return 1 if diffs else 3 if policy else 0


if __name__ == "__main__":
    sys.exit(main())
