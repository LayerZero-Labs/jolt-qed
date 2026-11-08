#!/usr/bin/env python3
"""Self-test of difftest.py's verdicts, with stand-in simulators that print
canned traces. It checks that each way a comparison can go wrong ends as
DIFFER or as a harness error, never as AGREE or POLICY.

    python3 scripts/difftest/test_difftest.py
"""

import json
import os
import struct
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
DIFFTEST = os.path.join(HERE, "difftest.py")
HTIF = 0x80001000
BUF = 0x80002000

FAKE = """#!/usr/bin/env python3
import os, sys, time
time.sleep(float(os.environ.get("FAKE_SLEEP", "0")))
sys.stdout.write(open(os.environ["FAKE_{tool}_OUT"]).read())
sys.exit(int(os.environ.get("FAKE_{tool}_RC", "0")))
"""


def elf_bytes():
    """A 64-bit little-endian RISC-V ELF header with no segments."""
    header = bytearray(64)
    header[:6] = b"\x7fELF\x02\x01"
    struct.pack_into("<HHIQQQIHHHHHH", header, 16, 2, 243, 1, 0x80000000, 64, 0, 0, 64, 56, 0,
                     64, 0, 0)
    return bytes(header)


def sail_step(n, pc, insn, enc=0x00000013, effects=()):
    lines = [f"mem[X,0x{pc:016X}] -> 0x{enc & 0xFFFF:04X}",
             f"[{n}] [M]: 0x{pc:016X} (0x{enc:08X}) {insn}    _start+{pc - 0x80000000}"]
    return lines + list(effects)


def sail_trace(steps, end="SUCCESS"):
    lines = ["HTIF located at 0x%x" % HTIF, "Entry point: 0x80000000",
             "CSR mstatus (0x300) <- 0x0000000000001800"]
    for s in steps:
        lines += s
    if end:
        lines.append(end)
    return "\n".join(lines) + "\n"


def jolt_step(n, pc, nxt, x=None, csr=None, mem=None):
    return json.dumps({"step": n, "pc": f"0x{pc:016x}", "next": f"0x{nxt:016x}",
                       "x": {str(k): f"0x{v:016x}" for k, v in (x or {}).items()},
                       "csr": {k: f"0x{v:016x}" for k, v in (csr or {}).items()},
                       "resv": {},
                       "mem": [[f"0x{a:016x}", f"0x{p:016x}", f"0x{q:016x}"]
                               for a, p, q in (mem or [])]})


EXIT = '{"end":"tohost","value":"0x0000000000000001"}'
STORE_EXIT = [f"mem[W,0x{HTIF:016X}] <- 0x0000000000000001"]


def straight(n):
    """n `addi` steps from 0x80000000, the same in both traces, then an SD of
    the exit command to tohost."""
    s, j = [], []
    for i in range(n):
        pc = 0x80000000 + 4 * i
        s.append(sail_step(i, pc, "addi x5, x5, 0x1", effects=[f"x5 <- 0x{i + 1:016X}"]))
        j.append(jolt_step(i, pc, pc + 4, x={5: i + 1}))
    pc = 0x80000000 + 4 * n
    s.append(sail_step(n, pc, "sd x31, 0x0(x30)", 0x01FF3023, STORE_EXIT))
    j.append(jolt_step(n, pc, pc + 4, mem=[(HTIF, 0, 1)]))
    return s, j


class Difftest(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory(prefix="difftest-test-")
        self.addCleanup(tmp.cleanup)
        self.dir = tmp.name
        self.elf = os.path.join(self.dir, "guest.elf")
        with open(self.elf, "wb") as f:
            f.write(elf_bytes())
        self.tools = {}
        for tool in ("SAIL", "JOLT"):
            path = os.path.join(self.dir, tool.lower())
            with open(path, "w") as f:
                f.write(FAKE.format(tool=tool))
            os.chmod(path, 0o755)
            self.tools[tool] = path

    def run_case(self, sail, jolt, sail_rc=0, jolt_rc=0, args=(), sleep=0):
        env = dict(os.environ, FAKE_SAIL_RC=str(sail_rc), FAKE_JOLT_RC=str(jolt_rc),
                   FAKE_SLEEP=str(sleep))
        for tool, text in (("SAIL", sail), ("JOLT", jolt)):
            out = os.path.join(self.dir, tool.lower() + ".out")
            with open(out, "w") as f:
                f.write(text)
            env[f"FAKE_{tool}_OUT"] = out
        result = os.path.join(self.dir, "result.json")
        if os.path.exists(result):
            os.remove(result)
        proc = subprocess.run([sys.executable, DIFFTEST, "--sail", self.tools["SAIL"],
                               "--config", "unused.json", "--jolt", self.tools["JOLT"],
                               "--json", result, *args, self.elf],
                              capture_output=True, text=True, env=env)
        return proc.returncode, proc.stdout + proc.stderr

    def agree_case(self):
        s, j = straight(3)
        return sail_trace(s), "\n".join(j + [EXIT]) + "\n"

    def test_agree(self):
        status, out = self.run_case(*self.agree_case())
        self.assertEqual(status, 0, out)

    def test_both_crash_without_output(self):
        status, out = self.run_case("", "", sail_rc=139, jolt_rc=134)
        self.assertEqual(status, 2, out)

    def test_sail_exit_1_without_failure_line(self):
        s, j = straight(3)
        status, out = self.run_case(sail_trace(s, end=None), "\n".join(j + [EXIT]) + "\n",
                                    sail_rc=1)
        self.assertEqual(status, 1, out)

    def test_both_crash_after_some_steps(self):
        s, j = straight(3)
        status, out = self.run_case(sail_trace(s[:2], end=None), "\n".join(j[:2]) + "\n",
                                    sail_rc=1, jolt_rc=134)
        self.assertEqual(status, 1, out)

    def test_jolt_status_overrides_end_record(self):
        sail, jolt = self.agree_case()
        status, out = self.run_case(sail, jolt, jolt_rc=101)
        self.assertEqual(status, 1, out)

    def test_unrecognised_sail_line(self):
        sail, jolt = self.agree_case()
        status, out = self.run_case(sail.replace("x5 <- 0x0000000000000002",
                                                 "x5 := 0x0000000000000002"), jolt)
        self.assertEqual(status, 2, out)

    def test_sail_numbering_gap(self):
        sail, jolt = self.agree_case()
        status, out = self.run_case(sail.replace("[2] [M]", "[5] [M]"), jolt)
        self.assertEqual(status, 2, out)

    def test_only_success_line(self):
        _, jolt = self.agree_case()
        status, out = self.run_case("HTIF located at 0x80001000\nSUCCESS\n", jolt)
        self.assertEqual(status, 2, out)

    def test_jolt_record_without_next(self):
        sail, jolt = self.agree_case()
        rec = json.loads(jolt.splitlines()[0])
        del rec["next"]
        status, out = self.run_case(sail, "\n".join([json.dumps(rec)] + jolt.splitlines()[1:]))
        self.assertEqual(status, 2, out)

    def test_jolt_without_end_record(self):
        sail, jolt = self.agree_case()
        status, out = self.run_case(sail, "\n".join(jolt.splitlines()[:-1]) + "\n")
        self.assertEqual(status, 2, out)

    def test_jolt_non_exit_tohost(self):
        sail, jolt = self.agree_case()
        status, out = self.run_case(sail, jolt.replace(EXIT, '{"end":"tohost","value":"0x0100000000000001"}'))
        self.assertEqual(status, 2, out)

    def test_wrong_final_next_pc(self):
        sail, jolt = self.agree_case()
        lines = jolt.splitlines()
        rec = json.loads(lines[-2])
        rec["next"] = "0x0000000080000100"
        status, out = self.run_case(sail, "\n".join(lines[:-2] + [json.dumps(rec), lines[-1]]))
        self.assertEqual(status, 1, out)

    def test_unchecked_suffix(self):
        s, j = straight(3)
        tail = sail_step(4, 0x80000010, "sd x5, 0x0(x8)", 0x00543023,
                         [f"mem[W,0x{BUF:016X}] <- 0x0000000000000005"])
        status, out = self.run_case(sail_trace(s + [tail]), "\n".join(j + [EXIT]) + "\n")
        self.assertEqual(status, 1, out)

    def test_htif_tail(self):
        s, j = straight(3)
        tail = [sail_step(4, 0x80000010, "auipc x30, 0x1", 0x00001F17, ["x30 <- 0x0000000080001010"]),
                sail_step(5, 0x80000014, "sw x0, -0x10(x30)", 0xFE0F2823,
                          [f"mem[W,0x{HTIF + 4:016X}] <- 0x00000000"])]
        status, out = self.run_case(sail_trace(s + tail), "\n".join(j + [EXIT]) + "\n")
        self.assertEqual(status, 0, out)

    def tail_case(self, tail):
        s, j = straight(3)
        return sail_trace(s + tail), "\n".join(j + [EXIT]) + "\n"

    def test_tail_with_jump(self):
        tail = [sail_step(4, 0x80000010, "auipc x30, 0x1", 0x00001F17, ["x30 <- 0x0000000080001010"]),
                sail_step(5, 0x90000000, "sw x0, -0x10(x30)", 0xFE0F2823,
                          [f"mem[W,0x{HTIF + 4:016X}] <- 0x00000000"])]
        status, out = self.run_case(*self.tail_case(tail))
        self.assertEqual(status, 1, out)

    def test_tail_with_unchanged_csr_write(self):
        tail = [sail_step(4, 0x80000010, "auipc x30, 0x1", 0x00001F17,
                          ["x30 <- 0x0000000080001010", "CSR mscratch (0x340) <- 0x0000000000000000"]),
                sail_step(5, 0x80000014, "sw x0, -0x10(x30)", 0xFE0F2823,
                          [f"mem[W,0x{HTIF + 4:016X}] <- 0x00000000"])]
        status, out = self.run_case(*self.tail_case(tail))
        self.assertEqual(status, 1, out)

    def test_tail_without_store(self):
        tail = [sail_step(4, 0x80000010, "fence rw, rw", 0x0330000F)]
        status, out = self.run_case(*self.tail_case(tail))
        self.assertEqual(status, 1, out)

    def test_tail_register_not_used_as_base(self):
        tail = [sail_step(4, 0x80000010, "auipc x29, 0x1", 0x00001E97, ["x29 <- 0x0000000080001010"]),
                sail_step(5, 0x80000014, "sw x0, 0x4(x30)", 0x000F2223,
                          [f"mem[W,0x{HTIF + 4:016X}] <- 0x00000000"])]
        status, out = self.run_case(*self.tail_case(tail))
        self.assertEqual(status, 1, out)

    def test_reset_register_rewritten(self):
        # Sail's reset sets x11; then Sail writes the same value again while
        # Jolt writes 0. The write ends the reset exemption.
        s, j = straight(2)
        s[1] = s[1] + ["x11 <- 0x0000000000001000"]
        sail = sail_trace(s).replace("Entry point: 0x80000000",
                                     "Entry point: 0x80000000\nx11 <- 0x0000000000001000")
        rec = json.loads(j[1])
        rec["x"]["11"] = "0x0000000000000000"
        j[1] = json.dumps(rec)
        status, out = self.run_case(sail, "\n".join(j + [EXIT]) + "\n")
        self.assertEqual(status, 1, out)

    def test_reset_register_unread(self):
        s, j = straight(2)
        sail = sail_trace(s).replace("Entry point: 0x80000000",
                                     "Entry point: 0x80000000\nx11 <- 0x0000000000001000")
        status, out = self.run_case(sail, "\n".join(j + [EXIT]) + "\n")
        self.assertEqual(status, 0, out)

    def test_both_reach_limit(self):
        s, j = straight(3)
        status, out = self.run_case(sail_trace(s[:3], end=None),
                                    "\n".join(j[:3] + ['{"end":"limit"}']) + "\n",
                                    args=("--limit", "3"))
        self.assertEqual(status, 2, out)

    def test_zero_limit_rejected(self):
        status, out = self.run_case(*self.agree_case(), args=("--limit", "0"))
        self.assertEqual(status, 2, out)

    def test_timeout(self):
        status, out = self.run_case(*self.agree_case(), args=("--timeout", "1"), sleep=3)
        self.assertEqual(status, 2, out)

    def test_reset_bits_swapped(self):
        # mstatus bit 3 (MIE): Sail resets it to 1, Jolt to 0; then both flip.
        s, j = straight(2)
        s[1] = s[1] + ["CSR mstatus (0x300) <- 0x0000000000000000"]
        sail = sail_trace(s).replace("CSR mstatus (0x300) <- 0x0000000000001800",
                                     "CSR mstatus (0x300) <- 0x0000000000000008", 1)
        lines = j + [EXIT]
        rec = json.loads(lines[1])
        rec["csr"] = {"mstatus": "0x0000000000000008"}
        lines[1] = json.dumps(rec)
        status, out = self.run_case(sail, "\n".join(lines) + "\n")
        self.assertEqual(status, 1, out)

    def policy_case(self, extra_x=None, jolt_end=EXIT, jolt_next=None, reset=()):
        """Both runs set x8 = BUF, x5 = 0x42 and x9 = BUF, then LR.W at (x9)
        and SC.D of x5 at (x8): Sail's SC succeeds, Jolt's fails. RESET lists
        registers among x8 (the SC address), x5 (the SC value) and x9 (the LR
        address) that the guest does not set; Sail's reset sets them instead,
        so only Sail has the value."""
        pc = 0x80000000
        init = {8: BUF, 5: 0x42, 9: BUF}
        common = [r for r in (8, 5, 9) if r not in reset]
        s, j = [], []
        for n, r in enumerate(common):
            s.append(sail_step(n, pc, f"addi x{r}, x0, 0x1", effects=[f"x{r} <- 0x{init[r]:016X}"]))
            j.append(jolt_step(n, pc, pc + 4, x={r: init[r]}))
            pc += 4
        n = len(common)
        s += [sail_step(n, pc, "lr.w x6, (x9)", 0x1004A32F, ["x6 <- 0x0000000000000000"]),
              sail_step(n + 1, pc + 4, "sc.d x7, x5, (x8)", 0x1854332F,
                        ["x7 <- 0x0000000000000000", f"mem[W,0x{BUF:016X}] <- 0x0000000000000042"]),
              sail_step(n + 2, pc + 8, "sd x31, 0x0(x30)", 0x01FF3023, STORE_EXIT)]
        sail = sail_trace(s).replace(
            "Entry point: 0x80000000",
            "\n".join(["Entry point: 0x80000000"] +
                      [f"x{r} <- 0x{init[r]:016X}" for r in (8, 5, 9) if r in reset]))
        x = {7: 1}
        x.update(extra_x or {})
        j += [jolt_step(n, pc, pc + 4),
              jolt_step(n + 1, pc + 4, jolt_next or pc + 8, x=x),
              jolt_step(n + 2, pc + 8, pc + 12, mem=[(HTIF, 0, 1)])]
        return sail, "\n".join(j + [jolt_end]) + "\n"

    def test_policy(self):
        status, out = self.run_case(*self.policy_case())
        self.assertEqual(status, 3, out)

    def test_policy_sc_address_differs(self):
        status, out = self.run_case(*self.policy_case(reset=[8]))
        self.assertEqual(status, 1, out)

    def test_policy_sc_value_differs(self):
        status, out = self.run_case(*self.policy_case(reset=[5]))
        self.assertEqual(status, 1, out)

    def test_policy_lr_address_differs(self):
        status, out = self.run_case(*self.policy_case(reset=[9]))
        self.assertEqual(status, 1, out)

    def test_policy_with_unrelated_difference(self):
        status, out = self.run_case(*self.policy_case(extra_x={10: 5}))
        self.assertEqual(status, 1, out)

    def test_policy_with_next_pc_difference(self):
        status, out = self.run_case(*self.policy_case(jolt_next=0x80000100))
        self.assertEqual(status, 1, out)

    def test_policy_then_panic(self):
        # Jolt panics at the exit store, step 5 at 0x80000014.
        panic = '{"end":"panic","step":5,"pc":"0x0000000080000014","msg":"decode"}'
        sail, jolt = self.policy_case()
        lines = jolt.splitlines()
        status, out = self.run_case(sail, "\n".join(lines[:-2] + [panic]) + "\n")
        self.assertEqual(status, 1, out)

    def test_expect_code(self):
        sail, jolt = self.agree_case()
        status, out = self.run_case(sail.replace("SUCCESS", "FAILURE: 2"),
                                    jolt.replace(EXIT, '{"end":"tohost","value":"0x0000000000000005"}'),
                                    sail_rc=1, args=("--expect-code", "0"))
        self.assertEqual(status, 2, out)


if __name__ == "__main__":
    unittest.main()
