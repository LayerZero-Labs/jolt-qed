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
  * the memory bytes whose value changed,
and at the end, how each run stopped. A difference is reported at the
instruction where it first appears or changes, so a register that stays
different is reported once. The comparison stops at the first control-flow
difference, since the two runs no longer execute the same instructions after
it.

Only a run that stops through an HTIF exit command (a write to `tohost`) is
complete. A run that reaches the instruction limit, panics, halts without an
exit command or crashes is a difference, even when both runs do the same; when
both reach the limit, the result is a harness error (raise --limit).

Some things are notes, not differences:
  * integer registers that differ at reset (Sail's reset sets a0 and a1), until
    either run writes them;
  * CSR bits that differ at reset, for as long as both runs keep their reset
    values;
  * Sail privilege-mode changes and traps;
  * Jolt RAM writes at instructions where Sail stores nothing;
  * up to four instructions Sail retires after Jolt's last one, when both
    runs end with the same exit code and Jolt's last instruction stored to
    `tohost`. Those instructions must follow on from Jolt's last one without
    control flow, traps or CSR writes; each must be a store into the `tohost`
    doubleword or compute the base address of such a later store; and the
    last must be such a store. Jolt stops at the first store that makes
    `tohost` an exit command; Sail's HTIF device acts on a store to the high
    half, so riscv-tests, which store the low half first and then compute the
    address of the high half, retire two more instructions in Sail. Their
    register writes are listed.

LR/SC reservations are a spec-legal policy choice. Jolt reserves the exact
address and fails an SC wider than its LR. Sail's emulator may be more
permissive (unpatched sail-riscv reserves an 8-byte granule and does not check
the width). A run is labelled POLICY, and compared no further, when its first
difference is an aligned SC that
  * follows an aligned LR in the same 8-byte granule, with no trap and no
    other SC in between, at another address or of a smaller width,
  * reads the same address and value in both runs, as did the LR's address,
  * succeeds in Sail (rd = 0 and a store of rs2 at the SC address) and fails
    in Jolt (rd = 1 and no memory change),
  * and differs in nothing else, including the next pc;
and both runs then end through an HTIF exit command.

Usage:
  difftest.py --sail SIM --config JSON --jolt JOLT_TRACE ELF [--json OUT]
              [--limit N] [--timeout SECONDS] [--expect-code N] [--keep DIR]

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

CSRS = ("mstatus", "mtvec", "mscratch", "mepc", "mcause", "mtval")
MAX_SEGMENT = 1 << 28
MAX_TAIL = 4


class HarnessError(Exception):
    """The comparison could not be made: bad input, a tool failure, or output
    the parser does not understand."""


def load_elf(path):
    """Return {address: byte} for the PT_LOAD segments of a 64-bit LE ELF."""
    with open(path, "rb") as f:
        data = f.read()
    if len(data) < 64 or data[:4] != b"\x7fELF" or data[4] != 2 or data[5] != 1:
        raise HarnessError(f"{path}: not a 64-bit little-endian ELF")
    phoff, = struct.unpack_from("<Q", data, 0x20)
    phentsize, phnum = struct.unpack_from("<HH", data, 0x36)
    if phentsize < 56 or phoff + phnum * phentsize > len(data):
        raise HarnessError(f"{path}: program headers lie outside the file")
    mem = {}
    for i in range(phnum):
        p_type, _, p_offset, p_vaddr, _, p_filesz, p_memsz = struct.unpack_from(
            "<IIQQQQQ", data, phoff + i * phentsize)
        if p_type != 1:
            continue
        if p_filesz > p_memsz or p_offset + p_filesz > len(data) or p_memsz > MAX_SEGMENT:
            raise HarnessError(f"{path}: malformed PT_LOAD segment {i}")
        for k in range(p_memsz):
            mem[p_vaddr + k] = data[p_offset + k] if k < p_filesz else 0
    return mem


class Step:
    def __init__(self, pc, insn="", priv="M", enc=None):
        self.pc = pc
        self.next = None
        self.insn = insn
        self.priv = priv
        self.enc = enc       # instruction encoding as Sail prints it (hex digits)
        self.event = None    # Sail only: "fetch fault" or "interrupt" step
        self.x = {}          # register index -> value written
        self.csr = {}        # CSR name -> value written
        self.writes = []     # (address, width, value) or (address, pre, post)
        self.trap = None
        self.resv = {}


def run(cmd, timeout, log):
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        raise HarnessError(f"{os.path.basename(cmd[0])} ran longer than {timeout} s")
    if log:
        with open(log, "w") as f:
            f.write(proc.stdout + proc.stderr)
    return proc


H = r"0x([0-9A-Fa-f]+)"
STEP_RE = re.compile(rf"^\[(\d+)\] \[(\w+)\]: {H} \({H}\) (.*?)\s*(\S+\+\d+)?$")
XW_RE = re.compile(rf"^x(\d+) <- {H}$")
CSRW_RE = re.compile(rf"^CSR (\w+) \({H}\) <- {H}$")
CSRR_RE = re.compile(rf"^CSR (\w+) \({H}\) -> {H}$")
MEM_RE = re.compile(rf"^mem\[(X|R|W|RW),{H}\] (<-|->) {H}$")
TRAP_RE = re.compile(rf"^handling (exc|int)#(\S+) at priv (\w+) with tval {H}$")
IGNORED_RE = re.compile(r"^(trapping from \w+ to \w+ to handle \S+|ret-ing from \w+ to \w+"
                        r"|Handling interrupt: .*)$")
PREAMBLE_RE = re.compile(rf"^(HTIF located at|Entry point:|begin_signature:|end_signature:) {H}$")
HTIF_IGNORED_RE = re.compile(rf"^htif-\?\?\?\? cmd: {H}")
FAILURE_RE = re.compile(r"^FAILURE: (\d+)$")


def run_sail(sim, config, elf, limit, timeout, log):
    """Run Sail and parse its trace strictly: every line must be understood,
    steps must be numbered consecutively, and the process status must match
    how the trace ends."""
    cmd = [sim, "--config", config, "--trace-instr", "--trace-reg", "--trace-mem",
           "--trace-exception", "--inst-limit", str(limit), elf]
    proc = run(cmd, timeout, log)
    if proc.stderr.strip():
        raise HarnessError(f"Sail wrote to stderr: {proc.stderr.strip().splitlines()[-1]}")
    steps, end, reset, info, notes = [], None, {"csr": {}, "x": {}}, {}, []
    cur = None

    def bad(no, line, why="unrecognised line"):
        raise HarnessError(f"Sail trace line {no + 1}: {why}: {line!r}")

    for no, line in enumerate(proc.stdout.splitlines()):
        line = line.strip()
        if not line:
            continue
        if end is not None:
            bad(no, line, "line after the end of the run")
        if (m := HTIF_IGNORED_RE.match(line)):
            # Sail's HTIF prints this without a newline when it ignores a
            # command; the rest of the line is the next record.
            notes.append(f"Sail HTIF ignored tohost command 0x{int(m[1], 16):x}")
            line = line[m.end():]
            if not line:
                continue
        if (m := STEP_RE.match(line)):
            number = int(m[1])
            if number != len(steps):
                # A fetch fault or interrupt that Sail does not count as a step
                # belongs to the instruction before it.
                if (number == len(steps) - 1 and steps and steps[-1].event
                        and len(steps) >= 2 and steps[-2].trap is None):
                    ev = steps.pop()
                    steps[-1].trap, steps[-1].csr = ev.trap, {**steps[-1].csr, **ev.csr}
                else:
                    bad(no, line, f"expected instruction number {len(steps)}")
            if steps and steps[-1].pc is None:
                bad(no, line, "a trap step without an mepc write")
            cur = Step(int(m[3], 16), m[5].strip(), m[2], m[4])
            steps.append(cur)
            continue
        if line == "SUCCESS":
            end = {"kind": "tohost", "code": 0}
            continue
        if (m := FAILURE_RE.match(line)):
            end = {"kind": "tohost", "code": int(m[1])}
            continue
        if (m := MEM_RE.match(line)):
            if m[1] in ("W", "RW") and m[3] == "<-":
                if cur is None:
                    bad(no, line, "store before the first instruction")
                cur.writes.append((int(m[2], 16), len(m[4]) // 2, int(m[4], 16)))
            elif m[3] != "->":
                bad(no, line)
            continue
        if (m := CSRR_RE.match(line)) or IGNORED_RE.match(line):
            continue
        if cur is None:
            # Reset writes happen before the first instruction.
            if (m := CSRW_RE.match(line)):
                reset["csr"][m[1]] = int(m[3], 16)
            elif (m := XW_RE.match(line)):
                reset["x"][int(m[1])] = int(m[2], 16)
            elif (m := PREAMBLE_RE.match(line)):
                info[m[1].rstrip(":")] = int(m[2], 16)
            else:
                bad(no, line)
            continue
        if (m := XW_RE.match(line)):
            if int(m[1]) != 0:
                cur.x[int(m[1])] = int(m[2], 16)
        elif (m := CSRW_RE.match(line)):
            cur.csr[m[1]] = int(m[3], 16)
            if m[1] == "mepc" and cur.event and cur.pc is None:
                cur.pc = int(m[3], 16)
        elif (m := TRAP_RE.match(line)):
            trap = f"{m[1]}#{m[2]} tval=0x{int(m[4], 16):x}"
            if m[1] == "int" or m[2].startswith("fetch-") or m[2] == "misaligned-fetch":
                # Taken before the next instruction executes: its own step.
                cur = Step(None, f"<{'interrupt' if m[1] == 'int' else 'fetch fault'}>")
                cur.event = "interrupt" if m[1] == "int" else "fetch fault"
                cur.trap = trap
                steps.append(cur)
            elif cur.trap is not None:
                bad(no, line, "a second trap in one instruction")
            else:
                cur.trap = trap
        else:
            bad(no, line)
    if steps and steps[-1].pc is None:
        raise HarnessError("Sail trace ends in a trap step without an mepc write")
    if not steps:
        raise HarnessError(f"Sail retired no instructions (exit {proc.returncode}): "
                           + " | ".join(proc.stdout.strip().splitlines()[-3:]))
    for a, b in zip(steps, steps[1:]):
        a.next = b.pc
    if end is None:
        if proc.returncode != 0:
            end = {"kind": "crash", "status": proc.returncode}
        elif len(steps) == limit:
            end = {"kind": "limit"}
        else:
            raise HarnessError(f"Sail stopped after {len(steps)} of {limit} instructions "
                               "without an exit and with status 0")
    elif proc.returncode != (0 if end["code"] == 0 else 1):
        end = {"kind": "crash", "status": proc.returncode, "after": dict(end)}
    if end["kind"] == "tohost" and "HTIF located at" not in info:
        raise HarnessError("Sail exited through HTIF but did not print its address")
    return {"steps": steps, "end": end, "reset": reset, "htif": info.get("HTIF located at"),
            "notes": notes}


def hexval(rec, key):
    v = rec[key]
    if not isinstance(v, str) or not v.startswith("0x"):
        raise HarnessError(f"jolt-trace: {key} is not a hex string: {v!r}")
    return int(v, 16)


def hexmap(rec, key, keytype):
    v = rec[key]
    if not isinstance(v, dict):
        raise HarnessError(f"jolt-trace: {key} is not an object")
    return {keytype(k): hexval(v, k) for k in v}


def run_jolt(binary, elf, limit, timeout, log):
    """Run jolt-trace and validate its JSON lines: one record per step,
    numbered from 0, then exactly one end record."""
    proc = run([binary, elf, "--limit", str(limit)], timeout, log)
    lines = proc.stdout.splitlines()
    if proc.returncode != 0:
        if not lines:
            raise HarnessError(f"jolt-trace exited with status {proc.returncode} and no output: "
                               + " | ".join(proc.stderr.strip().splitlines()[-3:]))
    crash = proc.returncode != 0
    end = None
    steps = []
    for no, line in enumerate(lines):
        try:
            rec = json.loads(line)
        except json.JSONDecodeError as e:
            raise HarnessError(f"jolt-trace line {no + 1}: {e}")
        if not isinstance(rec, dict):
            raise HarnessError(f"jolt-trace line {no + 1}: not an object")
        if end is not None:
            raise HarnessError(f"jolt-trace line {no + 1}: output after the end record")
        try:
            if "end" in rec:
                kind = rec["end"]
                end = {"kind": kind}
                if kind == "tohost":
                    value = hexval(rec, "value")
                    if value >> 48 or not value & 1:
                        raise HarnessError(f"jolt-trace: 0x{value:x} is not an HTIF exit command")
                    end["code"] = (value & ((1 << 48) - 1)) >> 1
                elif kind == "stall-tohost":
                    end["value"] = hexval(rec, "value")
                elif kind == "halt":
                    end["pc"] = hexval(rec, "pc")
                elif kind == "panic":
                    end["msg"] = rec["msg"]
                    end["pc"] = hexval(rec, "pc")
                    if rec["step"] != len(steps):
                        raise HarnessError("jolt-trace: panic record at the wrong step")
                elif kind != "limit":
                    raise HarnessError(f"jolt-trace: unknown end {kind!r}")
                continue
            if rec["step"] != len(steps):
                raise HarnessError(f"jolt-trace line {no + 1}: step {rec['step']}, "
                                   f"expected {len(steps)}")
            s = Step(hexval(rec, "pc"))
            s.next = hexval(rec, "next")
            s.x = hexmap(rec, "x", int)
            s.csr = hexmap(rec, "csr", str)
            s.resv = hexmap(rec, "resv", int)
            if not isinstance(rec["mem"], list):
                raise HarnessError("jolt-trace: mem is not a list")
            s.writes = []
            for w in rec["mem"]:
                if not isinstance(w, list) or len(w) != 3:
                    raise HarnessError("jolt-trace: a mem entry is not [address, pre, post]")
                s.writes.append(tuple(hexval(dict(enumerate(w)), k) for k in range(3)))
        except KeyError as e:
            raise HarnessError(f"jolt-trace line {no + 1}: missing field {e}")
        if not all(0 < r < 32 for r in s.x) or not set(s.csr) <= set(CSRS):
            raise HarnessError(f"jolt-trace line {no + 1}: unknown register")
        steps.append(s)
    if crash:
        # The tracer died outside the panic handler (an abort, say).
        end = {"kind": "crash", "status": proc.returncode,
               "tail": proc.stderr.strip().splitlines()[-3:]}
    elif end is None:
        raise HarnessError("jolt-trace printed no end record")
    if end["kind"] == "limit" and len(steps) != limit:
        raise HarnessError(f"jolt-trace reports the limit after {len(steps)} of {limit} steps")
    return {"steps": steps, "end": end}


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


# LR/SC as Sail disassembles them, such as "sc.d.aq x23, x6, (x8)".
LRSC_RE = re.compile(r"^(lr|sc)\.([wd])(?:\.\w+)*\s+x(\d+),\s*(?:x(\d+),\s*)?\(x(\d+)\)$")
# Instructions after which the next pc is not pc + length.
CONTROL_RE = re.compile(r"^(c\.)?(j|jal|jalr|jr|ret|b\w+|mret|sret|ecall|ebreak|wfi)\b")
# A store, with its base register.
STORE_RE = re.compile(r"^(?:c\.)?s[bhwd]\s+x\d+,\s*-?(?:0x[0-9a-f]+|\d+)\(x(\d+)\)$")
# Instructions that form an address in a register, without reading memory.
ADDRESS_RE = re.compile(r"^(?:c\.)?(auipc|lui|addi|li)\s+x(\d+),")


def fall_through(step):
    """The next pc of Sail's last instruction, which no later instruction
    header gives: pc + length for an instruction that cannot jump or trap."""
    if step.trap or step.event or CONTROL_RE.match(step.insn) or step.enc is None:
        return None
    return step.pc + (2 if len(step.enc) == 4 else 4)


def end_text(end):
    return ", ".join(f"{k}=0x{v:x}" if k in ("pc", "value") else f"{k}={v}"
                     for k, v in end.items())


def compare(elf, sail, jolt, mstatus_or=0, ignore=None):
    ignore = ignore or {}
    s_steps, s_end, s_reset = sail["steps"], sail["end"], sail["reset"]
    j_steps, j_end = jolt["steps"], jolt["end"]
    mem_s = load_elf(elf)
    mem_j = dict(mem_s)
    # Sail traces the registers its reset sets; Jolt's start at zero.
    xs, xj = [0] * 32, [0] * 32
    for r, v in s_reset["x"].items():
        if 0 < r < 32:
            xs[r] = v
    # Sail traces the CSRs its reset sets; the others reset to zero. Jolt's
    # virtual registers start at zero.
    cs, cj = {c: s_reset["csr"].get(c, 0) for c in CSRS}, {c: 0 for c in CSRS}
    reported = {}
    diffs, notes = [], list(sail["notes"])
    # Registers that differ at reset are a note, until either run writes
    # them: a guest sees one only by reading it, which shows in a compared
    # register, memory or control flow.
    exempt_x = {r for r in range(1, 32) if xs[r]}
    for r in sorted(exempt_x):
        notes.append(f"reset: x{r} Sail 0x{xs[r]:x}, Jolt 0x0")

    def view_of(cj):
        return dict(cj, mstatus=cj["mstatus"] | mstatus_or)

    # CSR bits that differ at reset are a note, not a difference, for as long
    # as both runs keep their reset values there: a guest sees them only by
    # reading the CSR (and the register it reads into is compared) or through
    # control flow (also compared). Once either run changes such a bit, it is
    # compared like any other.
    view0 = view_of(cj)
    exempt, reset_s, reset_j = {}, dict(cs), dict(view0)
    for c in CSRS:
        exempt[c] = (cs[c] ^ view0[c]) & ~ignore.get(c, 0)
        if exempt[c]:
            notes.append(f"reset: {c} Sail 0x{cs[c]:x}, Jolt 0x{view0[c]:x} "
                         f"(differ in 0x{exempt[c]:x})")

    n = min(len(s_steps), len(j_steps))
    stopped = policy = None
    resv = None     # (address, width) of Sail's last LR, while no SC or trap has followed
    for i in range(n):
        s, j = s_steps[i], j_steps[i]
        where = f"step {i} pc=0x{s.pc:x} [{s.insn}]"
        if s.pc != j.pc:
            stopped = f"{where}: Sail pc 0x{s.pc:x}, Jolt pc 0x{j.pc:x}"
            diffs.append("control flow: " + stopped)
            n = i
            break
        step = []    # (tag, text) of this step's differences

        def report(key, pair, text):
            if reported.get(key) != pair:
                reported[key] = pair
                if pair is not None:
                    step.append((key, text))

        # An LR or SC's operands, read before its effects; same_operands says
        # whether both runs read the same address (and, for an SC, value).
        lrsc = LRSC_RE.match(s.insn)
        if lrsc:
            rs1 = int(lrsc[5])
            addr, width = xs[rs1], 4 if lrsc[2] == "w" else 8
            same_operands = xs[rs1] == xj[rs1]
            if lrsc[1] == "sc":
                rs2 = int(lrsc[4])
                stored = xs[rs2] & ((1 << (8 * width)) - 1)
                same_operands = same_operands and xs[rs2] == xj[rs2]
        if s.priv != "M":
            notes.append(f"{where}: Sail runs in privilege {s.priv}")
        if s.trap:
            notes.append(f"{where}: Sail trap {s.trap}")
        for r, v in s.x.items():
            xs[r] = v
        for r, v in j.x.items():
            xj[r] = v
        exempt_x -= set(s.x) | set(j.x)
        for r in range(1, 32):
            pair = (xs[r], xj[r]) if xs[r] != xj[r] and r not in exempt_x else None
            report(("x", r), pair, f"{where}: x{r} Sail 0x{xs[r]:x}, Jolt 0x{xj[r]:x}")
        for c, v in s.csr.items():
            if c in cs:
                cs[c] = v
        for c, v in j.csr.items():
            cj[c] = v
        view = view_of(cj)
        for c in CSRS:
            exempt[c] &= ~((cs[c] ^ reset_s[c]) | (view[c] ^ reset_j[c]))
            # Keyed on the differing bits, so a constant difference (such as
            # the read-only mstatus.UXL/SXL fields) is reported once.
            xor = (cs[c] ^ view[c]) & ~ignore.get(c, 0) & ~exempt[c]
            report(("csr", c), xor or None,
                   f"{where}: {c} Sail 0x{cs[c]:x}, Jolt 0x{view[c]:x} (differ in 0x{xor:x})")
        changed_s = {a: b for a, b in sail_bytes(s.writes).items() if mem_s.get(a, 0) != b}
        changed_j = {a: b for a, b in jolt_bytes(j.writes).items() if mem_j.get(a, 0) != b}
        mem_s.update(changed_s)
        mem_j.update(changed_j)
        if changed_s != changed_j:
            step.append(("mem", f"{where}: memory Sail {fmt_bytes(changed_s)}, "
                                f"Jolt {fmt_bytes(changed_j)}"))
        if j.writes and not s.writes:
            ws = ", ".join(f"0x{a:x}: 0x{pre:x} -> 0x{post:x}" for a, pre, post in j.writes)
            notes.append(f"{where}: Jolt RAM write with no Sail store ({ws})")
        s_next = s.next if s.next is not None else fall_through(s) if i == len(s_steps) - 1 else None
        if s_next is None and i == len(s_steps) - 1 and s_end["kind"] == "tohost":
            step.append(("next", f"{where}: Sail's next pc after its last instruction is unknown"))
        elif s_next is not None and s_next != j.next:
            step.append(("next", f"{where}: next pc Sail 0x{s_next:x}, Jolt 0x{j.next:x}"))

        if lrsc and lrsc[1] == "sc" and same_operands and not diffs and step and is_policy_sc(
                lrsc, addr, width, stored, resv, s, changed_j, xs, xj, step):
            policy = (f"{where}: SC succeeds in Sail and fails in Jolt after an LR "
                      f"of {resv[1]} bytes at 0x{resv[0]:x} (spec-legal reservation "
                      "policy, compared no further)")
            stopped = policy
            n = i + 1
            break
        diffs += [text for _, text in step]
        if s.trap or s.event:
            resv = None
        elif lrsc:
            resv = (addr, width) if lrsc[1] == "lr" and same_operands else None
        if any(tag == "next" for tag, _ in step):
            stopped = "next pc"
            n = i + 1
            break

    if stopped is None:
        tail_ok = False
        if len(s_steps) > n and s_end["kind"] == j_end["kind"] == "tohost" \
                and s_end["code"] == j_end["code"]:
            tail_ok = valid_tail(s_steps[n:], j_steps, sail["htif"], xs, notes)
        if tail_ok:
            notes.append(f"Sail retired {len(s_steps) - n} more instruction(s) after Jolt's "
                         "exit, writing only tohost, before the same tohost exit")
        elif len(s_steps) != len(j_steps):
            diffs.append(f"length: Sail retired {len(s_steps)} instructions, Jolt {len(j_steps)}")
            if len(s_steps) > n:
                s = s_steps[n]
                notes.append(f"step {n} pc=0x{s.pc:x} [{s.insn}]: Sail continues"
                             + (f" with trap {s.trap}" if s.trap else ""))
        if (s_end["kind"], s_end.get("code")) != (j_end["kind"], j_end.get("code")):
            diffs.append(f"end: Sail {end_text(s_end)}; Jolt {end_text(j_end)}")
        elif s_end["kind"] == "limit":
            raise HarnessError(f"both runs reached the instruction limit ({len(s_steps)}); "
                               "raise --limit")
        elif s_end["kind"] != "tohost":
            diffs.append(f"end: neither run exits through tohost (both {s_end['kind']})")
    elif policy and not (s_end["kind"] == j_end["kind"] == "tohost"):
        diffs.append(f"end after the reservation-policy SC: Sail {end_text(s_end)}; "
                     f"Jolt {end_text(j_end)}")
    return diffs, notes, n, policy


def is_policy_sc(lrsc, addr, width, stored, resv, s, changed_j, xs, xj, step):
    """Whether this SC's differences are exactly those of a spec-legal
    reservation policy: Sail keeps a reservation that Jolt does not have.
    The caller has checked that both runs read the same SC operands, and
    `resv` is set only by an LR whose address both runs read the same."""
    rd = int(lrsc[3])
    if not resv or addr % width or resv[0] % resv[1] or s.trap:
        return False
    if resv[0] // 8 != addr // 8 or (resv[0] == addr and resv[1] >= width):
        return False
    if s.writes != [(addr, width, stored)] or changed_j:
        return False
    tags = {tag for tag, _ in step}
    if rd:
        return xs[rd] == 0 and xj[rd] == 1 and tags <= {("x", rd), "mem"} and ("x", rd) in tags
    return tags == {"mem"}


def valid_tail(tail, j_steps, htif, xs, notes):
    """Whether the instructions Sail retires after Jolt's exit store finish
    the same HTIF exit: at most MAX_TAIL M-mode instructions that follow on
    from Jolt's last one and from each other, with no trap, no CSR write and
    no control flow. Each is either a store into the tohost doubleword, or an
    address computation (AUIPC, LUI, ADDI, LI) into a register that a later
    store of the tail uses as its base. The last one is such a store, which
    is what makes Sail act on tohost. Jolt's last instruction must itself have
    written tohost. The registers the tail writes are listed as notes; Jolt
    never runs those instructions."""
    if htif is None or not j_steps or not tail or len(tail) > MAX_TAIL:
        return False
    if not any(a <= htif < a + 8 for a, _, _ in j_steps[-1].writes):
        return False
    pc = j_steps[-1].next
    for k, s in enumerate(tail):
        if s.pc != pc or s.trap or s.event or s.priv != "M" or s.csr:
            return False
        pc = fall_through(s)
        if pc is None or (s.next is not None and s.next != pc):
            return False
        store, address = STORE_RE.match(s.insn), ADDRESS_RE.match(s.insn)
        if store:
            if s.x or not s.writes or any(
                    not htif <= a < htif + 8 for a in sail_bytes(s.writes)):
                return False
        elif address:
            rd = int(address[2])
            later_bases = {m[1] for m in map(STORE_RE.match, (t.insn for t in tail[k + 1:])) if m}
            if s.writes or set(s.x) != {rd} or str(rd) not in later_bases:
                return False
        else:
            return False
    if not STORE_RE.match(tail[-1].insn):
        return False
    for s in tail:
        for r, v in s.x.items():
            if xs[r] != v:
                notes.append(f"pc=0x{s.pc:x} [{s.insn}]: after Jolt's exit Sail sets x{r} = 0x{v:x}")
    return True


def fmt_bytes(b):
    if not b:
        return "{}"
    return "{" + ", ".join(f"0x{a:x}=0x{v:02x}" for a, v in sorted(b.items())) + "}"


def positive(v):
    n = int(v, 0)
    if n <= 0:
        raise argparse.ArgumentTypeError("must be positive")
    return n


def csr_mask(v):
    c, sep, m = v.partition("=")
    if not sep or c not in CSRS:
        raise argparse.ArgumentTypeError(f"expected CSR=MASK with CSR one of {', '.join(CSRS)}")
    return c, int(m, 0)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("elf")
    ap.add_argument("--sail", required=True, help="sail_riscv_sim binary")
    ap.add_argument("--config", required=True, help="Sail configuration JSON")
    ap.add_argument("--jolt", required=True, help="jolt-trace binary")
    ap.add_argument("--limit", type=positive, default=100000,
                    help="instruction limit (positive; default 100000)")
    ap.add_argument("--timeout", type=positive, default=600,
                    help="seconds each simulator may run (default 600); longer is a harness error")
    ap.add_argument("--expect-code", type=int,
                    help="exit code the guest must end with; when both runs agree on another "
                         "code, the guest did not do what it should and the result is a harness "
                         "error")
    ap.add_argument("--json", help="write the result as JSON to this file")
    ap.add_argument("--ignore-bits", action="append", default=[], type=csr_mask, metavar="CSR=MASK",
                    help="leave these bits of CSR out of the comparison (repeatable)")
    ap.add_argument("--jolt-mstatus-or", type=lambda v: int(v, 0), default=0,
                    help="bits Jolt ORs into virtual register 39 when it reads mstatus "
                         "(0x1800 on Jolt versions that keep only MIE and MPIE there)")
    ap.add_argument("--keep", help="keep both raw traces in this directory")
    a = ap.parse_args()
    try:
        logs = (None, None)
        if a.keep:
            os.makedirs(a.keep, exist_ok=True)
            base = os.path.join(a.keep, os.path.splitext(os.path.basename(a.elf))[0])
            logs = (base + ".sail.log", base + ".jolt.jsonl")
        load_elf(a.elf)
        sail = run_sail(a.sail, a.config, a.elf, a.limit, a.timeout, logs[0])
        jolt = run_jolt(a.jolt, a.elf, a.limit, a.timeout, logs[1])
        ignore = {}
        for c, m in a.ignore_bits:
            ignore[c] = ignore.get(c, 0) | m
        diffs, notes, n, policy = compare(a.elf, sail, jolt, a.jolt_mstatus_or, ignore)
        s_end, j_end = sail["end"], jolt["end"]
        if a.expect_code is not None:
            codes = {e.get("code") for e in (s_end, j_end) if e["kind"] == "tohost"}
            if policy and codes != {a.expect_code}:
                diffs.append(f"exit codes after the reservation-policy SC: Sail "
                             f"{end_text(s_end)}; Jolt {end_text(j_end)}; expected {a.expect_code}")
            elif not diffs and not policy and codes != {a.expect_code}:
                raise HarnessError(f"both runs exit with {end_text(s_end)}, but the guest "
                                   f"should exit with code {a.expect_code}")
        name = os.path.basename(a.elf)
        verdict = "DIFFER" if diffs else "POLICY" if policy else "AGREE"
        if a.json:
            with open(a.json, "w") as f:
                json.dump({"elf": name, "verdict": verdict, "compared": n, "policy": policy,
                           "diffs": diffs, "notes": notes, "sail_end": s_end, "jolt_end": j_end},
                          f, indent=2)
    except Exception as e:
        print(f"difftest: {a.elf}: {e}", file=sys.stderr)
        return 2
    print(f"== {name}: {verdict} ({n} instructions compared)")
    print(f"   end: Sail {end_text(s_end)}; Jolt {end_text(j_end)}")
    if policy:
        print(f"   policy  {policy}")
    for d in diffs:
        print(f"   diff  {d}")
    for t in notes:
        print(f"   note  {t}")
    return 1 if diffs else 3 if policy else 0


if __name__ == "__main__":
    sys.exit(main())
