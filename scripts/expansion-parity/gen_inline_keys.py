#!/usr/bin/env python3
"""Generate the supported inline keys and their row checks.

The script writes two files:

- JoltBytecode/Inlines/Keys.lean: the type `InlineKey` of supported registered
  inlines, each key's encoding (opcode, funct3, funct7), its generated rows for both
  allocation cases, its row count, and whether its rows read the source `rd` (`rs3`).
- JoltConstraints/inline_rows_ok.lean: for every key and allocation case, the
  per-row check `ExpansionFacts.inlineRowOk` on each generated chunk, proved by
  `rfl`, and the assembled facts `InlineKey.rows_ok` and `InlineKey.rowsRdZero_ok`.

The encodings come from the expansion-parity driver's `inline_templates.json`
(written by `scripts/expansion-parity/run.sh` to WORK_DIR/out). The rows come from
JoltBytecode/Inlines/Generated/<Name>.lean, which the same driver run writes. The
script checks that both name the same Jolt commit.

`readsRd` is computed from the generated rows: a key reads `rs3` exactly when some
generated chunk of its `rd != x0` case takes `rs3` as a used parameter (the driver
renders an unused parameter as `_rs3`).

Supporting another inline adds its driver name to SUPPORTED and regenerates.

Usage, from the repository root:

    python3 scripts/expansion-parity/gen_inline_keys.py [--templates PATH]
    python3 scripts/expansion-parity/gen_inline_keys.py --check [--templates PATH]

PATH defaults to ~/claude-work/expansion-parity-work/out/inline_templates.json.
`--check` exits 1 if either file differs from what the script would write.
After regenerating, build with
`lake build JoltBytecode.Inlines.Keys JoltConstraints.inline_rows_ok`.
"""
import json, pathlib, re, sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
KEYS = ROOT / "JoltBytecode/Inlines/Keys.lean"
CHECKS = ROOT / "JoltConstraints/inline_rows_ok.lean"
DEFAULT_TEMPLATES = pathlib.Path.home() / "claude-work/expansion-parity-work/out/inline_templates.json"

# Driver names of the supported inlines, in the order of the `InlineKey` constructors.
SUPPORTED = [
    "SHA256_INLINE",
    "SHA256_INIT_INLINE",
    "KECCAK256_INLINE",
    "KECCAK256_ABSORB_PERMUTE_INLINE",
    "BLAKE2_INLINE",
]


def fail(message):
    print(f"gen_inline_keys: {message}", file=sys.stderr)
    sys.exit(2)


args = sys.argv[1:]
check = "--check" in args
templates = DEFAULT_TEMPLATES
if "--templates" in args:
    templates = pathlib.Path(args[args.index("--templates") + 1])
if not templates.exists():
    fail(f"{templates} not found; run scripts/expansion-parity/run.sh first or pass --templates")
data = json.loads(templates.read_text())
by_name = {inline["name"]: inline for inline in data["inlines"]}
commit = data["jolt_commit"]

keys = []
for name in SUPPORTED:
    inline = by_name.get(name) or fail(f"{name} is not in {templates}")
    base = inline["lean_def"].rsplit(".", 1)[1]
    if not base.endswith("RowsAuto"):
        fail(f"unexpected lean_def {inline['lean_def']}")
    base = base[: -len("RowsAuto")]
    source = (ROOT / inline["lean_file"]).read_text()
    if commit not in source:
        fail(f"{inline['lean_file']} was not generated from Jolt commit {commit}")
    if set(inline["cases"]) != {"normal", "rd_zero"}:
        fail(f"{name}: expected the cases normal and rd_zero")
    chunks = {}
    used_rs3 = False
    for case, suffix in (("normal", ""), ("rd_zero", "RdZero")):
        pattern = re.compile(
            rf"^def {base}RowsAuto{suffix}Chunk(\d+) \(([^)]*) : regidx\) : List JoltISA\.Instr := \[$"
            r"(.*?)^\]$",
            re.M | re.S,
        )
        found = [(int(n), params, body) for n, params, body in pattern.findall(source)]
        if not found or [n for n, _, _ in found] != list(range(len(found))):
            fail(f"{name}: chunks of {base}RowsAuto{suffix} not found in order")
        lengths = []
        for _, params, body in found:
            rows = [line for line in body.splitlines() if line.startswith("  .")]
            lengths.append(len(rows))
            if case == "normal" and "rs3" in params.split():
                used_rs3 = True
        expected = len(inline["cases"][case]["rows"])
        if sum(lengths) != expected:
            fail(f"{name} {case}: {sum(lengths)} rows in Lean, {expected} in the driver output")
        chunks[case] = lengths
    keys.append(
        dict(
            name=name,
            base=base,
            module=pathlib.Path(inline["lean_file"]).stem,
            opcode=inline["opcode"],
            funct3=inline["funct3"],
            funct7=inline["funct7"],
            reads_rd=used_rs3,
            chunks=chunks,
        )
    )

for k in keys:
    if k["opcode"] != 0x0B:
        fail(f"{k['name']}: opcode {k['opcode']:#x}, expected 0x0b")
pairs = [(k["funct3"], k["funct7"]) for k in keys]
if len(set(pairs)) != len(pairs):
    fail("two supported keys share an encoding")


def lean_bool(b):
    return "true" if b else "false"


# ---------------------------------------------------------------- Keys.lean
out = []
for k in keys:
    out.append(f"import JoltBytecode.Inlines.Generated.{k['module']}")
out.append(f'''
/-!
# Supported registered inlines

Generated by `scripts/expansion-parity/gen_inline_keys.py` from the expansion-parity
driver's output at a16z/jolt commit `{commit}`; do not edit by hand.

`InlineKey` lists the registered inlines that jolt-qed supports. Each key has Jolt's
encoding `(opcode, funct3, funct7)`, the generated rows of its two allocation cases
(`rd ≠ x0` and `rd = x0`), and its row count. Jolt's decoder stores an inline's `rd`
in the `rs3` slot (jolt/crates/jolt-program/src/image/decode.rs at the pin).
`readsRd` records whether the rows read `rs3`; the generator computes it from the
generated rows.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D
  LeanRV64D.Functions

set_option autoImplicit false

namespace JoltISA.Inlines

/-- A registered inline that jolt-qed supports.
Example: `InlineKey.keccak256AbsorbPermute` is Jolt's
`KECCAK256_ABSORB_PERMUTE_INLINE`, encoded with opcode `0x0B`, funct3 1, funct7 1. -/
inductive InlineKey where''')
for k in keys:
    out.append(f"  /-- `{k['name']}`: funct3 {k['funct3']}, funct7 {k['funct7']}. -/")
    out.append(f"  | {k['base']}")
out.append("  deriving DecidableEq, Repr")
out.append("")
out.append("namespace InlineKey")
out.append("")
out.append("/-- Every supported key, in constructor order.\nExample: the first is `sha256`. -/")
out.append("def all : List InlineKey :=\n  [" + ", ".join(f".{k['base']}" for k in keys) + "]")
out.append("")
out.append("/-- Jolt's name for the inline.\nExample: `sha256.name = \"SHA256_INLINE\"`. -/")
out.append("def name : InlineKey → String")
for k in keys:
    out.append(f"  | .{k['base']} => \"{k['name']}\"")
out.append("")
out.append("/-- The major opcode; every registered inline uses `0x0B`.\nExample: `blake2.opcode = 0x0B`. -/")
out.append("def opcode : InlineKey → BitVec 7")
for k in keys:
    out.append(f"  | .{k['base']} => {k['opcode']:#04x}")
out.append("")
out.append("/-- The `funct3` field of the encoding.\nExample: `sha256Init.funct3 = 1`. -/")
out.append("def funct3 : InlineKey → BitVec 3")
for k in keys:
    out.append(f"  | .{k['base']} => {k['funct3']}")
out.append("")
out.append("/-- The `funct7` field of the encoding.\nExample: `keccak256.funct7 = 1`. -/")
out.append("def funct7 : InlineKey → BitVec 7")
for k in keys:
    out.append(f"  | .{k['base']} => {k['funct7']}")
out.append("")
out.append("/-- Whether the key's rows read the source `rd` (the `rs3` operand).\n"
           "Example: no hash inline reads it, so `sha256.readsRd = false`. -/")
out.append("def readsRd : InlineKey → Bool")
for k in keys:
    out.append(f"  | .{k['base']} => {lean_bool(k['reads_rd'])}")
out.append("")
out.append("/-- The number of final rows of the key's expansion, in both allocation cases.\n"
           "Example: `keccak256AbsorbPermute.rowCount = 3121`. -/")
out.append("def rowCount : InlineKey → Nat")
for k in keys:
    n = sum(k["chunks"]["normal"])
    if n != sum(k["chunks"]["rd_zero"]):
        fail(f"{k['name']}: the two allocation cases differ in length")
    out.append(f"  | .{k['base']} => {n}")
out.append("")
out.append('''/-- The supported key with this encoding, if any.
Jolt's decoder accepts any `funct3` and `funct7` under opcodes `0x0B` and `0x2B`;
the registry lookup then rejects encodings no inline registered.
Example: `ofEncoding 0x0B 1 1 = some keccak256AbsorbPermute`, and
`ofEncoding 0x2B 1 1 = none`. -/
def ofEncoding (opcode : BitVec 7) (funct3 : BitVec 3) (funct7 : BitVec 7) :
    Option InlineKey :=
  all.find? fun key => key.opcode == opcode && key.funct3 == funct3 && key.funct7 == funct7

/-- Every key is found again from its own encoding.
Example: `ofEncoding blake2.opcode blake2.funct3 blake2.funct7 = some blake2`. -/
theorem ofEncoding_self (key : InlineKey) :
    ofEncoding key.opcode key.funct3 key.funct7 = some key := by
  cases key <;> rfl
''')
out.append("/-- The rows of the `rd ≠ x0` case: the generated `<name>RowsAutoList`.\n"
           "`rs3` is the source `rd`.\n"
           "Example: the first row of `keccak256AbsorbPermute.rows x10 x11 x12` loads `vr48` from `x10`. -/")
out.append("def rows : InlineKey → regidx → regidx → regidx → List JoltISA.Instr")
for k in keys:
    out.append(f"  | .{k['base']}, rs1, rs2, rs3 =>\n    Generated.{k['base']}RowsAutoList rs1 rs2 rs3")
out.append("")
out.append("/-- The rows of the `rd = x0` case, after Rust substitutes the instruction temporary\n"
           "`vr40` for `rd`: the generated `<name>RowsAutoRdZeroList`.\n"
           "Example: `sha256.rowsRdZero x10 x11` has 1900 rows. -/")
out.append("def rowsRdZero : InlineKey → regidx → regidx → List JoltISA.Instr")
for k in keys:
    out.append(f"  | .{k['base']}, rs1, rs2 => Generated.{k['base']}RowsAutoRdZeroList rs1 rs2")
out.append('''
/-- The rows Jolt's expander emits for the inline call `rd, rs1, rs2` with this key.
With `rd = x0`, Rust allocates an instruction temporary and passes it as `rd`
(jolt/crates/jolt-program/src/expand/mod.rs, `expand_source_instruction_with_provider`).
The allocator is in its initial state between source instructions, so that temporary
is always `vr40`, and the `rd = x0` rows are the generated `rowsRdZero`.
Example: `sha256.expandRows x10 x11 x0 = sha256.rowsRdZero x10 x11`. -/
def expandRows (key : InlineKey) (rs1 rs2 rd : regidx) : List JoltISA.Instr :=
  if JoltISA.isX0 rd then key.rowsRdZero rs1 rs2 else key.rows rs1 rs2 rd

end InlineKey

end JoltISA.Inlines
''')
keys_text = "\n".join(out)

# ---------------------------------------------------------------- inline_rows_ok.lean
out = ['import JoltConstraints.expansion_checks', 'import JoltBytecode.Inlines.Keys', f'''
/-!
# Row checks of the supported inlines

Generated by `scripts/expansion-parity/gen_inline_keys.py`; do not edit by hand.

Each `_chunkN` lemma checks one generated chunk (at most 100 rows) with
`ExpansionFacts.inlineRowOk` and states its length, by `rfl`. `rfl` works although
the rows take free register parameters: no check compares two architectural
registers. Each `_rows_ok` lemma chains its key's chunk facts with
`checked_append`, `InlineKey.rows_ok` and `InlineKey.rowsRdZero_ok` collect them by
key, and `ExpansionFacts.sequenceOk_of_inlineRowsOk` turns the row checks into the
sequence checks.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D
  LeanRV64D.Functions

set_option autoImplicit false

namespace JoltISA.Inlines.InlineRowsOk

open JoltISA.Inlines.Generated ExpansionFacts

/-- Checked rows stay checked when appended, and their lengths add.
For example, two checked chunks of 100 rows give 200 checked rows. -/
theorem checked_append {{first second : List JoltISA.Instr}} {{m k : Nat}}
    (firstOk : first.all inlineRowOk = true ∧ first.length = m)
    (secondOk : second.all inlineRowOk = true ∧ second.length = k) :
    (first ++ second).all inlineRowOk = true ∧ (first ++ second).length = m + k := by
  rw [List.all_append, List.length_append, firstOk.1, secondOk.1, firstOk.2, secondOk.2]
  exact ⟨rfl, rfl⟩
''']
assemble = {}
for k in keys:
    for case, suffix, params, args in (
        ("normal", "", "(rs1 rs2 rs3 : regidx)", "rs1 rs2 rs3"),
        ("rd_zero", "RdZero", "(rs1 rs2 : regidx)", "rs1 rs2"),
    ):
        names = []
        for n, length in enumerate(k["chunks"][case]):
            lemma = f"{k['base']}{suffix}_chunk{n}"
            names.append(lemma)
            label = "rd ≠ x0" if case == "normal" else "rd = x0"
            out.append(f"/-- Chunk {n} of `{k['name']}` ({label}): every row passes `inlineRowOk`,\n"
                       f"and the chunk has {length} rows. -/")
            out.append(f"theorem {lemma} {params} :\n"
                       f"    ({k['base']}RowsAuto{suffix}Chunk{n} {args}).all inlineRowOk = true ∧\n"
                       f"      ({k['base']}RowsAuto{suffix}Chunk{n} {args}).length = {length} :=\n"
                       f"  ⟨rfl, rfl⟩\n")
        assemble[(k["base"], case)] = names
        total = sum(k["chunks"][case])
        lst = f"{k['base']}RowsAuto{suffix}List"
        term = f"({names[0]} {args})"
        for name in names[1:]:
            term = f"(checked_append {term}\n      ({name} {args}))"
        out.append(f"/-- All {total} rows of `{k['name']}` ({label}) pass `inlineRowOk`. -/")
        out.append(f"theorem {k['base']}{suffix}_rows_ok {params} :\n"
                   f"    ({lst} {args}).all inlineRowOk = true ∧\n"
                   f"      ({lst} {args}).length = {total} := by\n"
                   f"  unfold {lst}\n"
                   f"  have chained := {term}\n"
                   f"  exact chained\n")

out.append("end JoltISA.Inlines.InlineRowsOk\n")
out.append("namespace JoltISA.Inlines.InlineKey\n")
out.append("open JoltISA.Inlines.Generated JoltISA.Inlines.InlineRowsOk ExpansionFacts\n")
for case, suffix, fn, params, args in (
    ("normal", "", "rows", "(rs1 rs2 rs3 : regidx)", "rs1 rs2 rs3"),
    ("rd_zero", "RdZero", "rowsRdZero", "(rs1 rs2 : regidx)", "rs1 rs2"),
):
    label = "rd ≠ x0" if case == "normal" else "rd = x0"
    out.append(f"/-- Every row of every supported key's `{label}` rows passes `inlineRowOk`, and\n"
               f"there are `rowCount` of them.\n"
               f"Example: the 3121 rows of `keccak256AbsorbPermute.{fn}` pass. -/")
    out.append(f"theorem {fn}_ok (key : InlineKey) {params} :\n"
               f"    (key.{fn} {args}).all inlineRowOk = true ∧\n      (key.{fn} {args}).length = key.rowCount := by")
    out.append("  cases key")
    for k in keys:
        out.append(f"  · exact {k['base']}{suffix}_rows_ok {args}")
    out.append("")

out.append('''/-- Every row Jolt emits for a supported inline call passes `inlineRowOk`.
Example: every row of `keccak256AbsorbPermute.expandRows x10 x11 x0` passes. -/
theorem expandRows_rowsOk (key : InlineKey) (rs1 rs2 rd : regidx) :
    (key.expandRows rs1 rs2 rd).all inlineRowOk = true := by
  unfold expandRows
  split
  · exact (rowsRdZero_ok key rs1 rs2).1
  · exact (rows_ok key rs1 rs2 rd).1

/-- The rows Jolt emits for any supported inline call pass the sequence checks.
Example: `keccak256AbsorbPermute.expandRows x10 x11 x0` passes `sequenceOk`. -/
theorem expandRows_sequenceOk (key : InlineKey) (rs1 rs2 rd : regidx) :
    sequenceOk (key.expandRows rs1 rs2 rd) = true :=
  sequenceOk_of_inlineRowsOk _ (expandRows_rowsOk key rs1 rs2 rd)

/-- Both allocation cases have `rowCount` rows.
Example: `(keccak256AbsorbPermute.expandRows x10 x11 x0).length = 3121`. -/
theorem expandRows_length (key : InlineKey) (rs1 rs2 rd : regidx) :
    (key.expandRows rs1 rs2 rd).length = key.rowCount := by
  unfold expandRows
  split
  · exact (rowsRdZero_ok key rs1 rs2).2
  · exact (rows_ok key rs1 rs2 rd).2

end JoltISA.Inlines.InlineKey
''')
checks_text = "\n".join(out)

if check:
    stale = [p for p, t in ((KEYS, keys_text), (CHECKS, checks_text)) if not p.exists() or p.read_text() != t]
    if stale:
        print("gen_inline_keys: out of date: " + ", ".join(str(p.relative_to(ROOT)) for p in stale))
        sys.exit(1)
    sys.exit(0)
KEYS.write_text(keys_text)
CHECKS.write_text(checks_text)
print(f"wrote {KEYS.relative_to(ROOT)} and {CHECKS.relative_to(ROOT)}")
