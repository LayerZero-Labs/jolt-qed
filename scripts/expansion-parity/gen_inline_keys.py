#!/usr/bin/env python3
"""Generate the supported inline keys and their row checks.

The script writes two files:

- JoltBytecode/Inlines/Keys.lean: the type `InlineKey` of supported registered
  inlines, each key's encoding (opcode, funct3, funct7), its generated rows for both
  allocation cases, its row count, and whether its rows read the source `rd` (`rs3`).
- JoltConstraints/inline_rows_ok.lean: for every allocation case that jolt-qed
  accepts, the per-row check `ExpansionFacts.inlineRowOk` on each generated chunk,
  proved by `rfl`. jolt-qed rejects the `rd = x0` case of a key that reads `rs3`
  (decision D7), so for that case the file states only the length of each chunk.
  The assembled facts are `InlineKey.rows_ok`, `InlineKey.rowsRdZero_ok` (which
  requires `readsRd = false`) and `InlineKey.rowsRdZero_length` (for every key).
  For example, `secp256k1MulqRdZero_rows_length` states only the length of the
  `rd = x0` rows of SECP256K1_MULQ.

The encodings come from the expansion-parity driver's `inline_templates.json`
(written by `scripts/expansion-parity/run.sh` to WORK_DIR/out). The rows come from
JoltBytecode/Inlines/Generated/<Name>.lean, which the same driver run writes. The
script checks that both name the same Jolt commit.

`readsRd` is computed from the generated rows: a key reads `rs3` exactly when some
generated chunk of its `rd != x0` case takes `rs3` as a used parameter (the driver
renders an unused parameter as `_rs3`).

Some inlines have `VirtualAdvice` rows, and their generated definitions take an
`advice : Nat → BitVec 64` argument. Their bytecode rows use the placeholder
`fun _ => 0`: the trace replaces each `VirtualAdvice` value with the row's runtime
advice (`JoltISA.Instr.withRuntimeAdvice`), so the bytecode value is never read.

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
    "SECP256K1_MULQ",
    "SECP256K1_MULR",
    "SECP256K1_SQUAREQ",
    "SECP256K1_SQUARER",
    "SECP256K1_DIVQ",
    "SECP256K1_DIVR",
    "SECP256K1_GLVR_ADV",
]

# The placeholder advice of the bytecode rows of an inline with `VirtualAdvice` rows.
PLACEHOLDER = "(fun _ => 0)"


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
    advice_params = set()
    for case, suffix in (("normal", ""), ("rd_zero", "RdZero")):
        pattern = re.compile(
            rf"^def {base}RowsAuto{suffix}Chunk(\d+) \(([^)]*) : regidx\)"
            r"((?: \(_?advice : Nat → BitVec 64\))?) : List JoltISA\.Instr := \[$"
            r"(.*?)^\]$",
            re.M | re.S,
        )
        found = []
        for n, params, advice, body in pattern.findall(source):
            advice_params.add(bool(advice))
            found.append((int(n), params, body))
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
    if len(advice_params) != 1:
        fail(f"{name}: some chunks take advice and some do not")
    keys.append(
        dict(
            name=name,
            base=base,
            module=pathlib.Path(inline["lean_file"]).stem,
            opcode=inline["opcode"],
            funct3=inline["funct3"],
            funct7=inline["funct7"],
            reads_rd=used_rs3,
            advice=advice_params.pop(),
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


def adv(k):
    """The advice argument of the key's generated definitions, if they take one."""
    return f" {PLACEHOLDER}" if k["advice"] else ""


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
(`rd ≠ x0` and `rd = x0`), and its row count. An inline's encoded `rd` field is the
rows' `rs3`: Jolt's decoder keeps it as the normalized `rd`
(jolt/crates/jolt-program/src/image/decode.rs, `format_inline_operands`), and the expander
reads that `rd` as `rs3` (jolt/crates/jolt-program/src/expand/inline.rs,
`InlineOperands::from_source_row`), both at the pin.
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
           "Example: no hash inline reads it, so `sha256.readsRd = false`; the secp256k1\n"
           "inlines store their output at the address in it, so `secp256k1Mulq.readsRd = true`. -/")
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
''')
out.append("/-- The rows of the `rd ≠ x0` case: the generated `<name>RowsAutoList`.\n"
           "`rs3` is the source `rd`. A key with `VirtualAdvice` rows gets the placeholder\n"
           "advice `fun _ => 0`; the trace replaces each value with the row's runtime advice.\n"
           "Example: the first row of `keccak256AbsorbPermute.rows x10 x11 x12` loads `vr48` from `x10`. -/")
out.append("def rows : InlineKey → regidx → regidx → regidx → List JoltISA.Instr")
for k in keys:
    out.append(f"  | .{k['base']}, rs1, rs2, rs3 =>\n    Generated.{k['base']}RowsAutoList rs1 rs2 rs3{adv(k)}")
out.append("")
out.append("/-- The rows of the `rd = x0` case, after Rust substitutes the instruction temporary\n"
           "`vr40` for `rd`: the generated `<name>RowsAutoRdZeroList`.\n"
           "Example: `sha256.rowsRdZero x10 x11` has 1900 rows. -/")
out.append("def rowsRdZero : InlineKey → regidx → regidx → List JoltISA.Instr")
for k in keys:
    out.append(f"  | .{k['base']}, rs1, rs2 =>\n    Generated.{k['base']}RowsAutoRdZeroList rs1 rs2{adv(k)}")
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
sequence checks. The `rd = x0` rows of the keys that read `rs3` (the secp256k1
inlines) read the uninitialized temporary `vr40`. jolt-qed excludes those encodings
(decision D7): `InlineEncoding.register` and `SourceInstruction.expand` reject them.
Jolt at the pin still expands them; a16z/jolt#2414 proposes the same rejection. For
those keys in that case the lemmas state only the length.
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

/-- Lengths add when lists are appended. For example, chunks of 100 and 35 rows give
135 rows. -/
theorem length_append_eq {{first second : List JoltISA.Instr}} {{m k : Nat}}
    (firstLength : first.length = m) (secondLength : second.length = k) :
    (first ++ second).length = m + k := by
  rw [List.length_append, firstLength, secondLength]
''']
assemble = {}
for k in keys:
    for case, suffix, params, args in (
        ("normal", "", "(rs1 rs2 rs3 : regidx)", "rs1 rs2 rs3"),
        ("rd_zero", "RdZero", "(rs1 rs2 : regidx)", "rs1 rs2"),
    ):
        names = []
        call = f"{args}{adv(k)}"
        # jolt-qed rejects `rd = x0` for a key that reads rs3 (D7), and those rows read the
        # uninitialized vr40, so only their length is stated.
        length_only = case == "rd_zero" and k["reads_rd"]
        label = "rd ≠ x0" if case == "normal" else "rd = x0"
        for n, length in enumerate(k["chunks"][case]):
            lemma = f"{k['base']}{suffix}_chunk{n}"
            names.append(lemma)
            if length_only:
                out.append(f"/-- Chunk {n} of `{k['name']}` ({label}) has {length} rows. -/")
                out.append(f"theorem {lemma} {params} :\n"
                           f"    ({k['base']}RowsAuto{suffix}Chunk{n} {call}).length = {length} :=\n"
                           f"  rfl\n")
                continue
            out.append(f"/-- Chunk {n} of `{k['name']}` ({label}): every row passes `inlineRowOk`,\n"
                       f"and the chunk has {length} rows. -/")
            out.append(f"theorem {lemma} {params} :\n"
                       f"    ({k['base']}RowsAuto{suffix}Chunk{n} {call}).all inlineRowOk = true ∧\n"
                       f"      ({k['base']}RowsAuto{suffix}Chunk{n} {call}).length = {length} :=\n"
                       f"  ⟨rfl, rfl⟩\n")
        assemble[(k["base"], case)] = names
        total = sum(k["chunks"][case])
        lst = f"{k['base']}RowsAuto{suffix}List"
        combine = "length_append_eq" if length_only else "checked_append"
        term = f"({names[0]} {args})"
        for name in names[1:]:
            term = f"({combine} {term}\n      ({name} {args}))"
        if length_only:
            out.append(f"/-- `{k['name']}` ({label}) has {total} rows. -/")
            out.append(f"theorem {k['base']}{suffix}_rows_length {params} :\n"
                       f"    ({lst} {call}).length = {total} := by\n"
                       f"  unfold {lst}\n"
                       f"  have chained := {term}\n"
                       f"  exact chained\n")
            continue
        out.append(f"/-- All {total} rows of `{k['name']}` ({label}) pass `inlineRowOk`. -/")
        out.append(f"theorem {k['base']}{suffix}_rows_ok {params} :\n"
                   f"    ({lst} {call}).all inlineRowOk = true ∧\n"
                   f"      ({lst} {call}).length = {total} := by\n"
                   f"  unfold {lst}\n"
                   f"  have chained := {term}\n"
                   f"  exact chained\n")

out.append("end JoltISA.Inlines.InlineRowsOk\n")
out.append("namespace JoltISA.Inlines.InlineKey\n")
out.append("open JoltISA.Inlines.Generated JoltISA.Inlines.InlineRowsOk ExpansionFacts\n")
out.append("/-- Every row of every supported key's `rd ≠ x0` rows passes `inlineRowOk`, and\n"
           "there are `rowCount` of them.\n"
           "Example: the 3121 rows of `keccak256AbsorbPermute.rows` pass. -/")
out.append("theorem rows_ok (key : InlineKey) (rs1 rs2 rs3 : regidx) :\n"
           "    (key.rows rs1 rs2 rs3).all inlineRowOk = true ∧\n"
           "      (key.rows rs1 rs2 rs3).length = key.rowCount := by")
out.append("  cases key")
for k in keys:
    out.append(f"  · exact {k['base']}_rows_ok rs1 rs2 rs3")
out.append("")
out.append("/-- The `rd = x0` rows of a key that does not read `rs3` pass `inlineRowOk`.\n"
           "Example: the 3121 rows of `keccak256AbsorbPermute.rowsRdZero` pass. -/")
out.append("theorem rowsRdZero_ok (key : InlineKey) (rs1 rs2 : regidx)\n"
           "    (reads : key.readsRd = false) :\n"
           "    (key.rowsRdZero rs1 rs2).all inlineRowOk = true := by")
out.append("  cases key")
for k in keys:
    if k["reads_rd"]:
        out.append("  · exact absurd reads (by decide)")
    else:
        out.append(f"  · exact ({k['base']}RdZero_rows_ok rs1 rs2).1")
out.append("")
out.append("/-- Every key's `rd = x0` rows have `rowCount` rows.\n"
           "Example: `(secp256k1Mulq.rowsRdZero x10 x11).length = secp256k1Mulq.rowCount`. -/")
out.append("theorem rowsRdZero_length (key : InlineKey) (rs1 rs2 : regidx) :\n"
           "    (key.rowsRdZero rs1 rs2).length = key.rowCount := by")
out.append("  cases key")
for k in keys:
    if k["reads_rd"]:
        out.append(f"  · exact {k['base']}RdZero_rows_length rs1 rs2")
    else:
        out.append(f"  · exact ({k['base']}RdZero_rows_ok rs1 rs2).2")
out.append("")

out.append("""/-- Every row Jolt emits for a supported inline call that jolt-qed accepts passes
`inlineRowOk`. jolt-qed rejects `rd = x0` for a key that reads `rs3` (decision D7).
Example: every row of `keccak256AbsorbPermute.expandRows x10 x11 x0` passes. -/
theorem expandRows_rowsOk (key : InlineKey) (rs1 rs2 rd : regidx)
    (registered : (JoltISA.isX0 rd && key.readsRd) = false) :
    (key.expandRows rs1 rs2 rd).all inlineRowOk = true := by
  unfold expandRows
  split
  · next zero => exact rowsRdZero_ok key rs1 rs2 (by simpa [zero] using registered)
  · exact (rows_ok key rs1 rs2 rd).1

/-- The rows Jolt emits for a supported inline call that jolt-qed accepts pass the
sequence checks.
Example: `keccak256AbsorbPermute.expandRows x10 x11 x0` passes `sequenceOk`. -/
theorem expandRows_sequenceOk (key : InlineKey) (rs1 rs2 rd : regidx)
    (registered : (JoltISA.isX0 rd && key.readsRd) = false) :
    sequenceOk (key.expandRows rs1 rs2 rd) = true :=
  sequenceOk_of_inlineRowsOk _ (expandRows_rowsOk key rs1 rs2 rd registered)

/-- Both allocation cases have `rowCount` rows.
Example: `(keccak256AbsorbPermute.expandRows x10 x11 x0).length = 3121`. -/
theorem expandRows_length (key : InlineKey) (rs1 rs2 rd : regidx) :
    (key.expandRows rs1 rs2 rd).length = key.rowCount := by
  unfold expandRows
  split
  · exact rowsRdZero_length key rs1 rs2
  · exact (rows_ok key rs1 rs2 rd).2

end JoltISA.Inlines.InlineKey
""")
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
