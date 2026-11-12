"""Regression tests for scripts/check-provenance.py.

Run from the repository root: python3 -m unittest discover -s scripts/tests
The tests that call main() read the real provenance.toml and Lean files and
need no Jolt clone.
"""

from __future__ import annotations

import contextlib
import importlib.util
import io
import re
import subprocess
import tempfile
import unittest
from collections import Counter
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent.parent
_spec = importlib.util.spec_from_file_location("check_provenance", SCRIPTS / "check-provenance.py")
prov = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(prov)

PIN = "580084fcfad4788ebf48413a92dd640ca090c45f"
CHECKED = "c6703570588e88033b8722bd4dec47c7f46f3b16"
OTHERS = [{"revision": "717aeca3", "repository": "riscv/riscv-isa-manual"}]
MANIFEST = SCRIPTS.parent / "provenance.toml"


def violations(text: str, checked: str | None = CHECKED) -> Counter:
    found = prov.scan_text("X.lean", text, PIN, checked, OTHERS)
    return Counter({(kind, t): n for (_, kind, t), n in found.items()})


def run_main(manifest_text: str, *extra: str) -> tuple[int, str]:
    with tempfile.NamedTemporaryFile("w", suffix=".toml", delete=False) as f:
        f.write(manifest_text)
    out = io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
        try:
            code = prov.main(["--manifest", f.name, *extra])
        except SystemExit as e:
            code = int(e.code)
    Path(f.name).unlink()
    return code, out.getvalue()


class RevisionTest(unittest.TestCase):
    # Review finding 5: all-digit and all-letter revisions escaped detection.
    def test_all_digit_revision_in_citation_context(self) -> None:
        self.assertEqual(violations("-- see commit 7538215\n"), Counter({("revision", "7538215"): 1}))
        self.assertEqual(violations("-- a16z/jolt@7538215\n"), Counter({("revision", "7538215"): 1}))

    def test_all_letter_revision_in_url(self) -> None:
        text = "-- https://github.com/a16z/jolt/blob/deadbeef/tracer/src/lib.rs\n"
        self.assertEqual(violations(text), Counter({("revision", "deadbeef"): 1}))

    def test_plain_numbers_and_words_are_not_revisions(self) -> None:
        self.assertEqual(violations("def big := 1000000\n-- a faceted, defaced word\n"), Counter())

    # Review finding 5: other repositories' revisions were exempt everywhere.
    def test_foreign_revision_cited_as_jolt(self) -> None:
        text = "-- https://github.com/a16z/jolt/blob/717aeca3/tracer/src/lib.rs\n"
        self.assertEqual(violations(text), Counter({("revision", "717aeca3"): 1}))

    def test_foreign_revision_in_its_own_repository(self) -> None:
        text = "-- https://github.com/riscv/riscv-isa-manual/blob/717aeca3/src/a.adoc\n"
        self.assertEqual(violations(text), Counter())

    def test_pin_and_checked_revisions_pass(self) -> None:
        text = f"-- a16z/jolt@{PIN[:9]} and https://github.com/a16z/jolt/blob/{CHECKED}/x.rs\n"
        self.assertEqual(violations(text), Counter())

    def test_mixed_hex_revision_still_detected(self) -> None:
        self.assertEqual(violations("-- at 8bbb2357\n"), Counter({("revision", "8bbb2357"): 1}))

    # Round-2 finding 4: the second endpoint of a compare URL was not checked.
    def test_both_compare_endpoints_are_checked(self) -> None:
        for sep in ("...", ".."):
            text = f"-- https://github.com/a16z/jolt/compare/580084fcf{sep}7538215\n"
            self.assertEqual(violations(text), Counter({("revision", "7538215"): 1}))
            text = f"-- https://github.com/a16z/jolt/compare/580084fcf{sep}717aeca3\n"
            self.assertEqual(violations(text), Counter({("revision", "717aeca3"): 1}))
            text = f"-- https://github.com/a16z/jolt/compare/7538215{sep}{PIN}\n"
            self.assertEqual(violations(text), Counter({("revision", "7538215"): 1}))
        text = f"-- https://github.com/a16z/jolt/compare/{CHECKED[:9]}...{PIN[:9]}\n"
        self.assertEqual(violations(text), Counter())

    # Round-3 finding 6: a foreign revision cited as a Jolt revision.
    def test_foreign_revision_in_jolt_prose(self) -> None:
        self.assertEqual(violations("-- Jolt commit 717aeca3\n"), Counter({("revision", "717aeca3"): 1}))
        self.assertEqual(violations("-- see a16z/jolt at 717aeca3\n"),
                         Counter({("revision", "717aeca3"): 1}))
        self.assertEqual(violations("-- the ISA manual at 717aeca3\n"), Counter())
        self.assertEqual(violations("-- jolt-qed's manual copy at 717aeca3\n"), Counter())

    # Round-3 finding 7: an uppercase revision escaped the scan.
    def test_uppercase_revision(self) -> None:
        full = "7538215BFE497AE316FC09E72D6D12BB131BEAD0"
        self.assertEqual(violations(f"-- Jolt at `{full}`\n"),
                         Counter({("revision", full.lower()): 1}))
        self.assertEqual(violations(f"-- https://github.com/a16z/jolt/blob/{PIN.upper()}/x.rs\n"),
                         Counter())
        self.assertEqual(violations(f"-- pinned at {PIN[:9].upper()}\n"), Counter())

    # Round-2 finding 4: "Jolt at `7538215`" escaped the citation words.
    def test_all_digit_revision_after_at_or_jolt(self) -> None:
        self.assertEqual(violations("-- Jolt at `7538215`\n"), Counter({("revision", "7538215"): 1}))
        self.assertEqual(violations("-- upstream 7538215\n"), Counter({("revision", "7538215"): 1}))


class BaselineTextTest(unittest.TestCase):
    # Review finding 6: the baseline named markers and owners, not citations.
    def test_local_path_records_whole_path(self) -> None:
        a = violations("-- /Users/someone/jolt/tracer/src/a.rs\n")
        b = violations("-- /Users/someone/other-fork/false.rs\n")
        self.assertEqual(set(a), {("local-path", "/Users/someone/jolt/tracer/src/a.rs")})
        self.assertNotEqual(set(a), set(b))

    def test_fork_records_whole_url(self) -> None:
        a = violations("-- https://github.com/abiswas3/jolt/tree/main/crates/x.rs#L3\n")
        self.assertEqual(set(a), {("fork", "github.com/abiswas3/jolt/tree/main/crates/x.rs#L3")})

    def test_replacing_a_baselined_local_path_fails(self) -> None:
        text = MANIFEST.read_text(encoding="utf-8")
        m = re.search(r'kind = "local-path"\ntext = "([^"]+)"', text)
        self.assertIsNotNone(m)
        code, out = run_main(text.replace(m.group(0), 'kind = "local-path"\ntext = "/Users/someone/other-fork/false.rs"', 1))
        self.assertEqual(code, 1, out)

    def test_manifest_does_not_cite_itself(self) -> None:
        code, out = run_main(MANIFEST.read_text(encoding="utf-8"))
        self.assertEqual(code, 0, out)

    # Round-2 finding 6: a [[known]] text spelled another way cited itself.
    def test_baseline_in_another_spelling_fails(self) -> None:
        text = MANIFEST.read_text(encoding="utf-8")
        entry = ("[[known]]\nfile = 'provenance.toml'\nkind = 'local-path'\n"
                 "text = '/Users/self/debt.rs'\ncount = 1\n\n")
        i = text.index("\n[[known]]\n") + 1
        for bad in (text[:i] + entry + text[i:],
                    text + "\n" + entry,
                    text.replace("count = 1\n", "count  =  1\n", 1)):
            code, out = run_main(bad)
            self.assertEqual(code, 1, out)
            self.assertIn("the [[known]] tables must end provenance.toml", out)

    def test_known_before_other_tables_fails(self) -> None:
        text = MANIFEST.read_text(encoding="utf-8")
        i = text.index("\n[[file]]\nlean") + 1
        entry = '[[known]]\nfile = "provenance.toml"\nkind = "local-path"\ntext = "/Users/self/debt.rs"\ncount = 1\n\n'
        code, out = run_main(text[:i] + entry + text[i:])
        self.assertEqual(code, 1, out)

    def test_known_count_must_be_a_positive_integer(self) -> None:
        text = MANIFEST.read_text(encoding="utf-8")
        for count in ('"1"', "0", "1.0", "true"):
            code, out = run_main(text.replace("count = 1\n", f"count = {count}\n", 1))
            self.assertEqual(code, 1, out)


class OtherRevisionTest(unittest.TestCase):
    # Round-2 finding 5: [[other_revision]] tables were not validated.
    def _with_other(self, body: str) -> tuple[int, str]:
        text = MANIFEST.read_text(encoding="utf-8")
        i = text.index("\n[[other_revision]]\n") + 1
        return run_main(text[:i] + "[[other_revision]]\n" + body + "\n" + text[i:])

    def test_short_or_bad_revisions_fail(self) -> None:
        for rev in ("753", "", "75382", "XYZ1234", "7538215Z"):
            code, out = self._with_other(f'repository = "riscv/riscv-isa-manual"\nrevision = "{rev}"\n')
            self.assertEqual(code, 2, out)
            self.assertIn("revision must be 7 to 40 lowercase hex digits", out)

    def test_repository_must_be_owner_and_name(self) -> None:
        code, out = self._with_other('repository = "riscv"\nrevision = "7538215"\n')
        self.assertEqual(code, 2, out)
        code, out = self._with_other('revision = "7538215"\n')
        self.assertEqual(code, 2, out)

    def test_jolt_repository_is_refused(self) -> None:
        code, out = self._with_other('repository = "a16z/jolt"\nrevision = "7538215"\n')
        self.assertEqual(code, 2, out)
        self.assertIn("checked field", out)

    def test_unknown_top_level_key_fails(self) -> None:
        code, out = run_main("allow = true\n" + MANIFEST.read_text(encoding="utf-8"))
        self.assertEqual(code, 1, out)
        self.assertIn("unexpected top-level keys ['allow']", out)


class ManifestTest(unittest.TestCase):
    # Review finding 3: models paths of entries without `checked` were unchecked.
    def test_new_unchecked_models_path_fails(self) -> None:
        text = MANIFEST.read_text(encoding="utf-8")
        old = ('lean = "JoltBytecode/Decode/Agreement.lean"\n'
               'models = ["crates/jolt-program/src/image/decode.rs"]\nnote')
        self.assertIn(old, text)  # an entry with models and no checked revision
        bad = text.replace(old, old.replace('decode.rs"]', 'decode.rs", "does/not/exist.rs"]'))
        code, out = run_main(bad)
        self.assertEqual(code, 1, out)
        self.assertIn("unchecked-model 'does/not/exist.rs'", out)

    # Review finding 3: the schema accepted an entry for README.md.
    def test_entry_outside_the_lean_roots_fails(self) -> None:
        text = MANIFEST.read_text(encoding="utf-8")
        i = text.index("\n[[file]]\nlean") + 1
        bad = text[:i] + '[[file]]\nlean = "README.md"\nmodels = []\n\n' + text[i:]
        code, out = run_main(bad)
        self.assertEqual(code, 1, out)
        self.assertIn("README.md: [[file]] entries are for Lean files", out)

    def test_unknown_entry_key_fails(self) -> None:
        text = MANIFEST.read_text(encoding="utf-8")
        i = text.index("[[file]]\nlean = ") + len("[[file]]\n")
        code, out = run_main(text[:i] + 'checkd = "x"\n' + text[i:])
        self.assertEqual(code, 1, out)


TREE = {
    "tracer/src/instruction/div.rs", "tracer/src/instruction/divu.rs",
    "tracer/src/instruction/rem.rs", "tracer/src/instruction/remuw.rs",
    "tracer/src/instruction/virtual_host_io.rs", "tracer/src/emulator/cpu.rs",
    "common/src/constants.rs", "crates/jolt-program/src/expand/mod.rs",
    "crates/jolt-riscv/src/instructions/i/ld.rs",
    *(f"crates/jolt-riscv/src/instructions/virt/{a}_{b}.rs"
      for a in ("load", "store", "shift_data") for b in ("b", "h", "w")),
    "crates/jolt-lookup-tables/src/traits.rs",
    "crates/jolt-lookup-tables/src/instructions/virt/floor_access.rs",
    "crates/jolt-lookup-tables/src/instructions/riscv/ld.rs",
    "crates/jolt-lookup-tables/src/instructions/riscv/sd.rs",
    "crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs",
    "crates/jolt-claims/src/protocols/jolt/relations/spartan/shift.rs",
    "crates/jolt-verifier/src/stages/stage3/spartan_shift.rs",
    "crates/jolt-verifier/src/lib.rs",
    "tracer/src/lib.rs",
}
DIRS = {"/".join(p.split("/")[:k]) for p in TREE for k in range(1, p.count("/") + 1)}


def cited(text: str) -> set[str]:
    return prov.cited_paths(text, TREE, DIRS)


class CitedPathsTest(unittest.TestCase):
    # Review finding 4: abbreviated citation lists were not expanded.
    def test_bare_names_after_a_path(self) -> None:
        text = ("-- See : jolt/tracer/src/instruction/div.rs, divu.rs, rem.rs,\n"
                "--       remuw.rs (trace)\n")
        self.assertEqual(cited(text), {"tracer/src/instruction/div.rs", "tracer/src/instruction/divu.rs",
                                       "tracer/src/instruction/rem.rs", "tracer/src/instruction/remuw.rs"})

    def test_brace_lists(self) -> None:
        got = cited("`crates/jolt-riscv/src/instructions/virt/{load,store}_{b,h}.rs`")
        self.assertEqual(got, {f"crates/jolt-riscv/src/instructions/virt/{a}_{b}.rs"
                               for a in ("load", "store") for b in ("b", "h")})

    def test_url_and_local_prefixes_are_dropped(self) -> None:
        got = cited("https://github.com/abiswas3/jolt/tree/main/common/src/constants.rs#L3\n"
                    "/Users/someone/Work/jolt/crates/jolt-program/src/expand/mod.rs\n")
        self.assertEqual(got, {"common/src/constants.rs", "crates/jolt-program/src/expand/mod.rs"})

    # Round-2 finding 2: paths relative to an earlier citation were dropped.
    def test_paths_relative_to_an_ancestor_of_the_last_citation(self) -> None:
        got = cited("Jolt's prover: `crates/jolt-riscv/src/instructions/i/ld.rs` and\n"
                    "`instructions/virt/{load,store,shift_data}_{b,h,w}.rs` (`jolt_instruction!`)\n")
        self.assertEqual(got, {"crates/jolt-riscv/src/instructions/i/ld.rs",
                               *(f"crates/jolt-riscv/src/instructions/virt/{a}_{b}.rs"
                                 for a in ("load", "store", "shift_data") for b in ("b", "h", "w"))})
        got = cited("`crates/jolt-lookup-tables/src/traits.rs`. Jolt's prover:\n"
                    "`instructions/virt/floor_access.rs` and `instructions/riscv/{ld,sd}.rs`\n")
        self.assertEqual(got, {"crates/jolt-lookup-tables/src/traits.rs",
                               "crates/jolt-lookup-tables/src/instructions/virt/floor_access.rs",
                               "crates/jolt-lookup-tables/src/instructions/riscv/ld.rs",
                               "crates/jolt-lookup-tables/src/instructions/riscv/sd.rs"})
        got = cited("Rust: tracer/src/instruction/virtual_host_io.rs; emulator/cpu.rs:1244-1333.")
        self.assertEqual(got, {"tracer/src/instruction/virtual_host_io.rs", "tracer/src/emulator/cpu.rs"})

    # Round-3 finding 3: an internal `jolt/` component was stripped.
    def test_internal_jolt_component_is_kept(self) -> None:
        path = "crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs"
        self.assertEqual(cited(f"Rust: `{path}`"), {path})
        self.assertEqual(cited(f"/Users/me/src/jolt/{path}"), {path})

    # Round-3 finding 4: shorthand paths with no full path before them.
    def test_unique_suffix_resolves(self) -> None:
        got = cited("`relations/spartan/shift.rs` and `stages/stage3/spartan_shift.rs`")
        self.assertEqual(got, {"crates/jolt-claims/src/protocols/jolt/relations/spartan/shift.rs",
                               "crates/jolt-verifier/src/stages/stage3/spartan_shift.rs"})
        # `src/lib.rs` ends two files of the tree, so on its own it names neither.
        self.assertEqual(cited("see `src/lib.rs`"), set())

    # Round-3 finding 8: a decorated comment line is a paragraph break too.
    def test_relative_names_do_not_cross_a_decorated_break(self) -> None:
        for sep in (" *", "--", " * ", "/-", "-/", "##"):
            got = cited(f"/- See tracer/src/instruction/div.rs.\n{sep}\n * The rem.rs of another.\n-/")
            self.assertEqual(got, {"tracer/src/instruction/div.rs"}, sep)

    # Round-2 review nits: context crossed paragraphs, and `./` was kept.
    def test_relative_names_do_not_cross_a_blank_line(self) -> None:
        got = cited("See tracer/src/instruction/div.rs.\n\nThe rem.rs of another component.\n")
        self.assertEqual(got, {"tracer/src/instruction/div.rs"})
        got = cited("-- See tracer/src/instruction/div.rs.\n--\n-- The rem.rs of another component.\n")
        self.assertEqual(got, {"tracer/src/instruction/div.rs"})

    def test_dot_slash_prefix(self) -> None:
        self.assertEqual(cited("see ./tracer/src/instruction/div.rs"), {"tracer/src/instruction/div.rs"})

    def test_paths_not_in_the_tree_do_not_count(self) -> None:
        self.assertEqual(cited("see tracer/src/instruction/nope.rs and foo/bar.rs"), set())

    def test_div_family_is_in_honest_trace_models(self) -> None:
        import tomllib
        entry = next(e for e in tomllib.loads(MANIFEST.read_text(encoding="utf-8"))["file"]
                     if e["lean"] == "JoltConstraints/honest_trace.lean")
        for name in ("div", "divu", "rem", "remu", "divw", "divuw", "remw", "remuw"):
            self.assertIn(f"tracer/src/instruction/{name}.rs", entry["models"])


class CloneCheckTest(unittest.TestCase):
    """--jolt-dir checks against a small Jolt tree built in a temporary git repository."""

    @classmethod
    def setUpClass(cls) -> None:
        cls.tmp = tempfile.TemporaryDirectory()
        root = Path(cls.tmp.name)
        for p in TREE | {"jolt-platform/src/advice.rs", "jolt-platform/src/cycle_tracking.rs",
                         "jolt-platform/src/print.rs"}:
            (root / p).parent.mkdir(parents=True, exist_ok=True)
            (root / p).write_text("// test\n")
        env = {"GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@t", "GIT_COMMITTER_NAME": "t",
               "GIT_COMMITTER_EMAIL": "t@t", "PATH": "/usr/bin:/bin:/usr/local/bin:/opt/homebrew/bin"}
        for cmd in (["init", "-q"], ["add", "-A"], ["commit", "-q", "-m", "tree"]):
            subprocess.run(["git", "-C", cls.tmp.name, *cmd], check=True, env=env)
        cls.rev = subprocess.run(["git", "-C", cls.tmp.name, "rev-parse", "HEAD"], check=True,
                                 capture_output=True, text=True).stdout.strip()

    @classmethod
    def tearDownClass(cls) -> None:
        cls.tmp.cleanup()

    # Round-2 finding 3: an entry with no checked revision could cite a Jolt
    # file that its models omits.
    def test_source_citation_missing_from_unchecked_models(self) -> None:
        text = MANIFEST.read_text(encoding="utf-8").replace(PIN, self.rev)
        old = '  "tracer/src/emulator/cpu.rs",\n  "tracer/src/instruction/virtual_host_io.rs",'
        self.assertIn(old, text)
        code, out = run_main(text.replace(old, '  "tracer/src/instruction/virtual_host_io.rs",'),
                             "--jolt-dir", self.tmp.name)
        self.assertEqual(code, 1, out)
        self.assertIn("HostIO.lean: cites tracer/src/emulator/cpu.rs, a file at the pin, "
                      "but models omits it", out)

    # Round-3 finding 6: a Jolt commit recorded as another repository's.
    def test_other_revision_that_is_a_jolt_commit_fails(self) -> None:
        text = MANIFEST.read_text(encoding="utf-8").replace(PIN, self.rev)
        i = text.index("\n[[other_revision]]\n") + 1
        bad = (text[:i] + f'[[other_revision]]\nrevision = "{self.rev[:9]}"\n'
               f'repository = "riscv/riscv-isa-manual"\n\n' + text[i:])
        code, out = run_main(bad, "--jolt-dir", self.tmp.name)
        self.assertEqual(code, 1, out)
        self.assertIn("names a commit in the Jolt clone", out)

    def test_no_omission_with_the_full_models(self) -> None:
        text = MANIFEST.read_text(encoding="utf-8").replace(PIN, self.rev)
        code, out = run_main(text, "--jolt-dir", self.tmp.name)
        self.assertNotIn("HostIO.lean: cites", out)


if __name__ == "__main__":
    unittest.main()
