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


def run_main(manifest_text: str) -> tuple[int, str]:
    with tempfile.NamedTemporaryFile("w", suffix=".toml", delete=False) as f:
        f.write(manifest_text)
    out = io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
        try:
            code = prov.main(["--manifest", f.name])
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


class CitedPathsTest(unittest.TestCase):
    # Review finding 4: abbreviated citation lists were not expanded.
    def test_bare_names_after_a_path(self) -> None:
        text = ("-- See : jolt/tracer/src/instruction/div.rs, divu.rs, rem.rs,\n"
                "--       remuw.rs (trace)\n")
        self.assertTrue({"tracer/src/instruction/div.rs", "tracer/src/instruction/divu.rs",
                         "tracer/src/instruction/rem.rs", "tracer/src/instruction/remuw.rs"}
                        <= prov.cited_paths(text))

    def test_brace_lists(self) -> None:
        got = prov.cited_paths("`crates/jolt-riscv/src/instructions/virt/{load,store}_{b,h}.rs`")
        self.assertEqual({p for p in got if p.endswith(".rs")},
                         {f"crates/jolt-riscv/src/instructions/virt/{a}_{b}.rs"
                          for a in ("load", "store") for b in ("b", "h")})

    def test_url_and_local_prefixes_are_dropped(self) -> None:
        got = prov.cited_paths(
            "https://github.com/abiswas3/jolt/tree/main/common/src/constants.rs#L3\n"
            "/Users/someone/Work/jolt/crates/jolt-program/src/expand/mod.rs\n")
        self.assertTrue({"common/src/constants.rs", "crates/jolt-program/src/expand/mod.rs"} <= got)

    def test_div_family_is_in_honest_trace_models(self) -> None:
        import tomllib
        entry = next(e for e in tomllib.loads(MANIFEST.read_text(encoding="utf-8"))["file"]
                     if e["lean"] == "JoltConstraints/honest_trace.lean")
        for name in ("div", "divu", "rem", "remu", "divw", "divuw", "remw", "remuw"):
            self.assertIn(f"tracer/src/instruction/{name}.rs", entry["models"])


if __name__ == "__main__":
    unittest.main()
