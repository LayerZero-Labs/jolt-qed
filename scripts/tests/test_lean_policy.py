"""Tests of scripts/check-lean-policy.py and scripts/lean_source.py.

Run with `python3 -m unittest discover -s scripts/tests` from the repository root; CI runs it in
the step that runs the policy check. Each fixture in scripts/tests/lean-policy/ except
`clean.lean` is Lean source the policy must reject. The fixtures live outside the scanned
libraries, so the policy check of the repository never sees them.
"""

import importlib.util
import pathlib
import unittest

SCRIPTS = pathlib.Path(__file__).resolve().parent.parent
FIXTURES = pathlib.Path(__file__).resolve().parent / "lean-policy"

_spec = importlib.util.spec_from_file_location("check_lean_policy",
                                               SCRIPTS / "check-lean-policy.py")
policy = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(policy)
import lean_source  # noqa: E402  (check-lean-policy.py puts scripts/ on sys.path)

# The fixtures about `maxRecDepth` are scanned as the generated file that the allowlist names,
# so that the allowlist entry `maxRecDepth 750` before `def is_CSR_accessible` applies.
ALLOWLISTED_FILE = "LeanRV64D/SysControl.lean"

# fixture: (the file it is scanned as, a problem the scan must report)
MUST_FAIL = {
    "sorry-ax.lean": (None, "`sorryAx`"),
    "guillemet-hides-admit.lean": (None, "`admit`"),
    "guillemet-hides-axiom.lean": (None, "`axiom bad`"),
    "guillemet-hides-max-heartbeats.lean": (None, "`maxHeartbeats`"),
    "guillemet-hides-string-start.lean": (None, "`admit`"),
    "char-literal-quote.lean": (None, "`admit`"),
    "nested-comment.lean": (None, "`admit`"),
    "interpolated-sorry.lean": (None, "`sorry`"),
    "interpolated-nested-string.lean": (None, "`admit`"),
    "ambiguous-string.lean": (None, "the policy scanner cannot tell how Lean reads it"),
    "two-options-one-line.lean": (ALLOWLISTED_FILE, "`maxRecDepth` option that"),
    "allowed-option-wrong-declaration.lean": (ALLOWLISTED_FILE, "`maxRecDepth` option that"),
    # A literal directly after a token that is not part of an identifier.
    "bang-raw-string.lean": (None, "`admit`"),
    "bang-char-literal.lean": (None, "`admit`"),
    "bang-interpolated-string.lean": (None, "`admit`"),
    "question-raw-string.lean": (None, "`admit`"),
    "digit-raw-string.lean": (None, "`admit`"),
    "paren-raw-string.lean": (None, "`admit`"),
    "comma-raw-string.lean": (None, "`admit`"),
    # An `r` or `s!` that ends a dotted identifier is part of the identifier.
    "dotted-name-raw-string.lean": (None, "`admit`"),
    "dotted-interpolation-head.lean": (None, "the policy scanner cannot tell how Lean reads it"),
    # `#check` ends where Lean's token table says, which the scanner does not know.
    "hash-command-raw-string.lean": (None, "where the `#` command name ends"),
}


def scan(name, where=None):
    allowed_axioms, allowed_options = policy.load_allowlist()
    where = where or f"scripts/tests/lean-policy/{name}"
    return policy.scan(where, (FIXTURES / name).read_text(), allowed_axioms, allowed_options,
                       set(), [])


class LeanPolicyFixtures(unittest.TestCase):
    def test_every_fixture_is_listed(self):
        names = {path.name for path in FIXTURES.glob("*.lean")}
        self.assertEqual(names, set(MUST_FAIL) | {"clean.lean"})

    def test_rejected(self):
        for name, (where, problem) in MUST_FAIL.items():
            with self.subTest(fixture=name):
                errors = scan(name, where)
                self.assertTrue(any(problem in error for error in errors),
                                f"{name}: expected a problem containing {problem!r}, got {errors}")

    def test_clean_passes(self):
        self.assertEqual(scan("clean.lean", ALLOWLISTED_FILE), [])

    def test_admit_line_number(self):
        # The `«…»` identifier on line 1 must not shift or hide the `admit` on line 2.
        errors = scan("guillemet-hides-admit.lean")
        self.assertIn("scripts/tests/lean-policy/guillemet-hides-admit.lean:2: `admit`", errors)


class LexerTokens(unittest.TestCase):
    """Token boundaries that no valid Lean file shows on its own."""

    def test_name_literal_is_not_a_raw_string(self):
        # `` `r `` is a name. The string after it is a plain string with an escaped quote.
        self.assertEqual(lean_source.strip_comments('`r"a\\"b" admit'), '`r"" admit')

    def test_identifier_continues_after_bang(self):
        # `get!r` is one identifier, and the `"…"` after it is a plain string.
        self.assertEqual(lean_source.strip_comments('get!r"a\\"b" admit'), 'get!r"" admit')

    def test_raw_string_after_field_dot_is_rejected(self):
        # Lean may read `r` after `.` as a field name rather than a raw string.
        with self.assertRaises(lean_source.LexError):
            lean_source.strip_comments('(x).r"a\\"b"')


if __name__ == "__main__":
    unittest.main()
