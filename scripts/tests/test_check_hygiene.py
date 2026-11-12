"""Regression tests for scripts/check_hygiene.py.

Run from the repository root: python3 -m unittest discover -s scripts/tests
"""

from __future__ import annotations

import importlib.util
import unittest
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent.parent
_spec = importlib.util.spec_from_file_location("check_hygiene", SCRIPTS / "check_hygiene.py")
hygiene = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(hygiene)


def tokens(src: str) -> list[tuple[int, str]]:
    return [(line, token) for line, token, _ in hygiene.scan_text(src)]


class HygieneScanTest(unittest.TestCase):
    # Review finding 1: interpolated strings hid executable code.
    def test_interpolated_string_term_is_code(self) -> None:
        self.assertEqual(tokens('def probe : String := s!"{(by sorry : Nat)}"\n'), [(1, "sorry")])

    def test_throw_error_interpolation_is_code(self) -> None:
        self.assertEqual(tokens('def f : MetaM Unit := throwError "x {(by admit : Nat)} y"\n'),
                         [(1, "admit")])

    def test_nested_string_inside_interpolation(self) -> None:
        self.assertEqual(tokens('def p : String := s!"{f "x" (by sorry)}"\n'), [(1, "sorry")])

    # Round-2 review: a plain literal with a brace inside an interpolation.
    def test_plain_brace_string_inside_interpolation(self) -> None:
        self.assertEqual(tokens('def p : String := s!"{String.length "{" + (by sorry : Nat)}"\n'),
                         [(1, "sorry")])

    # Round-2 review: brace text in an ordinary string is not code.
    def test_brace_text_in_plain_string_is_ignored(self) -> None:
        self.assertEqual(tokens('def message : String := "{sorry}"\n'), [])

    # A plain string after `]` or after a `!` macro that takes a term must not
    # open code at its `{`: the `"` that closes it would then start a string
    # that hides the rest of the line.
    def test_plain_string_after_bracket_or_bang(self) -> None:
        src = ('def a := Function.const Nat [1] "{" ++ toString (by sorry : Nat)\n'
               'def b : Nat := panic! "{" ++ toString (by admit : Nat)\n'
               'def c (xs : Array String) := xs[0]! ++ "{" ++ toString (by sorry : Nat)\n')
        self.assertEqual(tokens(src), [(1, "sorry"), (2, "admit"), (3, "sorry")])

    def test_aesop_and_macro_trace_interpolate(self) -> None:
        src = ('def a : MacroM Unit := do Macro.trace[debug] "{(by sorry : Nat)}"\n'
               'def b := do aesop_trace[steps] "{(by sorry : Nat)}"\n'
               'def c := do aesop_trace![steps] "{(by sorry : Nat)}"\n'
               'def d : IO Unit := println! "{(by sorry : Nat)}"\n')
        self.assertEqual(tokens(src), [(1, "sorry"), (2, "sorry"), (3, "sorry"), (4, "sorry")])

    def test_trace_and_argument_interpolators(self) -> None:
        src = ('def a : CoreM Unit := do trace[Meta.debug] "{(by sorry : Nat)}"\n'
               'def b (r : Syntax) : CoreM Unit := throwErrorAt r "x {(by admit : Nat)}"\n'
               'def c : String := toString "{sorry}"\n')
        self.assertEqual(tokens(src), [(1, "sorry"), (2, "admit")])

    def test_new_interpolating_syntax_counts(self) -> None:
        self.assertEqual(tokens('syntax "myErr " interpolatedStr(term) : term\n'), [(1, "interpolatedStr")])

    def test_plain_string_with_brace_does_not_hide_later_code(self) -> None:
        src = 'def x := "{"\ntheorem t : False := sorry\ndef y := "z"\n'
        self.assertEqual(tokens(src), [(2, "sorry")])

    def test_token_in_plain_string_text_is_ignored(self) -> None:
        self.assertEqual(tokens('def m := "uses sorry and native_decide"\n'), [])

    def test_escaped_brace_in_string_is_text(self) -> None:
        self.assertEqual(tokens('def m := s!"\\{sorry}"\n'), [])

    # Review finding 1: quoted identifiers confused comment handling.
    def test_quoted_identifier_is_not_a_comment(self) -> None:
        self.assertEqual(tokens("def «--» : Nat := by sorry\n"), [(1, "sorry")])
        self.assertEqual(tokens("def «/-» : Nat := by sorry\n"), [(1, "sorry")])
        # Round-2 review: Lean reads a quoted identifier across lines.
        self.assertEqual(tokens("def «/-\n» : Nat := by sorry\n"), [(2, "sorry")])

    def test_quoted_identifier_is_not_a_token(self) -> None:
        self.assertEqual(tokens("def «sorry» : Nat := 1\n"), [])

    def test_raw_string_is_text(self) -> None:
        self.assertEqual(tokens('def r := r#"a "sorry" b"#\ntheorem t : False := sorry\n'), [(2, "sorry")])

    # Review finding 2: axiom only matched at the start of a line.
    def test_axiom_after_set_option_in(self) -> None:
        self.assertEqual(tokens("set_option autoImplicit false in axiom probe : False\n"), [(1, "axiom")])

    def test_axiom_after_attribute_and_modifiers(self) -> None:
        self.assertEqual(tokens("@[simp] private axiom a : True\n"), [(1, "axiom")])

    def test_axioms_and_qualified_names_are_not_axioms(self) -> None:
        self.assertEqual(tokens("#print axioms foo\ndef g := Lean.axiom\n"), [])

    # Behaviour the review checked and that must keep working.
    def test_nested_block_comments_and_dash_in_strings(self) -> None:
        src = '/- a /- sorry -/ sorry -/\ndef s := "-- not a comment" ++ "x"\ntheorem t : False := sorry\n'
        self.assertEqual(tokens(src), [(3, "sorry")])

    def test_layout_is_kept(self) -> None:
        src = 'def a := s!"{x}\n" -- c\n/- d\n-/ «e f»\n'
        out = hygiene.strip_comments_and_strings(src)
        self.assertEqual(len(out), len(src))
        self.assertEqual(out.count("\n"), src.count("\n"))


if __name__ == "__main__":
    unittest.main()
