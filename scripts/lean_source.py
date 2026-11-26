"""Read Lean source text for the checks in scripts/.

`strip_comments` removes comments and the literal text of string and character literals,
keeping every newline, so that a pattern found in the result is code and its line number is
the line in the file. The scanner follows Lean's lexer where it matters for hiding code:

- `-- …` comments end at the line break; `/- … -/` comments nest;
- a `«…»` identifier ends at the first `»`, and nothing inside it starts a comment, a string
  or a character literal (`def «skip/-» := 0` is a definition, not a comment);
- a string literal handles escapes (`"\\""`), and a raw string (`r#"…"#`) ends at its own
  closing delimiter;
- a character literal is `'a'`, `'"'`, `'\\''`, `'\\n'`, `'\\x41'` or `'\\u0041'`.

A literal starts only where a token starts. The scanner therefore splits the text into tokens
the way Lean's `tokenFn` does. An identifier starts with a letter, `_` or a letter-like
character, and continues with those, digits, `'`, `!`, `?` and subscripts; a `.` followed by an
identifier start or `«` continues it. So `get!` and `x'` are single identifiers and `Foo.r"…"`
is the identifier `Foo.r` followed by a plain string, while a `!` or `?` with no identifier
before it is a token of its own: in `!r"…"`, `?r"…"` and `!'"'` the literal starts right after
it. A number (`2`, `0x1f`, `1.5e3`) is one token: `2r"…"` is a number and a raw string. A name
literal `` `r`` is the name `r`, never a raw string.

Two token boundaries depend on Lean's token table or on the parser, which the scanner does not
have, and the scanner raises `LexError` where they matter: a `#` command name that runs into
characters other than ASCII letters and `_`, or that ends in `r` directly before `"` or `#`
(`#checkr"…"`, where Lean reads `#check` and a raw string), and a raw string directly after a
`.` that does not belong to an identifier (`(x).r"…"`, where Lean may read `r` as a field
name).

Lean decides from the grammar, not from the text, whether `"…{x}…"` is an interpolated string
(after `s!`, `m!`, `throwError` and others) whose braces hold code, or a plain string. The
scanner reads every string both ways. When the interpolated reading fails (an unmatched `{`
in a plain string, say), Lean too can only read the string as plain. When both readings end at
the same place, the scanner keeps the text inside braces as code, which is never less strict
than blanking it. When they end at different places (a string inside the braces,
as in `"{", ".intercalate xs}"`), the scanner takes the interpolated reading directly after
the tokens `s!`, `m!` and `f!` (also in `!s!"…"`), and raises `LexError` anywhere else, including
after an identifier that ends in `s!` (`Foo.s!"…"`): code that reads one way to Lean could then
read another way to the scanner. Write such a string with `s!` or `m!`.
"""

import re

# The tokens after which Lean always reads an interpolated string.
INTERPOLATION_HEADS = ("s!", "m!", "f!")


class LexError(ValueError):
    """The scanner cannot tell how Lean reads the text at `line`."""

    def __init__(self, line, message):
        super().__init__(f"line {line}: {message}")
        self.line = line


def _is_letter_like(c):
    """Lean's `isLetterLike` (Init/Meta/Defs.lean)."""
    v = ord(c)
    return ((0x3B1 <= v <= 0x3C9 and v != 0x3BB)                    # lower Greek except λ
            or (0x391 <= v <= 0x3A9 and v not in (0x3A0, 0x3A3))    # upper Greek except Π, Σ
            or 0x3CA <= v <= 0x3FB                                  # Coptic
            or 0x1F00 <= v <= 0x1FFE                                # polytonic Greek
            or 0x2100 <= v <= 0x214F                                # letter-like symbols
            or 0x1D49C <= v <= 0x1D59F                              # script, double-struck
            or (0x00C0 <= v <= 0x00FF and v not in (0xD7, 0xF7))   # Latin-1 letters
            or 0x0100 <= v <= 0x017F)                               # Latin Extended-A


def _is_subscript_alnum(c):
    """Lean's `isSubScriptAlnum`."""
    v = ord(c)
    return 0x2080 <= v <= 0x2089 or 0x2090 <= v <= 0x209C or 0x1D62 <= v <= 0x1D6A or v == 0x2C7C


def _is_ascii_letter(c):
    return "a" <= c <= "z" or "A" <= c <= "Z"


def _is_digit(c):
    return "0" <= c <= "9"


def is_id_first(c):
    """Lean's `isIdFirst`: whether `c` can start an identifier."""
    return _is_ascii_letter(c) or c == "_" or _is_letter_like(c)


def is_id_rest(c):
    """Lean's `isIdRest`: whether `c` can continue an identifier (`x'`, `get!`, `h₁`)."""
    return (_is_ascii_letter(c) or _is_digit(c) or c in "_'!?" or _is_letter_like(c)
            or _is_subscript_alnum(c))


def _line(text, i):
    return text.count("\n", 0, i) + 1


def _blank(text, start, end):
    """The newlines of `text[start:end]`, so that line numbers stay right."""
    return "\n" * text.count("\n", start, end)


def _at(text, i):
    return text[i] if i < len(text) else ""


def _ident_end(text, i):
    """The index after the identifier that starts at `i` (`is_id_first` or `«`), read as Lean's
    `identFnAux` reads it: parts of identifier characters or `«…»`, joined by `.` when the
    character after the `.` starts another part."""
    j = i
    while True:
        if text[j] == "«":  # «
            close = text.find("»", j + 1)
            if close < 0:
                raise LexError(_line(text, j), "unterminated `«` identifier")
            j = close + 1
        else:
            j += 1
            while j < len(text) and is_id_rest(text[j]):
                j += 1
        after = _at(text, j + 1)
        if _at(text, j) == "." and after and (is_id_first(after) or after == "«"):
            j += 1
        else:
            return j


def _number_end(text, i):
    """The index after the number literal that starts with the digit at `i`, read as Lean's
    `numberFnAux` reads it (`1_000`, `0x1f`, `0b101`, `1.5`, `2e-3`)."""
    def digits(j, ok):
        while j < len(text) and (text[j] == "_" or ok(text[j])):
            j += 1
        return j

    if text[i] == "0" and _at(text, i + 1) in tuple("bBoOxX"):
        ok = {"b": lambda c: c in "01", "o": lambda c: "0" <= c <= "7",
              "x": lambda c: _is_digit(c) or "a" <= c.lower() <= "f"}[text[i + 1].lower()]
        return digits(i + 2, ok)
    j = digits(i + 1, _is_digit)
    if _at(text, j) == "." and _at(text, j + 1) != ".":
        j += 1
        if _is_digit(_at(text, j)):
            j = digits(j, _is_digit)
    if _at(text, j) in ("e", "E"):
        k = j + 1 + (_at(text, j + 1) in ("+", "-"))
        if _is_digit(_at(text, k)):
            j = digits(k, _is_digit)
    return j


def _raw_string_end(text, i):
    """If a raw string literal (`r"…"` or `r#"…"#`) starts at the token start `i`, return the
    index after it."""
    if text[i] != "r":
        return None
    j = i + 1
    while j < len(text) and text[j] == "#":
        j += 1
    if j >= len(text) or text[j] != '"':
        return None
    if i > 0 and text[i - 1] == ".":
        raise LexError(_line(text, i), "a raw string directly after `.`, where Lean may read "
                       "`r` as a field name; put a space before it")
    close = '"' + "#" * (j - i - 1)
    end = text.find(close, j + 1)
    if end < 0:
        raise LexError(_line(text, i), "unterminated raw string literal")
    return end + len(close)


_CHAR_ESCAPE = re.compile(r"""\\(?:[\\"'rnt]|x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4})""")


def _char_literal_end(text, i):
    """If a character literal (`'a'`, `'\\n'`, `'"'`) starts at the token start `i`, return the
    index after it. Lean reads `'` as the start of one unless the next character is `'` too."""
    if text[i] != "'" or _at(text, i + 1) in ("", "'"):
        return None
    if text[i + 1] == "\\":
        match = _CHAR_ESCAPE.match(text, i + 1)
        if not match:
            return None
        j = match.end()
    else:
        j = i + 2
    return j + 1 if _at(text, j) == "'" else None


def _command_name_end(text, i):
    """The index after the command name (`#check`, `#eval`) at `text[i] == "#"`.

    Lean ends it at the longest token in its token table, which the scanner does not have. The
    scanner takes `#` with the ASCII letters and `_` after it. That is where Lean ends the token
    too, or Lean ends it earlier and reads the rest as an identifier, which ends at the same
    place. The rest is a raw string instead only when it is a final `r` before `"` or `#`
    (`#checkr"…"`); the scanner raises `LexError` there, and where other characters follow."""
    end = _ident_end(text, i + 1)
    name = text[i + 1:end]
    if (not re.fullmatch(r"[A-Za-z_]+", name)
            or (name.endswith("r") and _at(text, end) in ('"', "#"))):
        raise LexError(_line(text, i), f"the scanner cannot tell where the `#` command name ends "
                       f"in `#{name}`; put a space after the command name")
    return end


def _plain_string_end(text, i):
    """The index after the string literal at `text[i] == '"'`, read as a plain string."""
    j = i + 1
    while j < len(text) and text[j] != '"':
        j += 2 if text[j] == "\\" else 1
    if j >= len(text):
        raise LexError(_line(text, i), "unterminated string literal")
    return j + 1


def _string(text, i, out):
    """Scan the string literal at `text[i] == '"'`, reading `{…}` as code. Append the result
    (`"`, the code in braces, the newlines of the literal text, `"`) and return the end."""
    out.append('"')
    j = i + 1
    while True:
        if j >= len(text):
            raise LexError(_line(text, i), "unterminated string literal")
        c = text[j]
        if c == '"':
            out.append('"')
            return j + 1
        if c == "\\":
            out.append(_blank(text, j, j + 2))
            j += 2
        elif c == "{":
            out.append(" ")
            j = _code(text, j + 1, out, in_braces=True)
            out.append(" ")
        else:
            if c == "\n":
                out.append("\n")
            j += 1


def _code(text, i, out, in_braces=False):
    """Scan code from `i`. Inside the braces of a string, stop after the matching `}`.

    Each step reads one whole token, comment or whitespace character, so that every step starts
    at a place where Lean can start a token."""
    depth = 0
    # The end and the text of the last identifier, so that a string directly after the token
    # `s!` is known to be interpolated.
    last_word = (-1, "")
    while i < len(text):
        c = text[i]
        if text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text.startswith("/-", i):
            # A comment separates tokens: `by/- c -/admit` is `by admit`.
            end = _block_comment_end(text, i)
            out.append(" " + _blank(text, i, end))
            i = end
        elif c == '"':
            plain_end = _plain_string_end(text, i)
            pieces = []
            try:
                end = _string(text, i, pieces)
            except LexError:
                # Lean cannot read it as an interpolated string, so it is a plain one.
                end, pieces = plain_end, ['""' + _blank(text, i, plain_end)]
            after_head = last_word[0] == i and last_word[1] in INTERPOLATION_HEADS
            if end != plain_end and not after_head:
                raise LexError(_line(text, i), "this string literal ends at a different place "
                               "when its braces are read as code (an interpolated string) and "
                               "when they are read as text; the policy scanner cannot tell how "
                               "Lean reads it")
            out.extend(pieces)
            i = end
        elif (end := _char_literal_end(text, i)) is not None:
            out.append("' '" + _blank(text, i, end))
            i = end
        elif text.startswith("''", i):
            # Lean never starts a character literal at `''`.
            out.append("''")
            i += 2
        elif _is_digit(c):
            end = _number_end(text, i)
            out.append(text[i:end])
            i = end
        elif c == "`" and (is_id_first(_at(text, i + 1)) or _at(text, i + 1) == "\u00ab"):
            # A name literal: what follows is an identifier, never a raw string.
            end = _ident_end(text, i + 1)
            out.append(text[i:end])
            i = end
        elif (end := _raw_string_end(text, i)) is not None:
            out.append('""' + _blank(text, i, end))
            i = end
        elif is_id_first(c) or c == "\u00ab":
            end = _ident_end(text, i)
            out.append(text[i:end])
            last_word = (end, text[i:end])
            i = end
        elif c == "#" and is_id_first(_at(text, i + 1)):
            end = _command_name_end(text, i)
            out.append(text[i:end])
            i = end
        elif in_braces and c == "}" and depth == 0:
            return i + 1
        else:
            if c == "{":
                depth += 1
            elif c == "}":
                depth -= 1
            out.append(c)
            i += 1
    if in_braces:
        raise LexError(_line(text, i - 1), "unterminated `{` in a string literal")
    return i


def _block_comment_end(text, i):
    """The index after the nested block comment that starts at `text[i:i+2] == "/-"`."""
    depth, j = 0, i
    while j < len(text):
        if text.startswith("/-", j):
            depth += 1
            j += 2
        elif text.startswith("-/", j):
            depth -= 1
            j += 2
            if depth == 0:
                return j
        else:
            j += 1
    raise LexError(_line(text, i), "unterminated block comment")


def strip_comments(text):
    """Remove `-- …` and nested `/- … -/` comments, and blank out the literal text of string
    and character literals (a string becomes `""`, or keeps the code in its braces), keeping
    every newline. A block comment becomes one space, so that the tokens on either side stay
    separate. Raise `LexError` where the scanner cannot tell how Lean reads the text."""
    out = []
    _code(text, 0, out)
    return "".join(out)
