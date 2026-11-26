"""Read Lean source text for the checks in scripts/.

`strip_comments` removes comments and the literal text of string and character literals,
keeping every newline, so that a pattern found in the result is code and its line number is
the line in the file. The scanner follows Lean's lexer where it matters for hiding code:

- `-- …` comments end at the line break; `/- … -/` comments nest;
- a `«…»` identifier ends at the first `»`, and nothing inside it starts a comment, a string
  or a character literal (`def «skip/-» := 0` is a definition, not a comment);
- a string literal handles escapes (`"\\""`), and a raw string (`r#"…"#`) ends at its own
  closing delimiter;
- a character literal is `'a'`, `'"'`, `'\\''`, `'\\n'`, `'\\x41'` or `'\\u{1F600}'`.

Lean decides from the grammar, not from the text, whether `"…{x}…"` is an interpolated string
(after `s!`, `m!`, `throwError` and others) whose braces hold code, or a plain string. The
scanner reads every string both ways. When the interpolated reading fails (an unmatched `{`
in a plain string, say), Lean too can only read the string as plain. When both readings end at
the same place, the scanner keeps the text inside braces as code, which is never less strict
than blanking it. When they end at different places (a string inside the braces,
as in `"{", ".intercalate xs}"`), the scanner takes the interpolated reading directly after
`s!`, `m!` and `f!`, and raises `LexError` anywhere else: code that reads one way to Lean could
then read another way to the scanner. Write such a string with `s!` or `m!`.
"""

import re

# Lean's `isLetterLike` and `isSubScriptAlnum`, besides ASCII letters, digits, `_`, `'`, `!`, `?`.
_LETTER_LIKE = re.compile(
    "[\u03b1-\u03c9\u0391-\u03a9\u03ca-\u03fb\u1f00-\u1ffe\u2100-\u214f"
    "\u2080-\u2089\u2090-\u209c\u1d62-\u1d6a\u2c7c\U0001d49c-\U0001d59f]")


class LexError(ValueError):
    """The scanner cannot tell how Lean reads the text at `line`."""

    def __init__(self, line, message):
        super().__init__(f"line {line}: {message}")
        self.line = line


def is_ident_char(c):
    """Whether `c` can continue a Lean identifier (`x'`, `h₁`, `α`)."""
    return (c.isalnum() and c != "\u03bb") or c in "_'!?" or bool(_LETTER_LIKE.match(c))


def _line(text, i):
    return text.count("\n", 0, i) + 1


def _blank(text, start, end):
    """The newlines of `text[start:end]`, so that line numbers stay right."""
    return "\n" * text.count("\n", start, end)


def _raw_string_end(text, i):
    """If a raw string literal (`r"…"` or `r#"…"#`) starts at `i`, return the index after it."""
    if text[i] != "r" or (i > 0 and is_ident_char(text[i - 1])):
        return None
    j = i + 1
    while j < len(text) and text[j] == "#":
        j += 1
    if j >= len(text) or text[j] != '"':
        return None
    close = '"' + "#" * (j - i - 1)
    end = text.find(close, j + 1)
    if end < 0:
        raise LexError(_line(text, i), "unterminated raw string literal")
    return end + len(close)


def _char_literal_end(text, i):
    """If a character literal (`'a'`, `'\\n'`, `'"'`) starts at `i`, return the index after it."""
    if text[i] != "'" or (i > 0 and is_ident_char(text[i - 1])):
        return None
    if text.startswith("\\", i + 1):
        match = re.compile(r"\\(?:x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.)'").match(text, i + 1)
        return match.end() if match else None
    if i + 2 < len(text) and text[i + 1] != "\n" and text[i + 2] == "'":
        return i + 3
    return None


def _plain_string_end(text, i):
    """The index after the string literal at `text[i] == '"'`, read as a plain string."""
    j = i + 1
    while j < len(text) and text[j] != '"':
        j += 2 if text[j] == "\\" else 1
    if j >= len(text):
        raise LexError(_line(text, i), "unterminated string literal")
    return j + 1


def _interpolation_head(text, i):
    """Whether the string at `i` directly follows `s!`, `m!` or `f!`, after which Lean always
    reads an interpolated string."""
    return (i >= 2 and text[i - 2:i] in ("s!", "m!", "f!")
            and (i == 2 or not is_ident_char(text[i - 3])))


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
    """Scan code from `i`. Inside the braces of a string, stop after the matching `}`."""
    depth = 0
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
        elif c == "\u00ab":  # «
            end = text.find("\u00bb", i + 1)
            if end < 0:
                raise LexError(_line(text, i), "unterminated `«` identifier")
            out.append(text[i:end + 1])
            i = end + 1
        elif c == '"':
            plain_end = _plain_string_end(text, i)
            pieces = []
            try:
                end = _string(text, i, pieces)
            except LexError:
                # Lean cannot read it as an interpolated string, so it is a plain one.
                end, pieces = plain_end, ['""' + _blank(text, i, plain_end)]
            if end != plain_end and not _interpolation_head(text, i):
                raise LexError(_line(text, i), "this string literal ends at a different place "
                               "when its braces are read as code (an interpolated string) and "
                               "when they are read as text; the policy scanner cannot tell how "
                               "Lean reads it")
            out.extend(pieces)
            i = end
        elif (end := _raw_string_end(text, i)) is not None:
            out.append('""' + _blank(text, i, end))
            i = end
        elif (end := _char_literal_end(text, i)) is not None:
            out.append("' '")
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
