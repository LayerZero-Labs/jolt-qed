"""Read Lean source text for the checks in scripts/.

`strip_comments` removes comments and the contents of string and character literals, keeping
every newline, so that a pattern found in the result is code and its line number is the line
in the file.
"""

IDENT_CHAR = set("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_'!?.")


def _skip_string(text, i):
    """Return the index after the string literal that starts at `text[i] == '"'`."""
    j = i + 1
    while j < len(text) and text[j] != '"':
        j += 2 if text[j] == "\\" else 1
    return j + 1


def _raw_string_end(text, i):
    """If a raw string literal (`r"…"` or `r#"…"#`) starts at `i`, return the index after it."""
    if text[i] != "r" or (i > 0 and text[i - 1] in IDENT_CHAR):
        return None
    j = i + 1
    while j < len(text) and text[j] == "#":
        j += 1
    if j >= len(text) or text[j] != '"':
        return None
    close = '"' + "#" * (j - i - 1)
    end = text.find(close, j + 1)
    return len(text) if end < 0 else end + len(close)


def _char_literal_end(text, i):
    """If a character literal (`'a'`, `'\\n'`, `'"'`) starts at `i`, return the index after it."""
    if text[i] != "'" or (i > 0 and text[i - 1] in IDENT_CHAR):
        return None
    if text.startswith("\\", i + 1):
        end = text.find("'", i + 2)
        return None if end < 0 or end - i > 12 else end + 1
    if i + 2 < len(text) and text[i + 2] == "'":
        return i + 3
    return None


def strip_comments(text):
    """Remove `-- …` and nested `/- … -/` comments, and blank out the contents of string and
    character literals (a string becomes `""`), keeping every newline."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if depth == 0 and text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth > 0 and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth > 0:
            if text[i] == "\n":
                out.append("\n")
            i += 1
        else:
            end = _raw_string_end(text, i)
            if end is None and text[i] == '"':
                end = _skip_string(text, i)
            if end is not None:
                out.append('""' + "\n" * text.count("\n", i, end))
                i = end
                continue
            end = _char_literal_end(text, i)
            if end is not None:
                out.append("' '")
                i = end
                continue
            out.append(text[i])
            i += 1
    return "".join(out)
