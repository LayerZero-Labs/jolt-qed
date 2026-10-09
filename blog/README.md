# Jolt QED blog

This is a Zola 0.23+ site. From this directory, run `zola serve` for a local preview and `zola build` to generate the site.

## Posts and tutorials

Put standalone posts directly under `content/blog/`. Put tutorial documents under `content/tutorials/`, give every document in a series the same `tutorials` taxonomy value, and assign increasing `weight` values to keep that series in reading order:

```toml
+++
title = "A tutorial, part 1"
date = 2026-10-01
weight = 10

[taxonomies]
tutorials = ["Example Tutorial"]
tags = ["proofs", "Lean"]
+++
```

The tutorials index is at `/tutorials/`; each series page lists all of its documents and shows the count. Tutorial documents get Previous and Next links when the adjacent weighted document belongs to the same series. Regular blog posts stay under `/blog/`. For a longer document with colocated assets, use a directory containing an `index.md` file.

## Math and code

MathJax is enabled site-wide. Use `$...$` or `\(...\)` inline, and `$$...$$` or `\[...\]` for display equations. Fenced code blocks are syntax highlighted with Zola's built-in Giallo highlighter:

````markdown
```lean
theorem example : True := trivial
```
````

Use a language name after the opening fence. Code fence annotations such as `,linenos` enable line numbers.

## Tera components

Zola 0.23 replaces shortcodes with Tera components. Components live in `templates/components.html` and are available directly in Markdown:

```tera
{{<callout title="Definition" message="A concise note for the reader."/>}}
{{<figure src="/images/diagram.svg" alt="A diagram of the proof structure" caption="Proof structure"/>}}
```

Put shared images in `static/` (or beside an individual post for page-specific assets). Escape literal Tera delimiters in examples with `{% raw %}...{% endraw %}`.
