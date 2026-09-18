# leantex

leantex compiles a LaTeX-shaped `.tex` document straight to PDF 2.0 or HTML
in one fast run — no TeX installation, no preamble, no aux-file reruns.

## Quick start

Prerequisite on macOS: the Xcode Command Line Tools, for the linker
(`xcode-select --install`).

```
curl -sSf https://elan.lean-lang.org/elan-init.sh | sh
lake build
./.lake/build/bin/leantex path/to/doc.tex
```

elan reads `lean-toolchain` and fetches the pinned Lean (v4.34.0) by itself;
`lake build` takes a few minutes cold. Two more invocations from
`leantex --help`:

```
leantex doc.tex -o out.html     the output name picks the backend
leantex doc.tex --watch         rebuild on every change
```

## Fonts

A document names font families, as LaTeX does (`\fonts{ body = "Source Serif
Pro" }`, or fontspec's `\setmainfont`/`\babelfont`), and leantex resolves
them against the fonts installed on the machine: on macOS
`/System/Library/Fonts`, its `Supplemental` folder, `/Library/Fonts`, and
`~/Library/Fonts`; on Linux `/usr/share/fonts` and `~/.fonts`; plus a TeX
Live tree when MacTeX/TeX Live is installed (asked of `kpsewhich`). So a
document that compiles under lualatex on a machine compiles under leantex on
the same machine: the fonts it names are there. Add directories with
`--font-dir` or `LEANTEX_FONT_PATH` (colon-separated); `leantex fonts` lists
every family the scan can see, and a family it cannot is error E0403 naming
the nearest ones. The first build scans once and caches under
`~/.cache/leantex` (or `$XDG_CACHE_HOME/leantex`).

A document that ships its own fonts names their directory, relative to
itself, and then renders the same on every machine whatever is installed:

```
\fonts{ dir = "fonts", body = "Source Serif Pro", sans = "Open Sans" }
\setmainfont{SourceSerifPro-Regular.otf}[Path=fonts/]    % the fontspec spelling
```

A font file name denotes its family, so the bold and italic beside it are
found too. A document that declares no `\fonts` gets a default sans face
from the same scan (`LEANTEX_FONT=<path to a .ttf/.otf>` overrides it).
macOS `.ttc` font collections are not yet readable and are skipped.

## Try it

`tests/corpus/*.tex` are ready-made examples, and every one that names a
font ships it in `tests/corpus/fonts/` (Source Serif Pro, Source Code Pro,
Open Sans, and an invented icon face — see the license files there), so
they build on any machine:

```
./.lake/build/bin/leantex tests/corpus/resume.tex
```

`declared.tex`, `layout.tex`, and `paragraphs.tex` name no font and take the
machine's default sans. `images.tex` shows `\includegraphics` and `figure`:
the synthetic PNG/JPEG fixtures beside it embed into the PDF and link from
the HTML. `talk.tex` and `deck.tex` are slide decks: each
frame is one `<section>` of the HTML deck and one page of the PDF handout.
`icons.tex` shows the fontawesome5 spellings
(`\faGithub`, `\faIcon{arrow-up}`): each icon is a glyph in whatever
installed or shipped face covers it, with a required text alternative.
`themed.tex` selects the built-in `moloch` theme (`leantex themes` in help:
`\usetheme{moloch}` or `\theme{moloch}`; `plain` is the quieter bundle) and
shows the frame-title bar, a section page with its progress bar, and a
standout frame. `theme-modern.tex` sketches the rest of the M5b bundle
(dark variant, chrome) and does not build yet.

Builds and runs on Linux and macOS. On the Amazon Linux 2 host the engine is
developed on, the `LEAN_CC`/`LIBRARY_PATH` exports in AGENTS.md work around an
old glibc; macOS needs nothing beyond the quick start.
