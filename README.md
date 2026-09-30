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

elan reads `lean-toolchain` and fetches the pinned Lean (v4.34.1) by itself;
`lake build` takes a few minutes cold. Two more invocations from
`leantex --help`:

```
leantex doc.tex -o out.html     the output name picks the backend
leantex doc.tex --watch         rebuild on every change
```

## LaTeX compatibility

Supported LaTeX commands and package interfaces translate into the engine's
native document model. Document-local `.sty` files are read through that
same translation; leantex does not execute arbitrary TeX packages, Lua code,
or external syntax highlighters. Unsupported constructs produce diagnostics
where they occur. The command-level contracts live in
[`tests/compat-index`](tests/compat-index).

## Fonts

A document names font families, as LaTeX does (`\fonts{ body = "Source Serif
Pro" }`, or fontspec's `\setmainfont`/`\babelfont`), and leantex resolves
them against the fonts installed on the machine: on macOS
`/System/Library/Fonts`, its `Supplemental` folder, `/Library/Fonts`, and
`~/Library/Fonts`; on Linux `/usr/share/fonts` and `~/.fonts`; plus a TeX
Live tree when MacTeX/TeX Live is installed (asked of `kpsewhich`). This lets
leantex find fonts already available to lualatex on the same machine;
the document's commands still need supported translations. Add directories
with `--font-dir` or `LEANTEX_FONT_PATH` (colon-separated); `leantex fonts` lists
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
the HTML. Self-contained SVG images work too. Building one requires
`xmllint` and `rsvg-convert` at document-build time: libxml checks the
supported subset, librsvg supplies the static vector face, and HTML publishes
the original SVG. Fragment references and plain CSS are supported; a paint
server is exactly `url(#id)` — fallback syntax such as `url(#id) red` is
refused. Exporter doctype identifiers are accepted without loading their
DTD and removed from the temporary converter input. DTD declarations,
non-predefined entity references, external resources, scripts and CSS
functions, escapes or at-rules are refused. A PDF image can select a page with
`\includegraphics[page=2]{figure.pdf}`; HTML output containing that PDF
requires Poppler's `pdftocairo` at document-build time to supply its SVG
browser face.

`\animategraphics[poster=last]{10}{figure}{}{}` selects the last page of
`figure.pdf` for the PDF poster. HTML uses `figure.svg` when present, preserving
its authored animation; otherwise it shows the same static poster. Printing
HTML or requesting reduced motion selects the static poster too. The first
frame determines the figure's dimensions, even when the poster has a
different size. The SVG owns playback timing: SMIL `repeatCount="1"` with
`fill="freeze"` plays once and holds the end; `repeatCount="indefinite"`
loops. An SVG embedded as an image has no standard pause control.
PDF JavaScript, playback controls, numbered file sequences and animation
timelines are not implemented and are diagnosed.
PDF 2.0 does not play SVG animations natively.

If browser conversion fails, HTML shows a labelled placeholder and reports
the converter error; the native PDF image remains available.

The converter oracle uses synthetic SVGs, including resources a converter
would silently omit: build `leantex Tests.SvgValidation`, then run
`lake env lean --run scripts/svg-check.lean` on a host with `xmllint` and
`rsvg-convert`. It is separate from the hermetic test suite.

`talk.tex` and `deck.tex` are slide decks: each
frame is one `<section>` of the HTML deck and one page of the PDF handout.
`icons.tex` shows the fontawesome5 spellings
(`\faGithub`, `\faIcon{arrow-up}`): each icon is a glyph in whatever
installed or shipped face covers it, with a required text alternative.
`listings.tex` shows `{lstlisting}` and `{minted}` — numbered captions,
scoped `\lstset` and `\setminted` defaults, line numbers, font sizes, tab
stops and wrapping. Lean and Python listings receive native syntax colors
in PDF and HTML; minted accepts `style=default` and `style=friendly`.
Keywords are bold and comments italic, and the colors adapt to the page
background. Other languages keep their source as plain code.
`math-cancel.tex` shows cancellation strokes and raised arrow targets,
including fractions and scoped colors, in both artifacts.
The siunitx spellings (`\num`, `\qty`, `\si`, `\ang`) provide locale-grouped
digits, real superscripts and unit symbols.
`themed.tex` selects the built-in `moloch` theme (`leantex themes` in help:
`\usetheme{moloch}` or `\theme{moloch}`; `plain` is the quieter bundle) and
shows the frame-title bar, a section page with its progress bar, and a
standout frame. `\chrome{standout-note=true}` keeps an explicit `\framefoot`
note on an unnumbered standout frame. A deck that declares no theme gets the
`daylight` bundle — warm paper, one azure accent, no title bar (`daylight.tex` shows it);
`\theme{default}` opts back to the bare look, as beamer's own
`\usetheme{default}` does. `theme-modern.tex` sketches the rest of the M5b
bundle (dark variant, chrome) and does not build yet.

Builds and runs on Linux and macOS. On the Amazon Linux 2 host the engine is
developed on, the `LEAN_CC`/`LIBRARY_PATH` exports in AGENTS.md work around an
old glibc; macOS needs nothing beyond the quick start.
