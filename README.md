# leantex

leantex compiles a LaTeX-shaped `.tex` document straight to PDF 2.0 or HTML
in one fast run — no TeX installation, no preamble, no aux-file reruns.

## Quick start

Prerequisite on macOS: the Xcode Command Line Tools, for the linker
(`xcode-select --install`). Documents with SVG images also need the runtime
conversion tools described below.

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
same translation; leantex does not execute arbitrary TeX packages or Lua code.
Installed Pygments lexers can supply checked syntax classifications, as
described below. Unsupported constructs produce diagnostics
where they occur. The command-level contracts live in
[`tests/compat-index`](tests/compat-index).

Include a Markdown file in a TeX document with the standard package spelling:

```tex
\usepackage{markdown}
\begin{document}
Text before the fragment.
\markdownInput{notes.md}
Text after the fragment.
\end{document}
```

The fragment renders in place in PDF and HTML, using the surrounding
document's theme and layout. It uses the same Markdown dialect as a `.md`
document: headings, emphasis, links, images, lists, quotes and fenced code.
Paths resolve from the main document's directory, as for `\input`; errors
inside the fragment name its `.md` file and line. Package-specific Markdown
extensions, options, inline environments and renderer customizations are
not implemented and remain diagnosed.

## Self-contained HTML

A successful HTML build produces one movable `.html` file. Selected embedded
fonts, images, animation posters and the favicon are data URLs; local declared
stylesheets are captured into the file. No neighboring asset directory is
needed. Ordinary hyperlinks and an optional Markdown alternate remain links.

Publication requires a checked page whose rendering references resolve to its
captured bytes (`HtmlResource.close_covers`, `HtmlDoc.emitClosed_covers`).
Unresolved resources, external stylesheets, CSS imports and unsupported
resource-bearing CSS cause E0606 before output is written, including under
`--best-effort`. To use Bulma, declare a readable local framework stylesheet.
The proof covers the emitted tree and captured-resource contract; SVG
validation, font/image decoding and browser behavior remain external checks.

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
the synthetic PNG/JPEG fixtures beside it embed into both artifacts. Self-contained SVG images work too. Building one requires
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

`\includegraphics{figure.svg}` converts the SVG during the build; no exported
PDF is needed. Use `{figure}` to prefer an existing PDF or raster and fall
back to SVG. An explicit `{figure.pdf}` still requires that file.

`\animategraphics[poster=last]{10}{figure}{}{}` selects the last page of
`figure.pdf` when present. With only `figure.svg`, it creates a static vector
poster from the end of one animation cycle, before repeat/fill handling.
This projection also requires `xsltproc`. It supports synchronized plain
`animate` tracks with finite durations in seconds, unitless decimal geometry
and opacity, or absolute `M`/`L` comma-pair paths. Tracks use linear or discrete
`values`; supplied `keyTimes` start at zero and strictly increase, ending at
one for linear tracks and below one for discrete tracks. Linear paths must
keep the same commands. Delays, CSS, referenced targets, other animation
elements and unsupported timing are diagnosed; use a PDF frame sequence for
those. `poster=first` and `poster=0` use the SVG's base drawing; later
numbered posters require a PDF sequence.

These tools must be on the `PATH` of the shell running leantex. One macOS
setup using Homebrew is:

```sh
brew install librsvg libxml2 libxslt
export PATH="$(brew --prefix)/bin:$(brew --prefix libxml2)/bin:$(brew --prefix libxslt)/bin:$PATH"
command -v xmllint rsvg-convert xsltproc
```

Keep that PATH setting in the shell configuration used to build documents.
Existing system XML tools also work; newer XML versions are not required.
HTML that includes a PDF source additionally needs `pdftocairo`
(`brew install poppler`). After installing a missing tool, rebuild the same
document: SVG conversion happens automatically, without a manual PDF export.

HTML publishes the original source or companion SVG unchanged, preserving
its animation; otherwise it shows the same static poster. Printing HTML or
requesting reduced motion selects the static poster too. For a PDF sequence,
the first frame determines the figure's dimensions, even when the poster has
a different size. The SVG owns playback timing: SMIL `repeatCount="1"` with
`fill="freeze"` plays once and holds the end; `repeatCount="indefinite"`
loops. An SVG embedded as an image has no standard pause control.
PDF JavaScript, playback controls and numbered file sequences are not
implemented and are diagnosed.
PDF 2.0 does not play SVG animations natively.

If browser conversion fails, HTML shows a labelled placeholder and reports
the converter error; the native PDF image remains available.
HTML embeds captured image and print-poster bytes as data URLs, so rebuilding
changed bytes updates the image without a neighboring asset directory.

The converter oracle uses synthetic SVGs, including resources a converter
would silently omit, and builds both outputs from SVG sources alone: build
`leantex Tests.SvgValidation Tests.SvgTerminal Tests.SvgBrowser Tests.SvgFaces Tests.SvgPublication`, then run
`lake env lean scripts/svg-check.lean` on a host with `xmllint`,
`xsltproc`, `rsvg-convert` and Poppler. It is separate from the hermetic test
suite.

`talk.tex` and `deck.tex` are slide decks: each frame is one HTML section
with numbered reveal steps and one PDF page per step. Overlay lists select
individual steps: `\uncover<1,4>{...}` selects steps 1 and 4, while
`\uncover<1-4>{...}` selects every step from 1 through 4. Lists and ranges
can be combined, as in `<1,3-5>`.
HTML slide links use `#titlepage`, then `#section-0`, `#section-1`, …
for section dividers, and `#1`, `#2`, … for content frames. Standout frames
advance the content count while hiding their footer. A frame with reveals
uses `#16.1`, `#16.2`, …; `#16` also opens its first reveal. After an
explicit frame-number reset, content links use `#appendix-1`, … to stay
distinct from the main deck. Repeated title pages use `#titlepage-2`, ….
Existing title-based anchors remain available unless they conflict with
a numbered or semantic slide link; such a conflict is diagnosed.
`icons.tex` shows the fontawesome5 spellings
(`\faGithub`, `\faIcon{arrow-up}`): each icon is a glyph in whatever
installed or shipped face covers it, with a required text alternative.
`listings.tex` shows `{lstlisting}` and `{minted}` — numbered captions,
scoped `\lstset` and `\setminted` defaults, line numbers, font sizes, tab
stops and wrapping. Lean and Python listings receive native syntax colors
in PDF and HTML; minted accepts `style=default` and `style=friendly`.
Keywords are bold and comments italic, and the colors adapt to the page
background. Other languages, including `bash` and `sh`, use the built-in
lexers of an installed Pygments (`python3 -m pip install Pygments`).
The compiler checks each reply against the complete original source before
applying colors through the same painter. If classification is unavailable,
it preserves the source as plain code and reports W0393.
`math-cancel.tex` shows cancellation strokes and raised arrow targets,
including fractions and scoped colors, in both artifacts.
The siunitx spellings (`\num`, `\qty`, `\si`, `\ang`) provide locale-grouped
digits, real superscripts and unit symbols.
`themed.tex` selects the built-in `moloch` theme (`leantex themes` in help:
`\usetheme{moloch}` or `\theme{moloch}`; `plain` is the quieter bundle) and
shows the frame-title bar, a section page with its progress bar, and a
standout frame. `\chrome{standout-note=true}` keeps an explicit `\framefoot`
note on a standout frame without showing its number. A deck that declares
no theme gets the `daylight` bundle — warm paper, one azure accent, no title bar
(`daylight.tex` shows it);
`\theme{default}` opts back to the bare look, as beamer's own
`\usetheme{default}` does. `theme-modern.tex` sketches the rest of the M5b
bundle (dark variant, chrome) and does not build yet.

Builds and runs on Linux and macOS. On the Amazon Linux 2 host the engine is
developed on, the `LEAN_CC`/`LIBRARY_PATH` exports in AGENTS.md work around an
old glibc. macOS needs no additional compiler setup beyond the quick start;
image conversion uses the runtime tools listed above.
