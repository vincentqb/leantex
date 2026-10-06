# leantex

A document engine written in Lean 4. Compile TeX or Markdown to PDF 2.0
or self-contained HTML on Linux and macOS.

## Install

Install [elan](https://github.com/leanprover/elan), then build from source.
On macOS, install the Xcode Command Line Tools first (`xcode-select --install`).

```sh
git clone https://github.com/vincentqb/leantex.git
cd leantex
lake build
export PATH="$PWD/.lake/build/bin:$PATH"
leantex testdata/corpus/resume.tex
```

elan downloads the Lean version pinned by the repository.

## Build documents

```sh
leantex document.tex                     # PDF beside the source
leantex document.tex -o document.html    # HTML with embedded assets
leantex document.md -o document.pdf      # Markdown input
leantex document.tex --watch             # Rebuild on changes
```

Declare `\output{formats=pdf,html}` in a document to build both formats.
A successful HTML build is one portable file containing its fonts, images
and styles. Ordinary hyperlinks remain links.

Diagnostics identify the source location and unsupported construct. Use `-v`
for more detail, `--porcelain` for JSON output, or `leantex --help` for all options.

## TeX and Markdown

leantex supports a subset of LaTeX commands and package interfaces, including
document-local `.sty` files. It does not execute arbitrary installed TeX packages
or Lua code; unsupported constructs produce diagnostics. A TeX installation
is not required for native rendering.

Markdown supports headings, emphasis, links, images, lists, quotes and fenced
code. Include a Markdown fragment in TeX with:

```tex
\usepackage{markdown}
% Inside the document:
\markdownInput{notes.md}
```

See the [example documents](testdata/corpus) and
[package compatibility index](testdata/compat-index) for supported syntax.

## Fonts and themes

Use installed `.ttf` or `.otf` fonts through `\setmainfont{Family Name}` or
`\fonts{body="Family Name"}`. List available families with `leantex fonts`;
add search directories with `--font-dir` or `LEANTEX_FONT_PATH`.
To bundle fonts with a document, use `\fonts{dir="fonts",body="Family Name"}`.
macOS `.ttc` collections are not supported.

List themes with `leantex themes` and select one with `\theme{moloch}`.

## Images and code

PNG, JPEG and PDF images embed directly in PDF output. SVG conversion runs
automatically during document builds; no manual PDF export is needed.
Use `\includegraphics{figure.svg}` or an extensionless `{figure}`.

Optional tools must be on the shell's `PATH`:

| Feature | Dependency |
|---|---|
| SVG images | `xmllint`, `rsvg-convert` |
| Final-frame SVG animation posters | `xsltproc`, plus the SVG tools |
| PDF images in HTML | Poppler's `pdftocairo` |
| Syntax highlighting beyond Lean and Python | Pygments (`python3 -m pip install Pygments`) |

For image support on macOS:

```sh
brew install librsvg libxml2 libxslt poppler
export PATH="$(brew --prefix)/bin:$(brew --prefix libxml2)/bin:$(brew --prefix libxslt)/bin:$PATH"
```

HTML preserves SVG animation. PDF displays a static poster:
`\animategraphics[poster=last]{10}{figure}{}{}` selects the final frame of
supported SVG animations or a PDF frame sequence. Unsupported animation
features are diagnosed.
