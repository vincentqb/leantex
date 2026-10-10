# leantex

A document engine written in Lean 4. Compile TeX or Markdown to PDF 2.0
or self-contained HTML on Linux and macOS.

## Install

Install [elan](https://github.com/leanprover/elan), then build from source,
with this repository's clone URL in place of `<repository-url>`.
On macOS, install the Xcode Command Line Tools first (`xcode-select --install`).

```sh
git clone <repository-url> leantex
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

Markdown supports headings, emphasis, links, images, lists, quotes, fenced
code and GitHub-style pipe tables, which set as booktabs tables. A table too
wide for the text block narrows its columns and wraps its cells to fit, as
a browser sets it; one whose words alone are too wide sets smaller, down to
`\scriptsize` (`\tiny` only to stay on the paper), centred across both
margins if it still overhangs. A Markdown document sets on a wider text
block than an article, with its code in the text face's matching monospaced
face: code blocks at `\footnotesize`, two sizes below the text, with long
lines wrapped to stay on the page, and inline code free to break after
punctuation such as `_`, `.`, `/` or `-` where a line needs it. A Markdown
fragment included in TeX keeps its tables' fit and takes its page, code and
line breaks from the TeX document around it. Include one with:

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
The fonts of the TeX distribution whose `lualatex` (else `luatex`, else `tex`)
comes first on `PATH` are found without running TeX: the `fonts/opentype` and
`fonts/truetype` directories of `~/texmf` (and macOS's `~/Library/texmf`), of
the site's `texmf-local` (or a package's `/usr/local/share/texmf`), and of the
distribution's trees in TeX Live's own layout (`texmf-dist`) and in the
Debian, Fedora, Arch, Homebrew, MacPorts, FreeBSD and Nix packages' layouts.
To bundle fonts with a document, use `\fonts{dir="fonts",body="Family Name"}`.
macOS `.ttc` collections are not supported.

List themes with `leantex themes` and select one with `\theme{moloch}`.

Generate a coordinated palette from ink, paper and accent RGB seeds:

```sh
lake build scripts.palette
lake env lean --run scripts/palette.lean --beamer-blocks Slide 192A3D FFFFFF FA9D25 > colors.tex
```

Load `colors.tex` after the Beamer theme. The export keeps the three seeds
unchanged and derives block surfaces, muted text and accent colors with
checked contrast. Use `SlideAccent` for decoration and `SlideAccentText` for text
on `SlidePaper` or `SlideSurface`. Use `SlideAccentEdge` for essential strokes
on those surfaces or `SlideAccentSoft`; `SlideAccentOnDark` is text on `SlideInk`.
For a saved palette, replace the three RGB arguments with `--seeds colors.json`,
where the JSON object has exactly `ink`, `paper` and `accent` hex strings.
Regenerate the TeX export after changing the seeds.

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
