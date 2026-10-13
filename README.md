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

Diagnostics identify the source location and unsupported construct. A warning
repeated in the same words within one phase of a build prints once, at its
first site, with its count; `-v` lists every site, `--porcelain` gives JSON
output, and `leantex --help` shows all options. A loss of the PDF's page, such
as a line that runs past the margin, is reported only when the build writes a
PDF.

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
margins if it still overhangs. HTML inside Markdown is read, never passed
through to any output: a comment on lines of its own shows nothing, `<br>`
breaks the line as a Markdown hard break does, an empty `<a name="…">` is a
link target, and a `<details>` block with a plain `<summary>` is a
disclosure: the HTML page ships the browser's own collapsible element, open
where the tag says `open`, and the PDF and the printed page set it expanded
(in a browser that styles a disclosure's content, `::details-content`, as
current Chromium does; an older one prints a closed disclosure closed);
any other tag is an error at its position whose help names the Markdown to
write instead. A Markdown document sets on a wider text block
than an article, with its code in a monospaced face (see Fonts and themes):
code blocks at `\footnotesize`, two sizes below the text, with long lines
wrapped to stay on the page, never inside a name or an operator such as
`:=` — in the PDF at a space where one fits, in a browser at a space or
between two such tokens — and inline code free to break after
punctuation such as `_`, `.`, `/` or `-` where a line needs it. A Markdown
fragment included in TeX keeps its tables' fit and takes its page, code and
line breaks from the TeX document around it. Include one with:

```tex
\usepackage{markdown}
% Inside the document:
\markdownInput{notes.md}
```

Source files are read as UTF-8 unless a byte-order mark says UTF-16, and a
line ends at LF, CR LF or a CR alone. A TeX document that declares
`\usepackage[latin1]{inputenc}` (or `latin9`, `cp1252`, `ansinew`,
`applemac`) has every file it reads read in that encoding, byte for byte as
pdfLaTeX reads it, unless a file is evidently UTF-8: valid UTF-8, or more
UTF-8 sequences than stray bytes. `applemac` follows Apple's current Mac OS
Roman table, so 0xDB is the euro sign where pdfLaTeX still prints ¤, and a
few symbols read as Apple has them where pdfLaTeX prints a near neighbour.
`\inputencoding` does not switch encodings partway through a file; it is
named where it stands. Bytes that are not text, U+0000 among them, become
U+FFFD, and one warning per file lists their offsets. The document still
builds, as long as one of its fonts has a glyph for U+FFFD.

See the [example documents](testdata/corpus) and
[package compatibility index](testdata/compat-index) for supported syntax.

## Fonts and themes

Use installed `.ttf` or `.otf` fonts, or the faces of a `.ttc` or `.otc`
collection (named by family; a path such as `LEANTEX_FONT` or a fontspec file
name must still be a `.ttf` or `.otf`), through `\setmainfont{Family Name}` or
`\fonts{body="Family Name"}`. List available families with `leantex fonts`;
add search directories with `--font-dir` or `LEANTEX_FONT_PATH`.
The fonts of the TeX distribution whose `lualatex` (else `luatex`, else `tex`)
comes first on `PATH` are found without running TeX: the `fonts/opentype` and
`fonts/truetype` directories of `~/texmf` (and macOS's `~/Library/texmf`), of
the site's `texmf-local` (or a package's `/usr/local/share/texmf`), and of the
distribution's trees in TeX Live's own layout (`texmf-dist`) and in the
Debian, Fedora, Arch, Homebrew, MacPorts, FreeBSD and Nix packages' layouts.
To bundle fonts with a document, use `\fonts{dir="fonts",body="Family Name"}`.
A document that declares no typewriter face sets its code in the text face's
matching monospaced face where one is installed, else in the first of SF
Mono, Menlo, DejaVu Sans Mono and Liberation Mono that is installed with
its bold and both its italics or neither, else, for a TeX document, in Latin Modern Mono where a TeX
distribution installs it, and warns only when none is. A TeX document that
declares its text face takes Latin Modern Mono first, as lualatex does,
unless that face's own monospace is installed and matches its x-height more
closely, within 6% — Fira Mono beside Fira Sans, Source Code Pro beside
Source Sans Pro or Source Serif Pro, IBM Plex Mono beside IBM Plex, Noto Sans
Mono beside Noto Sans or Noto Serif, DejaVu Sans Mono beside DejaVu Serif —
which then comes first. A
family installed without italics still serves: italic code sets upright in
it, and a note says so. A document that bundles its fonts takes these from its own font
directory first, then from the computer's.

List themes with `leantex themes` and select one with `\theme{moloch}`.

In HTML, the colours the stylesheet's rules paint and every named colour are
CSS custom properties a host stylesheet can override on `:root`. A colour role
is `--ltx-<key>`, named by its `\palette` key (`--ltx-bg`, `--ltx-fg`,
`--ltx-alert`, `--ltx-frametitlebg`, `--ltx-codekeyword`, …), and a page
declares exactly the roles something on it reads. Three keys colour the HTML
page alone, which the PDF does not paint: `tint` the code panel
(`--ltx-tint`), `focus` the focus ring (`--ltx-focus`), which follows the
accent (`--ltx-accent`) where nothing declares it, and `rule` a slide's
border on the paged deck (`--ltx-rule`). A colour from `\definecolor{name}` is
`--ltx-c-name`, letters and digits as written and any other character as `_`
and its six hex digits, and text set in it reads that property. A role the
document leaves undeclared is declared as the role it defaults to, so
overriding `--ltx-fg` also moves the code and section-title ink that follow
it. A paint the palette in force decides for one element — a block's title
band and body, a listing's panel, a standout frame's footline, an overlay's
covered ink, a code colour the engine derives where nothing declares its
role — is stated on the element as its value. The previous names (`--bg`, `--fg`, `--muted`,
`--ink`, `--surface`, `--accent`, `--tint`, `--rule` and each colour's own
name, where the stylesheet reads no property of that name) remain readable for
one release; override the `--ltx-*` property instead.

A palette can be generated from three seeds, an ink, a paper and one accent:

```tex
\palette[seeds]{ ink = #2B2440, paper = #FFFFFF, accent = #E85D2A }
```

The seeds ship as given; every other colour is derived from them in Oklab
and holds what its uses owe, 0.10 above WCAG 2.2's ratios: tinted grounds
for block titles and bodies (a neutral of the ink's or the paper's hue, and
the accent's own), a muted ink, the accent as text and as an edge on those
grounds, and their tones on the ink. A darkening amber or yellow turns
toward orange, at most 20°; any other hue holds. `blocks = tonal` (the
default) sets block titles in the ink on a tinted band over a lighter body;
`blocks = strong` sets them on the ink over an accent wash. An `alert`, an
`example` or a `neutral` seed may be named too. A deck's grounds stand
further from its page than a document's. The rule, the progress bar and the
title separator are the seeds' too, and a deck that generates its palette
takes none of its default theme's colours. A generated colour standing on a
ground it does not read on — a frame-title or block bar, the standout frame —
takes its family's tone there, and highlighted code takes colours derived
from the same palette, one tone wherever the listing stands. The seeds'
ink, paper and accent declare the page's text, ground and accent, so the later
of a seed and the document's own declaration of that role wins. Any other
colour the document declares, before `\palette[seeds]` or after it, keeps its
value over the generated one, and an element the seeds bind (a block's bar or
body, the progress bar) reads the role it is bound to as the document leaves
it.
Colours may also be written as `oklch(L C H)` or `oklab(L a b)`, as CSS
Color 4 spells them; one outside sRGB loses chroma at its own lightness and
hue.

To use the same palette under lualatex, export it as xcolor and beamer
declarations:

```sh
lake build scripts.palette
lake env lean --run scripts/palette.lean --beamer-blocks Slide 2B2440 FFFFFF E85D2A > colors.tex
```

Load `colors.tex` after the Beamer theme. It defines one colour per role
(`SlideInk`, `SlidePaper`, `SlideAccent`, `SlideMuted`, `SlideMutedOnDark`,
`SlideDiagramMuted`, `SlideSurface`, `SlideSurfaceStrong`, `SlideAccentWash`,
`SlideAccentSoft`, `SlideAccentText`, `SlideAccentEdge`, `SlideAccentOnDark`,
`SlideAlert`, `SlideAlertTitle`, `SlideExampleTitle`) and binds beamer's
`normal text`, `background canvas`, `footline`, `page number in head/foot`,
`alerted text`, six block elements, `progress bar` and `title separator` to
them.
Use `SlideAccent` for decoration and `SlideAccentText` for text on
`SlidePaper` or `SlideSurface`; `SlideAccentEdge` for essential strokes;
`SlideAccentOnDark` for text on `SlideInk`. `--blocks strong` picks the
strong block style, and `--depth documents` a document's lighter grounds.
For a saved palette, replace the three RGB arguments with `--seeds
colors.json`, where the JSON object has exactly `ink`, `paper` and `accent`
hex strings. `--check colors.tex` prints nothing and exits 1 when the file
is not what the seeds generate, so a build can refuse a stale export.

Add `--pygments friendly` (or `default`) to export the code colours the
engine derives from the generated palette: one colour per code role and a
`\SlidePygments` command (named by the prefix) redefining the highlighter's
token macros, with the style's colours only where the palette leaves a role
open. Load it after `minted` and apply it with
`\setminted{formatcom=\SlidePygments}`, so a lualatex build sets the colours
leantex sets; leantex reads the palette itself and runs no `formatcom`.

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
| Syntax highlighting beyond Lean, Python, shell scripts and sessions, and plain text | Pygments (`python3 -m pip install Pygments`) |

Highlighted code sets each token in one of six roles: the ink (identifiers,
a function's, a class's or a module's own name among them, so a definition
reads as the plain uses of its name do), keywords, names (builtins,
decorators, attributes, labels, properties), literals, comments, and errors
— what must not ship, such as a proof hole or an unimplemented branch. A
palette names a role's colour directly
(`\palette{ codeerror = #RRGGBB }`, and likewise `codeink`, `codekeyword`,
`codename`, `codeliteral`, `codecomment`), or by an xcolor colour of the
same name (`\definecolor{codekeyword}{HTML}{A63D24}`, `\colorlet{codecomment}{gray}`),
the spelling a TeX build compiles too. Such a colour is both the colour text
names (`--ltx-c-codekeyword` in HTML) and the role the tokens read
(`--ltx-codekeyword`); a later `\palette` key re-declares the role alone.
The per-type keys `codestring`, `codenumber`, `codebuiltin` and
`codeoperator` colour no listing, and a palette declaring one is told the
role key to declare instead. Otherwise
the role follows the palette: errors take `alert`, comments `muted` (or
the quietest tone of the ink's own hue that still reads as text),
literals `example` (or one more hue, set apart from the ink and the alert),
and keywords and names a tone of the ink's own hue, or the ink itself where
it has no hue of its own, keywords then set apart by weight alone. A role
the palette leaves open takes the minted style's colour for that role.
Every colour the engine derives or adapts stays legible on the ground the
listing stands on; a colour the document declares ships as declared, and
the contrast report names it if it reads too faintly. minted's
`formatcom` runs TeX on the highlighter's own macros and has an effect only
under a TeX engine.

For image support on macOS:

```sh
brew install librsvg libxml2 libxslt poppler
export PATH="$(brew --prefix)/bin:$(brew --prefix libxml2)/bin:$(brew --prefix libxslt)/bin:$PATH"
```

HTML preserves SVG animation. PDF displays a static poster:
`\animategraphics[poster=last]{10}{figure}{}{}` selects the final frame of
supported SVG animations or a PDF frame sequence. Unsupported animation
features are diagnosed.
