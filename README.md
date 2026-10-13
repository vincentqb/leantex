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
Mono beside Noto Sans or Noto Serif, DejaVu Sans Mono beside DejaVu Sans or
Serif —
which then comes first. A
family installed without italics still serves: italic code sets upright in
it, and a note says so. A document that bundles its fonts takes these from its own font
directory first, then from the computer's.

List themes with `leantex themes` and select one with `\theme{moloch}`.

A document that declares no colours ships what its class prints. Its HTML
page is white, as its PDF's paper is; list markers are the printed ink in
every class, on the page and on the light screen alike; the article, report,
book and résumé classes, posters, cards and a deck under beamer's default
theme set their secondary ink (line numbers, footers) in the ink, as LaTeX
prints them, and a markdown note and a web page in a quieter tone generated
from their default seeds, in both artifacts. A deck that declares no theme takes the
`daylight` bundle: warm paper, warm ink and one azure accent, its blocks
tinted cards generated from those seeds as `\palette[seeds]` generates them;
a deck that declares its own ink, paper or accent takes the bundle over
those, its cards generated from its own colours. `moloch`
draws its progress bar, title separator and alerted text in its lineage's
orange, exactly as lualatex sets them, the bar's track in moloch's own mix
of it; the orange reads at 2.6:1 on its page, which the contrast report
names where a document uses the alert. A bundle that states no seeds and no
secondary ink (`moloch`, `plain`, `gemini`) derives one from its ink as a
generated palette does: the quietest tone that reads on its page.

In HTML, the colours the stylesheet's rules paint and every named colour are
CSS custom properties a host stylesheet can override on `:root`. A colour role
is `--ltx-<key>`, named by its `\palette` key (`--ltx-bg`, `--ltx-fg`,
`--ltx-alert`, `--ltx-frametitlebg`, `--ltx-codekeyword`, …), and a page
declares exactly the roles something on it reads. Two keys colour the HTML
page alone, which the PDF does not paint: `focus` the focus ring
(`--ltx-focus`), which follows the accent (`--ltx-accent`) where nothing
declares it, and `rule` a slide's border on the paged deck (`--ltx-rule`).
`tint` (`--ltx-tint`) is the ground a listing stands on: a markdown note
and a web page paint it in both artifacts, and the LaTeX classes, slides,
posters and cards leave verbatim unpainted, as LaTeX does, unless the
document declares it. A colour from `\definecolor{name}` is
`--ltx-c-name`, letters and digits as written and any other character as `_`
and its six hex digits, and text set in it reads that property. A role the
document leaves undeclared is declared as the role it defaults to, so
overriding `--ltx-fg` also moves the code and section-title ink that follow
it. A paint the palette in force decides for one element — a block's title
band and body, a listing's panel, a standout frame's footline, an overlay's
covered ink — is stated on the element, through its role's property where
the page declares one; a code colour is its code role's property, which the
page states for a listing on its own code ground. The previous names (`--bg`, `--fg`, `--muted`,
`--ink`, `--surface`, `--accent`, `--tint`, `--rule` and each colour's own
name, where the stylesheet reads no property of that name) remain readable for
one release; override the `--ltx-*` property instead.

A web page offers its reader's colour schemes. A document's page ships
print, the light and dark screens, and each screen's increased contrast
(`prefers-contrast: more`); a deck, a poster and a card ship print, the
screen of their page's polarity and its increased contrast.
`\output{ schemes = print, light }` names them instead, from `print`,
`light`, `dark`, `lightMore` and `darkMore`. The colours a document declares
ship exactly in print and on the screen of their page's polarity. Every
other scheme carries them: on the other polarity each keeps its distance
from the page and its hue, and where the reader asks more contrast a colour
that falls short of the gate there (7:1 for text, 4.5:1 for large text and
edges) moves only as far as it must — or, where no tone of its hue can, the
ground under it does. Generated colours are generated again
for each scheme, or carried as declared ones are where their seeds generate
nothing there. A scheme that cannot carry a colour legibly is dropped from
that page alone, and the build names the colour once. Under
`forced-colors: active`, frame-title bars, standout frames and block title
bands keep a border, and on the screen of the other polarity than the
page's, images that see through and pictures stand on a plate of the page
as it prints. Highlighted code ships in every scheme:
each token wears its Pygments type's class behind `tok-` (`tok-k`,
`tok-s2`), whose rule reads its code role's property, and a listing whose
colours differ from the page's states them on its own box. A listing panel
on a `\definecolor` colour (minted's `bgcolor`) is carried as a ground, so
it states its colour in each scheme and follows no override of that
colour's `--ltx-c-` property, which text set in the colour still reads.

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
from the same palette, one tone wherever the listing stands: errors in the
alert, comments in the muted ink, literals in a named example's colour, and
otherwise keywords, names and literals each in a hue of its own, spaced
around the hue circle from the ink's and the alert's. Keywords keep the
ink's hue where it stands 60° or more from every other hue the code sets
in, and a code role the palette declares under its own key ships as
declared and the others are spaced around it. Where nothing the code sets
in shows a hue, keywords and names stay in the ink; on a ground where no
tone of a role's hue reads as it does on the page, such as the standout
frame, the role sets in the listing's own ink; and two arcs within a few
degrees of each other are chosen between by width, so seeds a step apart
can move a role's hue across the circle. The seeds'
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
engine derives from the generated palette: one colour per code role, a
command setting its argument in that colour (`\SlideCodeKeywordTok`), and a
`\SlidePygments` command (named by the prefix) redefining the highlighter's
token macros, with the style's colours only where the palette leaves a role
open. Load it after `minted` and `xcolor` (beamer loads `xcolor` itself)
and apply it with `\setminted{formatcom=\SlidePygments}`, so a lualatex build
sets the colours leantex sets; leantex reads the palette itself and runs no
`formatcom`, and reads the export without a warning where a document both
engines build loads it. Such a document keeps `\palette[seeds]` for leantex,
or names the exported colours under the code roles' own keys
(`\colorlet{codekeyword}{SlideCodeKeyword}`), which both engines read.

Add `--series N`, from 1 to 16, to export colours for a chart's N series,
`SlideSeries1` to `SlideSeriesN`, at the depth `--depth` names. The first is
`SlideAccentText`, which is `SlideAlert`, so a chart's subject stands in the
colour of the page's alerts. Each next one is the hue and tone farthest from
every series before it and from the ink, so a chart of fewer series reads
the first ones whatever N is, and a series keeps its colour from chart to
chart. Every series stands out from the paper as a mark, at 3.1:1 or more,
the first reads on it as text, and no two stand within ΔEOK 0.04 of each
other, nor any but the first within that of the ink.

## Images and code

PNG, JPEG and PDF images embed directly in PDF output. SVG images are read
and drawn by leantex itself, with no tool and no manual PDF export: shapes,
paths, gradients, clips, symbols and CSS draw as vectors, embedded PNG and
JPEG images embed as they would from `\includegraphics`, and an SVG's text
sets in the document's own fonts, so it matches the page and stays
selectable. Use `\includegraphics{figure.svg}` or an extensionless
`{figure}`. A feature leantex does not draw (a filter, a mask, a marker) is
named in a warning; with `rsvg-convert` installed, that one figure is drawn
by librsvg instead, and `\figures{ convert = none }` keeps every figure the
engine's own. An SVG's `<title>` is its text alternative when the document
gives none. SVG files may be UTF-8, UTF-16, or any single-byte encoding a
browser reads (`windows-1252`, the ISO 8859 family, KOI8 and others); save
a Shift_JIS, GBK, Big5, EUC or UTF-32 file as UTF-8.

Optional tools must be on the shell's `PATH`:

| Feature | Dependency |
|---|---|
| SVG features leantex does not draw | `rsvg-convert` |
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
it has no hue of its own, keywords then set apart by weight alone; a palette
generated from seeds gives keywords and names a hue of their own each (see
`\palette[seeds]` above). A role
the palette leaves open takes the minted style's colour for that role.
Every colour the engine derives or adapts stays legible on the ground the
listing stands on; a colour the document declares ships as declared, and
the contrast report names it if it reads too faintly. minted's
`formatcom` runs TeX on the highlighter's own macros and has an effect only
under a TeX engine.

For image support on macOS:

```sh
brew install librsvg poppler
```

HTML preserves SVG animation, and a still SVG with text ships as the page's
own SVG, its text live in the page's fonts. PDF displays a static pose:
`\animategraphics[poster=last]{10}{figure}{}{}` selects the final frame of
supported SVG animations or a PDF frame sequence, and the page prints that
pose. Unsupported animation features are diagnosed.
