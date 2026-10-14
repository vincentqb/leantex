# leantex

A document engine written in Lean 4. Compile TeX, Markdown, or a Lean,
Python or shell source file to PDF 2.0 or self-contained HTML on Linux and
macOS.

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
leantex Module.lean -o Module.html       # A Lean, Python or shell file
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

## Code files

A `.lean`, `.py` or `.sh` file reads as a document: its documentation
comments are prose, read as Markdown, and the code between them sets as
listings in the file's language, comments included, every code line exactly
as written; the blank lines around a listing ship nowhere.

- **Lean:** a `/-! … -/` module doc and a `/-- … -/` docstring that open a
  line are prose. A module doc with only lines that declare nothing before it
  (the header's `module`, `prelude` and `import` lines, and `section`,
  `namespace`, `open`, `set_option`, `universe` or `variable` lines) stands
  above them, as the file's description; any other doc comment stands where
  it is, a docstring above its declaration. An indented docstring, such as a
  structure field's, stays in the code, as do `--` and `/- … -/` comments.
- **Python:** the module docstring and each `def` and `class` docstring
  written as one string literal alone on its lines are prose, read as Python
  reads them (escapes, but for `\N{…}`, then `inspect.cleandoc`), a doctest
  (a `>>>` line through the next blank line) as code. The module docstring
  stands above the code before it, and a definition's docstring above its
  decorators and header, whose body follows in the same listing.
- **Shell:** the leading `#` comment block, after the `#!` line, is prose
  above the script.

A file's description that opens on a heading gives the document its title;
otherwise the file's name is the title, shown as the page's first heading.
The first line, or the line after `#!`, may hold a directive taking
`\output`'s keys and `theme`, in the file's own comment syntax; a directive
elsewhere among the leading comments is not read, and the run says so:

```python
#!/usr/bin/env python3
# leantex: formats = pdf, html, theme = gemini
```

A Lean file's directive may also say what its page shows: `show = math, code`
sets each top-level declaration's statement as mathematics above its code,
**Theorem** (`Tide.height_double`). ∀ rise, n ∈ ℕ, height(rise, 2 · n) =
2 · height(rise, n); `show = code, math` sets it after the code, `show = math`
sets the statements alone, and `decls = height, height_double` chooses which.
The default is `show = code`, which never runs Lean. A statement is Lean's own:
a small export that ships with leantex runs as `lake env lean` from the file's
project (the nearest directory holding a lakefile, else the file's own), under
the toolchain elan picks there, and elaborates the file command by command, as
`lean` would with Lean's frontend imported beside the file's imports, so the
file's `#eval` and macros run as they would under `lean`, and lake may write
the project's manifest. Each elaborated type sets through one notation table
(arithmetic, relations, logic, existence, ℕ ℤ ℚ ℝ ℂ and numerals), its
outermost implicit and instance binders hidden unless their type is a
proposition, which sets as a hypothesis, every implicit argument hidden, a
string as Lean writes it, and every other constant upright by its name; a line
may break after each operator of a statement's top level, between the names a
quantifier binds, and after each comma of an application's arguments, with no
change to the spacing. A theorem Lean holds unproved, or that rests on one, is
marked so; a statement Lean elaborated around an error is not set, and a page
that shows math alone sets that declaration's code in its place. Lean's whole
answer is kept under `~/.cache/leantex/lean`, keyed by the file's bytes and
path, the Lean the project runs, its manifest and lakefile, and the Lake trace
of each module the file imports; a refusal of the export is kept the same way.
When Lean gives no answer (no `lake` on PATH, packages not fetched, an import
not built, four minutes passed) the page sets the code alone, whatever `show`
asks, and the run says so once. The export reads Lean 4.24 and later.

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
and holds what its uses owe: tinted grounds for block titles and bodies (a
neutral of the ink's or the paper's hue, and the accent's own), a muted ink,
the accent as text and as an edge, and their tones on the ink. On a light
paper, a colour set on the paper stands at its use's floor
in its medium and no further, so it keeps the most colour its hue holds
there: a deck's text and marks at WCAG 2.2's large-scale 3:1, a document's
and a poster's text at 4.5:1 and their marks at 3:1, and an accent that
meets its floor ships as given. Text on the ink stands at 4.6:1; on a dark
paper, text stands at 6.5:1 and every other colour 0.10 above WCAG 2.2's
ratios. No colour the seeds derive, on any page or ground and in any scheme,
is one of the dark yellow-greens Material 3 never ships (its `DislikeAnalyzer`: HCT hue 90–111, chroma above 16, tone
below 65). A darkening amber turns toward orange, at most 20°, where that
keeps it out of them, and a tone that would still stand among them moves
just past their warm edge; any other hue holds. An accent whose own tone at
its text floor would be one of them, or keep less than half its colour — a
yellow on white — serves the page as a container instead, where the ink
reads on it at 7.1:1, the more-contrast scheme's text target, so one mark
serves every light scheme, as Material's Fidelity scheme keeps a brand
colour: it never sets as text, and `\alert` sets in the ink on a mark of the
accent itself, which both the PDF and the page paint behind the text and
break with it across lines; on a ground the accent reads on, such as the
standout frame, and in a scheme of the other polarity, the alert sets in the
accent's tone there instead, and an alert the document declares sets in its
own colour. The mark is the `alertmark` role,
which any palette may declare. `blocks = tonal` (the
default) sets block titles in the ink on a tinted band over a lighter body;
`blocks = strong` sets them on the ink over an accent wash. An `alert`, an
`example` or a `neutral` seed may be named too. A deck's and a poster's
grounds stand further from their page than a document's. The rule, the progress bar and the
title separator are the seeds' too, and a deck that generates its palette
takes none of its default theme's colours. A generated text colour standing
on a ground it does not read on — a frame-title or block bar, a block's body,
the standout frame — takes its family's tone there, and highlighted code takes colours derived
from the same palette, one tone wherever the listing stands: errors in the
alert, comments in the muted ink, literals in a named example's colour, and
otherwise keywords, names and literals each in a hue of its own, a quarter
turn from one another and from the alert's (or the mark's) around the hue
circle, all in one lightness band at the palette's text floor with the most
colour each hue holds there, as Solarized's accents share one; a quarter
among the disliked yellow-greens turns toward orange out of them, and
where the alert is the ink on a mark, errors take the mark's hue. Keywords take the
quarter nearest the ink's hue where the ink shows one, and a code role the
palette declares under its own key ships as declared and holds the quarter
nearest its hue. Where nothing the code sets in shows a hue, keywords and
names stay in the ink; on a ground where no tone of a role's hue reads as it
does on the page, such as the standout frame, the role sets in the listing's
own ink; and an ink whose hue stands halfway between two quarters can move
its keywords from one to the other with a step of its seed. The seeds'
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
`SlideAlert`, `SlideAlertTitle`, `SlideExampleTitle`, and `SlideAlertMark`
where the accent serves as a container) and binds beamer's `normal text`,
`background canvas`, `footline`, `page number in head/foot`, `alerted text`,
six block elements, `progress bar` and `title separator` to them.
Use `SlideAccent` for decoration and `SlideAccentText` for text on
`SlidePaper`: the text tones meet their floor on the paper, so a TeX build
sets them on a block's fill below it by the fill's ratio, where leantex sets
each run's family tone there; `SlideAccentEdge` for essential strokes;
`SlideAccentOnDark` for text on `SlideInk`; and, where `SlideAlertMark` is
defined, set an alert on it (lua-ul's `\highLight[alertmark]`), as leantex
does: the export names the mark `alertmark` too, which leantex reads as the
role. `--blocks strong` picks the
strong block style, `--depth documents` a document's lighter grounds and
text floor, and `--depth posters` a deck's grounds with a document's text
floor, as a poster takes them.
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
sets the colours leantex sets, Lean's `#` commands aside: leantex reads them as
Lean's own highlighter does, as keywords and `#exit` as an error, where
Pygments reads them as names. leantex reads the palette itself and runs no
`formatcom`, and reads the export without a warning where a document both
engines build loads it. Such a document keeps `\palette[seeds]` for leantex,
or names the exported colours under the code roles' own keys
(`\colorlet{codekeyword}{SlideCodeKeyword}`), which both engines read.

Add `--series N`, from 1 to 16, to export colours for a chart's N series,
`SlideSeries1` to `SlideSeriesN`, at the depth `--depth` names. The first is
`SlideAccentText`, which is `SlideAlert`, so a chart's subject stands in the
colour of the page's alerts (the ink, where the accent serves as a
container). Each next one is, of every hue at its tone at the marks' floor
and three steps beyond it, away from the yellow-greens (on a light paper
the yellows too, olives at a mark's floor) and pure red, the one
farthest from every series before it and from the ink as
the nearest of four readers sees it — typical vision and simulated
protanopia, deuteranopia and tritanopia (Machado, Oliveira and Fernandes,
2009) — of the other temperature than the one before it where one stands
far enough, as Okabe and Ito's Color Universal Design asks. A chart of fewer
series reads the first ones whatever N is, and a series keeps its colour
from chart to chart. Every series stands out from the paper as a mark, at
3:1 on a light paper and 3.1:1 on a dark one; the first reads on it as text,
and no two stand within ΔEOK 0.04 of each other, nor any but the first
within that of the ink, for any of the four readers.

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

HTML preserves SVG animation, and a still SVG with text that leantex draws
whole, with no embedded image, ships as the page's own SVG, its text live in
the page's fonts; any other still SVG ships as its own bytes. PDF displays a static pose:
`\animategraphics[poster=last]{10}{figure}{}{}` selects the final frame of
supported SVG animations or a PDF frame sequence, and the page prints that
pose. Unsupported animation features are diagnosed.
