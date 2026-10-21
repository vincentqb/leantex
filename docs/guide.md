# leantex guide

## Output and diagnostics

A successful HTML build is one portable file containing its fonts, images
and styles. Ordinary hyperlinks remain links. A document's web page takes the
layout of MyST's book theme: where the screen is wide enough, its outline
stands in a sidebar before the text and stays in view as the page scrolls.
`\page{ web = article }`, or `web: article` in a Markdown document's metadata
block, takes the article theme's instead, the outline in a margin column after a
wider text. A Markdown or code page sets its text at its layout's measure, the
book's sixty digits of its face unless its metadata declares the article's
seventy-two; a TeX page sets its text block's width unless it declares a layout
and no text width, which then sets that layout's measure, the article's
seventy-two digits.

A margin note (`\marginpar`, marginnote's `\marginnote`, sidenotes' numbered
`\sidenote`, or MyST's `:::{aside}` and `:::{margin}` in Markdown) sets on the
PDF page as LaTeX's size files set it: beside the line it stands on, in the
right margin of a one-sided page and the outer one of a two-sided page
(`\reversemarginpar` takes the other), below the note before it, at the
class's `\marginparwidth`, `\marginparsep` and `\marginparpush` or those the
preamble sets, the column never wider than the page's margin holds. A note
standing between paragraphs sets beside the last line of the paragraph before
it, or beside the first line of a list that follows a heading. On the web page
each note is an aside after its paragraph, a note to assistive technology; the
article layout sets it in its margin column beside its anchor, below the note
before it and the outline sharing that column, where the screen holds the
column and the browser anchors positions. A note inside a float, a box, a
table, a note, a display or a heading, one on a frame or card, and one on a
page whose margin leaves no room for the column sets in the text where it
stands, named.

Diagnostics identify the source location and unsupported construct. A warning
repeated in the same words within one phase of a build prints once, at its
first site, with its count; `-v` lists every site, `--porcelain` gives JSON
output, and `leantex --help` shows all options. A loss of the PDF's page, such
as a line that runs past the margin, is reported only when the build writes a
PDF. A setting the document declares that nothing it sets uses is named where
it stands, `W0449`: a colour nothing paints, a face no text is set in, listing
defaults no listing after them reads, a style for an element the document
never shows, or the citation metadata of a markdown document or a Lean page's
directive where it cites nothing. A colour an unknown or refused construct
names still counts as used, that construct's own warning naming the loss: an
unknown command's or environment's arguments, a refused key's value, a
formula the engine cannot set. What a package, class or theme declares is
never named, nor what a file one of them inputs declares, nor a macro's
definition; a file the document inputs is the document's own.

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
write instead. A Markdown document's PDF sets on LaTeX's article text block,
its margins article.cls's, with its code in a monospaced face (see Fonts
and themes): code blocks at `\footnotesize`, two sizes below the text,
with long lines wrapped to stay on the page, never inside a name or an
operator such as `:=` — in the PDF at a space where one fits, in a
browser at a space or between two such tokens — and inline code free to
break after punctuation such as `_`, `.`, `/` or `-` where a line needs
it. A Markdown fragment included in TeX keeps its tables' fit and takes
its page, code and line breaks from the TeX document around it. Include
one with:

```tex
\usepackage{markdown}
% Inside the document:
\markdownInput{notes.md}
```

An included file's text is Markdown alone, as the markdown package reads it
by default: a command, a brace or a `$` in it is text. Its emphasis, links
and code are the document's own constructs, which the TeX document's command
definitions do not reach: renewing `\emph` leaves its emphasis as it was,
where LaTeX's markdown package sets emphasis through `\emph` and follows the
renewal. The document's listing settings, such as `\lstset`'s, do reach its
code blocks, as the package's listings do. Under the package's `hybrid`
option, declared by `\usepackage[hybrid]{markdown}`, `\markdownSetup{hybrid}`
for the rest of its group or `\markdownInput[hybrid]{…}` for one file (and
`hybrid = false` to turn it off), its text is TeX within Markdown's
structure, as the package reads it then: its commands, groups, environments
and math are TeX's, even across its emphasis, links and paragraphs, and the
document's definitions reach it as they reach the TeX around it, though never
a Lean file one of its divisions includes. A verbatim span holding Markdown
syntax and an escaped TeX special such as `\_` stay TeX's as well, which the
package's reading mangles. A `%` comments out the rest of its line before the
Markdown is read, the line's end staying, so the next line begins its own
block where the package would join it to the commented one. A Lean file
`\inputlean` includes sets as its page sets it, whatever commands the
document defines.

Markdown cites as Pandoc does: `[@key]`, `[see @key, p. 33; @other]`,
`[-@key]` without the author's name, and `@key` or `@key [p. 33]` within a
sentence. A key is letters, digits and `_` with single punctuation marks
inside it (`:.#$%&-+?<>~/`), or braced, without white space,
`@{https://example.org/x}`; an e-mail address, code and `\@` stay text, and a
key no natbib key list can hold, one with a comma or a brace, sets as its text,
named. Citations are read only in a document that declares its bibliography,
in a YAML metadata block on its first line, or closing the document after a
blank line, as Pandoc reads one; without it an `@name` stays text (a Lean
file's documentation cites by its own rule, under Code files):

```markdown
---
bibliography: refs.bib
biblio-style: plainnat
natbiboptions: numbers
nocite: '@uncited'
reference-section-title: References
---
```

`bibliography` names one `.bib` file or a list of them, beside the document;
`biblio-style` takes a BibTeX style (plainnat by default, author and year in
brackets), `natbiboptions` natbib's options, `nocite` lists entries to include
uncited (`@*` for all), and `reference-section-title` heads the list where it
sets at the end. The list stands in the first `::: {#refs}` division, else at
the end, and only where something is cited or a Lean division sets its
documentation (`show = "docs"`, under Code files). Citations set as Pandoc's
LaTeX writer sets them under natbib, with the numbering, list, styles and
diagnostics of TeX's `\cite`; the web page links each to its entry. A citation
sets as its label with the reference list, never as a footnote, in every
artifact; only biblatex's `\footcite`, `\smartcite` and their kin in a TeX
document set one in a footnote, as LaTeX does. A citation inside another's
note, or in an image's text alternative, sets as its text, named. The markdown
twin writes citations back in Pandoc's syntax, the list as its division with
the entries in a comment there, and closes with a metadata block naming the
bibliography from where the twin stands, every listed entry as `nocite`,
wherever each citation reads back so in one list; otherwise it sets every
citation as its marks, linked to the entries it writes. Every other metadata
key but `web` (under Output and diagnostics) is named as not read, `csl` among
them, since no CSL processor runs; an included file's `web` is named, its page
taking the including document's layout. A
Markdown file included in TeX reads citations, into the TeX document's
bibliography, where the document loads the markdown package with its
`citations` option or `\markdownInput[citations]{…}` asks, as the markdown
package reads them.

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

`\edef` expands its text where it stands, from the definitions and lengths
in force there as TeX scopes them: text, the document's own macros, and
`\the`, `\number` or `\strip@pt` of a length or a `\dimexpr` over lengths;
a `\protected` macro, `\relax`, a length register and a control after
`\noexpand` stand, and each use of the definition expands to its text. Only
lengths the document allocates with `\newlength` are read, followed through
`\setlength` and `\addtolength`; one that another assignment changes, or code
the engine does not run may change, is not read (but for a bare assignment
opening a brace group, `{\len-1in …}`, which reads as an argument), and
anything else the expansion meets is named and the definition skipped. Lengths
read and print as TeX reads and prints them, each term on its grid of scaled
points, a `\dimexpr` division rounded and calc's truncated: `\the` of
`3.5truein` prints `252.94499pt`, and a `px` is TeX's pixel, a big point. A `\pdfvariable pageattr{…}` (or
`\pdfpageattr`) assignment, in a `shipout/before` hook or not, writes its
`/TrimBox`, `/BleedBox`, `/ArtBox` and `/CropBox` on every page, each inside
the paper, the last assignment standing as in TeX, and names any other
entry; `\expandafter{\the\pdfvariable pageattr …}` adds to the attribute in
force. `shipout/background` and `shipout/foreground` hooks draw their rules
under and over every page from its top-left corner. Boxes, bleed and marks
belong to the printed sheet, so the web page shows none of them.

leanblueprint's commands set as its print macros set them: in a statement or
proof, `\lean`, `\leanok`, `\uses`, `\proves`, `\notready`, `\mathlibok` and
`\discussion` set nothing in the PDF. The web page and the Markdown twin set
one line after the statement or proof: its Lean names as code, each linked
through the load's `link` option, a Lean file's link template whose `{name}`
it fills (`\usepackage[link={https://OWNER.github.io/REPO/docs/find/\#doc/{name}}]{blueprint}`),
else as the web blueprint links them, at `D/find/#doc/<name>` for a
`\dochome{D}`, and unlinked without either; its status in its author's words
(statement or proof marked formalized, marked in Mathlib, or marked not ready
to formalize), which leantex never checks; the statements it proves and
uses, as cross-references such as Lemma 2; and its discussion, linked to the
issue in `\github`'s repository. The commands are the package's where the
document loads it or defines one of them, as a blueprint's print macros do;
a document's own definition stands, though one written in expl3 is skipped,
so the built-in stands in its place. The dependency graph is not drawn, and
a web page's build says so once.

See the [example documents](../testdata/corpus) and
[package compatibility index](../testdata/compat-index) for supported syntax.

## Code files

A Lean (`.lean`), Python (`.py`), shell (`.sh`), C (`.c`, `.h`), C++ (`.cpp`,
`.cc`, `.cxx`, `.c++`, `.hpp`, `.hh`, `.hxx`, `.h++`), Rust (`.rs`) or Java
(`.java`) file reads as a document: its documentation comments are prose, read
as Markdown by their dialect's own rules, and the code between them sets as
listings in the file's language, comments included, every code line exactly as
written; the blank lines around a listing ship nowhere.

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
- **Rust:** rustdoc's `///` and `/** … */` outer docs and `//!` and
  `/*! … */` inner docs that open a line, indented or not, are prose where
  they stand. Inner docs before any code describe the file. As rustdoc reads
  them, a code block naming no language is Rust, its lines opening on `# `
  hidden, and a link to an item, such as `` [`Vec`] `` or
  `[text](std::vec::Vec)`, sets its text unlinked (`W0454`).
- **C and C++:** Doxygen's `/** … */`, `/*! … */`, `///` and `//!` comments
  that open a line are prose where they stand, read as Doxygen reads them:
  `\param`, `\tparam`, `\retval`, `\return`, `\throws`, `\see`, `\note`,
  `\warning` and its other paragraph commands set under Doxygen's labels;
  `\c`, `\p`, `\b` and `\e` mark a word; `\code{.py} … \endcode` is a listing
  in the language its extension names, the file's where it names none; `\ref`
  and `\link` set their text unlinked (`W0454`); and a comment holding `\file`
  describes the file. A command it does not read, such as a grouping, an
  output format's block or a formula, set as code, is named (`W0453`).
- **Java:** a `/** … */` Javadoc comment and a `///` Markdown doc comment that
  open a line are prose where they stand, read as the standard doclet reads
  them: `{@code}`, `{@literal}` and `{@link}`, its text unlinked (`W0454`);
  `<p>`, lists, emphasis, `<code>` and `<pre>`, a Java listing, as Markdown,
  a Javadoc comment's other text literally; and its block tags (`@param`,
  `@return`, `@throws`, `@see`, `@since`, `@author` and the rest) under the
  doclet's labels in its order, a deprecation first. An HTML element or a tag
  it does not read keeps its text and is named (`W0453`).

In these languages a run of line docs is one comment, `////` and `/***` are
plain comments, and a doc form inside a plain comment, a string or a
preprocessor line is no doc. A block doc's prose drops its leading `*`
decoration, and a line doc's its markers; then the margin its lines share
goes.

A code file's documentation cites into the bibliography it declares on a line
of its own, `Bibliography:` and a link to each `.bib` file relative to the
source, which the language's documentation tool shows as a link and leantex
reads as the declaration, setting no text for it. The line stands in a Lean
module docstring, a Python module docstring, a shell file's leading comments,
a Rust inner doc (`//!`), or any Doxygen or Javadoc comment; Javadoc's HTML
spells the link `<a href="refs.bib">refs.bib</a>`:

```lean
/-! Optimal line breaking [KnuthPlass1981].

Bibliography: [references.bib](../docs/references.bib) -/
```

Nothing else names a code file's bibliography: where it declares none, its
citations stay as written, and where its project's `docs/references.bib`
(beneath the nearest directory above the file holding its project's marker: a
lakefile for Lean, as doc-gen4 reads it, `Cargo.toml` for Rust, `pom.xml` or a
Gradle build for Java, `pyproject.toml`, `setup.py` or `setup.cfg` for Python,
`CMakeLists.txt`, `meson.build`, `configure.ac` or a `Makefile` for C and C++)
holds keys it cites, the run names them once with the line to declare. A
Doxygen `\cite key` cites as `[key]` does. A bracket cites as doc-gen4 resolves
one. doc-gen4 registers each key the bibliography holds that its scan finds
between a `[` and the next `]`, resuming after that `]`, so `[[Key]]` alone
registers nothing; then `[Key]`, `[Key][]` and `[Key](Theorem 2)` cite a
registered `Key`, set as its label, and `[text][Key]` sets the author's text,
linked to the entry, where the text is not the key itself and holds no link or
citation, which no link may hold. Pandoc's citations cite a group holding a
key the bibliography holds, any key it lacks set as `?` and named, so
`@List.map`, or a group with no such key, stays as written. Citations set in
the alpha style, as doc-gen4 labels its references (`[Doe12]`), unless the
directive names another (`biblio-style = plain`), and their list closes the
documentation's own References section, else stands at the page's end under
its own heading.

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
**Theorem** (`Tide.height_double`). ∀ rise, n : ℕ, height rise (2 · n) = 2 ·
height rise n; `show = code, math` sets it after the code, `show = math` sets
the statements alone, and `decls = height, height_double` chooses which. The
default is `show = code`. leantex never runs Lean: a statement is Lean's own,
read from the file's facts, which the exporter writes, a small Lake package in
this repository's `export/` directory that the file's project requires and runs
before leantex reads the file (see below). Each elaborated type sets through one
notation table (arithmetic, relations, logic, existence, `×`, `::`, ℕ ℤ ℚ ℝ ℂ and
numerals) and Lean's own notation for the rest: application by juxtaposition,
`f x (g y)`, and field notation, `xs.length`, where the facts name the binder it
reads (facts an older exporter wrote set `List.length xs`). Each outermost
implicit binder the rest of the statement refers to hides, an instance binder
and a binder whose type is a proposition set as hypotheses, every implicit
argument hides, and a string sets as Lean writes it. A variable sets as one
italic word and a constant or numeral upright, both in the body's face, the
symbols in the math face; a line may break after each operator of a statement's
top level, between the names a quantifier binds, and between the arguments of an
application standing alone, never inside a parenthesis. A theorem
Lean holds unproved, or that rests on one, is marked so; a statement Lean
elaborated around an error is not set, and a page that shows math alone sets
that declaration's code in its place. A file whose page asks for statements and
has no facts sets its code alone, with one note; facts that no longer line up
with the file set the code alone too, with one warning to run the exporter
again. The facts quote every command Lean read, so any command edited, moved,
added or cut since the export, a statement, a proof or an `open` alike, no
longer lines up, while a comment or a module's documentation edited within its
lines still does.

The exporter runs in the Lean project, under the project's own toolchain; it
builds and runs on Lean 4.24 and later. Require it in the project's lakefile,
with this repository's clone URL in place of `<repository-url>`:

```toml
[[require]]
name = "leantex-export"
git = "<repository-url>"
rev = "main"
subDir = "export"
```

Then build the project, export the files or modules a document shows, and run
leantex:

```sh
lake build
lake exe leantex-export Tide.lean Tide/Basic.lean
leantex Tide.lean -o Tide.pdf
```

The exporter takes a file by its path, or a module by its name (`Tide.Basic`).
It elaborates each command by command, as `lean` would with Lean's frontend
imported beside the file's imports, so a file's `#eval` and macros run as they
would under `lean`, and writes the file's facts beneath the `.lake/build/leantex`
of the nearest directory above it that holds a lakefile, the file's place there
with `.lean` made `.facts`, where leantex reads them for that file; a note for a
missing or stale facts file names the command to run. `facts = <path>` in a
directive, on `\inputlean` or on a Markdown division names another facts file
instead, beside the Lean file on a page and beside the document in an inclusion,
for a copy of what the exporter wrote; `facts` with no statement or folded proof
to read it for is named and ignored.

`show = prose` says each statement in words instead, its terms as formulas:
**Theorem** (`Tide.le_or_gt`). For all a, b : ℕ, either a ≤ b or b < a. A
quantifier binds typed groups, `x : T`, consecutive binders joining one
quantifier (for all xs : List ℕ and n : ℕ), a binder predicate its relation
(`∀ x ∈ S` as for every x ∈ S, and `∀ k < n` so where its other side names a
variable, which fixes the type), a type holding a quantifier or an arrow in
parentheses, and an outermost implicit binder the rest refers to hides; a binder whose type is a proposition, or an instance one, reads as a
hypothesis, `if …, then …`; `∃` as there is or there are; `∨ ↔ ¬` as either …
or, if and only if, and it is not the case that. A relation stays a formula. Two
plain statements a conjunction joins read A and B; any other conjunction sets as
a numbered list, each conjunct an item, a sentence of its own with its full
stop, a conjunction an item holds a list one level in, and a quantifier opening
a list ends on a colon; where an operand holds it, a hypothesis or one side of
an equivalence, it reads both … and. Indentation groups what the words do not,
as a written proof lays out a statement: a part whose end nothing else would
mark stands as a block, its lines a step in from the block around it and the
lines after it back at that block's indent, all at the paragraph's leading, a
comma or full stop that closes the block ending its last line. A quantifier's,
an existential's or a conditional's scope runs to the end of the block it stands
in, so one that more of its sentence follows is a block, as a hypothesis or a
first side is. An equivalence whose first side needs a block, more than a
formula, a plain relation (one whose words hold none of `and`, `or`, `if`,
`then`, `both` and `either`) or a conjunction, its both opening it, reads
the following are equivalent: and its two sides as a numbered list where a
sentence, an item or a scope holds it, so no item opens on a block; any other
equivalence is a block wherever it stands below the sentence's top or an
item's, its first side a block where it needs one, and its second side then too
where it is more than a formula or a plain relation, so the two stand alike. A negation, conjunction or disjunction as a conjunction's or a
disjunction's first side or as a hypothesis before another, and a relation that
is not plain where more of its sentence follows it, are blocks too, for the eye:

```text
Theorem (Tide.strict_hyp). If
    for every n : ℕ, n = 0,
then False.
```

The web page sets the same lines and lists, and bounds each scope with a
parenthesis at either end, out of sight, which a braille display, a copy and a
screen reader set to say parentheses read; a tagged PDF's lines carry the same
parentheses in their replacement text, and its lists are lists. The markdown
twin opens each line after the first with a hard break and an em and an en space
for each step, and sets each list as a numbered list. The words, with their
blocks' bounds and their items' marks, parse back to the statement they say,
implicit arguments hidden as in the math view. A declaration whose type is no
proposition, or a statement the words cannot say (a hypothesis the rest names, a
`let`), is set as mathematics, once on a page that also shows the math view, and
the run says so.
A directive may give a constant its own words, `#k` standing for its k-th
explicit argument:
`phrase.Tide.height = "the height after #2 steps of #1"` says its terms, and a
phrase that opens with a slot, `phrase.Calm = "#1 is calm"`, its propositions,
each in place of its constant's formula; a relation of the table one of whose
terms takes a phrase sets its symbol between the words, as `n = the height after
2 steps of n`. The run names each phrase it does not take (for no constant, or
several, a second for one constant, for a connective, with other slots than the
explicit arguments, with a comma, a colon, a parenthesis, a brace, a quote or a
full stop standing alone, or words that would
not read back) and each no sentence on the page uses, as on a page that says
nothing in words. Views combine in the order given, as `show = prose, code`,
`show = code, prose` or `show = math, prose, code`.

Two more options shape a Lean file's page. `proofs = collapse` folds each
top-level theorem's proof into a disclosure whose summary is Proof, after its
signature: from the proof's first character, or the next line after a bare
`:= by`, through its last line and the comments closing it. A proof written on
its signature's line stays in place; the disclosure is closed on the web page
and open in print and in the PDF. `proofs = remove` sets Lean's `⋯` in the
proof's place. The default is `proofs = show`. `link` makes each statement's
name a link to its declaration: a GitHub repository's root,
`link = https://github.com/OWNER/REPO`, reaches its lines at the commit the
file's repository holds it at, and any other value is a template whose
`{name}`, `{module}`, `{path}`, `{line}`, `{endline}` and `{commit}` each
declaration fills, percent-encoded, for instance
`link = "https://OWNER.github.io/REPO/docs/{module}.html#{name}"`. git is
asked only for the parts a template names; where it cannot give them (no
repository, a file the commit does not hold, a state it cannot read) the names
are set without links, and a file with changes its commit does not hold is
named, since its links show the committed text. An option a page cannot honour
(a `link` with no statement to carry it, `proofs` on a Python file, a `decls`
on a page that shows no statement) is named; an empty `decls` sets every
declaration, and a key written twice takes its last value.

A document includes a Lean file the same way: in TeX,
`\inputlean[show = {math, code}, decls = {height_double}, proofs = collapse]{Tide.lean}`
(`\usepackage{leantex}`, with `tex/leantex.sty` on lualatex's path, gives
lualatex the same command, which sets the whole file through minted and warns
when an option asks for more), and in Markdown a fenced division,
`::: {.lean file="Tide.lean" show="math, code"}` closed by `:::`. With no
option the whole file is one listing, as `\inputminted{lean4}{Tide.lean}`
sets it. Showing math or prose, or folding or removing proofs, reads the
file's facts, as above, and sets the whole file with each statement at its
declaration; `decls` sets only the declarations it names (theorems,
definitions and axioms), each with its views in order; `phrase.` entries
give constants their words there as a directive's do. An included file's
documentation comments are code, as its source has them, unless `show = docs`
sets the file as its page does, documentation as prose and code as listings.
Its citations then cite into the including document's bibliography: a bracket
cites by the keys of the files the Lean file's module docstring declares, and
the files it cites from join the document's reference list after its own, as
if `\bibliography` named them last (under biblatex, as resources added before
`\printbibliography`), so the citations number and set in the document's style
and a key both hold is set from the document's file. A list the document
writes itself, `thebibliography`, names no file, so they resolve against its
items; where the document has no list they show as `?`, named. A
`bibliography` option or directive key, which the module docstring's line
replaces, and a `biblio-style` are named and ignored, and `docs` beside
another view, `decls` or `proofs` sets the documentation view alone, named.

## The leantex classes

`tex/` holds LaTeX classes leantex reads as its own and lualatex compiles with `tex/` on its path
(`TEXINPUTS` and `LUAINPUTS`): `\documentclass{ltflow}` sets an article on rules both engines
implement. Its body is Latin Modern at 11pt on a 13.6pt leading, and every text line stands on
that leading's grid: headings, lists and theorems space in whole leadings, and the line after a
display or a box moves to the nearest grid line. The type scale is LaTeX's ratio of 1.2,
each size's line a whole number of leadings. The measure is 66 characters of the body face
(memoir's copy-fitting count) to the nearest pica; the text block takes the page's proportions in
whole lines, centred, with twice as much margin below it as above. A paragraph leaves no widow or
club and no page ends on a heading. `\page{ measure = 60 }` sets another measure, `\page{ grid = off }` turns the grid
off, and declared margins replace the derived ones. Presets: `\documentclass[preset=cookbook]{ltflow}`
sets two-sided chapters on `book.cls` with a `recipe` environment (`\begin{recipe}{Title}{Serves
four}`); `preset=cv` sets unnumbered headings, unindented paragraphs, a 75-character measure and
`\entry{dates}{title}{text}`; `preset=resume` is the CV asserted to fit one page with its ink in
the margins and no type below a 1.4mm x-height; `preset=cvweb` is the CV built as a web page and a
markdown twin (`llms.txt`). leantex reads `cookbook`, `cv`, `resume` and `webpage` as class names
for the same presets. Under lualatex `\page`, `\fonts`,
`\palette` and `\theme` are defined by `tex/ltkeys.sty`; a key only leantex reads warns once
there.

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

List themes with `leantex themes` and select one with `\theme{moloch}`. A deck's section
stands on a page of its own only where its theme declares a section page, as `moloch`, `plain`
and `daylight` do, or the document's `\AtBeginSection` sets a frame; under beamer's default
theme it opens no page or slide, as in beamer, its title reaching the footline and its label the
next frame. A deck naming no theme takes `daylight`, section pages included. A hook's own frame is
not set yet: its section stands on a page showing its title, and a warning names it.

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
meets its floor ships as given. A deck hides a pending overlay step, its
place kept, unless it declares a share, as beamer's default `invisible`
covering does; `\setbeamercovered{transparent}` covers it at beamer's 15%,
and `transparent=<n>` or `\palette{ covered = <n>\% }` at that share, while
`dynamic` and `highly dynamic`, which grade each step by its distance, cover
every pending step at its next steps' share, and a share past 99% at 99%,
each named with `W0109`. A share the body declares covers the steps after it
to the end of its group, a frame's or the document's, as beamer applies a
body `\setbeamercovered` to the frames after it, and a `covered` colour, as
every palette colour, from there on: a pending step covers at the share in
force where it starts, each run in the cover of its own colour, an item's
marker with its item, and a step inside a covered one once, by the outer's
cover, where beamer covers it twice. A share declared inside `\only` or
`\alt` covers past it on the steps that typeset it, as beamer's does; the
web page, whose steps no epoch can tell apart, carries it past only an
alternative showing that side on every step. A `\pause` reveals the rest of
its frame after it, past the column, list or block it stands in, as beamer
counts a frame's pauses; one inside `\only` or `\alt` counts on its own
steps alone, where beamer also counts it toward the frame's later pauses on
those steps, and one outside a frame's body, in a note or between frames,
reveals nothing, named with `W0105`. On the web page a step fades in where
it stands, from its share; a hidden one takes no focus or pointer until its
reveal starts. A seed or a declared colour ships as given at any share, and
`W0345` names the ink, or an alert or example a covered step sets, whose
covered form stands under 3:1 from it, or a declared `covered` colour under
3:1 from the ink, unless `\palette[decorative]{ covered = <n>\% }` declares
the covered steps decorative; a text tone the generator derives keeps the
covered-state contract there in every scheme, each covered form, mixed
toward the page in Oklab as the PDF covers and in sRGB as beamer and a web
page's opacity do, quieter on the page and 3:1 from it (SC 1.4.11). A share
at which black on a light page, or white on a dark one, would break the
contract binds nothing. Text on the ink stands at 4.6:1; on a dark
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
hue. A spot colour, an ink a press prints from its own plate, is
`spot("Ink Name", cmyk(c, m, y, k))`, or colorspace's
`\definespotcolor{name}{Ink Name}{c,m,y,k}`: the PDF paints it in a
Separation named by the ink, which a printer reads, over its CMYK
alternate, which the web page previews. `name!30` is a 30% tint; a mix of
an ink with anything but the paper prints as a process colour, named.
A CMYK colour shows on the web page as xcolor projects it, unless the
document names the press it prints for: under an output profile
(`\DocumentMetadata{ colorprofiles = { X = press.icc } }`) it shows, and is
judged for contrast, as that profile prints it. The engine's own colours, a
theme's, highlighted code's and a missing image's box, then print in the
profile's CMYK, a grey in black ink alone; the document's own RGB colours
print as declared.

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
six block elements, `progress bar` and `title separator` to them. As the
document's own file, the colours it leaves unused are named, `W0449`; saved
as a `.sty` file and loaded with `\usepackage` after the theme, they are the
package's.
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
floor, as a poster takes them. `--covered N` holds a deck's derived text
tones to the covered-state contract at the share N% it covers at, 15 under
`\setbeamercovered{transparent}`, and is refused at a depth that never
covers; without it nothing binds, as a deck declaring no share hides its
pending steps.
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
`formatcom`, and reads the export without a loss where a document both
engines build loads it, naming each exported colour only `formatcom` paints
(`W0449`, which `\allow{W0449}` accepts). Such a document keeps
`\palette[seeds]` for leantex, or names the exported colours under the code
roles' own keys (`\colorlet{codekeyword}{SlideCodeKeyword}`), which both
engines read.

Add `--series N`, from 1 to 16, to export colours for a chart's N series,
`SlideSeries1` to `SlideSeriesN`, at the depth `--depth` names. The first is
the accent's text tone with no share binding it: where nothing covers it is
`SlideAccentText`, which is `SlideAlert`, so a chart's subject stands in the
colour of the page's alerts (the ink, where the accent serves as a
container); the covered-state contract binds text, not marks, so where a
share darkens a derived text tone the first series keeps that tone. Each
next one is, of every hue at its tone at the marks' floor
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
| Syntax highlighting beyond Lean, Python, shell scripts and sessions, C, C++, Rust, Java and plain text | Pygments (`python3 -m pip install Pygments`) |

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
