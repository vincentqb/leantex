module

public import LeanTex.Core.Bib
public import LeanTex.Core.BibModel
public import LeanTex.Core.BibText
public import LeanTex.Core.BibLatex
public import LeanTex.Core.BibPunct
public import LeanTex.Core.Ir
import LeanTex.Core.Collate
import LeanTex.Core.BibMacro
import LeanTex.Core.Nfc
import Std.Data.HashSet

/-! A bibliography style, decomposed the way biblatex decomposed `.bst`
files: independent pure choices — how a citation renders inline, how the
reference list is ordered, which fields each entry type contributes in
what order, the order a name is written in, whether first names abbreviate
to initials (the last two carried by `NameFormat`), the month macros, and
alpha's labels. `unsrtnat` is one record; `plainnat` another over the same
field orders; `abbrvnat` and `abbrv` set the abbreviation axes; `alpha`
the labels; a style the engine does not know falls back to a record, never
to a separate code path. The formats transcribe plainnat.bst (Daly,
natbib's companion style, which `unsrtnat.bst` shares verbatim minus the
SORT pass) and plain.bst (`plainSteps`), each over the BibTeX view of the
one entry model (`Database.read`); a document that loads biblatex has its
list set by biblatex's standard drivers instead (`renderBbl`). -/

namespace LeanTex.Core.Bib

open LeanTex.Core

/-- How the reference list is ordered: `citation` keeps first-citation
order (the "unsrt" in `unsrtnat`); `plain` sorts by plain.bst's key — the
names, the year, the title (FUNCTION {presort}); `alpha` by alpha.bst's —
the label, then plain's key; `authorYear` by
plainnat.bst's — the label, the names, the year, the cite key, the title;
`bbl` is a biblatex sorting template (biblatex.def
`\DeclareSortingTemplate`, `bblTemplate`) under the load's options —
`nty` the numeric styles' default (name, title, year), `nyt` the
author-year ones' (name, year, title). Every BibTeX key ends in the cite
key, the tiebreak that keeps the comparison total; biblatex's keys end
where biber's do, and entries they leave equal keep their citation order,
as biber's stable sort keeps them. -/
public inductive SortOrder where
  | citation
  | plain
  | alpha
  | authorYear
  | bbl (template : String) (opts : BblOptions)
  deriving Repr, BEq, Inhabited

/-- One formatted piece of a reference-list entry: plainnat.bst's `format.*`
functions (unsrtnat.bst shares them verbatim), each owing its own dressing —
the `In` before a booktitle, the `pages` word, the `12(3):45–67` join — so
an entry type contributes only its sequence of pieces and boundaries
(`Step`). `field` outputs a stored value as written: a publisher, an
address, a school, an institution, an organization, a note. -/
public inductive Field where
  | authors
  /-- `Sam Roe, editor`, or `…, editors` for more than one (FUNCTION
  {format.editors}). -/
  | editors
  /-- Sentence case (FUNCTION {format.title}). -/
  | title
  /-- Emphasized, its case kept (FUNCTION {format.btitle}). -/
  | btitle
  /-- The journal name, emphasized (FUNCTION {article}). -/
  | journal
  /-- `12(3):45–67`, or `pages 45–67` when no volume or number stands
  (FUNCTION {format.vol.num.pages}). -/
  | volNumPages
  /-- `volume 3 of *Series*` (FUNCTION {format.bvolume}). -/
  | bvolume
  /-- `number 4 in Series`, or the series alone, when no volume stands
  (FUNCTION {format.number.series}). -/
  | numberSeries
  /-- `In Sam Roe, editor, *Booktitle*` (FUNCTION {format.in.ed.booktitle}). -/
  | inEdBooktitle
  /-- `pages 1–10`, or `page 5` (FUNCTION {format.pages}). -/
  | pages
  /-- `chapter 3, pages 1–10` (FUNCTION {format.chapter.pages}). -/
  | chapterPages
  /-- `third edition` inside a sentence, `Third edition` opening one
  (FUNCTION {format.edition}). -/
  | edition
  /-- `Technical Report 42`, or `Technical report` unnumbered (FUNCTION
  {format.tr.number}). -/
  | trNumber
  /-- The entry's `type`, else the kind's own words (FUNCTION
  {format.thesis.type}). -/
  | thesisType (words : String)
  /-- `month year` (FUNCTION {format.date}). -/
  | date
  /-- `doi: value`, linked to `https://doi.org/value` (FUNCTION
  {format.doi}). -/
  | doi
  /-- `URL value`, the value set as `\url` sets it (FUNCTION {format.url}). -/
  | url
  | isbn
  | issn
  | field (name : String)
  /-- The `key` field where the named field is empty (plainnat.bst FUNCTION
  {format.key}): what an entry with no author or editor opens with. -/
  | keyIf (name : String)
  /-- An article's reference to its listed parent: `In *Journal*` and a
  citation of the parent (FUNCTION {format.article.crossref}); `natbib` is
  plainnat's spelling — `\citet`, no key word — against plain's `\cite`. -/
  | articleCrossref (natbib : Bool)
  /-- A book's or chapter's reference to its listed parent: `Volume 2 of`
  or `In`, the parent's editors or series, and a citation of it (FUNCTION
  {format.book.crossref}). -/
  | bookCrossref (natbib : Bool)
  /-- A contribution's reference to its listed parent: `In` the parent's
  editors or booktitle, and a citation of it (FUNCTION
  {format.incoll.inproc.crossref}). -/
  | incollCrossref (natbib : Bool)
  deriving Repr, BEq

/-- One step of an entry type's function: a piece's `output`, or a block or
sentence boundary — the conditional ones (`new.block.checka`, `checkb`,
`new.sentence.checkb`) taken when any of the named fields is present. -/
public inductive Step where
  | out (f : Field)
  | newBlock
  | newSentence
  | newBlockIf (fields : List String)
  | newSentenceIf (fields : List String)
  deriving Repr, BEq

/-- How one name is written, used by the inline citation style and the
entry format alike. plainnat prints full first-first names in the list
(`{ff~}{vv~}{ll}{, jj}`, plainnat.bst FUNCTION {format.names}) and last
names inline; `initials` is the axis the abbrv styles set, `lastFirst`
the one alpha-shaped styles would. -/
public structure NameFormat where
  lastFirst : Bool := false
  /-- Abbreviate first names to initials — plain.bst's `{f.~}` designator,
  the one axis `abbrv`/`abbrvnat` set. -/
  initials : Bool := false
  /-- Truncate a list longer than this to its first name and `et al.`;
  `none` keeps every name, as plainnat does. -/
  etAlAfter : Option Nat := none
  deriving Repr, BEq, Inhabited

/-- A bibliography style: four independent choices composed. `unsrtnat` and
`plainnat` are records of this type; so is the fallback an unknown
`\bibliographystyle` gets (W0353) — a record, not a code path. -/
public structure Style where
  /-- Whether the style's `\bibitem`s carry natbib's author-year labels
  (plainnat's family does, plain's does not): a style that writes none puts
  natbib in numbers mode whatever was declared. The punctuation is natbib's
  row for the style's name (`natbibRows`), not the record's. -/
  labels : Bool
  sort : SortOrder
  /-- The steps an entry's type writes, the entry at hand deciding the
  branches the style's own function takes (`plainnatSteps`). -/
  steps : Entry → Array Step
  names : NameFormat
  /-- The month macros the style defines: its own abbreviations (abbrv.bst,
  abbrvnat.bst `MACRO {mar} {"Mar."}`), or the full names. -/
  shortMonths : Bool := false
  /-- alpha.bst's labels: `[Doe24]`, `[DR21]`, `[DRS+19]` in place of the
  list position, the mark every citation of the entry prints. -/
  alphabetic : Bool := false

/-- One name as the format writes it, in TeX: the name's parts as the
`.bib` spells them. Initials abbreviate each first-name token to its first
letter and a period, a hyphen kept between them (plain.bst's `{f.~}`
designator, `Bib.initials`). -/
public def NameFormat.render (nf : NameFormat) (n : Name) : String :=
  let first := if nf.initials then Bib.initials n.first else n.first
  let jr := if n.jr.isEmpty then "" else s!", {n.jr}"
  if nf.lastFirst then
    let tail := String.intercalate " " ([n.von, first].filter (!·.isEmpty))
    if tail.isEmpty then n.last ++ jr else s!"{n.last}, {tail}" ++ jr
  else
    String.intercalate " " ([first, n.von, n.last].filter (!·.isEmpty)) ++ jr

/-- An author value as the reference list writes it, in TeX: each name
through the format, the list through plain.bst's join (`andJoin`), a long
list elided at `etAlAfter`. -/
public def NameFormat.renderTeX (nf : NameFormat) (v : String) : String :=
  let ns := (splitNames v).toList
  let ns := match nf.etAlAfter with
    | some k => if ns.length > k then ns.take 1 ++ ["others"] else ns
    | none => ns
  andJoin (ns.map fun s => if s == "others" then "others" else nf.render (parseName s))

/-- An author value as plain text (`renderTeX` read by `text`, name by
name). -/
public def NameFormat.renderList (nf : NameFormat) (v : String) : String :=
  let ns := (splitNames v).toList
  let ns := match nf.etAlAfter with
    | some k => if ns.length > k then ns.take 1 ++ ["others"] else ns
    | none => ns
  andJoin (ns.map fun s =>
    if s == "others" then "others" else text (nf.render (parseName s)))

/-- The year a date field's value names in a label: its year, and a range's
end year after an en dash when it differs (an open end leaves the dash). -/
private def dateYears (dv : DateValue) : String :=
  let yr (d : Date) : String := (if d.year < 0 then "−" else "") ++ toString d.year.natAbs
  match dv.start, dv.stop with
  | some a, some (some b) => if b.year == a.year then yr a else s!"{yr a}–{yr b}"
  | some a, some none => s!"{yr a}–"
  | none, some (some b) => s!"–{yr b}"
  | some a, none => yr a
  | none, _ => ""

/-- The year an entry's label and inline citation print: its `year` (what a
BibTeX style reads), else its date's year (what biber reads, and what a
BibTeX style reads of a `date` it is not given a `year` beside); an entry
with neither prints `n.d.` (no date), the natbib and biblatex spelling, and
an unreadable date prints as written. -/
private def citeYear (e : Entry) : String :=
  match e.field? "year" with
  | some y => text y
  | none =>
    match e.field? "date" with
    | some d => match DateValue.parse d with
      | some dv => dateYears dv
      | none => text d
    | none => "n.d."

/-- The `"The "` a label or sort drops from an organization (plain.bst's
`"The " #4 organization chop.word`). -/
private def chopThe (v : String) : String :=
  if v.startsWith "The " then (v.drop 4).toString else v

/-- The names a label is built from, in TeX. natbib's: plainnat.bst's
`calc.short.authors` — a book's or a chapter's editors when it has no
author, a proceedings volume's editors first, a manual's organization —
then the `key`, then the cite key's first three characters (`cite$ #1 #3
substring$`). biblatex's: its labelname — the author, else the editor,
else the translator, three names with no von part — and the title where an
entry names nobody. -/
private def labelSource (e : Entry) (biblatex : Bool) (useprefix : Bool := false) : String :=
  let names (v : String) : String := labelNamesTeX v 2 true
  if biblatex then
    match labelNameList e with
    | some (_, l) => citeNamesTeX { useprefix } l {}
    | none => (e.field? "title").getD e.key
  else
    let key := (e.field? "key").getD ((e.key.take 3).toString)
    let org := (e.field? "organization").map fun o => ((text (chopThe o)).take 3).toString
    let first (fs : List (Option String)) : String := (fs.findSome? id).getD key
    let au := (e.field? "author").map names
    let ed := (e.field? "editor").map names
    match e.kind with
    | "book" | "inbook" => first [au, ed]
    | "proceedings" => first [ed, e.field? "key", org]
    | "manual" => first [au, e.field? "key", org]
    | _ => first [au]

/-- The label names a citation prints (`\citet`'s `Author et al.`): the
label's source (`labelSource`) as text, never silently empty. -/
private def citeAuthors (e : Entry) (biblatex : Bool := false) (useprefix : Bool := false) :
    String :=
  Ir.smartPunct (text (labelSource e biblatex useprefix))

/-- The anchor an entry's reference-list item carries and its citations
link to: `Ir.bibAnchor`, the one naming site, `#`-prefixed for the href.
The key is author text from the `.bib`; the typed HTML tree escapes it on
the way into the attribute (`escapeAttr`), so no spelling of a key can
break out of the `href`. -/
public def anchorOf (key : String) : String :=
  let a := Ir.bibAnchor key
  "#" ++ a

/-- One resolved citation, ready to render: the entry with its 1-based
position in the reference list, and the letter that tells it from entries
sharing its label (`extraLabels`), empty when its label is its own. -/
public structure Resolved where
  key : String
  position : Nat
  entry : Entry
  extra : String := ""
  /-- The mark a `thebibliography` entry's optional label sets in numbers
  mode (latex.ltx `\@lbibitem`), in place of its position. -/
  label : Option String := none
  /-- biblatex's: its labelname as its citations print it, uniqueness
  applied (`citeNamesTeX`), in TeX. -/
  citeNames : Option String := none
  /-- biblatex's, for an entry no name list labels: what its citations
  print in place of the names (`bblCiteLabel`), read as its fields are. -/
  citeLabel : Option (Array Ir.Inline) := none
  /-- The TeX the label a style writes is spelt in — alpha.bst's, or a
  biblatex shorthand in place of a number — where `label` holds its text
  read as `text` reads it; set as the entry's fields are set where it holds
  a control word (`labelInk`). -/
  labelTeX : Option String := none
  /-- What a citation prints for the names, where their TeX holds a control
  word: read as the entry's fields are, so `\textsc` and `\emph` in a
  name set as the body sets them (`inkOf`). -/
  namesInk : Option (Array Ir.Inline) := none
  /-- biblatex's shorthand as an author-year citation prints it, where its
  TeX holds a control word, read as the entry's fields are (`inkOf`). -/
  shortInk : Option (Array Ir.Inline) := none
  /-- biblatex's: what its extradate letter is grouped by — the names its
  citations show (`nameHashKey`). -/
  extraKey : Option String := none
  /-- biblatex's `namehash`: the names its citations show, whole
  (`nameHashFull`) — what a numeric textual citation groups its keys by. -/
  nameHash : Option String := none
  /-- biblatex's: its labelname's field and the names its `uniquelist`
  shows, which the reference list shows of that field too. -/
  labelUl : Option (String × Nat) := none
  /-- biblatex's: how many names of its sort list the sort key reads. -/
  sortShown : Option Nat := none
  /-- biblatex's `shorthand`: what its citations print in place of its
  label. -/
  shorthand : Option String := none
  /-- biblatex's label year (`bblLabelYear`) and whether it reads as
  numerals, which decides how its letter is set. -/
  labelYear : Option (String × Bool) := none
  /-- biblatex's `skipbib`: cited and numbered, never listed. -/
  skipbib : Bool := false
  /-- biblatex's `skiplab`: no number and no letter. -/
  skiplab : Bool := false
  /-- The entry as its `.bib` writes it, where the list is typeset under
  definitions its sort keys never see (`@preamble`, `Bib.preambleMacros`);
  `none` where the two are one. -/
  raw : Option Entry := none
  /-- What its field citations print (`Ir.CiteField`, and whether the star
  asks the full title), for the fields the document cites it by. -/
  fieldInk : Array ((Ir.CiteField × Bool) × Array Ir.Inline) := #[]
  /-- The boundary pictures its citation ink sets (`citeLabel`, `fieldInk`),
  which the document's request carries as the body's own. -/
  inkPictures : Array (String × Ir.PicSrc) := #[]
  deriving Repr

/-- The entry a sort key and alpha's label read: as its `.bib` writes it,
which BibTeX's `purify$` and biber's sort strings read where the `.bbl`'s
definitions do not reach. -/
public def Resolved.sortEntry (r : Resolved) : Entry := r.raw.getD r.entry

/-- The full author list natbib's starred forms print (`\citet*`), or the
key when no author is there, as `citeAuthors` does. -/
private def citeFullAuthors (e : Entry) : String :=
  match e.field? "author" with
  | some a => Ir.smartPunct (fullNames a)
  | none => e.key

/-- What one key prints: its names and year, its names alone, or its year
alone — natbib.sty's `\NAT@ctype` 0, 1 and 2. -/
private inductive CitePart where
  | both
  | names
  | year
  deriving BEq

/-- The loop's state between keys: the output so far, the separator the
last key left for the next (natbib.sty `\@citea`), the last key's names and
bare year — a key repeating the names prints only its year, and one
repeating both only its letter — and whether the last key printed a year,
which is what closes a textual citation's bracket. -/
private structure CiteAcc where
  out : Array Ir.Inline := #[]
  citea : String := ""
  last : Option String := none
  lastYear : Option String := none
  dated : Bool := false
  /-- The keys read so far. -/
  index : Nat := 0
  /-- The groups begun so far — a biblatex numeric textual citation's keys
  by one list of names share one (numeric.cbx's `textcite` against
  `\cbx@lasthash`); every other citation's keys each begin their own. -/
  groups : Nat := 0
  /-- The last key's `namehash`. -/
  lastHash : Option String := none

mutual

/-- Inline content carrying no citation, anywhere in its tree. -/
private def citeFreeOne : Ir.Inline → Bool
  | .cite _ _ => false
  | .styled _ body => citeFreeList body.toList
  | .colored _ _ body => citeFreeList body.toList
  | .located _ body => citeFreeList body.toList
  | .role _ body => citeFreeList body.toList
  | .link _ body => citeFreeList body.toList
  | .decorated _ body => citeFreeList body.toList
  | .onSteps _ body => citeFreeList body.toList
  | .altSteps _ active otherwise =>
    citeFreeList active.toList && citeFreeList otherwise.toList
  | .footnote _ body => citeFreeList body.toList
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _
  | .label _ | .ref _ _ _ _
  | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _ | .pageNumber | .pageCount | .linebreak _ => true

private def citeFreeList : List Ir.Inline → Bool
  | [] => true
  | x :: rest => citeFreeOne x && citeFreeList rest

end

private def emit (out : Array Ir.Inline) (s : String) : Array Ir.Inline :=
  if s.isEmpty then out else out.push (.text s)

private def emitLink (p : CitePunct) (out : Array Ir.Inline) (anchor s : String) :
    Array Ir.Inline :=
  out.push (.link anchor (match p.ink with
    | some (c, n) => #[.colored c n #[.text s]]
    | none => #[.text s]))

/-- A key's piece linked to its entry, after what precedes it: as the
inline content they are where neither carries a citation, as their plain
text otherwise — a citation's output never holds one
(`linkPiece_citeFree`). An empty piece links nothing: no link without a
name ships. -/
private def linkPiece (p : CitePunct) (out : Array Ir.Inline) (anchor : String)
    (before piece : Array Ir.Inline) : Array Ir.Inline :=
  if piece.isEmpty then
    if citeFreeList before.toList then out ++ before else emit out (Ir.plainText before)
  else if citeFreeList before.toList && citeFreeList piece.toList then
    (out ++ before).push (.link anchor (match p.ink with
      | some (c, n) => #[.colored c n piece]
      | none => piece))
  else emitLink p (emit out (Ir.plainText before)) anchor (Ir.plainText piece)

/-- The first letter capitalized — natbib's `\NAT@Up`, what `\Citet` does
to a name that opens with a lowercase particle. -/
private def upFirst (s : String) : String :=
  match s.toList with
  | c :: cs => String.ofList (c.toUpper :: cs)
  | [] => s

/-- `upFirst` over inline content: its first text's first letter, where
the content opens with text. -/
private def upFirstInk (xs : Array Ir.Inline) : Array Ir.Inline :=
  if let some (Ir.Inline.text t) := xs[0]? then xs.modify 0 fun _ => .text (upFirst t) else xs

/-- What natbib's command table sets for a command: whether it counts in
numbers (`\citenum` does in either mode), whether its brackets close the
whole citation (`\NAT@swa`: `\citep`) rather than each year (`\citet`),
which part of each key it prints (`\NAT@ctype`), and the brackets it draws
(`\NAT@par`: none for the `alt`/`alp` forms). -/
private structure Switches where
  numeric : Bool
  wrap : Bool
  part : CitePart
  op : String
  cl : String

private def switches (p : CitePunct) (f : Ir.CiteForm) : Switches :=
  let brackets := match f.cmd with
    | .textual | .paren | .auto | .yearPar | .text => true
    | .alt | .alp | .author | .year | .num | .nocite | .bracket _ | .field _ => false
  { numeric := p.numbers || f.cmd == .num
    wrap := match f.cmd with
      | .paren | .alp | .yearPar | .num | .text => true
      | .auto => p.numbers
      | .textual | .alt | .author | .year | .nocite | .bracket _ | .field _ => false
    part := match f.cmd with
      | .author => .names
      | .year | .yearPar => .year
      | .textual | .paren | .auto | .alt | .alp | .num | .text | .nocite | .bracket _
      | .field _ => .both
    op := if brackets then p.open else ""
    cl := if brackets then p.close else "" }

/-- The separator a textual citation's key leaves for the next when the
citation has `total` keys and this is key `k` (from 0): natbib's `sep`,
or biblatex's `\textcitedelim` — `, ` between keys, ` and ` before the last
of two, `, and ` before the last of more. -/
private def textSep (p : CitePunct) (f : Ir.CiteForm) (total k : Nat) : String :=
  if p.biblatex && f.cmd == .textual then
    if k + 2 == total then (if total ≥ 3 then ", and " else " and ") else ", "
  else p.sep ++ " "

/-- Does this citation group its keys by their names — a biblatex numeric
textual citation (numeric.cbx's `textcite`)? -/
private def groupsKeys (p : CitePunct) (f : Ir.CiteForm) (s : Switches) : Bool :=
  p.biblatex && s.numeric && f.cmd == .textual

/-- A citation's groups: one per key, except that a key of a grouping
citation (`groupsKeys`) whose `namehash` is the last key's joins its group
— what biblatex's `textcitetotal` counts. -/
private def citeGroups (p : CitePunct) (f : Ir.CiteForm) (s : Switches)
    (parts : Array (Option Resolved)) : Nat :=
  if groupsKeys p f s then
    (parts.foldl (init := (0, (none : Option String))) fun (n, last) o =>
      match o with
      | some r => if r.nameHash.isSome && r.nameHash == last then (n, last) else (n + 1, r.nameHash)
      | none => (n + 1, none)).1
  else parts.size

/-- One key under natbib's loop (natbib.sty `\NAT@citex`, `\NAT@citexnum`
in numbers mode): the separator the previous key left, this key's piece
linked to its entry, and the separator it leaves. natbib capitalizes names
only in author-year mode; a key repeating the previous key's names prints
only its year after `yysep`, and one repeating the year too only its
letter, with no space (`\NAT@exlab`: `2019a,b`) — biblatex's standard
styles print every key whole. In numbers mode natbib defines `\natexlab`
to print nothing, so no letter prints. An unresolvable key prints `?` in
its place with the separators a resolved one would have. `total` is the
citation's group count (`citeGroups`), which a biblatex textual citation's
last separator reads (`textSep`); a biblatex numeric textual citation's key
whose names are the last key's joins that key's bracket, as numeric.cbx's
`textcite` does (`Beta [3, 4]`). -/
private def citeStep (p : CitePunct) (f : Ir.CiteForm) (s : Switches) (total : Nat)
    (acc : CiteAcc) : Option Resolved → CiteAcc
  | none =>
    { out := emit acc.out (acc.citea ++ "?"), citea := p.sep ++ " ", index := acc.index + 1,
      groups := acc.groups + 1 }
  | some r =>
    let names := if f.full then citeFullAuthors r.entry
      else match r.citeNames with
        | some n => Ir.smartPunct (text n)
        | none => citeAuthors r.entry p.biblatex p.useprefix
    let up := f.up && !s.numeric
    let names := if up then upFirst names else names
    -- the names as the entry's fields set them where their TeX holds a
    -- control word; biblatex prints an entry no name list labels by its
    -- label title (`bblCiteLabel`), set as its fields are set
    let titled := if f.full then none else match r.namesInk with
      | some inl => some (if up then upFirstInk inl else inl)
      | none => if r.citeNames.isSome then none else r.citeLabel
    let txt (s : String) : Array Ir.Inline := if s.isEmpty then #[] else #[.text s]
    -- the names, and what follows them, as the linked piece
    let linked (after : String) : Array Ir.Inline := match titled with
      | some inl =>
        let tail := txt after
        inl ++ tail
      | none => #[.text (names ++ after)]
    -- the names inside what precedes the linked piece
    let lead (before after : String) : Array Ir.Inline := match titled with
      | some inl =>
        let tail := txt after
        txt before ++ inl ++ tail
      | none => txt (before ++ names ++ after)
    -- biblatex's label year, and its letter after a year that is no
    -- numeral in parentheses — brackets inside the citation's own
    -- (biblatex.def `extradate`)
    let (bare, numerals) := r.labelYear.getD (citeYear r.entry, true)
    let inParens := (s.wrap && !s.op.isEmpty) || f.cmd == .textual
    let letter := if p.numbers || r.extra.isEmpty then ""
      else if numerals then r.extra
      else if inParens then "[" ++ r.extra ++ "]" else "(" ++ r.extra ++ ")"
    let year := bare ++ letter
    -- biblatex's author-year citations print a shorthand in place of the
    -- names and year, or of the year after the names (authoryear.cbx
    -- `cite:shorthand`); numeric ones carry it as the label
    let sh := if p.biblatex && !s.numeric then r.shorthand.map (Ir.smartPunct ∘ text) else none
    let mark := if s.numeric then r.label.getD (toString r.position) else sh.getD year
    -- the shorthand as the entry's fields set it where its TeX holds a
    -- control word
    let shInk : Option (Array Ir.Inline) :=
      sh.map fun h => r.shortInk.getD #[.text h]
    let markInk : Array Ir.Inline := if s.numeric then #[.text mark] else shInk.getD #[.text mark]
    let pre := if f.pre.isEmpty then "" else f.pre ++ " "
    let same := !p.biblatex && acc.last == some names
    let sameYear := same && acc.lastYear == some bare && !letter.isEmpty
    let joins := groupsKeys p f s && r.nameHash.isSome && acc.lastHash == r.nameHash
    let tsep := textSep p f total (if joins then acc.groups - 1 else acc.groups)
    -- (what precedes the linked piece, the piece, the separator left behind)
    let t : Array Ir.Inline × Array Ir.Inline × String :=
      if joins then (txt (p.sep ++ " "), markInk, s.cl ++ tsep) else
      match s.part with
      -- biblatex's \citeauthor prints the labelname alone, so nothing for
      -- an entry no name list labels
      | .names => (txt acc.citea, if p.biblatex && r.citeNames.isNone then #[] else linked "",
          p.sep ++ " ")
      | .year => (txt acc.citea, #[.text (if p.biblatex then bare else year)], p.sep ++ " ")
      | .both =>
        if s.wrap then
          if s.numeric then (txt acc.citea, #[.text mark], p.sep ++ " ")
          else if let some h := shInk then (txt acc.citea, h, p.sep ++ " ")
          else if sameYear then (txt p.yysep, #[.text letter], p.sep ++ " ")
          else if same then (txt (p.yysep ++ " "), #[.text year], p.sep ++ " ")
          else (txt acc.citea, linked s!"{p.aysep} {year}", p.sep ++ " ")
        else if sameYear then (txt p.yysep, #[.text letter], s.cl ++ tsep)
        else
          (if same then txt (p.yysep ++ " " ++ (if s.numeric then pre else ""))
            else lead acc.citea (" " ++ s.op ++ pre), markInk, s.cl ++ tsep)
    { out := linkPiece p acc.out (anchorOf r.key) t.1 t.2.1
      citea := t.2.2
      last := some names
      lastYear := some bare
      dated := true
      index := acc.index + 1
      groups := if joins then acc.groups else acc.groups + 1
      lastHash := r.nameHash }

/-- The brackets around the loop's output: a wrapping form opens them with
its pre-note and closes them after its post-note (`notesep`); a textual
form has opened each year's bracket in the loop and closes the last,
after the post-note, when that key printed a year. A biblatex citation's
post-note is set as its `postnote` format sets it (`bblPostnote`: `p. 12`,
`pp. 12–15`), under the last key's `pagination`. -/
private def finish (p : CitePunct) (f : Ir.CiteForm) (s : Switches) (pagination : Option String)
    (acc : CiteAcc) : Array Ir.Inline :=
  let post := if f.post.isEmpty then ""
    else p.notesep ++ (if p.biblatex then bblPostnote pagination f.post else f.post)
  let (lead, trail) :=
    if s.wrap then (s.op ++ (if f.pre.isEmpty then "" else f.pre ++ " "), post ++ s.cl)
    else ("", (if s.numeric && s.part != .both then "" else post) ++
      (if acc.dated then s.cl else ""))
  emit (emit #[] lead ++ acc.out) trail

/-- natbib's `sort` (natbib.sty `\NAT@sort@cites`): a citation's keys in
reference-list order, in either mode; a key whose mark is not a number —
unresolved, or a `thebibliography` item's own label — goes after them in
the order written, natbib's non-sort list. -/
private def sortParts (parts : Array (Option Resolved)) : Array (Option Resolved) :=
  let numbered (o : Option Resolved) : Bool := o.any (·.label.isNone)
  let known := (parts.filterMap fun o => if numbered o then o else none).toList.mergeSort
    fun a b => decide (a.position ≤ b.position)
  let unknown := parts.filter (!numbered ·)
  (known.map some).toArray ++ unknown

/-- `compress`'s state between keys (natbib.sty `\NAT@citexnum`): the output
so far, the last position printed or held, and the key held back — the last
number of a run waits until the run ends (`\NAT@last@yr`), with what
precedes it: the separator after the run's first number, an en dash after
its second. -/
private structure RunAcc where
  acc : CiteAcc := {}
  last : Option Nat := none
  held : Option (String × Resolved) := none

/-- The held number, printed. -/
private def flushHeld (p : CitePunct) (out : Array Ir.Inline) :
    Option (String × Resolved) → Array Ir.Inline
  | some (pre, r) => emitLink p (emit out pre) (anchorOf r.key) (toString r.position)
  | none => out

/-- One key under `compress`: a number one past the last extends the run
and is held back; any other — a gap, a repeat, a mark that is no number (a
`thebibliography` label) — prints what was held, then itself. An unresolved
key ends the run and prints `?` where it stands. -/
private def runStep (p : CitePunct) (st : RunAcc) : Option Resolved → RunAcc
  | none =>
    { acc := { st.acc with out := emit (flushHeld p st.acc.out st.held) (st.acc.citea ++ "?"),
                           citea := p.sep ++ " " } }
  | some r =>
    if r.label.isNone && st.last.map (· + 1) == some r.position then
      { acc := { st.acc with citea := p.sep ++ " ", dated := true }, last := some r.position,
        held := some (if st.held.isSome then "–" else st.acc.citea, r) }
    else
      { acc := { st.acc with
          out := emitLink p (emit (flushHeld p st.acc.out st.held) st.acc.citea) (anchorOf r.key)
            (r.label.getD (toString r.position))
          citea := p.sep ++ " ", dated := true }
        last := if r.label.isNone then some r.position else none }

/-- natbib's `compress` over a numbered citation (natbib.sty `\NAT@cmprs`):
a run of three or more consecutive list positions sets as its ends joined
by an en dash (`[1–3, 5]`), a run of two keeps both numbers, and a repeated
number breaks a run and prints again. -/
private def compressRuns (p : CitePunct) (parts : Array (Option Resolved)) : CiteAcc :=
  let st := parts.foldl (runStep p) {}
  { st.acc with out := flushHeld p st.acc.out st.held }

/-- What a field citation prints for one key's entry (`Ir.CiteField`): the
ink its entry was given for the field, where it holds content and no
citation, `?` otherwise — a title or a date linked to the entry
(biblatex.def's `bibhyperref`), a URL or a whole entry carrying its own
links. -/
private def fieldPiece (w : Ir.CiteField) (full : Bool) (acc : Array Ir.Inline) :
    Option Resolved → Array Ir.Inline
  | some r =>
    let ink := ((r.fieldInk.find? (·.1 == (w, full))).map (·.2)).getD #[]
    if ink.isEmpty || !citeFreeList ink.toList then emit acc "?"
    else if w == .title || w == .date then acc.push (.link (anchorOf r.key) ink)
    else acc ++ ink
  | none => emit acc "?"

/-- One key of a field citation: the separator before it, then its piece. -/
private def fieldStep (p : CitePunct) (w : Ir.CiteField) (full : Bool) (acc : Array Ir.Inline)
    (o : Option Resolved) : Array Ir.Inline :=
  fieldPiece w full (if acc.isEmpty then acc else emit acc (p.sep ++ " ")) o

/-- A whole citation under natbib's punctuation, per its command (natbib.sty's
command table): `\citep` wraps its keys in the brackets with `sep` between
them (`[Doe, 2024; Roe, 2020]`, `[1, 2]`), `\citet` brackets each year
(`Doe [2024]`), the `alt`/`alp` forms drop the brackets, `\citeauthor` and
`\citeyear` print one part, `\citenum` the list position in either mode,
a bracket mark the one bracket it names (the halves of `\citetext`, whose
body stands between them), and `\nocite` nothing: its keys
only enter the list (`citedKeys`). Under the load's `sort` the keys stand in
list order; under `compress` a numbered citation that wraps its keys
(`\citep`, `\citealp`, `\citenum`) joins its runs (`compressRuns`), where a
textual one keeps every number, as natbib's textual branch does. A field
citation prints each key's field — the ink its entry was given, where that
carries no citation — and every other citation text and links over text
only: the output carries no `.cite`, which is `renderCite_citeFree`, the
leaf fact `apply_no_cite` rests on. -/
public def renderCite (p : CitePunct) (f : Ir.CiteForm) (parts : Array (Option Resolved)) :
    Array Ir.Inline :=
  if let .bracket o := f.cmd then emit #[] (if o then p.open else p.close)
  else if let .field w := f.cmd then
    -- a field citation (`\citetitle`, `\fullcite`, …): each key's field as
    -- its entry prints it, linked to the entry, the keys apart by the
    -- citation separator, the notes around them as a bare citation's
    let body := parts.foldl (fieldStep p w f.full) #[]
    let pre := if f.pre.isEmpty then "" else f.pre ++ " "
    let post := if f.post.isEmpty then ""
      else p.notesep ++ (if p.biblatex then bblPostnote none f.post else f.post)
    emit (emit #[] pre ++ body) post
  else if f.cmd == .text then emit #[] (p.open ++ f.pre ++ p.close)
  else if f.cmd == .nocite then #[]
  else
    let parts := if p.sort then sortParts parts else parts
    let s := switches p f
    let pagination := (parts.back?.join).bind (·.entry.field? "pagination")
    finish p f s pagination (if p.compress && s.numeric && s.wrap && s.part == .both then
        compressRuns p parts
      else parts.foldl (citeStep p f s (citeGroups p f s parts)) {})

/-- BibTeX's `n.dashify` (plain.bst): a lone `-` between page numbers
becomes `--`, the en dash, and a run of two or more stays as written. -/
private def dashify (v : String) : String := Id.run do
  let cs := v.toList.toArray
  let mut out := ""
  let mut i := 0
  for _ in [0:cs.size + 1] do
    if h : i < cs.size then
      if cs[i] == '-' then
        if cs[i + 1]? == some '-' then
          out := out.push '-'
          i := i + 1
          for _ in [i:cs.size] do
            if cs[i]? == some '-' then
              out := out.push '-'
              i := i + 1
            else break
        else
          out := out ++ "--"
          i := i + 1
      else
        out := out.push cs[i]
        i := i + 1
    else break
  return out

/-- A stored value is present when it holds anything but white space —
BibTeX's `empty$` false. -/
private def Entry.has (e : Entry) (name : String) : Bool :=
  (e.field? name).any fun v => !v.trimAscii.toString.isEmpty

/-- The reference list's writer: the diagnostics its field readings report,
gathered as the entry is set, and the texts read so far. -/
private abbrev RenderM := StateM (FieldReport × FieldCache)

/-- A field's TeX text through the reading in force, once per text
(`FieldCache.read`), its reports kept. -/
private def conv (cv : FieldText) (s : String) : RenderM (Array Ir.Inline) := do
  let (ds, cache) ← get
  let ((out, ds'), cache) := cache.read cv s
  set (ds ++ ds', cache)
  pure out

/-- plain.bst's `tie.or.space.connect`: a value shorter than three
characters ties to its word, so `volume 3` never breaks between them. -/
private def tieOrSpace (cv : FieldText) (word v : String) : RenderM (Array Ir.Inline) := do
  let gap := if (text v).length < 3 then "\u00a0" else " "
  pure (#[.text (word ++ gap)] ++ (← conv cv v))

/-- plain.bst's `format.pages`: `pages` for a range or a list (a `-`, `,`
or `+` in the value, `multi.page.check`), `page` for one. -/
private def formatPages (cv : FieldText) (p : String) : RenderM (Array Ir.Inline) :=
  if p.any fun c => c == '-' || c == ',' || c == '+' then tieOrSpace cv "pages" (dashify p)
  else tieOrSpace cv "page" p

/-- An editor list as plain.bst writes it (FUNCTION {format.editors}). -/
private def editorsTeX (nf : NameFormat) (ed : String) : String :=
  nf.renderTeX ed ++ if (splitNames ed).size > 1 then ", editors" else ", editor"

/-- plain.bst's `format.crossref.editor`: the parent's first editor by
`{vv~}{ll}`, the second after `and` when there are exactly two, `et al.`
past them. -/
private def crossrefEditor (ed : String) : String :=
  let ns := splitNames ed
  let short (s : String) : String := (parseName s).short
  match ns.toList with
  | [] => ""
  | [a] => short a
  | [a, b] =>
    let second := short b
    if b == "others" then short a ++ " et~al." else short a ++ " and " ++ second
  | a :: _ => short a ++ " et~al."

/-- A cross-reference's citation of its parent: plainnat's `\citet`,
plain's `\cite`. -/
private def crossrefCite (natbib : Bool) (key : String) : Ir.Inline :=
  .cite { cmd := if natbib then .textual else .auto } #[key]

/-- The parent's editor list stands for the parent unless it is missing
or is the child's own author list (`editor field.or.null author
field.or.null =`). -/
private def editorStands (e : Entry) : Bool :=
  e.has "editor" && e.field? "editor" != e.field? "author"

/-- One piece of one entry: THE piece renderer — every entry type renders
through this one function, and what varies per type is only the steps that
call it. `mid` is whether the piece continues a sentence, which the edition
and the series number read, as plainnat's do; `extra` is the entry's letter,
which the date carries. Author text goes through the field reading `cv`;
the style's own words are text. An absent field renders empty, and its step
writes nothing. -/
private def renderField (cv : FieldText) (nf : NameFormat) (e : Entry) (mid : Bool)
    (extra : String) : Field → RenderM (Array Ir.Inline)
  | .authors => do
    match e.field? "author" with
    | some a => conv cv (nf.renderTeX a)
    | none => pure #[]
  | .editors => do
    match e.field? "editor" with
    | some ed => conv cv (editorsTeX nf ed)
    | none => pure #[]
  | .title => do
    match e.field? "title" with
    | some t => conv cv (sentenceCase t)
    | none => pure #[]
  | .btitle => do
    match e.field? "title" with
    | some t => pure #[.styled .emph (← conv cv t)]
    | none => pure #[]
  | .journal => do
    match e.field? "journal" with
    | some j => pure #[.styled .emph (← conv cv j)]
    | none => pure #[]
  | .volNumPages => do
    let vol ← match e.field? "volume" with
      | some v => conv cv v
      | none => pure #[]
    let num ← match e.field? "number" with
      | some n => pure (#[.text "("] ++ (← conv cv n) ++ #[.text ")"])
      | none => pure #[]
    let head := vol ++ num
    match e.field? "pages" with
    | some p =>
      if head.isEmpty then formatPages cv p
      else pure (head ++ #[.text ":"] ++ (← conv cv (dashify p)))
    | none => pure head
  | .bvolume => do
    match e.field? "volume" with
    | some v =>
      let vol ← tieOrSpace cv "volume" v
      match e.field? "series" with
      | some sr => pure (vol ++ #[.text " of ", .styled .emph (← conv cv sr)])
      | none => pure vol
    | none => pure #[]
  | .numberSeries => do
    if e.has "volume" then return #[]
    let word := if mid then "number" else "Number"
    match e.field? "number", e.field? "series" with
    | some n, some sr =>
      pure ((← tieOrSpace cv word n) ++ #[.text " in "] ++ (← conv cv sr))
    | some n, none => tieOrSpace cv word n
    | none, some sr => conv cv sr
    | none, none => pure #[]
  | .inEdBooktitle => do
    match e.field? "booktitle" with
    | some b =>
      let eds ← match e.field? "editor" with
        | some ed => pure ((← conv cv (editorsTeX nf ed)) ++ #[.text ", "])
        | none => pure #[]
      pure (#[.text "In "] ++ eds ++ #[.styled .emph (← conv cv b)])
    | none => pure #[]
  | .pages => do
    match e.field? "pages" with
    | some p => formatPages cv p
    | none => pure #[]
  | .chapterPages => do
    match e.field? "chapter" with
    | some c =>
      let gap := if (text c).length < 3 then "\u00a0" else " "
      let word ← match e.field? "type" with
        | some ty => conv cv (lowerCase false ty)
        | none => pure #[.text "chapter"]
      let head := word ++ #[.text gap] ++ (← conv cv c)
      match e.field? "pages" with
      | some p => pure (head ++ #[.text ", "] ++ (← formatPages cv p))
      | none => pure head
    | none =>
      match e.field? "pages" with
      | some p => formatPages cv p
      | none => pure #[]
  | .edition => do
    match e.field? "edition" with
    | some ed => conv cv ((if mid then lowerCase false ed else sentenceCase ed) ++ " edition")
    | none => pure #[]
  | .trNumber => do
    let ty := (e.field? "type").getD "Technical Report"
    match e.field? "number" with
    | some n =>
      let gap := if (text n).length < 3 then "~" else " "
      conv cv (ty ++ gap ++ n)
    | none => conv cv (sentenceCase ty)
  | .thesisType words => do
    match e.field? "type" with
    | some ty => conv cv (sentenceCase ty)
    | none => pure #[.text (Ir.smartPunct words)]
  | .date => do
    match e.field? "year", e.field? "month" with
    | some y, some m => pure ((← conv cv m) ++ #[.text " "] ++ (← conv cv y) ++ #[.text extra])
    | some y, none => pure ((← conv cv y) ++ #[.text extra])
    | none, _ => pure (if extra.isEmpty then #[] else #[.text extra])
  | .doi => do
    match e.field? "doi" with
    | some d => pure #[.text "doi: ", .link ("https://doi.org/" ++ urlText d) #[.text (urlText d)]]
    | none => pure #[]
  | .url => do
    match e.field? "url" with
    | some u => pure #[.text "URL ", .link (urlText u) #[.styled .mono #[.text (urlText u)]]]
    | none => pure #[]
  | .isbn => do
    match e.field? "isbn" with
    | some v => pure (#[.text "ISBN "] ++ (← conv cv v))
    | none => pure #[]
  | .issn => do
    match e.field? "issn" with
    | some v => pure (#[.text "ISSN "] ++ (← conv cv v))
    | none => pure #[]
  | .field name => do
    match e.field? name with
    | some v => conv cv v
    | none => pure #[]
  | .keyIf name => do
    if e.has name then return #[]
    match e.field? "key" with
    | some k => conv cv k
    | none => pure #[]
  | .articleCrossref natbib => do
    let x := (e.field? "crossref").getD ""
    let lead ← if e.has "key" then
        if natbib then pure #[.text "In "] else pure (#[.text "In "] ++ (← conv cv ((e.field? "key").getD "")))
      else match e.field? "journal" with
        | some j => pure #[.text "In ", .styled .emph (← conv cv j)]
        | none => pure #[]
    pure (lead ++ #[.text " ", crossrefCite natbib x])
  | .bookCrossref natbib => do
    let x := (e.field? "crossref").getD ""
    let lead ← match e.field? "volume" with
      | some v => pure ((← tieOrSpace cv "Volume" v) ++ #[.text " of "])
      | none => pure #[.text "In "]
    let who ← if editorStands e then
        if natbib then pure #[] else conv cv (crossrefEditor ((e.field? "editor").getD ""))
      else if e.has "key" then
        if natbib then pure #[] else conv cv ((e.field? "key").getD "")
      else match e.field? "series" with
        | some sr => pure #[.styled .emph (← conv cv sr)]
        | none => pure #[]
    pure (lead ++ who ++ #[.text " ", crossrefCite natbib x])
  | .incollCrossref natbib => do
    let x := (e.field? "crossref").getD ""
    let lead ← if editorStands e then
        if natbib then pure #[.text "In "]
        else pure (#[.text "In "] ++ (← conv cv (crossrefEditor ((e.field? "editor").getD ""))))
      else if e.has "key" then
        if natbib then pure #[.text "In "] else pure (#[.text "In "] ++ (← conv cv ((e.field? "key").getD "")))
      else match e.field? "booktitle" with
        | some b => pure #[.text "In ", .styled .emph (← conv cv b)]
        | none => pure #[]
    pure (lead ++ #[.text " ", crossrefCite natbib x])

/-- The fields a piece reads: what a style that writes it prints. -/
public def Field.reads : Field → List String
  | .authors => ["author"]
  | .editors => ["editor"]
  | .title | .btitle => ["title"]
  | .journal => ["journal"]
  | .volNumPages => ["volume", "number", "pages"]
  | .bvolume => ["volume", "series"]
  | .numberSeries => ["number", "series"]
  | .inEdBooktitle => ["booktitle", "editor"]
  | .pages => ["pages"]
  | .chapterPages => ["chapter", "type", "pages"]
  | .edition => ["edition"]
  | .trNumber => ["type", "number"]
  | .thesisType _ => ["type"]
  | .date => ["year", "month"]
  | .doi => ["doi"]
  | .url => ["url"]
  | .isbn => ["isbn"]
  | .issn => ["issn"]
  | .field name => [name]
  | .keyIf name => [name, "key"]
  | .articleCrossref _ => ["journal", "key", "crossref"]
  | .bookCrossref _ => ["volume", "editor", "author", "key", "series", "crossref"]
  | .incollCrossref _ => ["editor", "author", "key", "booktitle", "crossref"]

/-- The fields a style's steps for an entry read. -/
public def readsOf (steps : Array Step) : List String :=
  steps.toList.flatMap fun
    | .out f => f.reads
    | .newBlockIf fs | .newSentenceIf fs => fs
    | .newBlock | .newSentence => []

/-- The entry functions of plainnat.bst, whose steps unsrtnat.bst and
abbrvnat.bst share verbatim — FUNCTION {article}, {book}, {booklet},
{inbook}, {incollection}, {inproceedings}, {manual}, {mastersthesis},
{misc}, {phdthesis}, {proceedings}, {techreport}, {unpublished} — one step
sequence per type, the entry deciding the branches the style's function
takes: on its author, its address, and its `crossref`, which the database
keeps only while the parent stands in the list (`Database.read`). An
unknown type is `misc` (FUNCTION {default.type}). -/
public def plainnatSteps (e : Entry) : Array Step :=
  let url : Array Step := #[.newBlockIf ["url"], .out .url]
  let note : Array Step := #[.newBlock, .out (.field "note")]
  let tail : Array Step := #[.newBlockIf ["doi"], .out .doi] ++ url ++ note
  let isbn : Array Step := #[.newBlockIf ["isbn"], .out .isbn]
  let xref := e.has "crossref"
  let who : Array Step := if e.has "author" then #[.out .authors]
    else #[.out .editors, .out (.keyIf "editor")]
  match e.kind with
  | "article" =>
    #[.out .authors, .out (.keyIf "author"), .newBlock, .out .title, .newBlock] ++
    (if xref then #[.out (.articleCrossref true), .out .pages]
     else #[.out .journal, .out .volNumPages, .out .date]) ++
    #[.newBlockIf ["issn"], .out .issn] ++ tail
  | "book" =>
    who ++ #[.newBlock, .out .btitle] ++
    (if xref then #[.newBlock, .out (.bookCrossref true)]
     else #[.out .bvolume, .newBlock, .out .numberSeries, .newSentence,
       .out (.field "publisher"), .out (.field "address")]) ++
    #[.out .edition, .out .date] ++ isbn ++ tail
  | "inbook" =>
    who ++ #[.newBlock, .out .btitle] ++
    (if xref then #[.out .chapterPages, .newBlock, .out (.bookCrossref true)]
     else #[.out .bvolume, .out .chapterPages, .newBlock, .out .numberSeries, .newSentence,
       .out (.field "publisher"), .out (.field "address")]) ++
    #[.out .edition, .out .date] ++ isbn ++ tail
  | "booklet" =>
    #[.out .authors, .out (.keyIf "author"), .newBlock, .out .title,
      .newBlockIf ["howpublished", "address"], .out (.field "howpublished"),
      .out (.field "address"), .out .date] ++ isbn ++ tail
  | "incollection" =>
    #[.out .authors, .out (.keyIf "author"), .newBlock, .out .title, .newBlock] ++
    (if xref then #[.out (.incollCrossref true), .out .chapterPages]
     else #[.out .inEdBooktitle, .out .bvolume, .out .numberSeries, .out .chapterPages,
       .newSentence, .out (.field "publisher"), .out (.field "address"), .out .edition,
       .out .date]) ++ isbn ++ tail
  | "inproceedings" | "conference" =>
    #[.out .authors, .out (.keyIf "author"), .newBlock, .out .title, .newBlock] ++
    (if xref then #[.out (.incollCrossref true), .out .pages]
     else #[.out .inEdBooktitle, .out .bvolume, .out .numberSeries, .out .pages] ++
       (if e.has "address" then
         #[.out (.field "address"), .out .date, .newSentence, .out (.field "organization"),
           .out (.field "publisher")]
       else
         #[.newSentenceIf ["organization", "publisher"], .out (.field "organization"),
           .out (.field "publisher"), .out .date])) ++ isbn ++ tail
  | "manual" =>
    #[.out .authors, .out (.keyIf "author"), .newBlock, .out .btitle,
      .newBlockIf ["organization", "address"],
      .out (.field "organization"), .out (.field "address"), .out .edition, .out .date] ++
      url ++ note
  | "mastersthesis" =>
    #[.out .authors, .out (.keyIf "author"), .newBlock, .out .title, .newBlock,
      .out (.thesisType "Master's thesis"), .out (.field "school"), .out (.field "address"),
      .out .date] ++ url ++ note
  | "phdthesis" =>
    #[.out .authors, .out (.keyIf "author"), .newBlock, .out .btitle, .newBlock,
      .out (.thesisType "PhD thesis"), .out (.field "school"), .out (.field "address"),
      .out .date] ++ url ++ note
  | "proceedings" =>
    #[.out .editors, .out (.keyIf "editor"), .newBlock, .out .btitle, .out .bvolume,
      .out .numberSeries, .out (.field "address"), .out .date, .newSentence,
      .out (.field "organization"), .out (.field "publisher")] ++ isbn ++ tail
  | "techreport" =>
    #[.out .authors, .out (.keyIf "author"), .newBlock, .out .title, .newBlock,
      .out .trNumber, .out (.field "institution"), .out (.field "address"), .out .date] ++
      url ++ note
  | "unpublished" =>
    #[.out .authors, .out (.keyIf "author"), .newBlock, .out .title, .newBlock,
      .out (.field "note"), .out .date] ++ url
  | _ =>
    #[.out .authors, .out (.keyIf "author"), .newBlockIf ["title", "howpublished"], .out .title,
      .newBlockIf ["howpublished"], .out (.field "howpublished"), .out .date,
      .newBlockIf ["issn"], .out .issn] ++ url ++ note

/-- The entry functions of plain.bst, which unsrt.bst, abbrv.bst and
alpha.bst share verbatim: plainnat's minus everything plain.bst predates —
no `key`, `doi`, `url`, `isbn`, `issn` — with plain's own spellings of the
cross-reference (`\cite`, the parent's editors named) and of a manual or a
proceedings volume that has no author or editor. -/
public def plainSteps (e : Entry) : Array Step :=
  let note : Array Step := #[.newBlock, .out (.field "note")]
  let xref := e.has "crossref"
  let who : Array Step := if e.has "author" then #[.out .authors] else #[.out .editors]
  match e.kind with
  | "article" =>
    #[.out .authors, .newBlock, .out .title, .newBlock] ++
    (if xref then #[.out (.articleCrossref false), .out .pages]
     else #[.out .journal, .out .volNumPages, .out .date]) ++ note
  | "book" =>
    who ++ #[.newBlock, .out .btitle] ++
    (if xref then #[.newBlock, .out (.bookCrossref false)]
     else #[.out .bvolume, .newBlock, .out .numberSeries, .newSentence,
       .out (.field "publisher"), .out (.field "address")]) ++
    #[.out .edition, .out .date] ++ note
  | "inbook" =>
    who ++ #[.newBlock, .out .btitle] ++
    (if xref then #[.out .chapterPages, .newBlock, .out (.bookCrossref false)]
     else #[.out .bvolume, .out .chapterPages, .newBlock, .out .numberSeries, .newSentence,
       .out (.field "publisher"), .out (.field "address")]) ++
    #[.out .edition, .out .date] ++ note
  | "booklet" =>
    #[.out .authors, .newBlock, .out .title, .newBlockIf ["howpublished", "address"],
      .out (.field "howpublished"), .out (.field "address"), .out .date] ++ note
  | "incollection" =>
    #[.out .authors, .newBlock, .out .title, .newBlock] ++
    (if xref then #[.out (.incollCrossref false), .out .chapterPages]
     else #[.out .inEdBooktitle, .out .bvolume, .out .numberSeries, .out .chapterPages,
       .newSentence, .out (.field "publisher"), .out (.field "address"), .out .edition,
       .out .date]) ++ note
  | "inproceedings" | "conference" =>
    #[.out .authors, .newBlock, .out .title, .newBlock] ++
    (if xref then #[.out (.incollCrossref false), .out .pages]
     else #[.out .inEdBooktitle, .out .bvolume, .out .numberSeries, .out .pages] ++
       (if e.has "address" then
         #[.out (.field "address"), .out .date, .newSentence, .out (.field "organization"),
           .out (.field "publisher")]
       else
         #[.newSentenceIf ["organization", "publisher"], .out (.field "organization"),
           .out (.field "publisher"), .out .date])) ++ note
  | "manual" =>
    (if e.has "author" then #[.out .authors]
     else #[.out (.field "organization"), .out (.field "address")]) ++
    #[.newBlock, .out .btitle] ++
    (if e.has "author" then
       #[.newBlockIf ["organization", "address"], .out (.field "organization"),
         .out (.field "address")]
     else if e.has "organization" then #[]
     else #[.newBlockIf ["address"], .out (.field "address")]) ++
    #[.out .edition, .out .date] ++ note
  | "mastersthesis" =>
    #[.out .authors, .newBlock, .out .title, .newBlock, .out (.thesisType "Master's thesis"),
      .out (.field "school"), .out (.field "address"), .out .date] ++ note
  | "phdthesis" =>
    #[.out .authors, .newBlock, .out .btitle, .newBlock, .out (.thesisType "PhD thesis"),
      .out (.field "school"), .out (.field "address"), .out .date] ++ note
  | "proceedings" =>
    (if e.has "editor" then #[.out .editors] else #[.out (.field "organization")]) ++
    #[.newBlock, .out .btitle, .out .bvolume, .out .numberSeries] ++
    (if e.has "address" then
       #[.out (.field "address"), .out .date, .newSentence] ++
       (if e.has "editor" then #[.out (.field "organization")] else #[]) ++
       #[.out (.field "publisher")]
     else
       (if e.has "editor" then
          #[.newSentenceIf ["organization", "publisher"], .out (.field "organization")]
        else #[.newSentenceIf ["publisher"]]) ++
       #[.out (.field "publisher"), .out .date]) ++ note
  | "techreport" =>
    #[.out .authors, .newBlock, .out .title, .newBlock, .out .trNumber,
      .out (.field "institution"), .out (.field "address"), .out .date] ++ note
  | "unpublished" =>
    #[.out .authors, .newBlock, .out .title, .newBlock, .out (.field "note"), .out .date]
  | _ =>
    #[.out .authors, .newBlockIf ["title", "howpublished"], .out .title,
      .newBlockIf ["howpublished"], .out (.field "howpublished"), .out .date] ++ note

/-- The output state plainnat.bst threads through an entry (`output.state`):
nothing written yet, inside a sentence, or a block or a sentence boundary
pending. -/
private inductive OutState where
  | beforeAll
  | mid
  | afterBlock
  | afterSentence
  deriving BEq

/-- Inline content with each citation and reference read as the key it
names: the text a `.bbl` holds where the field wrote `\cite{key}` or
`\ref{key}`, its closing brace aside. A leaf of `Ir.mapInlines`. -/
private def sourceText (xs : Array Ir.Inline) : Array Ir.Inline :=
  Ir.mapInlines (fun x => match x with
    | .cite _ keys => .text (keys.back?.getD "")
    | .ref k _ _ _ => .text k
    | x => x) xs

/-- BibTeX's `add.period$`: the entry so far takes a period unless it
already ends with `.`, `?` or `!` — read in the `.bbl` text the style
writes, where a citation or a reference a field holds is its command,
`\cite{key}` and `\ref{key}`, and the character before its closing brace
is its key's last (`sourceText`), never the `?` an unresolved one shows
for now. -/
private def addPeriod (out : Array Ir.Inline) : Array Ir.Inline :=
  match (Ir.plainText (sourceText out)).toList.getLast? with
  | none => out
  | some c => if c == '.' || c == '?' || c == '!' then out else out.push (.text ".")

/-- Adjacent text nodes as one: the pieces an entry is assembled from join
the way the `.bbl` line they stand for reads, so a run is shaped whole. -/
private def mergeText (xs : Array Ir.Inline) : Array Ir.Inline :=
  xs.foldl (fun acc x => match x, acc.back? with
    | .text b, some (.text a) => acc.pop.push (.text (a ++ b))
    | _, _ => acc.push x) #[]

/-- One reference-list entry as plainnat.bst's `output` writes it, with the
reports of its field readings: a piece joins its sentence with `, `; after
a block or sentence boundary the entry so far takes its period
(`add.period$`) and the piece opens the next; the entry closes with its
period (`fin.entry`). natbib's `\newblock` adds `\hskip .11em plus .33em
minus .07em` at a block boundary, which no IR node spells: the boundary is
one word space. `extra` is the entry's letter among those sharing its
label, which its date carries (`extraLabels`). -/
public def renderEntryCached (cv : FieldText) (nf : NameFormat) (steps : Array Step) (e : Entry)
    (extra : String) (cache : FieldCache) : (Array Ir.Inline × FieldReport) × FieldCache :=
  let run : RenderM (Array Ir.Inline) := do
    let mut out : Array Ir.Inline := #[]
    let mut st := OutState.beforeAll
    for step in steps do
      match step with
      | .out f =>
        let r ← renderField cv nf e (st == .mid) extra f
        unless r.isEmpty do
          out := match st with
            | .beforeAll => out
            | .mid => out.push (.text ", ")
            | _ => (addPeriod out).push (.text " ")
          out := out ++ r
          st := .mid
      | .newBlock => if st != .beforeAll then st := .afterBlock
      | .newSentence => if st == .mid then st := .afterSentence
      | .newBlockIf fs => if st != .beforeAll && fs.any e.has then st := .afterBlock
      | .newSentenceIf fs => if st == .mid && fs.any e.has then st := .afterSentence
    return mergeText (addPeriod out)
  let (out, ds, cache) := run.run ({}, cache)
  ((out, ds), cache)

/-- `renderEntryCached` with nothing read before. -/
public def renderEntryWith (cv : FieldText) (nf : NameFormat) (steps : Array Step) (e : Entry)
    (extra : String := "") : Array Ir.Inline × FieldReport :=
  (renderEntryCached cv nf steps e extra {}).1

/-- `renderEntryWith` under the reading that needs no elaborator
(`plainField`), its reports dropped. -/
public def renderEntry (nf : NameFormat) (steps : Array Step) (e : Entry) (extra : String := "") :
    Array Ir.Inline :=
  (renderEntryWith plainField nf steps e extra).1

/-- `unsrtnat`: the reference list in first-citation order (the "unsrt"),
the standard field orders, full names, author-year labels in its
`\bibitem`s — what `unsrtnat.bst` is, as one record. -/
public def Style.unsrtnat : Style where
  labels := true
  sort := .citation
  steps := plainnatSteps
  names := {}

/-- `plainnat`: the same fields and names, the list sorted by author then
year (natbib manual §4: plainnat is the author-year companion of plain). -/
public def Style.plainnat : Style where
  labels := true
  sort := .authorYear
  steps := plainnatSteps
  names := {}

/-- `plain`: numbers over a list sorted by its names, year and title
(plain.bst FUNCTION {presort}), formatted by plain.bst's own functions
(`plainSteps`). -/
public def Style.plain : Style where
  labels := false
  sort := .plain
  steps := plainSteps
  names := {}

/-- `alpha`: `plain`'s entries under alpha.bst's labels, the list sorted by
label (alpha.bst FUNCTION {presort}). -/
public def Style.alpha : Style :=
  { Style.plain with sort := .alpha, alphabetic := true }

/-- `unsrt`: `plain` in first-citation order, as unsrt.bst is. -/
public def Style.unsrt : Style :=
  { Style.plain with sort := .citation }

/-- The name format the abbrv-shaped styles share: first names abbreviate
to initials, first-first order — `{f.~}{vv~}{ll}{, jj}` in both abbrv.bst
and abbrvnat.bst FUNCTION {format.names}, so "J. Smith", never
"Smith, J.". The one axis the abbrv pair sets; everything else is
`plain`/`plainnat` verbatim. -/
public def abbrvNames : NameFormat := { initials := true }

/-- `abbrvnat`: `plainnat` with abbreviated first names — natbib ships
abbrvnat.bst as plainnat.bst minus only the name designator (natbib
manual §4 lists the three companion styles as one family). -/
public def Style.abbrvnat : Style :=
  { Style.plainnat with names := abbrvNames, shortMonths := true }

/-- `abbrv`: `plain` with abbreviated first names, the same relation
abbrv.bst has to plain.bst. -/
public def Style.abbrv : Style :=
  { Style.plain with names := abbrvNames, shortMonths := true }

/-- The style a `\bibliographystyle` name selects. `none` is W0353's cue;
the caller falls back to `unsrtnat` — a record, so the fallback loses the
name, never the machinery. -/
public def Style.named (name : String) : Option Style :=
  match name with
  | "unsrtnat" => some .unsrtnat
  | "unsrt" => some .unsrt
  | "plainnat" => some .plainnat
  | "plain" => some .plain
  | "abbrvnat" => some .abbrvnat
  | "abbrv" => some .abbrv
  | "alpha" => some .alpha
  | _ => none

/-- The month names abbrv.bst and abbrvnat.bst define for BibTeX's month
macros (`MACRO {jan} {"Jan."}` …). -/
private def shortMonthNames : Array String :=
  #["Jan.", "Feb.", "Mar.", "Apr.", "May", "June", "July", "Aug.", "Sept.", "Oct.", "Nov.", "Dec."]

/-! ## Resolution

`apply` is the pure half of the `\bibliography` effect: the driver reads
the named `.bib` file beside the document (`Ir.bibRefs` is the request) and
hands its text here; everything after — parsing, ordering, numbering,
formatting, the rewrite of every citation — is a function of the document
and that text. -/

/-- A key appended to an ordered set of keys: the array keeps first-appearance
order and the set answers membership in constant time, so collecting `n`
keys costs `n` steps, never `n²` — a `\nocite{*}` over a thesis-sized `.bib`
makes `n` the whole database. -/
private def addKey (acc : Array String × Std.HashSet String) (k : String) :
    Array String × Std.HashSet String :=
  if acc.2.contains k then acc else (acc.1.push k, acc.2.insert k)

/-- First-citation order: the keys the document cites, in order of first
appearance, each once — the sequence citation-order lists are sorted by
and numeric labels index into — among the citations `keep` admits (every
one by default; `\nocite`'s count, as they do for BibTeX). A leaf
projection of `Ir.foldDoc`, the one collect traversal, over every region
`resolveDoc` rewrites. -/
private def citedKeys (doc : Ir.Doc) (keep : Ir.CiteForm → Bool := fun _ => true) : Array String :=
  (Ir.foldDoc
    (fun acc x => match x with
      | .cite f keys => if keep f then keys.foldl addKey acc else acc
      | _ => acc) (#[], {}) doc).1

/-- `\nocite{*}`'s key, BibTeX's `\citation{*}`: every entry of the `.bib`
enters the list where it stands, in the database's order, after the keys
cited before it — a key already in the sequence keeps its place — but an
`@xdata` entry, which is data for other entries and never itself listed. -/
private def expandStar (entries : Array Entry) (cited : Array String) : Array String :=
  (cited.foldl (fun acc k =>
    if k == "*" then entries.foldl (fun acc e =>
      if e.kind == "xdata" then acc else addKey acc e.key) acc
    else addKey acc k) (#[], {})).1

/-- BibTeX's `sortify`: `purify$`, lowercased. -/
private def sortify (v : String) : String := (purify v).toLower

/-- plain.bst's `sort.format.names`: each name as `{vv{ } }{ll{ }}{  ff{
}}{  jj{ }}`, sortified, three spaces between names, and a closing
`others` as `et al`. -/
private def sortNames (v : String) : String :=
  let ns := splitNames v
  String.intercalate "   " (ns.toList.zipIdx.map fun (s, i) =>
    if i + 1 == ns.size && s == "others" then "et al"
    else
      let n := parseName s
      sortify ((if n.von.isEmpty then "" else n.von ++ " ") ++ n.last ++
        (if n.first.isEmpty then "" else "  " ++ n.first) ++
        (if n.jr.isEmpty then "" else "  " ++ n.jr)))

/-- plain.bst's `sort.format.title`: a leading `The `, `An ` or `A `
dropped, sortified. -/
private def sortTitle (v : String) : String :=
  let chop (w t : String) : String := if t.startsWith w then (t.drop w.length).toString else t
  sortify (chop "A " (chop "An " (chop "The " v)))

/-- The names plain.bst's `presort` reads by type: a book's or a chapter's
editors when it has no author, a proceedings volume's editors or
organization, a manual's author or organization, else the author, and the
`key` where none of them is there. -/
private def sortWho (e : Entry) : String :=
  let key := ((e.field? "key").map sortify).getD ""
  let org := (e.field? "organization").map fun o => sortify (chopThe o)
  let au := (e.field? "author").map sortNames
  let ed := (e.field? "editor").map sortNames
  let first (fs : List (Option String)) : String := (fs.findSome? id).getD key
  match e.kind with
  | "book" | "inbook" => first [au, ed]
  | "proceedings" => first [ed, org]
  | "manual" => first [au, org]
  | _ => first [au]

/-- plain.bst's sort key: the names, the year, the title, four spaces
apart; the cite key breaks a tie. -/
private def plainKey (r : Resolved) : String × String :=
  (sortWho r.sortEntry ++ "    " ++ sortify ((r.sortEntry.field? "year").getD "") ++ "    " ++
    sortTitle ((r.sortEntry.field? "title").getD ""), r.key)

/-- alpha.bst's `format.lab.names`: one author's `{v{}}{l{}}` letters, or
the first three letters of the last name where those are fewer than two;
two to four authors' letters in turn; past four the first three's and a
`+`, and a closing `others` as one. alpha.bst raises it (`\etalchar{+}`,
`$^{+}$`); a mark is plain text here, so it stands on the baseline. The
letters' length is `text.length$`'s, a special character one letter. -/
private def alphaNames (v : String) : String :=
  let ns := splitNames v
  let vl (s : String) : String :=
    let n := parseName s
    tokenLetters n.von ++ tokenLetters n.last
  if ns.size > 1 then
    let left := if ns.size > 4 then 3 else ns.size
    String.join ((List.range left).map fun i =>
      let s := ns[i]?.getD ""
      if i + 1 == ns.size && s == "others" then "+" else vl s) ++
      (if ns.size > 4 then "+" else "")
  else
    let s := ns[0]?.getD ""
    let a := vl s
    if textLength a < 2 then textPrefix (parseName s).last 3 else a

/-- alpha.bst's label stem by type (`calc.label`): the names `alphaNames`
reads — a book's or chapter's editors where it has no author, a
proceedings volume's editors — else the `key`'s first three letters; a
manual's or proceedings' organization only where it has no `key`
(`author.key.organization.label`, `editor.key.organization.label`, which
read the key first, where the sort reads the organization first); else
the cite key's first three characters. -/
private def alphaWho (e : Entry) (key : String) : String :=
  let k := (e.field? "key").map (textPrefix · 3)
  let org := (e.field? "organization").map fun o => textPrefix (chopThe o) 3
  let first (fs : List (Option String)) : String :=
    ((fs ++ [k]).findSome? id).getD ((key.take 3).toString)
  let au := (e.field? "author").map alphaNames
  let ed := (e.field? "editor").map alphaNames
  match e.kind with
  | "book" | "inbook" => first [au, ed]
  | "proceedings" => first [ed, k, org]
  | "manual" => first [au, k, org]
  | _ => first [au]

/-- An alpha label's year: the last `n` characters of the purified year. -/
private def yearTail (e : Entry) (n : Nat) : String :=
  let y := purify ((e.field? "year").getD "")
  (y.drop (y.length - n)).toString

/-- alpha.bst's sort label (`sort.label`): the stem and the year's last four
characters, sortified — what an entry's letter is decided by. -/
private def alphaSortLabel (r : Resolved) : String :=
  sortify (alphaWho r.sortEntry r.key ++ yearTail r.sortEntry 4)

/-- alpha.bst's sort key: the sort label, then plain.bst's. -/
private def alphaKey (r : Resolved) : String × String :=
  (alphaSortLabel r ++ "    " ++ (plainKey r).1, r.key)

/-- plainnat.bst's `sort.format.names`: plain's, except that a closing
`others` sorts as `zzzzz` and, in a list of three or more, the second name
after `zz`, the year and three spaces. -/
private def sortNamesNat (v year : String) : String :=
  let ns := splitNames v
  String.intercalate "   " (ns.toList.zipIdx.map fun (s, i) =>
    if i > 0 && i + 1 == ns.size && s == "others" then "zzzzz"
    else
      let n := parseName s
      (if ns.size > 2 && i == 1 then "zz" ++ year ++ "   " else "") ++
        sortify ((if n.von.isEmpty then "" else n.von ++ " ") ++ n.last ++
          (if n.first.isEmpty then "" else "  " ++ n.first) ++
          (if n.jr.isEmpty then "" else "  " ++ n.jr)))

/-- plainnat.bst's sort key, as bibtex computes it: the names by type
(`sortWho`'s choice, `sortNamesNat`), the year and the cite key, four
spaces apart. -/
private def plainnatKey (r : Resolved) : String × String :=
  let e := r.sortEntry
  let year := (e.field? "year").getD ""
  let key := ((e.field? "key").map sortify).getD ""
  let org := (e.field? "organization").map fun o => sortify (chopThe o)
  let au := (e.field? "author").map (sortNamesNat · year)
  let ed := (e.field? "editor").map (sortNamesNat · year)
  let first (fs : List (Option String)) : String := (fs.findSome? id).getD key
  let who := match e.kind with
    | "book" | "inbook" => first [au, ed]
    | "proceedings" => first [ed, org]
    | "manual" => first [au, org]
    | _ => first [au]
  (who ++ "    " ++ sortify year ++ "    " ++ r.key, r.key)

/-- Lexicographic order on two keys: the sort strings by collation
(`Collate`), the cite keys as written. For the purified ASCII keys BibTeX
compares this is its own order — spaces, then digits, then letters — and a
letter outside ASCII sorts with its base letter, where bibtex 0.99, reading
UTF-8 as bytes, put every accented capital after `Z`. -/
private def pairCompare (a b : Collate.Key × String) : Ordering :=
  (a.1.compare b.1).then (Ord.compare a.2 b.2)

/-- A BibTeX key with its sort string read for collation, once per entry. -/
private def collated (key : Resolved → String × String) (r : Resolved) : Collate.Key × String :=
  let (k, c) := key r
  (Collate.key k, c)

/-- One sortset's value under a biblatex template: a string compared by
collation, or a number (biber's integer and date-part sortsets). -/
private inductive SortVal where
  | str (k : Collate.Key)
  | int (n : Int)

private def SortVal.compare : SortVal → SortVal → Ordering
  | .str a, .str b => a.compare b
  | .int a, .int b => Ord.compare a b
  | .int _, .str _ => .lt
  | .str _, .int _ => .gt

/-- What a template's sortset reads (biblatex.def's `\sort{…}` elements):
`presort` (`mm` by default), `sortkey` (`final`: where it is set it stands
in for every later sortset), the names — `sortname`, `author`, `editor`,
`translator` under their `use` options, then `sorttitle` and `title` —
the titles, the year — `sortyear`, the date's or the legacy year, a number
or, where it is none, after every number — the year with `9999` where
there is none, and the volume, `0` where there is none. -/
private inductive SortSet where
  | presort
  | sortkey
  | names
  | titles
  | year
  | yearOr9999
  | volume
  deriving BEq

/-- biblatex's sorting templates the engine sorts by, each as its sortsets
and whether it sorts its year descending (biblatex.def `nty`, `nyt`,
`nyvt`, `ynt`, `ydnt`). -/
public def bblTemplates : List String := ["nty", "nyt", "nyvt", "ynt", "ydnt"]

private def bblTemplate : String → List SortSet × Bool
  | "nyt" => ([.presort, .sortkey, .names, .year, .titles, .volume], false)
  | "nyvt" => ([.presort, .sortkey, .names, .year, .volume, .titles], false)
  | "ynt" => ([.presort, .sortkey, .yearOr9999, .names, .titles], false)
  | "ydnt" => ([.presort, .sortkey, .yearOr9999, .names, .titles], true)
  | _ => ([.presort, .sortkey, .names, .titles, .year, .volume], false)

/-- A literal field as biber sorts it (Biber::Utils `normalise_string_sort`):
its TeX read as text — biber decodes it when it reads the file — every
other command's name and every brace dropped, white space runs one space. -/
private def sortText (v : String) : String :=
  " ".intercalate ((sortPlainText v).splitOn " " |>.filter (!·.isEmpty))

/-- A name's parts as biber's sorting name key reads them (biblatex.def
`\DeclareSortingNamekeyTemplate`): the prefix with the family under
`useprefix`, the given name, the suffix, the prefix after them without. -/
private def namePartsForSort (up : Bool) (n : Name) : List (String × String) :=
  (if up then [("prefix", n.von), ("family", n.last)] else [("family", n.last)]) ++
    [("given", n.first), ("suffix", n.jr)] ++ (if up then [] else [("prefix", n.von)])

/-- The name lists a biblatex list sorts by, each value read once: every
`author`, `editor`, `translator` and `sortname` the list's entries hold,
its names as biber splits them (`and others` dropped). -/
private def sortNameLists (es : List Entry) : Std.HashMap String (Array Name) :=
  es.foldl (init := {}) fun m e =>
    ["author", "editor", "translator", "sortname"].foldl (init := m) fun m f =>
      match e.field? f with
      | none => m
      | some v =>
        if m.contains v then m
        else m.insert v (((splitNames v).filter (· != "others")).map parseNameBiber)

/-- The longest each name part is written across the names a list sorts
(Biber::Section's `np_length`, which pads every part to it so that parts
compare part by part). -/
private def namePartLengths (lists : Std.HashMap String (Array Name)) : Std.HashMap String Nat :=
  lists.fold (init := {}) fun m _ ns =>
    ns.foldl (init := m) fun m n =>
      [("prefix", n.von), ("family", n.last), ("given", n.first), ("suffix", n.jr)].foldl
        (init := m) fun m (part, t) =>
          let len := (Nfc.normalize (sortText t)).length
          if len > m.getD part 0 then m.insert part len else m

/-- A name list's sort string (Biber::Internals `_namestring`): the names
its sorting shows, each part padded to the list's longest, joined with
nothing between them, and biber's `et al.` mark where the list is cut. -/
private def nameSortString (lens : Std.HashMap String Nat) (up : Bool) (shown : Option Nat)
    (names : Array Name) : String :=
  let real := names.toList
  let vis := match shown with
    | some k => real.take k
    | none => real
  let pad (part t : String) : String :=
    if t.isEmpty then ""
    else
      let t := sortText t
      t ++ String.ofList (List.replicate (lens.getD part 0 - (Nfc.normalize t).length) ' ')
  String.join (vis.map fun n =>
    String.join ((namePartsForSort (n.useprefix.getD up) n).map fun (part, t) => pad part t)) ++
    (if vis.length < real.length then String.singleton (Char.ofNat 0x10FFFD) else "")

/-- A sortset's integer as biber's sort compares it (Biber.pm's
`sort_list`): the number, or past every number where the value is none —
how `final`'s `sortkey` reads where it stands in for an integer sortset. -/
private def sortInt (v : String) : Int := ((text v).trimAscii.toString.toInt?).getD 2000000000

/-- A roman numeral's value as biber reads an integer field for sorting
(Biber::Internals `_sort_integer`, through Text::Roman's `isroman` and
`roman2int`): either case, the numeral forms of U+2160 to U+217F as the
letters they decompose to, no I, X, C or M four times running and no V, L
or D twice, none of the interleavings Text::Roman refuses (IXI, IVI, VIV
and their kin), and the value the symbols sum to read greedily from the
left, a subtractive pair before a single symbol. `none` where the text is
not one. -/
private def romanValue (s : String) : Option Nat := Id.run do
  let forms := #["I", "II", "III", "IV", "V", "VI", "VII", "VIII", "IX", "X", "XI", "XII",
    "L", "C", "D", "M"]
  let mut u := ""
  for c in s.toList do
    let n := c.toNat
    if 0x2160 ≤ n && n ≤ 0x216F then u := u ++ (forms[n - 0x2160]?.getD "")
    else if 0x2170 ≤ n && n ≤ 0x217F then u := u ++ (forms[n - 0x2170]?.getD "")
    else u := u.push c.toUpper
  let cs := u.toList.toArray
  if cs.isEmpty || !cs.all ("IVXLCDM".contains ·) then return none
  let holds (piece : String) : Bool := (u.splitOn piece).length > 1
  let run (c : Char) (k : Nat) : String := String.ofList (List.replicate k c)
  if ['I', 'X', 'C', 'M'].any (holds <| run · 4) || ['V', 'L', 'D'].any (holds <| run · 2) then
    return none
  if ["IXI", "XCX", "CMC", "IVI", "VXV", "XLX", "LCL", "CDC", "DMD", "VIV", "XVX", "LXL", "CLC",
      "DCD", "MDM"].any holds then
    return none
  let pairs : List (String × Nat) :=
    [("IV", 4), ("IX", 9), ("XL", 40), ("XC", 90), ("CD", 400), ("CM", 900)]
  let single (c : Char) : Nat := match c with
    | 'I' => 1 | 'V' => 5 | 'X' => 10 | 'L' => 50 | 'C' => 100 | 'D' => 500 | _ => 1000
  let mut total := 0
  let mut i := 0
  for _ in [0:cs.size + 1] do
    if h : i < cs.size then
      match pairs.lookup (String.ofList [cs[i], cs[i + 1]?.getD ' ']) with
      | some v =>
        total := total + v
        i := i + 2
      | none =>
        total := total + single cs[i]
        i := i + 1
    else break
  return some total

/-- An integer field's sort value (Biber::Internals `_sort_integer`): a
roman numeral as its value, else as `sortInt` reads it. -/
private def sortIntField (v : String) : Int :=
  let t := (text v).trimAscii.toString
  match romanValue t with
  | some n => n
  | none => sortInt t

/-- The tailoring file a biblatex list sorts by: its `sortlocale`, `auto`
read as babel's main language (`english` without babel), through biber's
language map (`Collate.biberLocale`) to the file Unicode::Collate::Locale
accepts it under (`Collate.localeFile`; `""` is the default table). -/
public def bblSortFile (o : BblOptions) : String :=
  Collate.localeFile (Collate.biberLocale
    (if o.sortlocale == "auto" then o.babelMain.getD "english" else o.sortlocale))

/-- The tailoring a biblatex list sorts by, where `Collate`'s rows carry
it; the default table where the file is none or of another script. -/
private def bblTailoring (o : BblOptions) : Collate.Tailoring :=
  (Collate.tailoringFor (bblSortFile o)).getD {}

/-- An entry's biblatex sort key under a template (Biber::Internals
`_generatesortinfo`, Biber.pm's `sort_list`): each sortset's value,
`final`'s `sortkey` standing in for every later one where it is set, each
string collated under the list's locale (`bblTailoring`). -/
private def bblSortKey (template : String) (o : BblOptions) (tl : Collate.Tailoring)
    (lists : Std.HashMap String (Array Name)) (lens : Std.HashMap String Nat)
    (r : Resolved) : Array SortVal := Id.run do
  let e := r.sortEntry
  let oe := o.forEntry e
  let nonEmpty (f : String) := (e.field? f).filter fun v => !v.trimAscii.toString.isEmpty
  let str (s : String) : SortVal := .str (Collate.keyWith tl s)
  let titles : SortVal := str (sortText (((nonEmpty "sorttitle").orElse fun _ => nonEmpty "title").getD ""))
  let names : SortVal :=
    let used := [("sortname", true), ("author", oe.useauthor), ("editor", oe.useeditor),
      ("translator", oe.usetranslator)]
    match used.findSome? fun (f, use) => if use then nonEmpty f else none with
    | some v =>
      let names := (lists.get? v).getD
        (((splitNames v).filter (· != "others")).map parseNameBiber)
      str (nameSortString lens oe.useprefix r.sortShown names)
    | none => titles
  let yearOf : Option Int := match (nonEmpty "sortyear") with
    | some y => some (sortIntField y)
    | none => match e.dateParts #[] "" with
      | .parsed dv => some ((dv.start.map (·.year)).getD 2000000000)
      | .legacy y _ => some (sortIntField y)
      | .written _ => some 2000000000
      | .none => none
  let volume : SortVal := .int ((nonEmpty "volume").map sortIntField |>.getD 0)
  let (sets, descending) := bblTemplate template
  let mut out : Array SortVal := #[]
  let mut final : Option String := none
  for set in sets do
    match final with
    | some k => out := out.push (if set == .year || set == .yearOr9999 || set == .volume then
        .int (sortInt k) else str k)
    | none =>
      match set with
      | .presort => out := out.push (str (sortText ((nonEmpty "presort").getD "mm")))
      | .sortkey =>
        match nonEmpty "sortkey" with
        | some k =>
          final := some (sortText k)
          out := out.push (str "")
        | none => out := out.push (str "")
      | .names => out := out.push names
      | .titles => out := out.push titles
      | .year =>
        let y := yearOf.getD 2000000000
        out := out.push (.int (if descending then -y else y))
      | .yearOr9999 =>
        let y := yearOf.getD 9999
        out := out.push (.int (if descending then -y else y))
      | .volume => out := out.push volume
  return out

/-- Two biblatex keys, sortset by sortset. -/
private def bblCompare (a b : Array SortVal) : Ordering := Id.run do
  for i in [0:Nat.min a.size b.size] do
    match a[i]?, b[i]? with
    | some x, some y =>
      match x.compare y with
      | .eq => pure ()
      | o => return o
    | _, _ => pure ()
  return .eq

/-- The comparison a sort order names, over entries carrying their
first-citation position. Citation order compares the positions, which are
distinct by construction; BibTeX's orders compare their keys, each ending
in the cite key; a biblatex template compares its sortsets, padded against
the two entries alone (the list sorts against the whole list,
`sortResolved`). -/
public def SortOrder.compare (so : SortOrder) (a b : Resolved) : Ordering :=
  match so with
  | .citation => Ord.compare a.position b.position
  | .plain => pairCompare (collated plainKey a) (collated plainKey b)
  | .alpha => pairCompare (collated alphaKey a) (collated alphaKey b)
  | .authorYear => pairCompare (collated plainnatKey a) (collated plainnatKey b)
  | .bbl t o =>
    let lists := sortNameLists [a.sortEntry, b.sortEntry]
    let lens := namePartLengths lists
    let tl := bblTailoring o
    bblCompare (bblSortKey t o tl lists lens a) (bblSortKey t o tl lists lens b)

/-- A merge sort over keys computed once per entry. -/
private def sortByKey {κ : Type} (key : Resolved → κ) (cmp : κ → κ → Ordering) (xs : List Resolved) :
    List Resolved :=
  ((xs.map fun r => (key r, r)).mergeSort fun a b => cmp a.1 b.1 != .gt).map (·.2)

/-- The list sorted by the order's comparison, in `n log n` steps: a merge
sort (stable), over keys computed once per entry rather than once per
comparison — a thesis-sized list is thousands of entries, and the
insertion sort this replaces was quadratic in them. A biblatex template's
names pad against every name the list sorts. -/
public def sortResolved (so : SortOrder) (xs : List Resolved) : List Resolved :=
  match so with
  | .citation => xs.mergeSort fun a b => decide (a.position ≤ b.position)
  | .plain => sortByKey (collated plainKey) pairCompare xs
  | .alpha => sortByKey (collated alphaKey) pairCompare xs
  | .authorYear => sortByKey (collated plainnatKey) pairCompare xs
  | .bbl t o =>
    let lists := sortNameLists (xs.map (·.sortEntry))
    let lens := namePartLengths lists
    sortByKey (bblSortKey t o (bblTailoring o) lists lens) bblCompare xs

/-- What one key renders as, everywhere it is cited: its entry at its
1-based position in the reference list. -/
@[expose] public def Resolver := String → Option Resolved

/-- The label two entries must share to take letters: plainnat.bst's
`calc.label`, which its `forward.pass` compares — the label names a
citation prints and the year; and biber's extradate group — the labelname
whole, given names and all, as many names as a citation shows, and the
label year — the names as uniqueness reads them (`nameHashKey`, the
entry's `extraKey`), so two authors a citation tells apart take no letters,
and two it cannot take them. -/
private def labelOf (r : Resolved) (biblatex : Bool := false) : String :=
  let e := r.entry
  let year := if citeYear e == "n.d." then "" else citeYear e
  if biblatex then
    let year := match r.labelYear with
      | some (t, _) => t
      | none => year
    match r.extraKey with
    | some k => k ++ "(" ++ year
    | none => citeAuthors e true ++ "(" ++ year
  else citeAuthors e biblatex ++ "(" ++ year

/-- The letter of the `i`-th entry among those sharing a label: `a`, `b`,
… `z`, then `aa`, `ab`, … — biblatex's `\mknumalph`, and for BibTeX's
styles a departure from `int.to.chr$`, which past `z` sets `{`, `|` and
on into control characters no face has a glyph for. -/
private def extraLetter (i : Nat) : String := Id.run do
  -- bijective base 26 over the 1-based index: 1 is `a`, 26 `z`, 27 `aa`
  let mut n := i + 1
  let mut out : List Char := []
  for _ in [0:i + 2] do
    if n == 0 then break
    out := Char.ofNat ('a'.toNat + (n - 1) % 26) :: out
    n := (n - 1) / 26
  return String.ofList out

/-- The letters plainnat.bst's `forward.pass` and `reverse.pass` give a
reference list, and unsrtnat.bst's the same: the entries sharing a label
(`labelOf`) take `a`, `b`, … in list order, and an entry whose label is its
own takes none. Each label is computed once and grouped through a map, so
the letters cost one pass over the list, never a comparison per pair. -/
private def extraLabels (rs : Array Resolved) (biblatex : Bool := false) : Array Resolved :=
  -- an entry with no labels (`skiplab`) takes no letter and counts for none
  let labels := rs.map fun r =>
    if r.skiplab then "\u0000" ++ r.key
    else labelOf r biblatex
  let counts : Std.HashMap String Nat := labels.foldl (fun m l => m.insert l (m.getD l 0 + 1)) {}
  let ranks := (labels.foldl (fun (acc : Std.HashMap String Nat × Array Nat) l =>
    (acc.1.insert l (acc.1.getD l 0 + 1), acc.2.push (acc.1.getD l 0))) ({}, #[])).2
  rs.mapIdx fun i r =>
    { r with extra :=
        if counts.getD (labels[i]?.getD "") 0 < 2 then "" else extraLetter (ranks[i]?.getD 0) }

/-- alpha.bst's labels over the sorted list (`calc.label`, `forward.pass`,
`reverse.pass`): each entry's stem and the year's last two characters, and
— where neighbours share a sort label — the letters `a`, `b`, … in list
order, as plain text. -/
private def alphaMarks (rs : Array Resolved) : Array Resolved :=
  let sl := rs.map alphaSortLabel
  let ranks := (sl.foldl (fun (acc : Array Nat × Option String) l =>
    let r := if acc.2 == some l then (acc.1.back?.getD 0) + 1 else 0
    (acc.1.push r, some l)) (#[], none)).1
  rs.mapIdx fun i r =>
    let rank := ranks[i]?.getD 0
    let run := rank > 0 || (sl[i + 1]? == sl[i]? && sl[i + 1]?.isSome)
    let letter := if run then extraLetter rank else ""
    let year := yearTail r.sortEntry 2
    let tex := alphaWho r.sortEntry r.key ++ year
    { r with label := some (text tex ++ letter), labelTeX := some (tex ++ letter) }

/-- What biber reads of a biblatex list before it sorts and labels it, each
entry under its own options (`BblOptions.forEntry`): its uniqueness over
the whole list (`uniqueness`) — the labelname its citations print, the key
its letter groups by, the names its `uniquelist` shows — the names its
sort key reads (biber's `process_visible_names` over the list sorting
reads), its label year, its `shorthand`, and whether it is listed and
labelled (`skipbib`, `skiplab`). -/
private def bblAnnotate (o : BblOptions) (months : Array String) (rs : Array Resolved) :
    Array Resolved :=
  let uo := o.unique'
  let opts := rs.map fun r => o.forEntry r.entry
  let lists := (rs.zip opts).map fun (r, oe) => oe.labelName r.entry
  let us := uniqueness uo (lists.map fun l => (l.map (·.2)).getD {})
  ((rs.zip opts).zip (lists.zip us)).map fun ((r, oe), l, u) =>
    let nonEmpty (f : String) := (r.entry.field? f).filter fun v => !v.trimAscii.toString.isEmpty
    let sortList := [("sortname", true), ("author", oe.useauthor), ("editor", oe.useeditor),
      ("translator", oe.usetranslator)].findSome? fun (f, use) =>
        if use then (nonEmpty f).map fun v =>
          (f, match l with
            | some (lf, nl) => if lf == f then nl else NameList.ofValue v
            | none => NameList.ofValue v)
        else none
    { r with
      citeNames := l.map fun (_, nl) => citeNamesTeX uo nl u
      extraKey := l.map fun (_, nl) => nameHashKey uo nl u
      nameHash := l.map fun (_, nl) => nameHashFull uo nl u
      labelUl := l.bind fun (f, _) => u.ul.map (f, ·)
      sortShown := sortList.map fun (f, nl) =>
        shownCount nl.names.size oe.maxsortnames oe.minsortnames
          (if l.any (·.1 == f) then u.ul else none)
      shorthand := nonEmpty "shorthand"
      labelYear := some (bblLabelYear months r.entry)
      skipbib := oe.skipbib
      skiplab := oe.skiplab }

/-- biblatex's numeric labels (biblatex.sty's `labelnumber`): an entry's
number counts the listed entries before it that are numbered — neither a
shorthand, which stands in for the number, nor an entry with no labels
(`skiplab`), whose citations print an empty label as biblatex's do. -/
private def numericLabels (rs : Array Resolved) : Array Resolved :=
  if rs.any fun r => r.shorthand.isSome || r.skiplab then
    let numbers := (rs.foldl (init := ((#[] : Array Nat), 0)) fun (acc, n) r =>
      if r.shorthand.isSome || r.skiplab then (acc.push n, n) else (acc.push (n + 1), n + 1)).1
    rs.mapIdx fun i r =>
      { r with label := some (match r.shorthand with
        | some sh => Ir.smartPunct (text sh)
        | none => if r.skiplab then "" else toString (numbers[i]?.getD 0))
               labelTeX := r.shorthand }
  else rs

/-- The reference list a style builds from the cited entries: sorted by
the style's order, positions assigned by list index — so the numeric
marker IS the sort position, the fact `\cite` marks rest on — and each
entry's letter among those sharing its label (`extraLabels`). A biblatex
list (`bbl`) reads its uniqueness first (`bblAnnotate`), and a numeric one
numbers past its shorthands and unlabelled entries (`numericLabels`). -/
public def resolveEntries (style : Style) (cited : Array String)
    (find : String → Option Entry) (biblatex : Bool := false)
    (bbl : Option (BblOptions × Bool) := none) (months : Array String := Locale.en.months)
    (findRaw : String → Option Entry := fun _ => none) : Array Resolved :=
  -- First-citation positions (1-based, in cited order) feed the sort;
  -- the final position is the index in the sorted list.
  let hits := cited.foldl (fun acc k =>
    match find k with
    | some e => acc.push { key := k, position := acc.size + 1, entry := e, raw := findRaw k }
    | none => acc) #[]
  let hits := match bbl with
    | some (o, _) => bblAnnotate o months hits
    | none => hits
  let sorted := sortResolved style.sort hits.toList
  let rs := extraLabels (sorted.toArray.mapIdx fun i r => { r with position := i + 1 }) biblatex
  let rs := match bbl with
    | some (_, true) => numericLabels rs
    | _ => rs
  if style.alphabetic then alphaMarks rs else rs

/-- The mark an item carries: in numbers mode its label, else its
position; none in author-year mode. -/
public def itemMarker (p : CitePunct) (r : Resolved) : Option String :=
  if p.numbers then some (r.label.getD (toString r.position)) else none

/-- The items a `\bibliography` block ships, each with what reading its
fields reported: each resolved entry formatted per the style through the
field reading `cv`, marked by its position in numbers mode and by nothing
in author-year mode — natbib's `\@biblabel` is the number there and an
empty hanging label here. The date carries the entry's letter in
author-year mode (FUNCTION {format.date}); numbers mode's `\natexlab`
prints nothing. -/
public def bibItemsWith (cvOf : String → FieldText) (p : CitePunct) (style : Style)
    (resolved : Array Resolved) : Array (Ir.BibItem × FieldReport) :=
  let renders := (resolved.foldl (init := ((#[] : Array (Array Ir.Inline × FieldReport)),
      ({} : FieldCache))) fun (acc, cache) r =>
    let (out, cache) := renderEntryCached (cvOf r.key) style.names (style.steps r.entry) r.entry
      (if p.numbers then "" else r.extra) cache
    (acc.push out, cache)).1
  resolved.mapIdx fun i r =>
    let rd := renders[i]?.getD (#[], {})
    ({ key := r.key, marker := itemMarker p r, content := rd.1,
       labelFlush := p.numbers && r.label.isSome }, rd.2)

/-- The entries a biblatex list prints: all but those under `skipbib`,
which are cited and numbered and never listed. -/
public def bblListed (resolved : Array Resolved) : Array Resolved :=
  resolved.filter (!·.skipbib)

/-- The items biblatex's standard styles set (`renderBbl`), each with what
reading its fields reported and the fields its driver read: the listed
entries (`bblListed`), numbered in numbers mode, the entry's extradate
letter in authoryear's head, and authoryear's dash where an entry's head
names repeat the previous entry's (`bblHeadNames`). -/
public def bblItems (o : BblOptions) (cvOf : String → FieldText) (p : CitePunct)
    (resolved : Array Resolved) (months : Array String := Locale.en.months) :
    Array ((Ir.BibItem × FieldReport) × List String) :=
  let listed := bblListed resolved
  let renders := (listed.foldl (init := ((#[] : Array (Array Ir.Inline × FieldReport × List String)),
      (none : Option String), ({} : FieldCache))) fun (acc, prev, cache) r =>
    let names := bblHeadNames o r.entry
    let dash := o.style == .authoryear && o.dashed && names.isSome && names == prev
    let (out, cache) := renderBblCached o (cvOf r.key) r.entry
      (if o.style == .authoryear then r.extra else "") dash r.labelUl months cache
    (acc.push out, names, cache)).1
  listed.mapIdx fun i r =>
    let rd := renders[i]?.getD (#[], {}, [])
    (({ key := r.key, marker := itemMarker p r, content := rd.1 }, rd.2.1), rd.2.2)

/-- `bibItemsWith` under the reading that needs no elaborator. -/
public def bibItems (p : CitePunct) (style : Style) (resolved : Array Resolved) :
    Array Ir.BibItem :=
  (bibItemsWith (fun _ => plainField) p style resolved).map (·.1)

/-! ### The theorems the four-axis shape earns

Each axis being a pure function is what makes these statable; a
transcribed `.bst` has none of them. -/

/-- Numbering is the sort position: in numbers mode, the marker of the
reference list's `i`-th entry is its label, else its 1-based index in the
sorted list — under whatever field reading the build gives the list
(`cvOf`) — the fact every `\cite` mark rests on, `positions_exact` below
being the half that says the positions the marks look up are those same
indices. Floats state the same vocabulary in `Ir.numberFloats_exact` — a
label is the index of first appearance in a sequence, `List.range'` both
times — but over a different data shape (a counter threaded through a tree
walk, not a `mapIdx` over a sorted list). Deliberately not unified: a
shared "consecutive assignment" lemma would leave each proof's hard part —
here a one-line `simp`, there the tree induction — untouched. -/
public theorem bibItems_marker_exact (cvOf : String → FieldText) (p : CitePunct) (style : Style)
    (resolved : Array Resolved) (h : p.numbers = true) (i : Nat) (hi : i < resolved.size) :
    (bibItemsWith cvOf p style resolved)[i]?.bind (·.1.marker) =
      some (resolved[i].label.getD (toString resolved[i].position)) := by
  simp [bibItemsWith, itemMarker, Array.getElem?_mapIdx, Array.getElem?_eq_getElem hi, h]

/-- **biblatex's numbered list marks each item as its citations do**: in
numbers mode the `i`-th item biblatex's styles set carries the `i`-th
listed entry's label (`numericLabels`: its number among the numbered, its
shorthand, or the empty label of an entry with none), else its position. -/
public theorem bblItems_marker_exact (o : BblOptions) (cvOf : String → FieldText)
    (p : CitePunct) (resolved : Array Resolved) (months : Array String) (h : p.numbers = true)
    (i : Nat) (hi : i < (bblListed resolved).size) :
    (bblItems o cvOf p resolved months)[i]?.bind (·.1.1.marker) =
      some ((bblListed resolved)[i].label.getD (toString (bblListed resolved)[i].position)) := by
  simp [bblItems, itemMarker, Array.getElem?_mapIdx, Array.getElem?_eq_getElem hi, h]

/-- The positions `resolveEntries` hands the marks are the 1-based indices
of the sorted list: position `i + 1` at index `i`, whatever the sort
order did, and alpha's and the shorthands' labels leave them. Together with
`bibItems_marker_exact`, the numeric marker at index `i` is `i + 1` where
the style gives the entry no label of its own. -/
public theorem positions_exact (style : Style) (cited : Array String)
    (find : String → Option Entry) (biblatex : Bool) (bbl : Option (BblOptions × Bool))
    (months : Array String) (findRaw : String → Option Entry)
    (i : Nat) (hi : i < (resolveEntries style cited find biblatex bbl months findRaw).size) :
    (resolveEntries style cited find biblatex bbl months findRaw)[i].position = i + 1 := by
  unfold resolveEntries at hi ⊢
  rcases bbl with _ | ⟨o, _ | _⟩ <;>
    simp only [numericLabels] at hi ⊢ <;>
    split <;> (try split) <;> simp [alphaMarks, extraLabels] at hi ⊢

/-- The sorted list holds exactly the input's elements — the membership
half of "the emitted list is a permutation of the cited set". -/
public theorem sortResolved_mem (so : SortOrder) (xs : List Resolved) (z : Resolved) :
    z ∈ sortResolved so xs ↔ z ∈ xs := by
  cases so <;> simp [sortResolved, sortByKey]

/-- The sorted list is exactly as long as the input: with `sortResolved_mem`
this is the counting half of the permutation claim. -/
public theorem sortResolved_length (so : SortOrder) (xs : List Resolved) :
    (sortResolved so xs).length = xs.length := by
  cases so <;> simp [sortResolved, sortByKey]

/-- The comparison is total in the order-theoretic sense: two entries
always compare, one way or the other — `gt` one way implies not-`gt` the
other for citation order, whose comparison is over the distinct
first-citation positions. Author-year's chained string comparison owes the
same statement; it is the recorded remainder of this slice. -/
public theorem compare_citation_asymm (a b : Resolved)
    (h : SortOrder.citation.compare a b = .gt) :
    SortOrder.citation.compare b a ≠ .gt := by
  simp [SortOrder.compare, Nat.compare_eq_gt] at h ⊢
  omega

/-- The sorted list is sorted: no element compares `gt` against a later
one, for citation order. (`Pairwise` over the comparison; author-year is
the recorded remainder beside `compare_citation_asymm`.) -/
public theorem sortResolved_sorted_citation (xs : List Resolved) :
    (sortResolved .citation xs).Pairwise
      (fun a b => SortOrder.citation.compare a b ≠ .gt) := by
  have h := List.pairwise_mergeSort (le := fun (a b : Resolved) => decide (a.position ≤ b.position))
    (fun a b c hab hbc => by simp at hab hbc ⊢; omega)
    (fun a b => by simp; omega) xs
  refine h.imp fun {a b} hab => ?_
  simp [SortOrder.compare, Nat.compare_eq_gt] at hab ⊢
  omega

mutual

/-- The citation rewrite: every `.cite` node becomes its rendering under the
document's punctuation (`renderCite`), everything else passes through with
its body walked. The one edit is the citation; `resolveInline_id` below is
the machine-checked form of that sentence. -/
-- conserves: none — resolution rewrites citation marks into the style's
-- rendering; `resolveInline_id` states the walk's identity off citations.
private def resolveInline (p : CitePunct) (find : Resolver)
    (out : Array Ir.Inline) : Ir.Inline → Array Ir.Inline
  | .cite form keys =>
    let rendered := renderCite p form (keys.map find)
    out ++ rendered
  | .styled st body => out.push (.styled st (resolveInlines p find #[] body.toList))
  | .colored c nm body => out.push (.colored c nm (resolveInlines p find #[] body.toList))
  | .located nm body => out.push (.located nm (resolveInlines p find #[] body.toList))
  | .role nm body => out.push (.role nm (resolveInlines p find #[] body.toList))
  | .link u body => out.push (.link u (resolveInlines p find #[] body.toList))
  | .decorated kind body =>
    out.push (.decorated kind (resolveInlines p find #[] body.toList))
  | .onSteps spec body => out.push (.onSteps spec (resolveInlines p find #[] body.toList))
  | .altSteps spec active otherwise =>
    out.push (.altSteps spec (resolveInlines p find #[] active.toList)
      (resolveInlines p find #[] otherwise.toList))
  -- a citation inside a note resolves like any other
  | .footnote n body => out.push (.footnote n (resolveInlines p find #[] body.toList))
  | .text s => out.push (.text s)
  | .math d src => out.push (.math d src)
  | .formula d src body => out.push (.formula d src body)
  | .image src size alt => out.push (.image src size alt)
  | .icon c label => out.push (.icon c label)
  | .label k => out.push (.label k)
  | .ref k form text anchor => out.push (.ref k form text anchor)
  | .fill => out.push .fill
  | .hspace g keep => out.push (.hspace g keep)
  | .rule w h r => out.push (.rule w h r)
  | .strut h => out.push (.strut h)
  | .italicCorr m => out.push (.italicCorr m)
  | .pageNumber => out.push .pageNumber
  | .pageCount => out.push .pageCount
  | .linebreak e => out.push (.linebreak e)

private def resolveInlines (p : CitePunct) (find : Resolver)
    (out : Array Ir.Inline) : List Ir.Inline → Array Ir.Inline
  | [] => out
  | x :: rest => resolveInlines p find (resolveInline p find out x) rest

end

private def resolveArr (p : CitePunct) (find : Resolver)
    (xs : Array Ir.Inline) : Array Ir.Inline :=
  resolveInlines p find #[] xs.toList


private theorem resolveInlines_acc (p : CitePunct) (find : Resolver)
    (out : Array Ir.Inline) (xs : List Ir.Inline) :
    resolveInlines p find out xs = out ++ resolveInlines p find #[] xs := by
  induction xs generalizing out with
  | nil => simp [resolveInlines]
  | cons x rest ih =>
    rw [resolveInlines, resolveInlines, ih (resolveInline p find out x),
      ih (resolveInline p find #[] x), resolveInline_acc, ← Array.append_assoc]
where
  resolveInline_acc (p : CitePunct) (find : Resolver)
      (out : Array Ir.Inline) (x : Ir.Inline) :
      resolveInline p find out x = out ++ resolveInline p find #[] x := by
    match x with
    | .cite _ _ => simp [resolveInline]
    | .styled _ body | .colored _ _ body | .located _ body | .role _ body | .link _ body
    | .decorated kind body | .onSteps _ body | .footnote _ body => simp [resolveInline]
    | .altSteps _ _ _ => simp [resolveInline]
    | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _
    | .label _ | .ref _ _ _ _
    | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _ | .pageNumber | .pageCount | .linebreak _ =>
      simp [resolveInline]

mutual

/-- Style independence, the walk half: resolution is the identity on
content carrying no citation — whatever the style and whatever the
bibliography, only citations and the reference list change. The
citation-side analogue of `artifact_flag_free`: two styles can differ
only where a `.cite` stood or a `\bibliography` marker fills. -/
private theorem resolveInline_id (p : CitePunct) (find : Resolver)
    (out : Array Ir.Inline) (x : Ir.Inline) (h : citeFreeOne x = true) :
    resolveInline p find out x = out.push x := by
  match x with
  | .styled st body =>
    rw [citeFreeOne] at h
    rw [resolveInline, resolveInlines_id p find body.toList h]
  | .colored c nm body =>
    rw [citeFreeOne] at h
    rw [resolveInline, resolveInlines_id p find body.toList h]
  | .located nm body =>
    rw [citeFreeOne] at h
    rw [resolveInline, resolveInlines_id p find body.toList h]
  | .role nm body =>
    rw [citeFreeOne] at h
    rw [resolveInline, resolveInlines_id p find body.toList h]
  | .link u body =>
    rw [citeFreeOne] at h
    rw [resolveInline, resolveInlines_id p find body.toList h]
  | .decorated kind body =>
    rw [citeFreeOne] at h
    rw [resolveInline, resolveInlines_id p find body.toList h]
  | .onSteps spec body =>
    rw [citeFreeOne] at h
    rw [resolveInline, resolveInlines_id p find body.toList h]
  | .altSteps spec active otherwise =>
    rw [citeFreeOne, Bool.and_eq_true] at h
    rw [resolveInline, resolveInlines_id p find active.toList h.1,
      resolveInlines_id p find otherwise.toList h.2]
  | .footnote n body =>
    rw [citeFreeOne] at h
    rw [resolveInline, resolveInlines_id p find body.toList h]
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _
  | .label _ | .ref _ _ _ _
  | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _ | .pageNumber | .pageCount | .linebreak _ =>
    rw [resolveInline]

private theorem resolveInlines_id (p : CitePunct) (find : Resolver)
    (xs : List Ir.Inline) (h : citeFreeList xs = true) :
    resolveInlines p find #[] xs = xs.toArray := by
  match xs with
  | [] => rw [resolveInlines]
  | x :: rest =>
    rw [citeFreeList, Bool.and_eq_true] at h
    rw [resolveInlines, resolveInline_id p find #[] x h.1,
      resolveInlines_acc, resolveInlines_id p find rest h.2]
    simp

end

/-- A paragraph TeX never begins: nothing in it but `\nocite`s and the spaces
between them. `\nocite` sets no ink and leaves vertical mode alone, and a
space in vertical mode is dropped, so the page is the page of the document
without it (lualatex: the same step between the paragraphs around it). -/
private def nociteOnly (content : Array Ir.Inline) : Bool :=
  content.any (fun x => match x with | .cite f _ => f.cmd == .nocite | _ => false) &&
    content.all fun x => match x with
      | .cite f _ => f.cmd == .nocite
      | .text s => s.all Char.isWhitespace
      | _ => false

mutual

/-- The block half of the rewrite: citations resolve wherever inline
content stands, each `\bibliography` marker takes the items the style
built — their content resolved as the body's is, which leaves an entry the
list resolved already as it stands (`resolveInlines_id`) — and a paragraph
of `\nocite`s alone is dropped (`nociteOnly`). -/
-- conserves: none — resolution rewrites citation marks and fills the
-- reference list; `resolveInline_id` carries the off-citation identity.
private def resolveBlock (p : CitePunct) (find : Resolver)
    (items : Array Ir.BibItem) (out : Array Ir.Block) (b : Ir.Block) :
    Array Ir.Block :=
  match b with
  | .bibliography src declared _ =>
    out.push (.bibliography src declared
      (items.map fun it => { it with content := resolveArr p find it.content }))
  | .para content =>
    if nociteOnly content then out else out.push (.para (resolveArr p find content))
  | .equation n content =>
    out.push (.equation (resolveArr p find n) (resolveArr p find content))
  | .section l st num title => out.push (.section l st num (resolveArr p find title))
  | .abstract body => out.push (.abstract (resolveBlocks p find items #[] body.toList))
  | .list ordered its => out.push (.list ordered (resolveItems p find items #[] its.toList))
  | .center body => out.push (.center (resolveBlocks p find items #[] body.toList))
  | .ragged s body => out.push (.ragged s (resolveBlocks p find items #[] body.toList))
  | .quote body => out.push (.quote (resolveBlocks p find items #[] body.toList))
  | .titled kind title body =>
    out.push (.titled kind (resolveArr p find title)
      (resolveBlocks p find items #[] body.toList))
  | .disclosure summary expanded body =>
    out.push (.disclosure (resolveArr p find summary) expanded
      (resolveBlocks p find items #[] body.toList))
  | .role nm body => out.push (.role nm (resolveBlocks p find items #[] body.toList))
  | .link target body => out.push (.link target (resolveBlocks p find items #[] body.toList))
  | .spaced g body => out.push (.spaced g (resolveBlocks p find items #[] body.toList))
  | .columns cols => out.push (.columns (resolveCols p find items #[] cols.toList))
  | .onSteps spec body =>
    out.push (.onSteps spec (resolveBlocks p find items #[] body.toList))
  | .altSteps spec active otherwise =>
    out.push (.altSteps spec (resolveBlocks p find items #[] active.toList)
      (resolveBlocks p find items #[] otherwise.toList))
  | .only t body => out.push (.only t (resolveBlocks p find items #[] body.toList))
  | .nav spec body => out.push (.nav spec (resolveBlocks p find items #[] body.toList))
  | .note body => out.push (.note (resolveBlocks p find items #[] body.toList))
  | .frame title standout va br body =>
    out.push (.frame (resolveArr p find title) standout va br
      (resolveBlocks p find items #[] body.toList))
  | .framefoot content => out.push (.framefoot (resolveArr p find content))
  | .float k n ca body caption =>
    out.push (.float k n ca (resolveBlocks p find items #[] body.toList)
      (resolveArr p find caption))
  | .table cols pl pr rows rules spans =>
    out.push (.table cols pl pr
      (rows.map fun row => row.map (resolveArr p find)) rules spans)
  -- A citation resolves inside a line and its comment, as in a cell.
  | .algorithm n sm lines =>
    out.push (.algorithm n sm (lines.map fun l =>
      { l with
        content := resolveArr p find l.content
        comment := l.comment.map (resolveArr p find) }))
  | .logo content => out.push (.logo (resolveArr p find content))
  | .verbatim c s sp => out.push (.verbatim c s sp)
  | .setPalette p => out.push (.setPalette p)
  | .setTokens tk => out.push (.setTokens tk)
  | .pagebreak => out.push .pagebreak
  | .rule c nm th => out.push (.rule c nm th)
  | .picture pic => out.push (.picture pic)
termination_by structural b

private def resolveBlocks (p : CitePunct) (find : Resolver)
    (items : Array Ir.BibItem) (out : Array Ir.Block) (bs : List Ir.Block) :
    Array Ir.Block :=
  match bs with
  | [] => out
  | b :: rest => resolveBlocks p find items (resolveBlock p find items out b) rest
termination_by structural bs

private def resolveItems (p : CitePunct) (find : Resolver)
    (items : Array Ir.BibItem) (out : Array (Array Ir.Block))
    (its : List (Array Ir.Block)) : Array (Array Ir.Block) :=
  match its with
  | [] => out
  | item :: rest =>
    resolveItems p find items
      (out.push (resolveBlocks p find items #[] item.toList)) rest
termination_by structural its

private def resolveCols (p : CitePunct) (find : Resolver)
    (items : Array Ir.BibItem) (out : Array (Ir.BoxWidth × Array Ir.Block))
    (cs : List (Ir.BoxWidth × Array Ir.Block)) :
    Array (Ir.BoxWidth × Array Ir.Block) :=
  match cs with
  | [] => out
  | (w, body) :: rest =>
    resolveCols p find items
      (out.push (w, resolveBlocks p find items #[] body.toList)) rest
termination_by structural cs

end

/-- The citation rewrite over the whole document: the body through
`resolveBlocks`, every furniture region through `resolveArr` — `Ir.mapDoc`
hands both the regions the pending census (`Ir.foldDoc`) reads, so a
`\cite` in a running head resolves as one in the body does. -/
public def resolveDoc (p : CitePunct) (find : Resolver) (items : Array Ir.BibItem)
    (doc : Ir.Doc) : Ir.Doc :=
  Ir.mapDoc (resolveArr p find)
    (fun bs => resolveBlocks p find items #[] bs.toList) doc

/-- Bibliography resolution emits one block per input block except a
paragraph consisting only of nonprinting citations. Source metadata follows
this decision, independently of the citation style or external entries. -/
public def keepsBlock : Ir.Block → Bool
  | .para content => !nociteOnly content
  | .bibliography .. | .equation .. | .section .. | .abstract .. | .list ..
  | .center .. | .ragged .. | .quote .. | .titled .. | .disclosure .. | .role .. | .link ..
  | .spaced .. | .columns .. | .onSteps .. | .altSteps .. | .only .. | .nav ..
  | .note .. | .frame .. | .framefoot .. | .float .. | .table .. | .algorithm ..
  | .logo .. | .verbatim .. | .setPalette .. | .setTokens .. | .pagebreak
  | .rule .. | .picture .. => true

private theorem resolveBlock_size_exact (p : CitePunct) (find : Resolver)
    (items : Array Ir.BibItem) (out : Array Ir.Block) (b : Ir.Block) :
    (resolveBlock p find items out b).size =
      out.size + if keepsBlock b then 1 else 0 := by
  cases b <;> simp [resolveBlock, keepsBlock]
  split <;> simp_all

private theorem resolveBlocks_size_exact (p : CitePunct) (find : Resolver)
    (items : Array Ir.BibItem) (bs : List Ir.Block) (out : Array Ir.Block) :
    (resolveBlocks p find items out bs).size =
      out.size + (bs.filter keepsBlock).length := by
  induction bs generalizing out with
  | nil => simp [resolveBlocks]
  | cons b bs ih =>
    rw [resolveBlocks, ih, resolveBlock_size_exact]
    cases hk : keepsBlock b <;> simp [hk] <;> omega

/-- Preserve metadata attached to surviving top-level blocks. Indices refer
to the input document; values, including expansion origins, pass unchanged.
Invalid indices and the removed nonprinting paragraphs have no output site. -/
public def remapSources {α : Type} (doc : Ir.Doc) (sites : Array (Nat × α)) :
    Array (Nat × α) :=
  sites.filterMap fun (i, source) =>
    if doc.body[i]?.any keepsBlock then
      some (((doc.body.toList.take i).filter keepsBlock).length, source)
    else none

/-- Each surviving source's new offset is the size of its prefix after the
actual bibliography rewrite, for every style, resolver and reference list. -/
public theorem remapSources_projects {α : Type} (doc : Ir.Doc)
    (sites : Array (Nat × α)) (i : Nat) (source : α) (b : Ir.Block)
    (hs : (i, source) ∈ sites) (hb : doc.body[i]? = some b)
    (hk : keepsBlock b = true)
    (p : CitePunct) (find : Resolver) (items : Array Ir.BibItem) :
    ((resolveDoc p find items
        { doc with body := (doc.body.toList.take i).toArray }).body.size, source) ∈
      remapSources doc sites := by
  have hsize := resolveBlocks_size_exact p find items (doc.body.toList.take i) #[]
  simp only [Array.size_empty, Nat.zero_add] at hsize
  apply Array.mem_filterMap.mpr
  refine ⟨(i, source), hs, ?_⟩
  simp [hb, hk, resolveDoc, Ir.mapDoc, hsize]

/-- natbib's author-year label in a `\bibitem`'s optional argument
(natbib.sty `\NAT@parse`: `Jones et al.(1990)Jones, Baker, and Williams`):
the names before the parentheses and the year inside them. -/
private def natbibLabel? (label : String) : Option (String × String) :=
  match label.splitOn "(" with
  | names :: rest =>
    match ("(".intercalate rest).splitOn ")" with
    | year :: _ :: _ =>
      let names := names.trimAscii.toString
      let year := year.trimAscii.toString
      if names.isEmpty || year.isEmpty then none else some (names, year)
    | _ => none
  | [] => none

/-- The entry a `thebibliography` item cites as in author-year mode: its
label's names as the author (natbib's `et al.` as BibTeX's `and others`)
and its year. -/
private def ownEntry (key : String) (label : Option (String × String)) : Entry :=
  let fields := match label with
    | some (names, year) =>
      let names := if names.endsWith " et al." then (names.dropEnd 7).toString ++ " and others"
        else names
      #[("author", names), ("year", year)]
    | none => #[]
  { (default : Entry) with key, fields }

/-- A document's own reference list, `thebibliography`, resolved: its
entries in source order (the list is printed as written, never sorted).
natbib reads it in numbers mode unless every entry carries an author-year
label (natbib.sty, reading each `\bibitem`); in numbers mode an entry's mark
is its label as written, or the list counter, which only an entry without a
label steps (latex.ltx `\@bibitem` against `\@lbibitem`). An author-year
entry cites as its label's names and year. -/
private def ownList (p : CitePunct) (own : Array Ir.BibItem) :
    CitePunct × Array Resolved × Array Ir.BibItem := Id.run do
  let ay := own.map fun it => it.marker.bind natbibLabel?
  let p := if ay.all (·.isSome) then p else { p with numbers := true }
  let mut resolved : Array Resolved := #[]
  let mut items : Array Ir.BibItem := #[]
  let mut n := 0
  for (it, i) in own.zipIdx do
    if it.marker.isNone then n := n + 1
    let label := if p.numbers then it.marker else none
    resolved := resolved.push
      { key := it.key, position := n, entry := ownEntry it.key (ay[i]?).join, label }
    -- a label written by hand sets flush left, as latex.ltx's `\@lbibitem`
    -- sets it (`\item[\@biblabel{#1}\hfill]`); a number right-aligned
    items := items.push
      { it with marker := if p.numbers then some (label.getD (toString n)) else none
                labelFlush := p.numbers && it.marker.isSome }
  return (p, resolved, items)

/-- A field's `\cite` read as biblatex's author-year styles read it: the
bare citation (`Doe 2024`), natbib's `\citealp`. The compatibility pass
renames the body's spelling where it reads the load (`Compat`'s
`\cite` row); a field's text is read without that state, so its
citations are renamed here, on the node. A leaf of `Ir.mapInlines`. -/
private def bareCites (xs : Array Ir.Inline) : Array Ir.Inline :=
  Ir.mapInlines (fun x => match x with
    | .cite f keys => if f.cmd == .auto then .cite { f with cmd := .alp } keys else .cite f keys
    | x => x) xs

/-- The field citations a document makes (`Ir.CiteField`): each key, the
field, and whether the star asks the full title. A leaf of `Ir.foldDoc`. -/
private def citeFieldUses (doc : Ir.Doc) : Array (String × Ir.CiteField × Bool) :=
  Ir.foldDoc (fun acc x => match x with
    | .cite f keys => match f.cmd with
      | .field w => keys.foldl (fun acc k => acc.push (k, w, f.full)) acc
      | _ => acc
    | _ => acc) #[] doc

/-- What a field citation prints under a BibTeX style, which defines none:
the title as written, starred or not, the URL a link, the year, and the
entry as the style sets it, its closing period dropped. -/
private def bibtexCiteField (cv : FieldText) (r : Resolved) (w : Ir.CiteField)
    (rendered : Array (Ir.BibItem × FieldReport)) : Array Ir.Inline × Array (String × Ir.PicSrc) :=
  match w with
  | .title => match r.entry.field? "title" with
    | some t => let read := cv t; (read.1, read.2.pictures)
    | none => (#[], #[])
  | .url => match r.entry.field? "url" with
    | some u => (#[.link (text u) #[.styled .mono #[.text (text u)]]], #[])
    | none => (#[], #[])
  | .date => (#[.text (citeYear r.entry)], #[])
  | .full => match rendered.find? (·.1.key == r.key) with
    | some (it, rep) =>
      (match it.content.back? with
        | some (.text t) =>
          if t.endsWith "." then it.content.pop.push (.text (t.dropEnd 1).toString) else it.content
        | _ => it.content, rep.pictures)
    | none => (#[], #[])

/-- One run of the reference list over a sequence of citations: the
database the processor reads for them, the entries the style resolves, the
items it sets with what reading their fields reported, and the fields each
set entry's driver read. -/
private structure ListRun where
  cited : Array String
  db : Database
  resolved : Array Resolved
  rendered : Array (Ir.BibItem × FieldReport)
  readSets : Array (List String)

/-- The keys the set entries' own fields cite (a `\cite` in a `note`), in
the order the list sets them, each once, with the first entry citing it: a
leaf of `Ir.foldInlines` over each item's content. -/
private def fieldCites (rendered : Array (Ir.BibItem × FieldReport)) : Array (String × String) :=
  (rendered.foldl (init := ((#[] : Array (String × String)), (∅ : Std.HashSet String)))
    fun acc (it, _) => Ir.foldInlines (fun (out, seen) x => match x with
      | .cite _ keys => keys.foldl (init := (out, seen)) fun (out, seen) k =>
          if seen.contains k then (out, seen) else (out.push (k, it.key), seen.insert k)
      | _ => (out, seen)) acc it.content).1

/-- The keys of `uncited` that `named` does not hold, when it holds one at
least: what a round of `settleFieldCites` leaves, shorter by what it spent. -/
private def spend (uncited : List String) (named : Std.HashSet String) :
    Option { rest : List String // rest.length < uncited.length } :=
  if h : uncited.filter (named.contains ·) = [] then none
  else some ⟨uncited.filter (!named.contains ·), by
    rw [List.length_filter_lt_length_iff_exists]
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ h
    exact ⟨x, (List.mem_filter.mp hx).1, by simp [(List.mem_filter.mp hx).2]⟩⟩

/-- The keys a list run's set entries cite in their fields, each read
through `canon`, that `seen` does not hold, each once in the order the list
sets them. -/
private def freshCites (canon : String → String) (r : ListRun) (seen : Std.HashSet String) :
    Array String :=
  ((fieldCites r.rendered).foldl (init := ((#[] : Array String), seen))
    fun (out, seen) (k, _) =>
      let k := canon k
      if seen.contains k then (out, seen) else (out.push k, seen.insert k)).1

/-- Where the field citations of `frontier`'s entries lead, round by round,
each round setting only the entries the round before added, so a chain of
field citations costs its length rather than its length times the list's:
`found` with every key reached appended, in the order reached, and
`foundSet` its keys. A list's composition can change what an entry prints
— a parent `minCrossrefs` lists, a letter — so this is a search, not the
answer: `settleFieldCites` holds what it found to the whole list. -/
private def discoverFieldCites (run : Array String → ListRun) (canon : String → String)
    (uncited : List String) (frontier found : Array String) (foundSet : Std.HashSet String) :
    Array String × Std.HashSet String :=
  let fresh := freshCites canon (run frontier) foundSet
  let foundSet := fresh.foldl (·.insert ·) foundSet
  match spend uncited foundSet with
  | none => (found ++ fresh, foundSet)
  | some ⟨rest, _⟩ => discoverFieldCites run canon rest fresh (found ++ fresh) foundSet
termination_by uncited.length

/-- **A field's citation completes the list.** LaTeX sets a `.bbl`'s
`\cite` where the list stands, which writes the citation to the `.aux`, so
the next BibTeX or biber run lists its entry after every citation the body
made, and the run after that resolves it: the rerun cycle `latexmk` repeats
until nothing changes. Here the cycle is a function — run the list for the
citations (`run`), append the keys the set entries' fields cite that the
citations lack (`freshCites`, each read through `canon`, an entry's `ids`),
and run again while that cites an entry no citation named before; after a
round that adds some, the entries it added lead the search for the rest
(`discoverFieldCites`) before the whole list runs again. `uncited` holds
the database keys no citation names yet; a round that names none of them
is the fixed point, and a round that continues spends one of them at least,
which is the measure — the rounds are at most the entries. -/
private def settleFieldCites (run : Array String → ListRun) (canon : String → String)
    (uncited : List String) (cited : Array String) : ListRun :=
  let r := run cited
  let citedSet : Std.HashSet String := cited.foldl (·.insert ·) {}
  let fresh := freshCites canon r citedSet
  let freshSet : Std.HashSet String := fresh.foldl (·.insert ·) {}
  match spend uncited freshSet with
  | none => { r with cited := cited ++ fresh }
  | some ⟨rest, hrest⟩ =>
    let (more, moreSet) :=
      discoverFieldCites run canon rest fresh (cited ++ fresh) (fresh.foldl (·.insert ·) citedSet)
    let left := rest.filter (!moreSet.contains ·)
    have : left.length < uncited.length := Nat.lt_of_le_of_lt (List.length_filter_le _ _) hrest
    settleFieldCites run canon left more
termination_by uncited.length

/-- Resolve the document's citations and reference lists against its
`.bib` sources — the pure half of the `\bibliography` effect. `sources`
maps each requested name (`Ir.bibRefs`) to the file text the driver read;
a name the driver could not read is simply absent, its diagnostic already
fired. Emits W0352 for each malformed `.bib` entry (skipped, the rest
kept), W0353 when the declared style is unknown (the fallback record
formats the list and says so), and W0351 for each cited key no entry
answers (its citation shows `?`, LaTeX's own rendering). It runs on every
document: with no `\bibliography` marker there are no sources and every
key resolves to `?` — the elaborator has already named each such citation
at its site (W0351, the no-bibliography cause), so none is named twice
here — and no `.cite` node survives in any region (`apply_no_cite`), which
is what lets the backends' `.cite` arms be dead code. `analyse` is the
reading half — sources, style, the resolver and the reference list, with
the diagnostics — and `apply` is that half followed by the one rewrite. -/
private def analyse (sources : Array (String × String)) (doc : Ir.Doc) (rd : FieldReading) :
    CitePunct × Resolver × Array Ir.BibItem × Array Diag × Array (String × Ir.PicSrc) × Nat :=
    Id.run do
  let requested := Ir.bibRefs doc
  let declared := (Ir.bibStyleName doc).map fun name => (name, Style.named name)
  -- The month macros are the style's (abbrv.bst spells `mar` `Mar.`), in
  -- the document's language where the style is English.
  let months := if (declared.bind (·.2)).any (·.shortMonths) && doc.info.locale.tag == "en"
    then shortMonthNames else doc.info.locale.months
  let mut diags : Array Diag := #[]
  let mut entries : Array Entry := #[]
  let mut origin : Std.HashMap String String := {}
  let mut seen : Std.HashSet String := {}
  let mut preambles : Array String := #[]
  -- One `@string` store for the list's files, read in turn: a strings file
  -- named before the files that use it defines their macros, as BibTeX and
  -- biber read a list's files into one store.
  let mut store := monthMacros months
  let mut undefined : Std.HashMap String (Array String) := {}
  for src in requested do
    match sources.find? (·.1 == src) with
    | none => pure ()  -- the driver's missing-file diagnostic already fired
    | some (_, text) =>
      let parsed := parse text store (biber := (CitePunct.ofDoc doc.natbib none true).biblatex)
      store := parsed.macros
      for (k, n) in parsed.undefined do
        unless (undefined.getD k #[]).contains n do
          undefined := undefined.insert k ((undefined.getD k #[]).push n)
      preambles := preambles ++ parsed.preambles
      for (pos, msg) in parsed.errors do
        diags := diags.push (Diag.of .W0352 s!"malformed .bib entry: {msg}; \
          the entry is skipped and the rest of '{sourceName src}' is kept"
          (some ⟨sourceName src, pos⟩))
      for e in parsed.entries do
        unless seen.contains e.key do
          entries := entries.push e
          seen := seen.insert e.key
          origin := origin.insert e.key src
  let declared ← do
    match declared with
    | none => pure none
    | some (_, some s) => pure (some s)
    | some (name, none) =>
        let cites := if doc.natbib.isSome then ", and its citations as author-year ones" else ""
        diags := diags.push (Diag.of .W0353 s!"bibliography style '{name}' is not \
          one the engine knows; the reference list is set as 'unsrtnat'{cites}"
          (help := "styles known: unsrtnat, unsrt, plainnat, plain, abbrvnat, abbrv, alpha"))
        pure (some Style.unsrtnat)
  let p := CitePunct.ofDoc doc.natbib ((Ir.bibStyleName doc).bind (natbibRows.lookup ·))
    (declared.all (·.labels))
  let p := { p with ink := (doc.styles.find? "cite").bind (·.color) }
  -- biblatex sorts its list by its own schemes: the load's `sorting`, nty
  -- for the numeric styles and nyt for the author-year ones by default, and
  -- `none` citation order.
  let bbl := (BblOptions.ofDecls doc.natbib).map ({ · with mainLang := doc.info.locale.tag })
  let style := declared.getD Style.unsrtnat
  let style := match bbl with
    | some o => { style with sort := match bblSorting doc.natbib with
        | "none" => .citation
        | t => .bbl (if bblTemplates.contains t then t
            else if o.style == .authoryear then "nyt" else "nty") o }
    | none => if p.biblatex && style.sort != .citation then
        { style with sort := .bbl (if p.numbers then "nty" else "nyt") {} } else style
  let p := { p with useprefix := bbl.any (·.useprefix) }
  let proc : Processor := if p.biblatex then .biber else .bibtex
  -- An entry's `ids` are other keys it is cited by (biblatex manual §2.2.3,
  -- "ids"): a citation of one is a citation of the entry. BibTeX reads no
  -- `ids`; the alias resolves under its styles too, where it would show as
  -- '?' unanswered.
  let keys : Std.HashSet String := entries.foldl (·.insert ·.key) {}
  let aliases : Std.HashMap String String := entries.foldl (init := {}) fun m e =>
    (e.refsBy "ids").foldl (init := m) fun m a =>
      if keys.contains a || m.contains a then m else m.insert a e.key
  let canon (k : String) : String := aliases.getD k k
  let cited := expandStar entries ((citedKeys doc).map canon)
  let shown := (citedKeys doc (·.cmd != .nocite)).foldl (·.insert ·) (∅ : Std.HashSet String)
  -- biblatex sets an `@set` entry as one entry of its members (standard.bbx's
  -- `set` driver, `\entryset`); the engine lists each member as an entry
  -- of its own, cites the set as its first member, and names the
  -- difference.
  let sets : Std.HashMap String (Array String) := if proc != .biber then {} else
    entries.foldl (init := {}) fun m e =>
      match (e.field? "entryset").filter (fun _ => e.kind == "set") with
      | some v => m.insert e.key (((text v).splitOn ",").map (·.trimAscii.toString)
          |>.filter (!·.isEmpty)).toArray
      | none => m
  let listedOf (cited : Array String) : Array String := if sets.isEmpty then cited else
    (cited.foldl (init := ((#[] : Array String), (∅ : Std.HashSet String))) fun (acc, seen) k =>
      (sets.getD k #[k]).foldl (init := (acc, seen)) fun (acc, seen) m =>
        if seen.contains m then (acc, seen) else (acc.push m, seen.insert m)).1
  -- The list is typeset under its `@preamble`s' definitions and sorted
  -- without them, as the `.bbl` carries them to the one and not the other.
  let macros := preambleMacros preambles
  let typeset := if macros.isEmpty then entries else
    entries.map fun e => { e with fields := e.fields.map fun (f, v) => (f, expandMacros macros v) }
  -- Each entry's fields are read where the entry stands in its `.bib`.
  let positions : Std.HashMap String Pos := entries.foldl (fun m e => m.insert e.key e.pos) {}
  let spanOf (k : String) : Span :=
    ⟨sourceName ((origin.get? k).getD ""), (positions.get? k).getD {}⟩
  let cv (k : String) : FieldText := rd (spanOf k)
  let own := Ir.ownBibItemsBlocks doc.body
  -- The database's own work once, for every list a round reads off it.
  let prepared := Database.prepare proc months typeset
  let rawPrepared := if macros.isEmpty then prepared else Database.prepare proc months entries
  -- The TeX a label or a citation's names are spelt in, set as the
  -- entry's fields are, the list's `@preamble` definitions expanded, where
  -- it holds a control word and the reading reports no loss (a note
  -- records a faithful translation) and draws no picture and sets no note,
  -- which a label's text cannot carry; elsewhere `text`'s reading stands,
  -- which keeps an unknown command's name in sight.
  let inkOf (k tex : String) : Option (Array Ir.Inline) :=
    if !tex.contains '\\' then none else
      let read := cv k (if macros.isEmpty then tex else expandMacros macros tex)
      if read.2.diags.all (·.severity == .note) && read.2.pictures.isEmpty &&
          !Ir.hasListNote read.1 then some read.1
      else none
  let labelInk (r : Resolved) : Resolved :=
    match r.labelTeX.bind (inkOf r.key) with
    | some inl => { r with label := some (Ir.plainText inl) }
    | none => r
  let runFor (cited : Array String) : ListRun :=
    let listed := listedOf cited
    let db := prepared.list listed
    let rawDb := if macros.isEmpty then db else rawPrepared.list listed
    let findEntry (k : String) : Option Entry := db.entries.get? k
    let findRaw (k : String) : Option Entry :=
      if macros.isEmpty then none else rawDb.entries.get? k
    let resolved := (resolveEntries style db.list findEntry p.biblatex
      (bbl.map (·, p.numbers)) months findRaw).map labelInk
    match bbl with
    | some o =>
      let out := bblItems o cv p resolved months
      { cited, db, resolved, rendered := out.map (·.1), readSets := out.map (·.2) }
    | none =>
      { cited, db, resolved, rendered := bibItemsWith cv p style resolved
        readSets := resolved.map fun r => readsOf (style.steps r.entry) }
  let citedSet : Std.HashSet String := cited.foldl (·.insert ·) {}
  let uncited := (entries.filter fun e => !citedSet.contains e.key).toList.map (·.key)
  let run := if own.isEmpty then settleFieldCites runFor canon uncited cited else
    { cited, db := prepared.list (listedOf cited), resolved := #[]
      rendered := #[], readSets := #[] }
  let cited := run.cited
  let db := run.db
  let findEntry (k : String) : Option Entry := db.entries.get? k
  let (p, resolved, rendered, readSets) :=
    if own.isEmpty then (p, run.resolved, run.rendered, run.readSets)
    else
      let (p, resolved, items) := ownList p own
      (p, resolved, items.map (·, ({} : FieldReport)), #[])
  -- biblatex cites an entry no name list labels by its label title, read
  -- as the entry's fields are (`bblCiteLabel`)
  let labelled (r : Resolved) : Resolved :=
    let r := match bbl with
      | some o => if r.citeNames.isSome then r else
        let (l, pics) := bblCiteLabel o (cv r.key) months r.entry
        if l.isEmpty then r
        else { r with citeLabel := some l, inkPictures := r.inkPictures ++ pics }
      | none => r
    -- the names and the shorthand a citation prints, set as the fields are
    let namesTeX := if p.biblatex then r.citeNames else some (labelSource r.entry false p.useprefix)
    { r with namesInk := namesTeX.bind (inkOf r.key), shortInk := r.shorthand.bind (inkOf r.key) }
  -- read only for the entries a citation prints: the body's, `\nocite`
  -- aside, a field's, and a cited @set's first member
  let printed : Std.HashSet String :=
    let ks := (fieldCites rendered).foldl (fun s (k, _) => s.insert (canon k))
      (shown.fold (fun s k => s.insert (canon k)) {})
    sets.fold (init := ks) fun s k ms =>
      if ks.contains k then (ms[0]?.map (s.insert ·)).getD s else s
  let byCite : Std.HashMap String Resolved :=
    resolved.foldl (fun m r => m.insert r.key (if printed.contains r.key then labelled r else r)) {}
  let byCite := sets.fold (init := byCite) fun m k ms =>
    match ms[0]?.bind byCite.get? with
    | some r => m.insert k r
    | none => m
  -- A field citation prints its entry's field (`Ir.CiteField`): each one the
  -- document makes, read once per entry and field, as the style prints it.
  let fieldUses := citeFieldUses doc
  let labelFind : Resolver := fun k => byCite.get? (canon k)
  let byCite := fieldUses.foldl (init := byCite) fun m (k, w, full) =>
    match m.get? (canon k) with
    | none => m
    | some r =>
      if r.fieldInk.any (·.1 == (w, full)) then m else
      let (ink, pics) := match bbl with
        | some o => bblCiteField o (cv r.key) months r.entry r.extra w full
        | none => bibtexCiteField (cv r.key) r w rendered
      -- a citation inside the field resolves as a label citation
      let ink := resolveArr p labelFind ink
      m.insert (canon k) { r with fieldInk := r.fieldInk.push ((w, full), ink)
                                  inkPictures := r.inkPictures ++ pics }
  let find : Resolver := fun k => byCite.get? (canon k)
  -- An entry's own citations — a cross-reference's parent, a `\cite` in a
  -- field or a `\bibitem` — resolve as the body's do; a field's bare
  -- `\cite` under biblatex's author-year citations is the bare citation
  -- the body's is (`bareCites`).
  let bare := bbl.any (·.cite == .authoryear)
  let items := rendered.map fun (it, _) =>
    { it with content := resolveArr p find (if bare then bareCites it.content else it.content) }
  -- An entry's declared language (`langid`, BibTeX's `hyphenation`) tags its
  -- text, so its words hyphenate by its patterns and a reader is told the
  -- language: biblatex's `autolang=hyphen`, a departure from its default
  -- `none` and from BibTeX, which read no language.
  let items := items.map fun it =>
    match (db.own.get? it.key).bind fun e =>
        (e.field? "langid").orElse fun _ => e.field? "hyphenation" with
    | some l =>
      let tag := Locale.babelTagOf (text l).trimAscii.toString
      if tag.isEmpty || tag == doc.info.locale.tag then it
      else { it with content := #[.styled (.lang tag) it.content] }
    | none => it
  -- The notes the list's fields set number where the list stands, after the
  -- notes before it (`Ir.Doc.listNotes`), in the order the list sets them;
  -- a citation that prints a field (`\fullcite`, a label title) numbers its
  -- notes after the list's, once per entry and field.
  let base := (doc.listNotes[0]?.map (·.1)).getD 0
  let (afterList, items) := Ir.numberNotesItems base items
  let inkKeys := ((byCite.toArray.filter fun (_, r) =>
      r.citeLabel.any Ir.hasListNote || r.fieldInk.any (Ir.hasListNote ·.2)).map (·.1)).qsort (· < ·)
  let (afterInk, byCite) := inkKeys.foldl (init := (afterList, byCite)) fun (k, m) key =>
    match m.get? key with
    | none => (k, m)
    | some r =>
      let (k, label) := match r.citeLabel with
        | some l => let x := Ir.numberNotesList k #[] l.toList; (x.1, some x.2)
        | none => (k, none)
      let (k, inks) := r.fieldInk.foldl (init := (k, #[])) fun (k, out) (w, ink) =>
        let x := Ir.numberNotesList k #[] ink.toList
        (x.1, out.push (w, x.2))
      (k, m.insert key { r with citeLabel := label, fieldInk := inks })
  let find : Resolver := fun k => byCite.get? (canon k)
  -- What reading an entry's fields reported names that entry's place in
  -- its `.bib`; one report per site, the same loss at many sites counted
  -- by the run's tally as the body's are (`Diag.tallySites`).
  let mut reported : Std.HashSet String := {}
  for (it, ds) in rendered do
    let span : Option Span := (origin.get? it.key).map fun src =>
      ⟨sourceName src, ((findEntry it.key).map (·.pos)).getD {}⟩
    for d in ds.diags do
      let d := { d with span := span.orElse fun _ => d.span }
      -- a refused field is named for the field it stands for in this entry
      let d := if d.kind != .W0429 then d else match findEntry it.key with
        | some e => nameUnread (entries.find? (·.key == it.key)) e d
        | none => d
      let site := s!"{d.code}\u0000{d.message}\u0000{repr d.span}\u0000{d.subject}"
      unless reported.contains site do
        reported := reported.insert site
        diags := diags.push d
  -- A content field the style prints nowhere for an entry that declares
  -- it: named once per field as the `.bib` spells it, with the entries that
  -- keep one (N0029).
  let styleName := match bbl with
    | some o => if o.style == BblStyle.authoryear then "biblatex's authoryear style"
      else "biblatex's numeric style"
    | none => s!"the bibliography style '{(Ir.bibStyleName doc).getD "unsrtnat"}'"
  let written : Std.HashMap String Entry := entries.foldl (fun m e => m.insert e.key e) {}
  -- premise: biblatexFieldCoverageChecks — the drivers read every field standard.bbx's print, against biber line for line
  let listedReads := if bbl.isSome then (bblListed resolved).zip readSets else resolved.zip readSets
  -- each field with the entries that keep one and the types they are: a
  -- style may print a field for one type and not another (plainnat prints
  -- a @misc's howpublished and not a @manual's)
  let mut dropped : Array (String × Array String × Array String) := #[]
  let mut droppedAt : Std.HashSet String := {}
  for (r, reads) in listedReads do
    let mine := (written.get? r.key).getD r.entry
    let kind := ((db.own.get? r.key).map (·.kind)).getD mine.kind
    for (f, v) in mine.fields do
      if contentFields.contains f && !v.trimAscii.toString.isEmpty &&
          !reads.contains (readsAs proc kind f) && !reads.contains f &&
          !droppedAt.contains (f ++ "\u0000" ++ r.key) then
        droppedAt := droppedAt.insert (f ++ "\u0000" ++ r.key)
        let addKind (ts : Array String) : Array String :=
          if ts.contains mine.kind then ts else ts.push mine.kind
        dropped := match dropped.findIdx? (·.1 == f) with
          | some i => dropped.modify i fun (f, ks, ts) => (f, ks.push r.key, addKind ts)
          | none => dropped.push (f, #[r.key], #[mine.kind])
  for (f, ks, ts) in dropped do
    let shown := String.intercalate ", " (ks.toList.take 5) ++ (if ks.size > 5 then ", …" else "")
    let types := " or ".intercalate (ts.toList.map (s!"@{·}"))
    diags := diags.push (Diag.of .N0029 s!"{styleName} prints no '{f}' field in {types} \
      entries; {ks.size} {if ks.size == 1 then "entry keeps" else "entries keep"} one ({shown})"
      (subject := some ("bibfield:" ++ f)))
  -- A reference a listed entry's reading left unresolved: the entry is set
  -- without what it would lend (W0425), where BibTeX and biber warn — or,
  -- for a cycle, where biber stops.
  for r in db.broken do
    let k := r.holder
    let m := r.target
    let fld := r.field
    let xf := r.source
    let atEntry : Option Span := (origin.get? k).map fun src => ⟨sourceName src, (positions.get? k).getD {}⟩
    let near := entries.find? fun e => e.key != m && e.key.toLower == m.toLower
    let takes := s!"the {fld} of '{k}' takes the {xf} of '{m}'"
    let (what, help) : String × String := match r.fault with
      | .missing =>
        (if xf.isEmpty then s!"the {fld} '{m}' that '{k}' names is no entry of the bibliography; \
            '{k}' is set without the fields it would inherit"
          else s!"{takes}, which is no entry of the bibliography; '{k}' is set without it",
         match near with
          | some e => s!"the entry '{e.key}' differs only in case; biber matches keys exactly: \
            write '{if xf.isEmpty then s!"{fld} = \{{e.key}}" else e.key}'"
          | none => s!"add an entry with key '{m}' to the .bib file, or fix the spelling in '{fld}'")
      | .unread =>
        (s!"the {fld} '{m}' that '{k}' names stands before it in the .bib, where BibTeX, which \
            reads the file once in order, has passed it before anything asks for it; '{k}' is set \
            without the fields it would inherit",
         s!"move '{m}' after the entries that cross-reference it, or cite '{m}' as well")
      | .notData =>
        (if xf.isEmpty then s!"the xdata '{m}' that '{k}' names is no @xdata entry, which biber \
            refuses; '{k}' is set without its fields"
          else s!"{takes}, which is no @xdata entry; '{k}' is set without it",
         s!"make '{m}' an @xdata entry, or name the data '{k}' needs in '{fld}'")
      | .cycle path =>
        let chain := " → ".intercalate (path.toList.map (s!"'{·}'"))
        (if xf.isEmpty then s!"the xdata '{m}' that '{k}' names closes a cycle ({chain}), \
            where biber stops; the engine skips it"
          else s!"{takes}, which closes a cycle ({chain}), where biber stops; the engine skips it",
         s!"remove the reference to '{m}' from the {fld} of '{k}'")
      | .noField _ =>
        (s!"{takes}, which '{m}' does not hold; '{k}' is set without it",
         s!"add '{xf}' to '{m}', or write the {fld} of '{k}' out")
      | .noPosition _ n =>
        (s!"the {fld} of '{k}' takes item {n} of the {xf} of '{m}', which has no item {n}; \
          '{k}' is set without it",
         s!"name an item '{m}' holds, or write the {fld} of '{k}' out")
      | .shapes _ =>
        (s!"{takes}, a field of another kind, which biber refuses; '{k}' is set without it",
         s!"take a field of the kind '{fld}' is, or write the {fld} of '{k}' out")
      | .malformed =>
        (s!"the {fld} of '{k}' is '{m}', an xdata reference naming no field to take; \
          '{k}' is set without it",
         s!"write it 'xdata=<key>-<field>', or write the {fld} of '{k}' out")
    diags := diags.push (Diag.of .W0425 what atEntry (help := help)
      (subject := some (if xf.isEmpty then s!"bibref:{m}" else s!"bibref:{m}-{xf}")))
  -- A listed entry's value naming a macro no `@string` defined before it:
  -- the name prints where BibTeX and biber print nothing (W0426).
  for k in db.list do
    for n in undefined.getD k #[] do
      let atEntry : Option Span := (origin.get? k).map fun src => ⟨sourceName src, (positions.get? k).getD {}⟩
      diags := diags.push (Diag.of .W0426 s!"the string '{n}' that '{k}' uses is defined by \
        no @string read before it; its name prints in its place" atEntry
        (help := s!"define it before its first use: '@string\{{n} = \"...\"}', in the .bib \
          file named first")
        (subject := some s!"bibstring:{n}"))
  -- What biblatex's styles print of an entry that the engine does not set:
  -- the entries a `related` field names (standard.bbx's `related` macro).
  if bbl.isSome then
    for r in bblListed resolved do
      let mine := (db.own.get? r.key).getD r.entry
      if let some rel := mine.field? "related" then
        diags := diags.push (Diag.of .W0423 s!"biblatex sets the entries '{text rel}' that \
          '{r.key}' names as related after it; the engine does not set related entries"
          ((origin.get? r.key).map fun src => ⟨sourceName src, mine.pos⟩)
          (subject := some ("bibrelated:" ++ r.key)))
  -- biblatex words its list in babel's main language (`language=autodetect`)
  -- or the one its load names, and under `autolang=other` an entry with a
  -- `langid` in that language; the strings and dates set here are
  -- english.lbx's, so any other language is named, once.
  -- premise: biblatexOracleChecks — the strings and dates set are english.lbx's, line for line
  if let some o := (if requested.isEmpty then none else bbl) then
    let main := (o.language.filter fun l => !["autodetect", "auto"].contains l).orElse
      fun _ => o.babelMain
    let help := "load biblatex with 'language=english' and 'autolang=hyphen' to word the \
      list in English, as biblatex then does"
    let mut worded : Array String := #[]
    if let some m := main then
      if m != "english" then
        worded := worded.push m
        diags := diags.push (Diag.of .W0421 s!"biblatex words this reference list's strings \
          and dates in '{m}'; the engine sets the English ones" (subject := some ("bibstrings:" ++ m))
          (help := help))
    if ["other", "other*", "langname"].contains o.autolang then
      for k in db.list do
        let lang := (db.own.get? k).bind fun e =>
          (e.field? "langid").orElse fun _ => e.field? "hyphenation"
        if let some l := lang.map (text · |>.trimAscii.toString) then
          if !l.isEmpty && l != "english" && some l != main && !worded.contains l then
            worded := worded.push l
            diags := diags.push (Diag.of .W0421 s!"under 'autolang={o.autolang}' biblatex words \
              entries with langid '{l}' in it; the engine sets the English strings"
              (subject := some ("bibstrings:" ++ l)) (help := help))
  -- biber sorts by the list's locale (`bblSortFile`); a tailoring among the
  -- Latin letters sorts here as there, one of another script is named.
  -- premise: biblatexLocaleSortChecks — every carried tailoring the probe reaches sorts its list as biber does, line for line
  if let some o := (if requested.isEmpty then none else bbl) then
    let file := bblSortFile o
    if Collate.outsideRows file then
      diags := diags.push (Diag.of .W0427 s!"biber sorts this reference list by the '{file}' \
        collation, which the engine does not carry; it is sorted by the default one"
        (help := "load biblatex with 'sortlocale=en_US' to sort the list by the default collation")
        (subject := some ("bibsort:" ++ file)))
  for k in cited do
    if let some ms := sets.get? k then
      diags := diags.push (Diag.of .W0422 s!"biblatex sets the @set entry '{k}' as one entry \
        of its members; the engine lists its {ms.size} members each as an entry of its own"
        (((origin.get? k).map fun src => ⟨sourceName src, ((db.own.get? k).map (·.pos)).getD {}⟩))
        (subject := some ("bibset:" ++ k)))
  -- A date biber cannot read prints as written, named (W0420): a value
  -- outside its grammar or its calendar, and a legacy month it reads as no
  -- month.
  for r in resolved do
    let mine := (db.own.get? r.key).getD r.entry
    let atEntry : Option Span := (origin.get? r.key).map fun src => ⟨sourceName src, mine.pos⟩
    for f in ["date", "urldate", "eventdate", "origdate"] do
      if let some v := mine.field? f then
        if !v.trimAscii.toString.isEmpty && (DateValue.parse v).isNone then
          diags := diags.push (Diag.of .W0420 s!"the {f} '{text v}' of '{r.key}' is not one \
            biblatex reads; it prints as written" atEntry
            (help := s!"write it as YYYY, YYYY-MM or YYYY-MM-DD, a range with '/': \
              '{f} = \{2020-03}'")
            (subject := some s!"bibdate:{r.key}:{f}"))
    if proc == .biber then
      if let some m := mine.field? "month" then
        if !m.trimAscii.toString.isEmpty && (monthNumber months m).isNone then
          diags := diags.push (Diag.of .W0420 s!"the month '{text m}' of '{r.key}' is not one \
            biblatex reads; it prints as written" atEntry
            (help := "write it as a number, 1 to 12, or as a month's name: 'month = {3}'")
            (subject := some s!"bibdate:{r.key}:month"))
  -- A key a set entry's field cites (`fieldCites`) names that entry's place.
  let citedBy : Std.HashMap String String := (fieldCites rendered).foldl (init := {})
    fun m (k, by_) => if m.contains (canon k) then m else m.insert (canon k) by_
  unless requested.isEmpty && own.isEmpty do
    for k in cited do
      if (find k).isNone then
        let (cmd, loss) := if shown.contains k || citedBy.contains k then ("cite", "it shows as '?'")
          else ("nocite", "\\nocite adds nothing for it")
        let atEntry : Option Span := if shown.contains k then none else
          (citedBy.get? k).bind fun e => (origin.get? e).map fun src =>
            ⟨sourceName src, (positions.get? e).getD {}⟩
        diags := diags.push (Diag.of .W0351 s!"citation '{k}' has no entry in the \
          bibliography; {loss}" atEntry
          (help := if own.isEmpty then s!"add an entry with key '{k}' to the .bib file, \
            or fix the spelling in \\{cmd}"
            else s!"add \\bibitem\{{k}} to the reference list, or fix the spelling in \\{cmd}")
          (subject := some k))
  -- The boundary pictures the list's fields and its citations' ink set:
  -- the document's request carries them as the body's own (`apply`).
  let pictures := resolved.foldl (init := rendered.foldl (init := #[]) fun acc (_, rep) =>
      acc ++ rep.pictures) fun acc r =>
    match find r.key with
    | some r' => acc ++ r'.inkPictures
    | none => acc
  return (p, find, items, diags, pictures, afterInk - base)

/-- A loss the reference list reports at a site after the run has named it —
in the body (`prior`) or at an earlier entry — as the body's own later
sites ride: a note with no help, beside the first site's warning, which
the run's tally gives the count (`Diag.tallySites`). -/
public def demoteRepeated (prior ds : Array Diag) : Array Diag :=
  let key (d : Diag) : Option String := d.subject.map fun s =>
    s!"{d.code}\u0000{s}\u0000{repr d.output}"
  let seen : Std.HashSet String := prior.foldl (init := {}) fun m d =>
    match key d with
    | some k => m.insert k
    | none => m
  (ds.foldl (init := ((#[] : Array Diag), seen)) fun (out, seen) d =>
    match key d with
    | some k =>
      if seen.contains k then (out.push { d.demote with help := none }, seen)
      else (out.push d, seen.insert k)
    | none => (out.push d, seen)).1

/-- Resolve the document's citations and reference lists against its `.bib`
sources, every field read through `rd` at its entry's place: the build
passes the document's own inline elaborator (`Bib.FieldDoor.read`, through
`Bib.resolve`), and a caller with no source context names the reading that
needs none (`plainReading`) — there is no default, so no caller reads
fields some other way than it says. -/
public def apply (sources : Array (String × String)) (doc : Ir.Doc)
    (rd : FieldReading) : Ir.Doc × Array Diag :=
  match analyse sources doc rd with
  | (p, find, items, diags, pictures, notes) =>
    (((resolveDoc p find items doc).addPictures pictures).withListNotes notes, diags)

/-- The keys of the references the document's reference lists hold, each
once in list order — `pending`, only those no label answered, which the
list sets as `??`. A collector over the list items' inlines alone, the
body's set aside: where the document's judge locates a key only a list
holds (`refSpanOf`). -/
public def listRefKeys (doc : Ir.Doc) (pending : Bool) : Array String :=
  Ir.foldBlocks (fun out b => match b with
    | .bibliography _ _ items => items.foldl (init := out) fun out it =>
        Ir.foldInlines (fun out x => match x with
          | .ref key _ _ target =>
            if (pending && target.isSome) || out.contains key then out else out.push key
          | _ => out) out it.content
    | _ => out) (fun out _ => out) #[] doc.body

/-- A reference list's references resolved against the document's labels
(`table`, the one the body's resolved against): LaTeX sets a `.bbl`'s
`\ref` where the list stands, the labels read from the `.aux`, so a
field's `\ref{key}` sets the number the body's sets. The list is built
after the body's references were resolved, so its own are resolved here;
the body's resolve again to what they are. A document with no reference is
returned as it is. -/
public def resolveListRefs (table : Ir.RefTable) (doc : Ir.Doc) : Ir.Doc :=
  if (Ir.bibRefs doc).isEmpty || !Ir.foldDoc (fun b x => b || x matches .ref ..) false doc
  then doc
  else { doc with body := Ir.resolveRefs doc.info.locale table doc.body }

/-- Where W0349 names a key: the body's first site (`bodySpan`), else, for a
key only a reference list's entries hold (`listed`, `listRefKeys`), the
list's command (`listSpan`) — an entry's fields carry no source span of
their own. The judge is the document's (`Ir.refDiags`), whose census reads
a list's entries with the body, so a key the body and a field both leave
`??` is named once, at the body's site, as the body's own repeats are. -/
public def refSpanOf (bodySpan : String → Option Span) (listSpan : Option Span)
    (listed : Array String) (key : String) : Option Span :=
  (bodySpan key).orElse fun _ => if listed.contains key then listSpan else none

/-! ## Resolution leaves no citation

The census fact `apply_no_cite` rests on two things: every node the rewrite
emits in a citation's place carries no citation (`renderCite_citeFree`: text
and links over text, or a field citation's cite-free ink), and every other
node passes through with only its body rewritten. Stated over the census fold (`Ir.pendingStep`) with the
accumulator generalised, so each walk shape is one induction. -/

/-- A citation link's body: its mark's text, or that text in the declared
ink (`CitePunct.ink`). -/
private def plainMark : Ir.Inline → Bool
  | .text _ => true
  | .colored _ _ b => b.all fun x => match x with | .text _ => true | _ => false
  | _ => false

/-- A node the citation renderer emits for a label citation: text, or a
link whose body is a mark (`plainMark`). Neither carries a pending leaf. -/
private def plainCite : Ir.Inline → Bool
  | .text _ => true
  | .link _ body => body.all plainMark
  | _ => false

private theorem emit_plain (out : Array Ir.Inline) (s : String)
    (h : out.all plainCite = true) : (emit out s).all plainCite = true := by
  unfold emit
  split
  · exact h
  · rw [Array.all_push, h]; rfl

private theorem emitLink_plain (p : CitePunct) (out : Array Ir.Inline) (anchor s : String)
    (h : out.all plainCite = true) : (emitLink p out anchor s).all plainCite = true := by
  rw [emitLink, Array.all_push, h]
  cases p.ink <;> simp [plainCite, plainMark]

private theorem flushHeld_plain (p : CitePunct) (out : Array Ir.Inline)
    (h : Option (String × Resolved))
    (hout : out.all plainCite = true) : (flushHeld p out h).all plainCite = true := by
  cases h with
  | none => exact hout
  | some ph => exact emitLink_plain _ _ _ _ (emit_plain _ _ hout)

private theorem runStep_plain (p : CitePunct) (st : RunAcc) (o : Option Resolved)
    (h : st.acc.out.all plainCite = true) : (runStep p st o).acc.out.all plainCite = true := by
  cases o with
  | none => exact emit_plain _ _ (flushHeld_plain _ _ _ h)
  | some r =>
    simp only [runStep]
    split
    · exact h
    · exact emitLink_plain _ _ _ _ (emit_plain _ _ (flushHeld_plain _ _ _ h))

private theorem compressRuns_plain (p : CitePunct) (parts : Array (Option Resolved)) :
    (compressRuns p parts).out.all plainCite = true := by
  unfold compressRuns
  refine flushHeld_plain _ _ _ ?_
  exact Array.foldl_induction (motive := fun _ (a : RunAcc) => a.acc.out.all plainCite = true)
    (by simp) (fun _ b hb => runStep_plain p b _ hb)

/-- The renderer emits text and links over text only. -/
private theorem plainCite_citeFree (x : Ir.Inline) (h : plainCite x = true) :
    citeFreeOne x = true := by
  cases x <;> simp only [plainCite] at h <;> try exact absurd h (by decide)
  case text s => rfl
  case link u body =>
    rw [citeFreeOne]
    suffices hl : ∀ l : List Ir.Inline, (∀ y ∈ l, plainMark y = true) → citeFreeList l = true from
      hl body.toList fun y hy => Array.all_eq_true_iff_forall_mem.mp h y (Array.mem_def.mpr hy)
    intro l hl
    induction l with
    | nil => rfl
    | cons y rest ih =>
      rw [citeFreeList, Bool.and_eq_true]
      refine ⟨?_, ih fun z hz => hl z (List.mem_cons_of_mem _ hz)⟩
      have hy := hl y (List.mem_cons_self ..)
      cases y <;> simp only [plainMark] at hy <;> try exact absurd hy (by decide)
      case text t => rfl
      case colored c nm b =>
        rw [citeFreeOne]
        suffices hb : ∀ m : List Ir.Inline,
            (∀ z ∈ m, (match z with | .text _ => true | _ => false) = true) →
            citeFreeList m = true from
          hb b.toList fun z hz => Array.all_eq_true_iff_forall_mem.mp hy z (Array.mem_def.mpr hz)
        intro m hm
        induction m with
        | nil => rfl
        | cons z rest ih' =>
          rw [citeFreeList, Bool.and_eq_true]
          refine ⟨?_, ih' fun w hw => hm w (List.mem_cons_of_mem _ hw)⟩
          have hz := hm z (List.mem_cons_self ..)
          cases z <;> simp_all [citeFreeOne]

mutual

/-- **Cite-free content adds no citation to the census**: whatever the
pending fold collects over inline content carrying no citation
(`citeFreeOne`) is a reference, never a citation. -/
private theorem citeFree_census (x : Ir.Inline) (h : citeFreeOne x = true) :
    ∀ (acc : Array Ir.Unresolved) (q : Ir.Unresolved),
      q ∈ Ir.foldInline Ir.pendingStep acc x → q ∈ acc ∨ q.isCite = false := by
  match x with
  | .styled _ body | .colored _ _ body | .located _ body | .role _ body | .link _ body
  | .decorated _ body | .onSteps _ body | .footnote _ body =>
    intro acc q hq
    simp only [citeFreeOne] at h
    simp only [Ir.foldInline, Ir.pendingStep, Ir.pendingLeaf, Array.append_empty] at hq
    exact citeFreeList_census body.toList h acc q hq
  | .altSteps _ active otherwise =>
    intro acc q hq
    simp only [citeFreeOne, Bool.and_eq_true] at h
    simp only [Ir.foldInline, Ir.pendingStep, Ir.pendingLeaf, Array.append_empty] at hq
    rcases citeFreeList_census otherwise.toList h.2 _ q hq with h' | hc
    · exact citeFreeList_census active.toList h.1 acc q h'
    · exact .inr hc
  | .cite _ _ => simp [citeFreeOne] at h
  | .ref key form text target =>
    intro acc q hq
    simp only [Ir.foldInline, Ir.pendingStep] at hq
    cases target with
    | none =>
      simp only [Ir.pendingLeaf, Array.mem_append, Array.mem_singleton] at hq
      rcases hq with hq | rfl
      · exact .inl hq
      · exact .inr rfl
    | some a =>
      simp only [Ir.pendingLeaf, Array.append_empty] at hq
      exact .inl hq
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _ | .label _
  | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _ | .pageNumber | .pageCount
  | .linebreak _ =>
    intro acc q hq
    simp only [Ir.foldInline, Ir.pendingStep, Ir.pendingLeaf, Array.append_empty] at hq
    exact .inl hq

private theorem citeFreeList_census (xs : List Ir.Inline) (h : citeFreeList xs = true) :
    ∀ (acc : Array Ir.Unresolved) (q : Ir.Unresolved),
      q ∈ Ir.foldInlineList Ir.pendingStep acc xs → q ∈ acc ∨ q.isCite = false := by
  match xs with
  | [] => intro acc q hq; exact .inl hq
  | x :: rest =>
    intro acc q hq
    rw [citeFreeList, Bool.and_eq_true] at h
    rw [Ir.foldInlineList] at hq
    rcases citeFreeList_census rest h.2 _ q hq with h' | hc
    · exact citeFree_census x h.1 acc q h'
    · exact .inr hc

end

private theorem citeFreeList_append (xs ys : List Ir.Inline)
    (hx : citeFreeList xs = true) (hy : citeFreeList ys = true) :
    citeFreeList (xs ++ ys) = true := by
  induction xs with
  | nil => simpa using hy
  | cons x rest ih =>
    rw [citeFreeList, Bool.and_eq_true] at hx
    rw [List.cons_append, citeFreeList, hx.1, ih hx.2]
    rfl

private theorem citeFree_of_plain (xs : Array Ir.Inline) (h : xs.all plainCite = true) :
    citeFreeList xs.toList = true := by
  suffices hl : ∀ l : List Ir.Inline, (∀ y ∈ l, plainCite y = true) → citeFreeList l = true from
    hl xs.toList fun y hy => Array.all_eq_true_iff_forall_mem.mp h y (Array.mem_def.mpr hy)
  intro l hl
  induction l with
  | nil => rfl
  | cons y rest ih =>
    rw [citeFreeList, plainCite_citeFree y (hl y (List.mem_cons_self ..)),
      ih fun z hz => hl z (List.mem_cons_of_mem _ hz)]
    rfl

private theorem emit_citeFree (out : Array Ir.Inline) (t : String)
    (h : citeFreeList out.toList = true) : citeFreeList (emit out t).toList = true := by
  unfold emit
  split
  · exact h
  · rw [Array.toList_push]; exact citeFreeList_append _ _ h rfl

private theorem linkPiece_citeFree (p : CitePunct) (out : Array Ir.Inline) (anchor : String)
    (before piece : Array Ir.Inline) (h : citeFreeList out.toList = true) :
    citeFreeList (linkPiece p out anchor before piece).toList = true := by
  unfold linkPiece
  split
  · split
    · rename_i hb
      rw [Array.toList_append]
      exact citeFreeList_append _ _ h hb
    · exact emit_citeFree _ _ h
  split
  · rename_i hg
    simp only [Bool.and_eq_true] at hg
    rw [Array.toList_push, Array.toList_append]
    refine citeFreeList_append _ _ (citeFreeList_append _ _ h hg.1) ?_
    cases p.ink <;> simp [citeFreeList, citeFreeOne, hg.2]
  · rw [emitLink, Array.toList_push]
    refine citeFreeList_append _ _ (emit_citeFree _ _ h) ?_
    cases p.ink <;> simp [citeFreeList, citeFreeOne]

private theorem citeStep_citeFree (p : CitePunct) (f : Ir.CiteForm) (s : Switches) (n : Nat)
    (acc : CiteAcc) (o : Option Resolved) (h : citeFreeList acc.out.toList = true) :
    citeFreeList (citeStep p f s n acc o).out.toList = true := by
  cases o with
  | none => exact emit_citeFree _ _ h
  | some r => exact linkPiece_citeFree _ _ _ _ _ h

private theorem finish_citeFree (p : CitePunct) (f : Ir.CiteForm) (s : Switches)
    (pagination : Option String) (acc : CiteAcc) (h : citeFreeList acc.out.toList = true) :
    citeFreeList (finish p f s pagination acc).toList = true := by
  refine emit_citeFree _ _ ?_
  rw [Array.toList_append]
  exact citeFreeList_append _ _ (emit_citeFree _ _ rfl) h

/-- A field citation's keys, each its ink — a link over cite-free content —
or a `?`, apart by text: content with no citation in it. -/
private theorem fieldStep_citeFree (p : CitePunct) (w : Ir.CiteField) (full : Bool)
    (acc : Array Ir.Inline) (o : Option Resolved) (h : citeFreeList acc.toList = true) :
    citeFreeList (fieldStep p w full acc o).toList = true := by
  have hsep : citeFreeList (if acc.isEmpty then acc else emit acc (p.sep ++ " ")).toList = true := by
    split
    · exact h
    · exact emit_citeFree _ _ h
  unfold fieldStep
  cases o with
  | none => exact emit_citeFree _ _ hsep
  | some r =>
    simp only [fieldPiece]
    split
    · exact emit_citeFree _ _ hsep
    · rename_i hink
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true'] at hink
      split
      · rw [Array.toList_push]
        refine citeFreeList_append _ _ hsep ?_
        simp [citeFreeList, citeFreeOne, hink.2]
      · rw [Array.toList_append]
        exact citeFreeList_append _ _ hsep (by simpa using hink.2)

/-- **The renderer emits no citation**: text and links over text, and a
field citation's inks, each content carrying no citation. -/
private theorem renderCite_citeFree (p : CitePunct) (f : Ir.CiteForm)
    (parts : Array (Option Resolved)) :
    citeFreeList (renderCite p f parts).toList = true := by
  unfold renderCite
  split
  · exact citeFree_of_plain _ (emit_plain _ _ (by simp))
  split
  · refine emit_citeFree _ _ ?_
    rw [Array.toList_append]
    refine citeFreeList_append _ _ (emit_citeFree _ _ rfl) ?_
    exact Array.foldl_induction (motive := fun _ (a : Array Ir.Inline) => citeFreeList a.toList = true)
      rfl (fun _ b hb => fieldStep_citeFree p _ _ b _ hb)
  split
  · exact citeFree_of_plain _ (emit_plain _ _ (by simp))
  split
  · rfl
  · refine finish_citeFree _ _ _ _ _ ?_
    split
    · exact citeFree_of_plain _ (compressRuns_plain p _)
    · exact Array.foldl_induction (motive := fun _ (a : CiteAcc) => citeFreeList a.out.toList = true)
        rfl (fun _ b hb => citeStep_citeFree p f _ _ b _ hb)

/-- A rendered citation adds no citation to the pending census. -/
private theorem renderCite_pending (p : CitePunct) (f : Ir.CiteForm)
    (parts : Array (Option Resolved)) (acc : Array Ir.Unresolved) (q : Ir.Unresolved)
    (h : q ∈ Ir.foldInlineList Ir.pendingStep acc (renderCite p f parts).toList) :
    q ∈ acc ∨ q.isCite = false :=
  citeFreeList_census _ (renderCite_citeFree p f parts) acc q h

mutual

/-- Resolution's census, inline face: whatever a rewritten node adds to the
pending census is not a citation — the citation arm emits plain content
(`renderCite_pending`), every other node keeps its own leaf. -/
private theorem resolveInline_pending (p : CitePunct) (find : Resolver) (x : Ir.Inline) :
    ∀ (acc : Array Ir.Unresolved) (q : Ir.Unresolved),
      q ∈ Ir.foldInlineList Ir.pendingStep acc (resolveInline p find #[] x).toList →
      q ∈ acc ∨ q.isCite = false := by
  match x with
  | .styled _ body | .colored _ _ body | .located _ body | .role _ body | .link _ body
  | .decorated kind body | .onSteps _ body | .footnote _ body =>
    intro acc q h
    simp only [resolveInline, Array.toList_push, List.nil_append,
      Ir.foldInlineList, Ir.foldInline, Ir.pendingStep, Ir.pendingLeaf,
      Array.append_empty] at h
    exact resolveInlines_pending p find body.toList acc q h
  | .altSteps _ active otherwise =>
    intro acc q h
    simp only [resolveInline, Array.toList_push, List.nil_append,
      Ir.foldInlineList, Ir.foldInline, Ir.pendingStep, Ir.pendingLeaf,
      Array.append_empty] at h
    rcases resolveInlines_pending p find otherwise.toList _ q h with h' | hc
    · exact resolveInlines_pending p find active.toList acc q h'
    · exact .inr hc
  | .cite form keys =>
    intro acc q h
    simp only [resolveInline, Array.empty_append] at h
    exact renderCite_pending p form (keys.map find) acc q h
  | .ref key form text target =>
    intro acc q h
    simp only [resolveInline, Array.toList_push, List.nil_append,
      Ir.foldInlineList, Ir.foldInline, Ir.pendingStep] at h
    cases target with
    | none =>
      simp only [Ir.pendingLeaf, Array.mem_append, Array.mem_singleton] at h
      rcases h with h | rfl
      · exact .inl h
      · exact .inr rfl
    | some a =>
      simp only [Ir.pendingLeaf, Array.append_empty] at h
      exact .inl h
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _ | .label _
  | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _ | .pageNumber | .pageCount | .linebreak _ =>
    intro acc q h
    simp only [resolveInline, Array.toList_push, List.nil_append,
      Ir.foldInlineList, Ir.foldInline, Ir.pendingStep, Ir.pendingLeaf,
      Array.append_empty] at h
    exact .inl h

private theorem resolveInlines_pending (p : CitePunct) (find : Resolver) (xs : List Ir.Inline) :
    ∀ (acc : Array Ir.Unresolved) (q : Ir.Unresolved),
      q ∈ Ir.foldInlineList Ir.pendingStep acc (resolveInlines p find #[] xs).toList →
      q ∈ acc ∨ q.isCite = false := by
  match xs with
  | [] => intro acc q h; exact .inl h
  | x :: rest =>
    intro acc q h
    rw [resolveInlines, resolveInlines_acc, Array.toList_append, Ir.foldInlineList_append] at h
    rcases resolveInlines_pending p find rest _ q h with h' | hc
    · exact resolveInline_pending p find x acc q h'
    · exact .inr hc

end

private theorem tableCells_pending (p : CitePunct) (find : Resolver) :
    ∀ (cells : List (Array Ir.Inline)) (acc : Array Ir.Unresolved) (q : Ir.Unresolved),
      q ∈ Ir.foldTableCells Ir.pendingStep acc (cells.map (resolveArr p find)) →
      q ∈ acc ∨ q.isCite = false := by
  intro cells
  induction cells with
  | nil => intro acc q h; exact .inl h
  | cons c rest ih =>
    intro acc q h
    rw [List.map_cons, Ir.foldTableCells] at h
    rcases ih _ q h with h' | hc
    · exact resolveInlines_pending p find c.toList acc q h'
    · exact .inr hc

private theorem tableRows_pending (p : CitePunct) (find : Resolver) :
    ∀ (rows : List (Array (Array Ir.Inline))) (acc : Array Ir.Unresolved) (q : Ir.Unresolved),
      q ∈ Ir.foldTableRows Ir.pendingStep acc
        (rows.map fun row => row.map (resolveArr p find)) →
      q ∈ acc ∨ q.isCite = false := by
  intro rows
  induction rows with
  | nil => intro acc q h; exact .inl h
  | cons row rest ih =>
    intro acc q h
    rw [List.map_cons, Ir.foldTableRows, Array.toList_map] at h
    rcases ih _ q h with h' | hc
    · exact tableCells_pending p find row.toList acc q h'
    · exact .inr hc

private theorem algLines_pending (p : CitePunct) (find : Resolver) :
    ∀ (lines : List Ir.AlgLine) (acc : Array Ir.Unresolved) (q : Ir.Unresolved),
      q ∈ Ir.foldAlgLines Ir.pendingStep acc (lines.map fun l =>
        { l with
          content := resolveArr p find l.content
          comment := l.comment.map (resolveArr p find) }) →
      q ∈ acc ∨ q.isCite = false := by
  intro lines
  induction lines with
  | nil => intro acc q h; exact .inl h
  | cons l rest ih =>
    intro acc q h
    rw [List.map_cons, Ir.foldAlgLines] at h
    rcases ih _ q h with h' | hc
    · cases hc' : l.comment with
      | none =>
        simp only [hc', Option.map] at h'
        exact resolveInlines_pending p find l.content.toList acc q h'
      | some c =>
        simp only [hc', Option.map] at h'
        rcases resolveInlines_pending p find c.toList _ q h' with h'' | hcc
        · exact resolveInlines_pending p find l.content.toList acc q h''
        · exact .inr hcc
    · exact .inr hc

/-- A reference list's entries, each through `resolveArr`, folded in turn. -/
private theorem bibItems_pending (p : CitePunct) (find : Resolver) :
    ∀ (items : List Ir.BibItem) (acc : Array Ir.Unresolved) (q : Ir.Unresolved),
      q ∈ Ir.foldBibItems Ir.pendingStep acc
        (items.map fun it => { it with content := resolveArr p find it.content }) →
      q ∈ acc ∨ q.isCite = false := by
  intro items
  induction items with
  | nil => intro acc q h; exact .inl h
  | cons it rest ih =>
    intro acc q h
    rw [List.map_cons, Ir.foldBibItems] at h
    rcases ih _ q h with h' | hc
    · exact resolveInlines_pending p find it.content.toList acc q h'
    · exact .inr hc

mutual

/-- Resolution's census, block face, generalised over the output prefix:
whatever the rewritten block adds to the census beyond what the prefix
already contributed is not a citation. -/
private theorem resolveBlock_pending (p : CitePunct) (find : Resolver) (items : Array Ir.BibItem)
    (b : Ir.Block) :
    ∀ (out : Array Ir.Block) (acc : Array Ir.Unresolved) (q : Ir.Unresolved),
      q ∈ Ir.foldBlockList (fun a _ => a) Ir.pendingStep acc
        (resolveBlock p find items out b).toList →
      q ∈ Ir.foldBlockList (fun a _ => a) Ir.pendingStep acc out.toList ∨ q.isCite = false := by
  match b with
  | .para content =>
    intro out acc q h
    simp only [resolveBlock] at h
    split at h
    · exact .inl h
    · simp only [Ir.foldBlockList_push, Ir.foldBlock] at h
      exact resolveInlines_pending p find content.toList _ q h
  | .framefoot content | .logo content =>
    intro out acc q h
    simp only [resolveBlock, Ir.foldBlockList_push, Ir.foldBlock] at h
    exact resolveInlines_pending p find content.toList _ q h
  | .equation n content =>
    intro out acc q h
    simp only [resolveBlock, Ir.foldBlockList_push, Ir.foldBlock] at h
    rcases resolveInlines_pending p find n.toList _ q h with h' | hc
    · exact resolveInlines_pending p find content.toList _ q h'
    · exact .inr hc
  | .section _ _ _ title =>
    intro out acc q h
    simp only [resolveBlock, Ir.foldBlockList_push, Ir.foldBlock] at h
    exact resolveInlines_pending p find title.toList _ q h
  | .abstract body | .center body | .ragged _ body | .quote body | .role _ body
  | .link _ body | .spaced _ body | .onSteps _ body | .only _ body | .nav _ body | .note body =>
    intro out acc q h
    simp only [resolveBlock, Ir.foldBlockList_push, Ir.foldBlock] at h
    exact resolveBlocks_pending p find items body.toList #[] _ q h
  | .altSteps _ active otherwise =>
    intro out acc q h
    simp only [resolveBlock, Ir.foldBlockList_push, Ir.foldBlock] at h
    rcases resolveBlocks_pending p find items otherwise.toList #[] _ q h with h' | hc
    · exact resolveBlocks_pending p find items active.toList #[] _ q h'
    · exact .inr hc
  | .titled _ title body | .disclosure title _ body | .frame title _ _ _ body =>
    intro out acc q h
    simp only [resolveBlock, Ir.foldBlockList_push, Ir.foldBlock] at h
    rcases resolveBlocks_pending p find items body.toList #[] _ q h with h' | hc
    · exact resolveInlines_pending p find title.toList _ q h'
    · exact .inr hc
  | .float _ _ _ body caption =>
    intro out acc q h
    simp only [resolveBlock, Ir.foldBlockList_push, Ir.foldBlock] at h
    rcases resolveBlocks_pending p find items body.toList #[] _ q h with h' | hc
    · exact resolveInlines_pending p find caption.toList _ q h'
    · exact .inr hc
  | .list _ its =>
    intro out acc q h
    simp only [resolveBlock, Ir.foldBlockList_push, Ir.foldBlock] at h
    exact resolveItems_pending p find items its.toList #[] _ q h
  | .columns cols =>
    intro out acc q h
    simp only [resolveBlock, Ir.foldBlockList_push, Ir.foldBlock] at h
    exact resolveCols_pending p find items cols.toList #[] _ q h
  | .table _ _ _ rows _ _ =>
    intro out acc q h
    simp only [resolveBlock, Ir.foldBlockList_push, Ir.foldBlock, Array.toList_map] at h
    exact tableRows_pending p find rows.toList _ q h
  | .algorithm _ _ lines =>
    intro out acc q h
    simp only [resolveBlock, Ir.foldBlockList_push, Ir.foldBlock, Array.toList_map] at h
    exact algLines_pending p find lines.toList _ q h
  | .bibliography _ _ _ =>
    intro out acc q h
    simp only [resolveBlock, Ir.foldBlockList_push, Ir.foldBlock, Array.toList_map] at h
    exact bibItems_pending p find items.toList _ q h
  | .verbatim _ _ _ | .setPalette _ | .setTokens _ | .pagebreak
  | .rule _ _ _ | .picture _ =>
    intro out acc q h
    simp only [resolveBlock, Ir.foldBlockList_push, Ir.foldBlock] at h
    exact .inl h

private theorem resolveBlocks_pending (p : CitePunct) (find : Resolver) (items : Array Ir.BibItem)
    (bs : List Ir.Block) :
    ∀ (out : Array Ir.Block) (acc : Array Ir.Unresolved) (q : Ir.Unresolved),
      q ∈ Ir.foldBlockList (fun a _ => a) Ir.pendingStep acc
        (resolveBlocks p find items out bs).toList →
      q ∈ Ir.foldBlockList (fun a _ => a) Ir.pendingStep acc out.toList ∨ q.isCite = false := by
  match bs with
  | [] => intro out acc q h; exact .inl h
  | b :: rest =>
    intro out acc q h
    rw [resolveBlocks] at h
    rcases resolveBlocks_pending p find items rest _ acc q h with h' | hc
    · exact resolveBlock_pending p find items b out acc q h'
    · exact .inr hc

private theorem resolveItems_pending (p : CitePunct) (find : Resolver) (items : Array Ir.BibItem)
    (its : List (Array Ir.Block)) :
    ∀ (out : Array (Array Ir.Block)) (acc : Array Ir.Unresolved) (q : Ir.Unresolved),
      q ∈ Ir.foldBlockItems (fun a _ => a) Ir.pendingStep acc
        (resolveItems p find items out its).toList →
      q ∈ Ir.foldBlockItems (fun a _ => a) Ir.pendingStep acc out.toList ∨ q.isCite = false := by
  match its with
  | [] => intro out acc q h; exact .inl h
  | item :: rest =>
    intro out acc q h
    rw [resolveItems] at h
    rcases resolveItems_pending p find items rest _ acc q h with h' | hc
    · simp only [Array.toList_push, Ir.foldBlockItems_append, Ir.foldBlockItems] at h'
      exact resolveBlocks_pending p find items item.toList #[] _ q h'
    · exact .inr hc

private theorem resolveCols_pending (p : CitePunct) (find : Resolver) (items : Array Ir.BibItem)
    (cs : List (Ir.BoxWidth × Array Ir.Block)) :
    ∀ (out : Array (Ir.BoxWidth × Array Ir.Block)) (acc : Array Ir.Unresolved) (q : Ir.Unresolved),
      q ∈ Ir.foldBlockCols (fun a _ => a) Ir.pendingStep acc
        (resolveCols p find items out cs).toList →
      q ∈ Ir.foldBlockCols (fun a _ => a) Ir.pendingStep acc out.toList ∨ q.isCite = false := by
  match cs with
  | [] => intro out acc q h; exact .inl h
  | (_, body) :: rest =>
    intro out acc q h
    rw [resolveCols] at h
    rcases resolveCols_pending p find items rest _ acc q h with h' | hc
    · simp only [Array.toList_push, Ir.foldBlockCols_append, Ir.foldBlockCols] at h'
      exact resolveBlocks_pending p find items body.toList #[] _ q h'
    · exact .inr hc

end

/-- The furniture regions, each through `resolveArr`, folded in turn. -/
private theorem regions_pending (p : CitePunct) (find : Resolver) :
    ∀ (rs : List (Array Ir.Inline)) (acc : Array Ir.Unresolved) (q : Ir.Unresolved),
      q ∈ rs.foldl (fun acc r => Ir.foldInlines Ir.pendingStep acc (resolveArr p find r)) acc →
      q ∈ acc ∨ q.isCite = false := by
  intro rs
  induction rs with
  | nil => intro acc q h; exact .inl h
  | cons r rest ih =>
    intro acc q h
    rw [List.foldl_cons] at h
    rcases ih _ q h with h' | hc
    · exact resolveInlines_pending p find r.toList acc q h'
    · exact .inr hc

/-- **Resolution leaves no citation**: the pending census of a resolved
document names no `.cite`, in any region `foldDoc` reads. -/
public theorem resolveDoc_no_cite (p : CitePunct) (find : Resolver) (items : Array Ir.BibItem)
    (doc : Ir.Doc) :
    ∀ u ∈ Ir.pendingNodes (resolveDoc p find items doc), u.isCite = false := by
  intro u hu
  unfold Ir.pendingNodes Ir.foldDoc at hu
  rw [resolveDoc, Ir.furnitureInlines_mapDoc, Array.foldl_map, ← Array.foldl_toList] at hu
  have hbody : (Ir.mapDoc (resolveArr p find)
      (fun bs => resolveBlocks p find items #[] bs.toList) doc).body =
        resolveBlocks p find items #[] doc.body.toList := rfl
  rw [hbody] at hu
  rcases regions_pending p find _ _ u hu with h' | hc
  · unfold Ir.foldBlocks at h'
    rcases resolveBlocks_pending p find items doc.body.toList #[] #[] u h' with h'' | hc
    · simp [Ir.foldBlockList] at h''
    · exact hc
  · exact hc

/-- **No citation reaches a backend**: `apply` runs on every document and
leaves no `.cite` node in any region, so the backends' `.cite` arms —
kept explicit, as every walk's arms are — are dead by this theorem; a
citation's rendering is the style's inlines and nothing else. The
citation half of the resolution gate (`pending_named`). -/
public theorem apply_no_cite (sources : Array (String × String)) (doc : Ir.Doc)
    (rd : FieldReading) :
    ∀ u ∈ Ir.pendingNodes (apply sources doc rd).1, u.isCite = false := by
  intro u hu
  unfold apply at hu
  rcases h : analyse sources doc rd with ⟨p, find, items, diags, pictures, notes⟩
  rw [h, Ir.pendingNodes_withListNotes, Ir.pendingNodes_addPictures] at hu
  exact resolveDoc_no_cite p find items doc u hu


end LeanTex.Core.Bib
