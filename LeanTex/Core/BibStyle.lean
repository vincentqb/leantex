import LeanTex.Core.Bib
import LeanTex.Core.Ir
import LeanTex.Core.MathParse
import Std.Data.HashSet

/-! A bibliography style, decomposed the way biblatex decomposed `.bst`
files: five independent pure choices — how a citation renders inline, how
the reference list is ordered, which fields each entry type contributes in
what order, the order a name is written in, and whether first names
abbreviate to initials (the last two carried by `NameFormat`). `unsrtnat`
is one record of the five; `plainnat` is another over the same field
orders; `abbrvnat` and `abbrv` set only the abbreviation axis; a style the
engine does not know falls back to a record, never to a separate code
path. The formats themselves transcribe plainnat.bst (Daly, natbib's
companion style), which `unsrtnat.bst` shares verbatim minus the SORT
pass. -/

namespace LeanTex.Core.Bib

open LeanTex.Core

/-- natbib's citation punctuation: the seven values `\bibpunct` sets
(natbib.sty `\NAT@open`, `\NAT@close`, `\NAT@sep`, the mode letter,
`\NAT@aysep`, `\NAT@yrsep`, `\NAT@cmt`), each at natbib's own load
value, and the load's `sort` and `compress` (`\NAT@sort`, `\NAT@cmprs`),
which order a citation's keys and join its runs of numbers — options no
`\bibpunct` or style row touches. -/
structure CitePunct where
  numbers : Bool := false
  «open» : String := "("
  close : String := ")"
  sep : String := ";"
  aysep : String := ","
  yysep : String := ","
  notesep : String := ", "
  sort : Bool := false
  compress : Bool := false
  /-- The citations are biblatex's (its standard styles' defaults, biblatex
  manual §3.1.2.1 and §3.9): up to three label names (`maxcitenames`), no
  von part (`useprefix=false`), a textual citation's last key joined by
  `and`, and a key repeating the last key's names printed whole. (Its bare
  author-year `\cite` is natbib's `\citealp`, a rename where it is read.) -/
  biblatex : Bool := false
  deriving Repr, BEq, Inhabited

/-- natbib's `\bibstyle@plainnat` row, which `abbrvnat` and `unsrtnat`
share (natbib.sty: `\bibpunct{[}{]}{,}{a}{,}{,}`): author-year, square
brackets, a comma between citations. -/
def natPunct : CitePunct := { «open» := "[", close := "]", sep := "," }

/-- natbib's `\bibstyle@plain` row, which `abbrv` and `unsrt` share
(`\bibpunct{[}{]}{,}{n}{}{,}`): numbers in square brackets, LaTeX's own
`\cite` too (latex.ltx `\@cite`, `[1, 2]`). -/
def latexPunct : CitePunct :=
  { numbers := true, «open» := "[", close := "]", sep := ",", aysep := "" }

/-- natbib's `\bibstyle@<name>` rows (natbib.sty:206–234, and the `\let`
aliases beside them): the punctuation natbib gives a style by its name
while its `\bibstyle` door stays open, whether or not the engine formats
that style's list. A name with no row leaves natbib's declared punctuation
standing — natbib.sty reads an undefined `\bibstyle@<name>` as nothing —
which is what an `apalike` document cites with: `(Doe, 2024; Roe, 2020)`.
Each row is the six values its `\bibpunct` sets, the note separator at
`\bibpunct`'s default `, `; agu's `,~` year separator is the `,` natbib
sets (its `\unskip` takes the tie). natbib's `nature` row, superscript
numbers, has no entry: the engine sets no superscript citation, as it
refuses natbib's `super` option. -/
def natbibRows : List (String × CitePunct) :=
  let ay (o c sep aysep : String) : CitePunct :=
    { «open» := o, close := c, sep, aysep, yysep := "," }
  let num (o c : String) (yysep : String := ",") : CitePunct :=
    { numbers := true, «open» := o, close := c, sep := ",", aysep := "", yysep }
  [("chicago", ay "(" ")" ";" ","), ("named", ay "[" "]" ";" ","),
   ("agu", ay "[" "]" ";" ","), ("copernicus", ay "(" ")" ";" ","),
   ("egu", ay "(" ")" ";" ","), ("egs", ay "(" ")" ";" ","),
   ("agsm", ay "(" ")" "," ""), ("kluwer", ay "(" ")" "," ""),
   ("dcu", ay "(" ")" ";" ";"), ("aa", ay "(" ")" ";" ""),
   ("pass", ay "(" ")" ";" ","), ("anngeo", ay "(" ")" ";" ","),
   ("nlinproc", ay "(" ")" ";" ","),
   ("cospar", num "/" "/" (yysep := "")), ("esa", num "(Ref.\u00a0" ")" (yysep := "")),
   ("plain", latexPunct), ("alpha", latexPunct), ("abbrv", latexPunct), ("unsrt", latexPunct),
   ("plainnat", natPunct), ("abbrvnat", natPunct), ("unsrtnat", natPunct)]

/-- `\setcitestyle`'s keywords (natbib.sty `\setcitestyle`, the package
options by the same names): each a row, read in the order written. -/
def citeKeywords : List (String × (CitePunct → CitePunct)) :=
  [("round", fun p => { p with «open» := "(", close := ")" }),
   ("square", fun p => { p with «open» := "[", close := "]" }),
   ("angle", fun p => { p with «open» := "<", close := ">" }),
   ("curly", fun p => { p with «open» := "{", close := "}" }),
   ("semicolon", fun p => { p with sep := ";" }),
   ("colon", fun p => { p with sep := ";" }),
   ("comma", fun p => { p with sep := "," }),
   ("authoryear", fun p => { p with numbers := false }),
   ("numbers", fun p => { p with numbers := true })]

/-- `\setcitestyle`'s `key=value` declarations (natbib.sty `\setcitestyle`:
`open`, `close`, `aysep`, `yysep`, `notesep`, `citesep`), the values
`\bibpunct` sets by position. -/
def citeKeys : List (String × (CitePunct → String → CitePunct)) :=
  [("open", fun p v => { p with «open» := v }), ("close", fun p v => { p with close := v }),
   ("aysep", fun p v => { p with aysep := v }), ("yysep", fun p v => { p with yysep := v }),
   ("notesep", fun p v => { p with notesep := v }),
   ("citesep", fun p v => { p with sep := v })]

/-- A value as TeX reads a delimited argument: one outer brace group is
stripped (`open={(}` is `(`), anything else is kept as written. -/
def stripGroup (v : String) : String := Id.run do
  let cs := v.toList
  unless cs.head? == some '{' && cs.getLast? == some '}' do return v
  let mut depth : Int := 0
  let mut k := 0
  for c in cs do
    k := k + 1
    if c == '{' then depth := depth + 1
    else if c == '}' then
      depth := depth - 1
      if depth == 0 && k < cs.length then return v
  return String.ofList (cs.drop 1 |>.dropLast)

/-- A `key=value` declaration's key and value, when it is one. -/
private def keyValue? (d : String) : Option (String × String) :=
  match d.splitOn "=" with
  | k :: v :: rest => some (k, stripGroup (String.intercalate "=" (v :: rest)))
  | _ => none

/-- Does natbib read this declaration — a keyword, a key it knows, or a
door word? Exactly as written: natbib compares whole items, so ` round`
after a comma and a space is a word it does not know. -/
def CitePunct.reads (d : String) : Bool :=
  d == "nobibstyle" || d == "bibstyle" || (citeKeywords.lookup d).isSome ||
    ((keyValue? d).bind fun (k, _) => citeKeys.lookup k).isSome

/-- One declaration over the punctuation and natbib's `\bibstyle` door, the
door a bibliography style's own punctuation comes through at
`\begin{document}`: `nobibstyle` closes it and `bibstyle` reopens it
(natbib's option names), `sort` and `compress` set the load's two
citation options, a keyword or a `key=value` updates the punctuation, and
anything else leaves both as they were — natbib reads an unknown item as
nothing. -/
def CitePunct.step (st : CitePunct × Bool) (d : String) : CitePunct × Bool :=
  if d == "nobibstyle" then (st.1, false)
  else if d == "bibstyle" then (st.1, true)
  else if d == "sort" then ({ st.1 with sort := true }, st.2)
  else if d == "compress" then ({ st.1 with compress := true }, st.2)
  else if d == "biblatex" then ({ st.1 with biblatex := true }, st.2)
  else if let ["citestyle", name] := d.splitOn "=" then
    -- `\citestyle{name}` (natbib.sty): the name's `\bibstyle@` row, or
    -- nothing for a name with none; the load's options stand.
    match natbibRows.lookup name with
    | some r => ({ r with sort := st.1.sort, compress := st.1.compress,
                          biblatex := st.1.biblatex }, st.2)
    | none => st
  else match citeKeywords.lookup d, keyValue? d with
    | some f, _ => (f st.1, st.2)
    | none, some (k, v) =>
      match citeKeys.lookup k with
      | some f => (f st.1 v, st.2)
      | none => st
    | none, none => st

/-- The items of a `\setcitestyle` list, split where natbib's `\@for` splits
them — at commas outside braces — and kept exactly as written. -/
def citeItems (src : String) : Array String := Id.run do
  let mut out : Array String := #[]
  let mut cur := ""
  let mut depth : Int := 0
  for c in src.toList do
    if c == ',' && depth == 0 then
      out := out.push cur
      cur := ""
    else
      if c == '{' then depth := depth + 1
      else if c == '}' then depth := depth - 1
      cur := cur.push c
  return (out.push cur).filter (!·.isEmpty)

/-- natbib's package options in its own declaration order (natbib.sty's
`\DeclareOption`s — `\ProcessOptions` runs them in this order, whatever
order a load lists them in), each as the declarations it executes in
`\setcitestyle`'s vocabulary: `numbers` is `numbers` with `square`, `comma`
and `nobibstyle` there. `sort`, `compress` and `sort&compress` set the two
citation options only a load declares (`CitePunct.step`). -/
def natbibOptions : List (String × List String) :=
  [("numbers", ["numbers", "square", "comma", "nobibstyle"]),
   ("authoryear", ["authoryear", "round", "semicolon", "bibstyle"]),
   ("round", ["round", "nobibstyle"]), ("square", ["square", "nobibstyle"]),
   ("angle", ["angle", "nobibstyle"]), ("curly", ["curly", "nobibstyle"]),
   ("comma", ["comma", "nobibstyle"]), ("semicolon", ["semicolon", "nobibstyle"]),
   ("colon", ["semicolon", "nobibstyle"]),
   ("nobibstyle", ["nobibstyle"]), ("bibstyle", ["bibstyle"]),
   ("sort", ["sort"]), ("compress", ["compress"]), ("sort&compress", ["sort", "compress"])]

/-- How the reference list is ordered: `citation` keeps first-citation
order (the "unsrt" in `unsrtnat`); `authorYear` sorts by the label names,
then year, then key — the tiebreak that keeps the comparison total when
two entries share authors and year; `nty` and `nyt` are biblatex's
default sorting schemes (biblatex manual §3.1.2.1: name, title, year for
the numeric styles; name, year, title for the author-year ones), a name
sorted by its family name first. -/
inductive SortOrder where
  | citation
  | authorYear
  | nty
  | nyt
  deriving Repr, BEq, Inhabited

/-- One formatted piece of a reference-list entry: plainnat.bst's `format.*`
functions (unsrtnat.bst shares them verbatim), each owing its own dressing —
the `In` before a booktitle, the `pages` word, the `12(3):45–67` join — so
an entry type contributes only its sequence of pieces and boundaries
(`Step`). `field` outputs a stored value as written: a publisher, an
address, a school, an institution, an organization, a note. -/
inductive Field where
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
  deriving Repr, BEq

/-- One step of an entry type's function: a piece's `output`, or a block or
sentence boundary — the conditional ones (`new.block.checka`, `checkb`,
`new.sentence.checkb`) taken when any of the named fields is present. -/
inductive Step where
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
structure NameFormat where
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
structure Style where
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

/-- One name as the format writes it. Initials abbreviate each first-name
token to its first letter and a period (plain.bst's `{f.~}` designator). -/
def NameFormat.render (nf : NameFormat) (n : Name) : String :=
  let first :=
    if nf.initials then
      String.intercalate " " (((n.first.splitOn " ").filter (!·.isEmpty)).map
        fun t => String.ofList [t.toList.headD 'x'] ++ ".")
    else n.first
  let jr := if n.jr.isEmpty then "" else s!", {n.jr}"
  if nf.lastFirst then
    let tail := String.intercalate " " ([n.von, first].filter (!·.isEmpty))
    if tail.isEmpty then n.last ++ jr else s!"{n.last}, {tail}" ++ jr
  else
    String.intercalate " " ([first, n.von, n.last].filter (!·.isEmpty)) ++ jr

/-- An author value as the reference list prints it: each name through the
format, the list through plain.bst's join (`andJoin`), a long list elided
at `etAlAfter`. -/
def NameFormat.renderList (nf : NameFormat) (v : String) : String :=
  let ns := (splitNames v).toList
  let ns := match nf.etAlAfter with
    | some k => if ns.length > k then ns.take 1 ++ ["others"] else ns
    | none => ns
  andJoin (ns.map fun s =>
    if s == "others" then "others" else text (nf.render (parseName s)))

/-- The year an inline citation prints: the field as written, which is a
bare number in every `.bib` this engine has met; a missing year prints
`n.d.` (no date), the natbib spelling for one. -/
def citeYear (e : Entry) : String :=
  match e.field? "year" with
  | some y => text y
  | none => "n.d."

/-- The label names of an entry's authors (`\citet`'s `Author et al.`):
the author field through `labelNames` — natbib's two names, or biblatex's
three with no von part — or the key itself when no author is there,
visible, never silently empty. -/
def citeAuthors (e : Entry) (biblatex : Bool := false) : String :=
  match e.field? "author" with
  | some a => Ir.smartPunct (labelNames a (if biblatex then 3 else 2) (!biblatex))
  | none => e.key

/-- The anchor an entry's reference-list item carries and its citations
link to: `Ir.bibAnchor`, the one naming site, `#`-prefixed for the href.
The key is author text from the `.bib`; the typed HTML tree escapes it on
the way into the attribute (`escapeAttr`), so no spelling of a key can
break out of the `href`. -/
def anchorOf (key : String) : String :=
  let a := Ir.bibAnchor key
  "#" ++ a

/-- One resolved citation, ready to render: the entry with its 1-based
position in the reference list, and the letter that tells it from entries
sharing its label (`extraLabels`), empty when its label is its own. -/
structure Resolved where
  key : String
  position : Nat
  entry : Entry
  extra : String := ""
  /-- The mark a `thebibliography` entry's optional label sets in numbers
  mode (latex.ltx `\@lbibitem`), in place of its position. -/
  label : Option String := none
  deriving Repr

/-- The full author list natbib's starred forms print (`\citet*`), or the
key when no author is there, as `citeAuthors` does. -/
def citeFullAuthors (e : Entry) : String :=
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

private def emit (out : Array Ir.Inline) (s : String) : Array Ir.Inline :=
  if s.isEmpty then out else out.push (.text s)

private def emitLink (out : Array Ir.Inline) (anchor s : String) : Array Ir.Inline :=
  out.push (.link anchor #[.text s])

/-- The first letter capitalized — natbib's `\NAT@Up`, what `\Citet` does
to a name that opens with a lowercase particle. -/
private def upFirst (s : String) : String :=
  match s.toList with
  | c :: cs => String.ofList (c.toUpper :: cs)
  | [] => s

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
    | .alt | .alp | .author | .year | .num | .nocite | .bracket _ => false
  { numeric := p.numbers || f.cmd == .num
    wrap := match f.cmd with
      | .paren | .alp | .yearPar | .num | .text => true
      | .auto => p.numbers
      | .textual | .alt | .author | .year | .nocite | .bracket _ => false
    part := match f.cmd with
      | .author => .names
      | .year | .yearPar => .year
      | .textual | .paren | .auto | .alt | .alp | .num | .text | .nocite | .bracket _ => .both
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

/-- One key under natbib's loop (natbib.sty `\NAT@citex`, `\NAT@citexnum`
in numbers mode): the separator the previous key left, this key's piece
linked to its entry, and the separator it leaves. natbib capitalizes names
only in author-year mode; a key repeating the previous key's names prints
only its year after `yysep`, and one repeating the year too only its
letter, with no space (`\NAT@exlab`: `2019a,b`) — biblatex's standard
styles print every key whole. In numbers mode natbib defines `\natexlab`
to print nothing, so no letter prints. An unresolvable key prints `?` in
its place with the separators a resolved one would have. `total` is the
citation's key count, which a biblatex textual citation's last separator
reads (`textSep`). -/
private def citeStep (p : CitePunct) (f : Ir.CiteForm) (s : Switches) (total : Nat)
    (acc : CiteAcc) : Option Resolved → CiteAcc
  | none =>
    { out := emit acc.out (acc.citea ++ "?"), citea := p.sep ++ " ", index := acc.index + 1 }
  | some r =>
    let names := if f.full then citeFullAuthors r.entry else citeAuthors r.entry p.biblatex
    let names := if f.up && !s.numeric then upFirst names else names
    let bare := citeYear r.entry
    let letter := if p.numbers then "" else r.extra
    let year := bare ++ letter
    let mark := if s.numeric then r.label.getD (toString r.position) else year
    let pre := if f.pre.isEmpty then "" else f.pre ++ " "
    let same := !p.biblatex && acc.last == some names
    let sameYear := same && acc.lastYear == some bare && !letter.isEmpty
    let tsep := textSep p f total acc.index
    -- (what precedes the linked piece, the piece, the separator left behind)
    let t : String × String × String := match s.part with
      | .names => (acc.citea, names, p.sep ++ " ")
      | .year => (acc.citea, if p.biblatex then bare else year, p.sep ++ " ")
      | .both =>
        if s.wrap then
          if s.numeric then (acc.citea, mark, p.sep ++ " ")
          else if sameYear then (p.yysep, letter, p.sep ++ " ")
          else if same then (p.yysep ++ " ", year, p.sep ++ " ")
          else (acc.citea, s!"{names}{p.aysep} {year}", p.sep ++ " ")
        else if sameYear then (p.yysep, letter, s.cl ++ tsep)
        else
          (if same then p.yysep ++ " " ++ (if s.numeric then pre else "")
            else acc.citea ++ names ++ " " ++ s.op ++ pre, mark, s.cl ++ tsep)
    { out := emitLink (emit acc.out t.1) (anchorOf r.key) t.2.1
      citea := t.2.2
      last := some names
      lastYear := some bare
      dated := true
      index := acc.index + 1 }

/-- The brackets around the loop's output: a wrapping form opens them with
its pre-note and closes them after its post-note (`notesep`); a textual
form has opened each year's bracket in the loop and closes the last,
after the post-note, when that key printed a year. -/
private def finish (p : CitePunct) (f : Ir.CiteForm) (s : Switches) (acc : CiteAcc) :
    Array Ir.Inline :=
  let post := if f.post.isEmpty then "" else p.notesep ++ f.post
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
private def flushHeld (out : Array Ir.Inline) : Option (String × Resolved) → Array Ir.Inline
  | some (pre, r) => emitLink (emit out pre) (anchorOf r.key) (toString r.position)
  | none => out

/-- One key under `compress`: a number one past the last extends the run
and is held back; any other — a gap, a repeat, a mark that is no number (a
`thebibliography` label) — prints what was held, then itself. An unresolved
key ends the run and prints `?` where it stands. -/
private def runStep (p : CitePunct) (st : RunAcc) : Option Resolved → RunAcc
  | none =>
    { acc := { st.acc with out := emit (flushHeld st.acc.out st.held) (st.acc.citea ++ "?"),
                           citea := p.sep ++ " " } }
  | some r =>
    if r.label.isNone && st.last.map (· + 1) == some r.position then
      { acc := { st.acc with citea := p.sep ++ " ", dated := true }, last := some r.position,
        held := some (if st.held.isSome then "–" else st.acc.citea, r) }
    else
      { acc := { st.acc with
          out := emitLink (emit (flushHeld st.acc.out st.held) st.acc.citea) (anchorOf r.key)
            (r.label.getD (toString r.position))
          citea := p.sep ++ " ", dated := true }
        last := if r.label.isNone then some r.position else none }

/-- natbib's `compress` over a numbered citation (natbib.sty `\NAT@cmprs`):
a run of three or more consecutive list positions sets as its ends joined
by an en dash (`[1–3, 5]`), a run of two keeps both numbers, and a repeated
number breaks a run and prints again. -/
private def compressRuns (p : CitePunct) (parts : Array (Option Resolved)) : CiteAcc :=
  let st := parts.foldl (runStep p) {}
  { st.acc with out := flushHeld st.acc.out st.held }

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
textual one keeps every number, as natbib's textual branch does. The output
is text and links over text only — no `.cite`, no `.ref` — which is
`renderCite_plain`, the leaf fact `apply_no_cite` rests on. -/
def renderCite (p : CitePunct) (f : Ir.CiteForm) (parts : Array (Option Resolved)) :
    Array Ir.Inline :=
  if let .bracket o := f.cmd then emit #[] (if o then p.open else p.close)
  else if f.cmd == .text then emit #[] (p.open ++ f.pre ++ p.close)
  else if f.cmd == .nocite then #[]
  else
    let parts := if p.sort then sortParts parts else parts
    let s := switches p f
    finish p f s (if p.compress && s.numeric && s.wrap && s.part == .both then compressRuns p parts
      else parts.foldl (citeStep p f s parts.size) {})

/-- An en dash between page numbers: `45--67` and `45-67` both print
`45–67`, the range dash `.bib` files spell both ways. `text` already
turns `--` into an en dash; a single `-` between digits is promoted here. -/
private def pageRange (v : String) : String :=
  String.intercalate "–" (((text v).splitOn "-").filter (!·.isEmpty))

/-- A stored value split at its `$…$` spans: `(true, source)` for each span,
`(false, text)` between them. An escaped `\$` is text, and an unclosed span
keeps its dollar and stays text. -/
def mathSpans (v : String) : Array (Bool × String) := Id.run do
  let cs := v.toList.toArray
  let mut out : Array (Bool × String) := #[]
  let mut cur := ""
  let mut inMath := false
  let mut i := 0
  for _ in [0:cs.size + 1] do
    if h : i < cs.size then
      let c := cs[i]
      if c == '\\' then
        cur := cur.push c
        if let some d := cs[i + 1]? then cur := cur.push d
        i := i + 2
      else if c == '$' then
        unless cur.isEmpty do out := out.push (inMath, cur)
        cur := ""
        inMath := !inMath
        i := i + 1
      else
        cur := cur.push c
        i := i + 1
    else break
  let tail := if inMath then "$".append cur else cur
  return if tail.isEmpty then out else out.push (false, tail)

/-- One `$…$` span as the elaborator sets inline math: the math parser's
atoms when it can model the span, else the span's floor, which `analyse`
names (W0012). -/
def formulaOf (src : String) : Ir.Inline :=
  let (toks, _) := Lex.lex "" ("$" ++ src ++ "$")
  match (Parse.parse "" toks).1.toList with
  | [.math false body _] =>
    match MathParse.parseMath false body with
    | .ok (l, _) => .formula false (Parse.rawSrc body) l
    | .error _ => .math false (Parse.rawSrc body)
  | _ => .math false src

/-- A stored value as the reference list sets it — the `.bbl` is body text to
LaTeX, so the body's rules: the plain text `text` reads, then the body's
typographic punctuation (`Ir.smartPunct`: TeX's quote and dash ligatures),
each `$…$` span a formula. -/
def fieldInlines (v : String) : Array Ir.Inline := Id.run do
  let spans := mathSpans v
  let mut out : Array Ir.Inline := #[]
  let mut pending := ""
  for (math, s) in spans, k in [0:spans.size] do
    if math then
      unless pending.isEmpty do out := out.push (.text (Ir.smartPunct pending))
      pending := ""
      out := out.push (formulaOf s)
    else
      let t := textSpan s (lead := k != 0)
      pending := pending ++ (if k + 1 == spans.size then t.trimAsciiEnd.toString else t)
  unless pending.isEmpty do out := out.push (.text (Ir.smartPunct pending))
  return out

/-- A stored value is present when it holds anything but white space —
BibTeX's `empty$` false. -/
def Entry.has (e : Entry) (name : String) : Bool :=
  (e.field? name).any fun v => !v.trimAscii.toString.isEmpty

/-- plainnat's `tie.or.space.connect`: a value shorter than three characters
ties to its word, so `volume 3` never breaks between them. -/
private def tieOrSpace (word v : String) : String :=
  word ++ (if v.length < 3 then "\u00a0" else " ") ++ v

/-- plainnat's `format.pages`: `pages` for a range or a list (a `-`, `,` or
`+` in the value, `multi.page.check`), `page` for one. -/
private def formatPages (p : String) : String :=
  if p.any fun c => c == '-' || c == ',' || c == '+' then tieOrSpace "pages" (pageRange p)
  else tieOrSpace "page" (text p)

/-- A URL or DOI as `\url` reads it: braces dropped and an escaped character
itself, everything else verbatim — never `text`'s ligatures and ties, which
would turn `--` into a dash and `~` into a space. -/
private def urlText (u : String) : String := Id.run do
  let mut out := ""
  let mut esc := false
  for c in u.trimAscii.toString.toList do
    if esc then
      out := out.push c
      esc := false
    else if c == '\\' then esc := true
    else if c != '{' && c != '}' then out := out.push c
  return out

/-- An editor list as plainnat writes it (FUNCTION {format.editors}). -/
private def editorsText (nf : NameFormat) (ed : String) : String :=
  Ir.smartPunct (nf.renderList ed ++ if (splitNames ed).size > 1 then ", editors" else ", editor")

/-- One piece of one entry: THE piece renderer — every entry type renders
through this one function, and what varies per type is only the steps that
call it. `mid` is whether the piece continues a sentence, which the edition
and the series number read, as plainnat's do; `extra` is the entry's letter,
which the date carries. An absent field renders empty, and its step writes
nothing. -/
def renderField (nf : NameFormat) (e : Entry) (mid : Bool) (extra : String) :
    Field → Array Ir.Inline
  | .authors =>
    match e.field? "author" with
    | some a => #[.text (Ir.smartPunct (nf.renderList a))]
    | none => #[]
  | .editors =>
    match e.field? "editor" with
    | some ed => #[.text (editorsText nf ed)]
    | none => #[]
  | .title => ((e.field? "title").map (fieldInlines ∘ sentenceCase)).getD #[]
  | .btitle =>
    match e.field? "title" with
    | some t => #[.styled .emph (fieldInlines t)]
    | none => #[]
  | .journal =>
    match e.field? "journal" with
    | some j => #[.styled .emph (fieldInlines j)]
    | none => #[]
  | .volNumPages =>
    let head := ((e.field? "volume").map text).getD "" ++
      ((e.field? "number").map fun n => s!"({text n})").getD ""
    match e.field? "pages" with
    | some p => #[.text (if head.isEmpty then formatPages p else head ++ ":" ++ pageRange p)]
    | none => if head.isEmpty then #[] else #[.text head]
  | .bvolume =>
    match e.field? "volume" with
    | some v =>
      let vol := tieOrSpace "volume" (text v)
      match e.field? "series" with
      | some sr => #[.text (vol ++ " of "), .styled .emph (fieldInlines sr)]
      | none => #[.text vol]
    | none => #[]
  | .numberSeries =>
    if e.has "volume" then #[] else
    match e.field? "number", e.field? "series" with
    | some n, some sr =>
      #[.text (tieOrSpace (if mid then "number" else "Number") (text n) ++ " in ")] ++
        fieldInlines sr
    | some n, none => #[.text (tieOrSpace (if mid then "number" else "Number") (text n))]
    | none, some sr => fieldInlines sr
    | none, none => #[]
  | .inEdBooktitle =>
    match e.field? "booktitle" with
    | some b =>
      let eds := ((e.field? "editor").map fun ed => editorsText nf ed ++ ", ").getD ""
      #[.text ("In " ++ eds), .styled .emph (fieldInlines b)]
    | none => #[]
  | .pages => ((e.field? "pages").map fun p => #[.text (formatPages p)]).getD #[]
  | .chapterPages =>
    match e.field? "chapter" with
    | some c =>
      let head := tieOrSpace (((e.field? "type").map (lowerCase false)).getD "chapter") (text c)
      match e.field? "pages" with
      | some p => #[.text (head ++ ", " ++ formatPages p)]
      | none => #[.text head]
    | none => ((e.field? "pages").map fun p => #[.text (formatPages p)]).getD #[]
  | .edition =>
    match e.field? "edition" with
    | some ed => fieldInlines ((if mid then lowerCase false ed else sentenceCase ed) ++ " edition")
    | none => #[]
  | .trNumber =>
    let ty := ((e.field? "type").map text).getD "Technical Report"
    match e.field? "number" with
    | some n => #[.text (tieOrSpace ty (text n))]
    | none => fieldInlines (sentenceCase ty)
  | .thesisType words =>
    match e.field? "type" with
    | some ty => fieldInlines (sentenceCase ty)
    | none => #[.text (Ir.smartPunct words)]
  | .date =>
    match e.field? "year", e.field? "month" with
    | some y, some m => #[.text (text m ++ " " ++ text y ++ extra)]
    | some y, none => #[.text (text y ++ extra)]
    | none, _ => if extra.isEmpty then #[] else #[.text extra]
  | .doi =>
    match e.field? "doi" with
    | some d => #[.text "doi: ", .link ("https://doi.org/" ++ urlText d) #[.text (urlText d)]]
    | none => #[]
  | .url =>
    match e.field? "url" with
    | some u => #[.text "URL ", .link (urlText u) #[.styled .mono #[.text (urlText u)]]]
    | none => #[]
  | .isbn => ((e.field? "isbn").map fun v => #[.text ("ISBN " ++ text v)]).getD #[]
  | .issn => ((e.field? "issn").map fun v => #[.text ("ISSN " ++ text v)]).getD #[]
  | .field name => ((e.field? name).map fieldInlines).getD #[]

/-- The entry functions of plainnat.bst, whose steps unsrtnat.bst shares
verbatim — FUNCTION {article}, {book}, {booklet}, {inbook},
{incollection}, {inproceedings}, {manual}, {mastersthesis}, {misc},
{phdthesis}, {proceedings}, {techreport}, {unpublished} — one step
sequence per type, the entry deciding the branch `inproceedings` takes
on its address. An unknown type is `misc` (FUNCTION {default.type}); a
type's cross-reference branch is not taken (no `crossref` is read). -/
def plainnatSteps (e : Entry) : Array Step :=
  let url : Array Step := #[.newBlockIf ["url"], .out .url]
  let note : Array Step := #[.newBlock, .out (.field "note")]
  let tail : Array Step := #[.newBlockIf ["doi"], .out .doi] ++ url ++ note
  let isbn : Array Step := #[.newBlockIf ["isbn"], .out .isbn]
  let who : Step := if e.has "author" then .out .authors else .out .editors
  match e.kind with
  | "article" =>
    #[.out .authors, .newBlock, .out .title, .newBlock, .out .journal, .out .volNumPages,
      .out .date, .newBlockIf ["issn"], .out .issn] ++ tail
  | "book" =>
    #[who, .newBlock, .out .btitle, .out .bvolume, .newBlock, .out .numberSeries,
      .newSentence, .out (.field "publisher"), .out (.field "address"), .out .edition,
      .out .date] ++ isbn ++ tail
  | "inbook" =>
    #[who, .newBlock, .out .btitle, .out .bvolume, .out .chapterPages, .newBlock,
      .out .numberSeries, .newSentence, .out (.field "publisher"), .out (.field "address"),
      .out .edition, .out .date] ++ isbn ++ tail
  | "booklet" =>
    #[.out .authors, .newBlock, .out .title, .newBlockIf ["howpublished", "address"],
      .out (.field "howpublished"), .out (.field "address"), .out .date] ++ isbn ++ tail
  | "incollection" =>
    #[.out .authors, .newBlock, .out .title, .newBlock, .out .inEdBooktitle, .out .bvolume,
      .out .numberSeries, .out .chapterPages, .newSentence, .out (.field "publisher"),
      .out (.field "address"), .out .edition, .out .date] ++ isbn ++ tail
  | "inproceedings" | "conference" =>
    #[.out .authors, .newBlock, .out .title, .newBlock, .out .inEdBooktitle, .out .bvolume,
      .out .numberSeries, .out .pages] ++
    (if e.has "address" then
      #[.out (.field "address"), .out .date, .newSentence, .out (.field "organization"),
        .out (.field "publisher")]
    else
      #[.newSentenceIf ["organization", "publisher"], .out (.field "organization"),
        .out (.field "publisher"), .out .date]) ++ isbn ++ tail
  | "manual" =>
    #[.out .authors, .newBlock, .out .btitle, .newBlockIf ["organization", "address"],
      .out (.field "organization"), .out (.field "address"), .out .edition, .out .date] ++
      url ++ note
  | "mastersthesis" =>
    #[.out .authors, .newBlock, .out .title, .newBlock, .out (.thesisType "Master's thesis"),
      .out (.field "school"), .out (.field "address"), .out .date] ++ url ++ note
  | "phdthesis" =>
    #[.out .authors, .newBlock, .out .btitle, .newBlock, .out (.thesisType "PhD thesis"),
      .out (.field "school"), .out (.field "address"), .out .date] ++ url ++ note
  | "proceedings" =>
    #[.out .editors, .newBlock, .out .btitle, .out .bvolume, .out .numberSeries,
      .out (.field "address"), .out .date, .newSentence, .out (.field "organization"),
      .out (.field "publisher")] ++ isbn ++ tail
  | "techreport" =>
    #[.out .authors, .newBlock, .out .title, .newBlock, .out .trNumber,
      .out (.field "institution"), .out (.field "address"), .out .date] ++ url ++ note
  | "unpublished" =>
    #[.out .authors, .newBlock, .out .title, .newBlock, .out (.field "note"), .out .date] ++ url
  | _ =>
    #[.out .authors, .newBlockIf ["title", "howpublished"], .out .title,
      .newBlockIf ["howpublished"], .out (.field "howpublished"), .out .date,
      .newBlockIf ["issn"], .out .issn] ++ url ++ note

/-- The output state plainnat.bst threads through an entry (`output.state`):
nothing written yet, inside a sentence, or a block or a sentence boundary
pending. -/
inductive OutState where
  | beforeAll
  | mid
  | afterBlock
  | afterSentence
  deriving BEq

/-- BibTeX's `add.period$`: the entry so far takes a period unless it
already ends with `.`, `?` or `!`. -/
def addPeriod (out : Array Ir.Inline) : Array Ir.Inline :=
  match (Ir.plainText out).toList.getLast? with
  | none => out
  | some c => if c == '.' || c == '?' || c == '!' then out else out.push (.text ".")

/-- One reference-list entry as plainnat.bst's `output` writes it: a piece
joins its sentence with `, `; after a block or sentence boundary the entry
so far takes its period (`add.period$`) and the piece opens the next; the
entry closes with its period (`fin.entry`). natbib's `\newblock` adds
`\hskip .11em plus .33em minus .07em` at a block boundary, which no IR
node spells: the boundary is one word space. `extra` is the entry's letter
among those sharing its label, which its date carries (`extraLabels`). -/
def renderEntry (nf : NameFormat) (steps : Array Step) (e : Entry) (extra : String := "") :
    Array Ir.Inline := Id.run do
  let mut out : Array Ir.Inline := #[]
  let mut st := OutState.beforeAll
  for step in steps do
    match step with
    | .out f =>
      let r := renderField nf e (st == .mid) extra f
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
  return addPeriod out

/-- `unsrtnat`: the reference list in first-citation order (the "unsrt"),
the standard field orders, full names, author-year labels in its
`\bibitem`s — what `unsrtnat.bst` is, as one record. -/
def Style.unsrtnat : Style where
  labels := true
  sort := .citation
  steps := plainnatSteps
  names := {}

/-- `plainnat`: the same fields and names, the list sorted by author then
year (natbib manual §4: plainnat is the author-year companion of plain). -/
def Style.plainnat : Style where
  labels := true
  sort := .authorYear
  steps := plainnatSteps
  names := {}

/-- `plain`: what the record model buys — plain.bst is numbers over an
author-sorted list, zero new code, only another pairing of the axes. -/
def Style.plain : Style where
  labels := false
  sort := .authorYear
  steps := plainnatSteps
  names := {}

/-- `unsrt`: `plain` in first-citation order, as unsrt.bst is. -/
def Style.unsrt : Style :=
  { Style.plain with sort := .citation }

/-- The name format the abbrv-shaped styles share: first names abbreviate
to initials, first-first order — `{f.~}{vv~}{ll}{, jj}` in both abbrv.bst
and abbrvnat.bst FUNCTION {format.names}, so "J. Smith", never
"Smith, J.". The one axis the abbrv pair sets; everything else is
`plain`/`plainnat` verbatim. -/
def abbrvNames : NameFormat := { initials := true }

/-- `abbrvnat`: `plainnat` with abbreviated first names — natbib ships
abbrvnat.bst as plainnat.bst minus only the name designator (natbib
manual §4 lists the three companion styles as one family). -/
def Style.abbrvnat : Style :=
  { Style.plainnat with names := abbrvNames }

/-- `abbrv`: `plain` with abbreviated first names, the same relation
abbrv.bst has to plain.bst. -/
def Style.abbrv : Style :=
  { Style.plain with names := abbrvNames }

/-- The punctuation a document's citations draw with — natbib's rule. No
natbib is LaTeX's own `\cite` (`latexPunct`). With natbib, its
declarations replay over its load values (`CitePunct.step`); then, while
natbib's `\bibstyle` door stays open, the declared style's row
(`natbibRows`, by name) replaces them all at `\begin{document}` — a style
with no row leaves them standing — and a style whose `\bibitem`s carry no
author-year label (`labels`) puts natbib in numbers mode whatever was
declared (natbib.sty reading a `\bibitem` without one). A document that
declares no style has no row to apply. -/
def CitePunct.ofDoc (natbib : Option (Array String)) (row : Option CitePunct)
    (labels : Bool) : CitePunct :=
  match natbib with
  | none => latexPunct
  | some decls =>
    let (p, door) := decls.foldl CitePunct.step ({}, true)
    let q := if door then row.getD p else p
    let q := { q with sort := p.sort, compress := p.compress, biblatex := p.biblatex }
    if labels then q else { q with numbers := true }

/-- The style a `\bibliographystyle` name selects. `none` is W0353's cue;
the caller falls back to `unsrtnat` — a record, so the fallback loses the
name, never the machinery. -/
def Style.named (name : String) : Option Style :=
  match name with
  | "unsrtnat" => some .unsrtnat
  | "unsrt" => some .unsrt
  | "plainnat" => some .plainnat
  | "plain" => some .plain
  | "abbrvnat" => some .abbrvnat
  | "abbrv" => some .abbrv
  | _ => none

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
def addKey (acc : Array String × Std.HashSet String) (k : String) :
    Array String × Std.HashSet String :=
  if acc.2.contains k then acc else (acc.1.push k, acc.2.insert k)

/-- First-citation order: the keys the document cites, in order of first
appearance, each once — the sequence citation-order lists are sorted by
and numeric labels index into — among the citations `keep` admits (every
one by default; `\nocite`'s count, as they do for BibTeX). A leaf
projection of `Ir.foldDoc`, the one collect traversal, over every region
`resolveDoc` rewrites. -/
def citedKeys (doc : Ir.Doc) (keep : Ir.CiteForm → Bool := fun _ => true) : Array String :=
  (Ir.foldDoc
    (fun acc x => match x with
      | .cite f keys => if keep f then keys.foldl addKey acc else acc
      | _ => acc) (#[], {}) doc).1

/-- `\nocite{*}`'s key, BibTeX's `\citation{*}`: every entry of the `.bib`
enters the list where it stands, in the database's order, after the keys
cited before it — a key already in the sequence keeps its place. -/
def expandStar (entries : Array Entry) (cited : Array String) : Array String :=
  (cited.foldl (fun acc k =>
    if k == "*" then entries.foldl (fun acc e => addKey acc e.key) acc
    else addKey acc k) (#[], {})).1

/-- An entry's author-year sort key, computed once per entry: the label
names lowercased, the year, and — the tiebreak totality forces — the key. -/
def ayKey (r : Resolved) : String × String × String :=
  ((citeAuthors r.entry).toLower, citeYear r.entry, r.key)

/-- The order on author-year keys: the names, then the year, then the key. -/
def ayCompare (a b : String × String × String) : Ordering :=
  (Ord.compare a.1 b.1).then ((Ord.compare a.2.1 b.2.1).then (Ord.compare a.2.2 b.2.2))

/-- biblatex's sort key, computed once per entry, as its schemes name the
fields — `nty` (name, title, year) or `nyt` (name, year, title) — then the
key: the names each family name first (`useprefix=false` sorts `de Pome`
under P), the title and the year as written, lowercased. -/
def biblatexKey (titleFirst : Bool) (r : Resolved) : String × String × String × String :=
  let names := ((r.entry.field? "author").map fun a =>
    String.intercalate " " ((splitNames a).toList.map fun s =>
      let n := parseName s
      text (String.intercalate " " ([n.last, n.first].filter (!·.isEmpty))))).getD ""
  let title := ((r.entry.field? "title").map text).getD ""
  let (b, c) := if titleFirst then (title, citeYear r.entry) else (citeYear r.entry, title)
  (names.toLower, b.toLower, c.toLower, r.key)

/-- The order on biblatex's keys, field by field. -/
def biblatexCompare (a b : String × String × String × String) : Ordering :=
  (Ord.compare a.1 b.1).then ((Ord.compare a.2.1 b.2.1).then
    ((Ord.compare a.2.2.1 b.2.2.1).then (Ord.compare a.2.2.2 b.2.2.2)))

/-- The comparison a sort order names, over entries carrying their
first-citation position. Citation order compares the positions, which are
distinct by construction; author-year compares the label names, then the
year, then — the tiebreak totality forces — the key, so two entries by the
same authors in the same year still have one order; biblatex's schemes
compare their keys (`biblatexKey`). -/
def SortOrder.compare (so : SortOrder) (a b : Resolved) : Ordering :=
  match so with
  | .citation => Ord.compare a.position b.position
  | .authorYear => ayCompare (ayKey a) (ayKey b)
  | .nty => biblatexCompare (biblatexKey true a) (biblatexKey true b)
  | .nyt => biblatexCompare (biblatexKey false a) (biblatexKey false b)

/-- A merge sort over keys computed once per entry. -/
def sortByKey {κ : Type} (key : Resolved → κ) (cmp : κ → κ → Ordering) (xs : List Resolved) :
    List Resolved :=
  ((xs.map fun r => (key r, r)).mergeSort fun a b => cmp a.1 b.1 != .gt).map (·.2)

/-- The list sorted by the order's comparison, in `n log n` steps: a merge
sort (stable), over keys computed once per entry rather than once per
comparison — a thesis-sized list is thousands of entries, and the
insertion sort this replaces was quadratic in them. -/
def sortResolved (so : SortOrder) (xs : List Resolved) : List Resolved :=
  match so with
  | .citation => xs.mergeSort fun a b => decide (a.position ≤ b.position)
  | .authorYear => sortByKey ayKey ayCompare xs
  | .nty => sortByKey (biblatexKey true) biblatexCompare xs
  | .nyt => sortByKey (biblatexKey false) biblatexCompare xs

/-- What one key renders as, everywhere it is cited: its entry at its
1-based position in the reference list. -/
def Resolver := String → Option Resolved

/-- The label plainnat.bst's `calc.label` builds and its `forward.pass`
compares between entries: the label names a citation prints and the
year. -/
def labelOf (e : Entry) (biblatex : Bool := false) : String :=
  citeAuthors e biblatex ++ "(" ++ ((e.field? "year").map text).getD ""

/-- The letter of the `i`-th entry among those sharing a label: `a`, `b`,
… (`int.to.chr$` from `"a" chr.to.int$`). -/
def extraLetter (i : Nat) : String := String.singleton (Char.ofNat ('a'.toNat + i))

/-- The letters plainnat.bst's `forward.pass` and `reverse.pass` give a
reference list, and unsrtnat.bst's the same: the entries sharing a label
(`labelOf`) take `a`, `b`, … in list order, and an entry whose label is its
own takes none. Each label is computed once and grouped through a map, so
the letters cost one pass over the list, never a comparison per pair. -/
def extraLabels (rs : Array Resolved) (biblatex : Bool := false) : Array Resolved :=
  let labels := rs.map (labelOf ·.entry biblatex)
  let counts : Std.HashMap String Nat := labels.foldl (fun m l => m.insert l (m.getD l 0 + 1)) {}
  let ranks := (labels.foldl (fun (acc : Std.HashMap String Nat × Array Nat) l =>
    (acc.1.insert l (acc.1.getD l 0 + 1), acc.2.push (acc.1.getD l 0))) ({}, #[])).2
  rs.mapIdx fun i r =>
    { r with extra :=
        if counts.getD (labels[i]?.getD "") 0 < 2 then "" else extraLetter (ranks[i]?.getD 0) }

/-- The reference list a style builds from the cited entries: sorted by
the style's order, positions assigned by list index — so the numeric
marker IS the sort position, the fact `\cite` marks rest on — and each
entry's letter among those sharing its label (`extraLabels`). -/
def resolveEntries (style : Style) (cited : Array String)
    (find : String → Option Entry) (biblatex : Bool := false) : Array Resolved :=
  -- First-citation positions (1-based, in cited order) feed the sort;
  -- the final position is the index in the sorted list.
  let hits := cited.foldl (fun acc k =>
    match find k with
    | some e => acc.push { key := k, position := acc.size + 1, entry := e }
    | none => acc) #[]
  let sorted := sortResolved style.sort hits.toList
  extraLabels (sorted.toArray.mapIdx fun i r => { r with position := i + 1 }) biblatex

/-- The items a `\bibliography` block ships: each resolved entry formatted
per the style, marked by its position in numbers mode and by nothing in
author-year mode — natbib's `\@biblabel` is the number there and an
empty hanging label here. The date carries the entry's letter in
author-year mode (FUNCTION {format.date}); numbers mode's `\natexlab`
prints nothing. -/
def bibItems (p : CitePunct) (style : Style) (resolved : Array Resolved) :
    Array Ir.BibItem :=
  resolved.map fun r =>
    { key := r.key
      marker := if p.numbers then some (toString r.position) else none
      content := renderEntry style.names (style.steps r.entry) r.entry
        (if p.numbers then "" else r.extra) }

/-! ### The theorems the four-axis shape earns

Each axis being a pure function is what makes these statable; a
transcribed `.bst` has none of them. -/

/-- Numbering is the sort position: in numbers mode, the marker of the
reference list's `i`-th entry is its 1-based index in the sorted list —
the fact every `\cite` mark rests on, `positions_exact` below being the
half that says the positions the marks look up are those same indices.
Floats state the same vocabulary in `Ir.numberFloats_exact` — a label is
the index of first appearance in a sequence, `List.range'` both times —
but over a different data shape (a counter threaded through a tree walk,
not a `mapIdx` over a sorted list). Deliberately not unified: a shared
"consecutive assignment" lemma would leave each proof's hard part — here a
one-line `simp`, there the tree induction — untouched. -/
theorem bibItems_marker_exact (p : CitePunct) (style : Style) (resolved : Array Resolved)
    (h : p.numbers = true) (i : Nat) (hi : i < resolved.size) :
    (bibItems p style resolved)[i]?.bind (·.marker) =
      some (toString (resolved[i].position)) := by
  simp [bibItems, Array.getElem?_map, Array.getElem?_eq_getElem hi, h]

/-- The positions `resolveEntries` hands the marks are the 1-based indices
of the sorted list: position `i + 1` at index `i`, whatever the sort
order did. Together with `bibItems_marker_exact`, the numeric marker at
index `i` is `i + 1`. -/
theorem positions_exact (style : Style) (cited : Array String)
    (find : String → Option Entry) (i : Nat)
    (hi : i < (resolveEntries style cited find).size) :
    (resolveEntries style cited find)[i].position = i + 1 := by
  simp [resolveEntries, extraLabels] at hi ⊢

/-- The sorted list holds exactly the input's elements — the membership
half of "the emitted list is a permutation of the cited set". -/
theorem sortResolved_mem (so : SortOrder) (xs : List Resolved) (z : Resolved) :
    z ∈ sortResolved so xs ↔ z ∈ xs := by
  cases so <;> simp [sortResolved, sortByKey]

/-- The sorted list is exactly as long as the input: with `sortResolved_mem`
this is the counting half of the permutation claim. -/
theorem sortResolved_length (so : SortOrder) (xs : List Resolved) :
    (sortResolved so xs).length = xs.length := by
  cases so <;> simp [sortResolved, sortByKey]

/-- The comparison is total in the order-theoretic sense: two entries
always compare, one way or the other — `gt` one way implies not-`gt` the
other for citation order, whose comparison is over the distinct
first-citation positions. Author-year's chained string comparison owes the
same statement; it is the recorded remainder of this slice. -/
theorem compare_citation_asymm (a b : Resolved)
    (h : SortOrder.citation.compare a b = .gt) :
    SortOrder.citation.compare b a ≠ .gt := by
  simp [SortOrder.compare, Nat.compare_eq_gt] at h ⊢
  omega

/-- The sorted list is sorted: no element compares `gt` against a later
one, for citation order. (`Pairwise` over the comparison; author-year is
the recorded remainder beside `compare_citation_asymm`.) -/
theorem sortResolved_sorted_citation (xs : List Resolved) :
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
  | .role nm body => out.push (.role nm (resolveInlines p find #[] body.toList))
  | .link u body => out.push (.link u (resolveInlines p find #[] body.toList))
  | .decorated kind body =>
    out.push (.decorated kind (resolveInlines p find #[] body.toList))
  | .step n last body => out.push (.step n last (resolveInlines p find #[] body.toList))
  | .alt n last active otherwise =>
    out.push (.alt n last (resolveInlines p find #[] active.toList)
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

mutual

/-- Inline content carrying no citation, anywhere in its tree. -/
def citeFreeOne : Ir.Inline → Bool
  | .cite _ _ => false
  | .styled _ body => citeFreeList body.toList
  | .colored _ _ body => citeFreeList body.toList
  | .role _ body => citeFreeList body.toList
  | .link _ body => citeFreeList body.toList
  | .decorated _ body => citeFreeList body.toList
  | .step _ _ body => citeFreeList body.toList
  | .alt _ _ active otherwise =>
    citeFreeList active.toList && citeFreeList otherwise.toList
  | .footnote _ body => citeFreeList body.toList
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _
  | .label _ | .ref _ _ _ _
  | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _ | .pageNumber | .pageCount | .linebreak _ => true

def citeFreeList : List Ir.Inline → Bool
  | [] => true
  | x :: rest => citeFreeOne x && citeFreeList rest

end

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
    | .styled _ body | .colored _ _ body | .role _ body | .link _ body
    | .decorated kind body | .step _ _ body | .footnote _ body => simp [resolveInline]
    | .alt _ _ _ _ => simp [resolveInline]
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
theorem resolveInline_id (p : CitePunct) (find : Resolver)
    (out : Array Ir.Inline) (x : Ir.Inline) (h : citeFreeOne x = true) :
    resolveInline p find out x = out.push x := by
  match x with
  | .styled st body =>
    rw [citeFreeOne] at h
    rw [resolveInline, resolveInlines_id p find body.toList h]
  | .colored c nm body =>
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
  | .step n last body =>
    rw [citeFreeOne] at h
    rw [resolveInline, resolveInlines_id p find body.toList h]
  | .alt n last active otherwise =>
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

theorem resolveInlines_id (p : CitePunct) (find : Resolver)
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
def nociteOnly (content : Array Ir.Inline) : Bool :=
  content.any (fun x => match x with | .cite f _ => f.cmd == .nocite | _ => false) &&
    content.all fun x => match x with
      | .cite f _ => f.cmd == .nocite
      | .text s => s.all Char.isWhitespace
      | _ => false

mutual

/-- The block half of the rewrite: citations resolve wherever inline
content stands, each `\bibliography` marker takes the items the style
built, and a paragraph of `\nocite`s alone is dropped (`nociteOnly`). -/
-- conserves: none — resolution rewrites citation marks and fills the
-- reference list; `resolveInline_id` carries the off-citation identity.
private def resolveBlock (p : CitePunct) (find : Resolver)
    (items : Array Ir.BibItem) (out : Array Ir.Block) (b : Ir.Block) :
    Array Ir.Block :=
  match b with
  | .bibliography src declared _ => out.push (.bibliography src declared items)
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
  | .role nm body => out.push (.role nm (resolveBlocks p find items #[] body.toList))
  | .link target body => out.push (.link target (resolveBlocks p find items #[] body.toList))
  | .spaced g body => out.push (.spaced g (resolveBlocks p find items #[] body.toList))
  | .columns cols => out.push (.columns (resolveCols p find items #[] cols.toList))
  | .step n last body =>
    out.push (.step n last (resolveBlocks p find items #[] body.toList))
  | .alt n last active otherwise =>
    out.push (.alt n last (resolveBlocks p find items #[] active.toList)
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
def resolveDoc (p : CitePunct) (find : Resolver) (items : Array Ir.BibItem)
    (doc : Ir.Doc) : Ir.Doc :=
  Ir.mapDoc (resolveArr p find)
    (fun bs => resolveBlocks p find items #[] bs.toList) doc

/-- natbib's author-year label in a `\bibitem`'s optional argument
(natbib.sty `\NAT@parse`: `Jones et al.(1990)Jones, Baker, and Williams`):
the names before the parentheses and the year inside them. -/
def natbibLabel? (label : String) : Option (String × String) :=
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
def ownEntry (key : String) (label : Option (String × String)) : Entry :=
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
def ownList (p : CitePunct) (own : Array Ir.BibItem) :
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
    items := items.push
      { it with marker := if p.numbers then some (label.getD (toString n)) else none }
  return (p, resolved, items)

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
def analyse (sources : Array (String × String)) (doc : Ir.Doc) :
    CitePunct × Resolver × Array Ir.BibItem × Array Diag := Id.run do
  let requested := Ir.bibRefs doc
  let mut diags : Array Diag := #[]
  let mut entries : Array Entry := #[]
  let mut seen : Std.HashSet String := {}
  for src in requested do
    match sources.find? (·.1 == src) with
    | none => pure ()  -- the driver's missing-file diagnostic already fired
    | some (_, text) =>
      let parsed := parse text (monthMacros doc.info.locale.months)
      for (pos, msg) in parsed.errors do
        diags := diags.push (Diag.of .W0352 s!"malformed .bib entry: {msg}; \
          the entry is skipped and the rest of '{src}' is kept"
          (some ⟨src, pos⟩))
      for e in parsed.entries do
        unless seen.contains e.key do
          entries := entries.push e
          seen := seen.insert e.key
  let declared ← do
    match Ir.bibStyleName doc with
    | none => pure none
    | some name =>
      match Style.named name with
      | some s => pure (some s)
      | none =>
        let cites := if doc.natbib.isSome then ", and its citations as author-year ones" else ""
        diags := diags.push (Diag.of .W0353 s!"bibliography style '{name}' is not \
          one the engine knows; the reference list is set as 'unsrtnat'{cites}"
          (help := "styles known: unsrtnat, unsrt, plainnat, plain, abbrvnat, abbrv"))
        pure (some Style.unsrtnat)
  let p := CitePunct.ofDoc doc.natbib ((Ir.bibStyleName doc).bind (natbibRows.lookup ·))
    (declared.all (·.labels))
  -- biblatex sorts its list by its own schemes: nty for the numeric styles,
  -- nyt for the author-year ones (sorting=none keeps citation order).
  let style := declared.getD Style.unsrtnat
  let style := if p.biblatex && style.sort != .citation then
      { style with sort := if p.numbers then .nty else .nyt } else style
  let cited := expandStar entries (citedKeys doc)
  let shown := (citedKeys doc (·.cmd != .nocite)).foldl (·.insert ·) (∅ : Std.HashSet String)
  let byKey : Std.HashMap String Entry := entries.foldl (fun m e => m.insert e.key e) {}
  let findEntry (k : String) : Option Entry := byKey.get? k
  let own := Ir.ownBibItemsBlocks doc.body
  let (p, resolved, items) :=
    if own.isEmpty then
      let resolved := resolveEntries style cited findEntry p.biblatex
      (p, resolved, bibItems p style resolved)
    else ownList p own
  let byCite : Std.HashMap String Resolved := resolved.foldl (fun m r => m.insert r.key r) {}
  let find : Resolver := byCite.get?
  unless requested.isEmpty && own.isEmpty do
    for k in cited do
      if (find k).isNone then
        let (cmd, loss) := if shown.contains k then ("cite", "it shows as '?'")
          else ("nocite", "\\nocite adds nothing for it")
        diags := diags.push (Diag.of .W0351 s!"citation '{k}' has no entry in the \
          bibliography; {loss}"
          (help := if own.isEmpty then s!"add an entry with key '{k}' to the .bib file, \
            or fix the spelling in \\{cmd}"
            else s!"add \\bibitem\{{k}} to the reference list, or fix the spelling in \\{cmd}")
          (subject := some k))
  -- A `$…$` span the math parser cannot model sets as its floor (`formulaOf`):
  -- named once per spelling, as the elaborator names one in the body.
  let floors := if !own.isEmpty then #[] else items.foldl (fun acc it => Ir.foldInlines (fun acc x => match x with
    | .math _ src => if acc.contains src then acc else acc.push src
    | _ => acc) acc it.content) (#[] : Array String)
  for src in floors do
    diags := diags.push (Diag.of .W0012 s!"math in a reference-list entry is not \
      rendered yet; the formula sets as its text content" (subject := some ("math:" ++ src)))
  return (p, find, items, diags)

def apply (sources : Array (String × String)) (doc : Ir.Doc) : Ir.Doc × Array Diag :=
  match analyse sources doc with
  | (p, find, items, diags) => (resolveDoc p find items doc, diags)

/-! ## Resolution leaves no citation

The census fact `apply_no_cite` rests on two things: every node the rewrite
emits in a citation's place is text or a link over text
(`renderCite_plain`), and every other node passes through with only its
body rewritten. Stated over the census fold (`Ir.pendingStep`) with the
accumulator generalised, so each walk shape is one induction. -/

/-- A node the citation renderer may emit: text, or a link whose body is
text. Neither carries a pending leaf. -/
private def plainCite : Ir.Inline → Bool
  | .text _ => true
  | .link _ body => body.all fun x => match x with | .text _ => true | _ => false
  | _ => false

private theorem foldInlineList_text (acc : Array Ir.Unresolved) :
    ∀ l : List Ir.Inline,
      (∀ x ∈ l, (match x with | .text _ => true | _ => false) = true) →
      Ir.foldInlineList Ir.pendingStep acc l = acc := by
  intro l
  induction l generalizing acc with
  | nil => intro _; rfl
  | cons x rest ih =>
    intro h
    have hx := h x (List.mem_cons_self ..)
    have hrest := fun y hy => h y (List.mem_cons_of_mem _ hy)
    cases x <;> simp only at hx <;> try exact absurd hx (by decide)
    rw [Ir.foldInlineList, Ir.foldInline, ih _ hrest]
    simp [Ir.pendingStep, Ir.pendingLeaf]

private theorem foldInline_plain (acc : Array Ir.Unresolved) (x : Ir.Inline)
    (h : plainCite x = true) : Ir.foldInline Ir.pendingStep acc x = acc := by
  cases x <;> simp only [plainCite] at h <;> try exact absurd h (by decide)
  case text s => simp [Ir.foldInline, Ir.pendingStep, Ir.pendingLeaf]
  case link u body =>
    rw [Ir.foldInline, foldInlineList_text]
    · simp [Ir.pendingStep, Ir.pendingLeaf]
    · intro y hy
      exact Array.all_eq_true_iff_forall_mem.mp h y (Array.mem_def.mpr hy)

private theorem foldInlineList_plain (acc : Array Ir.Unresolved) :
    ∀ l : List Ir.Inline, (∀ x ∈ l, plainCite x = true) →
      Ir.foldInlineList Ir.pendingStep acc l = acc := by
  intro l
  induction l generalizing acc with
  | nil => intro _; rfl
  | cons x rest ih =>
    intro h
    rw [Ir.foldInlineList, foldInline_plain acc x (h x (List.mem_cons_self ..))]
    exact ih acc fun y hy => h y (List.mem_cons_of_mem _ hy)

private theorem emit_plain (out : Array Ir.Inline) (s : String)
    (h : out.all plainCite = true) : (emit out s).all plainCite = true := by
  unfold emit
  split
  · exact h
  · rw [Array.all_push, h]; rfl

private theorem emitLink_plain (out : Array Ir.Inline) (anchor s : String)
    (h : out.all plainCite = true) : (emitLink out anchor s).all plainCite = true := by
  rw [emitLink, Array.all_push, h]; simp [plainCite]

private theorem citeStep_plain (p : CitePunct) (f : Ir.CiteForm) (s : Switches) (n : Nat)
    (acc : CiteAcc) (o : Option Resolved) (h : acc.out.all plainCite = true) :
    (citeStep p f s n acc o).out.all plainCite = true := by
  cases o with
  | none => exact emit_plain _ _ h
  | some r => exact emitLink_plain _ _ _ (emit_plain _ _ h)

private theorem finish_plain (p : CitePunct) (f : Ir.CiteForm) (s : Switches)
    (acc : CiteAcc) (h : acc.out.all plainCite = true) :
    (finish p f s acc).all plainCite = true := by
  refine emit_plain _ _ ?_
  rw [Array.all_append, emit_plain _ _ (by simp), h]; rfl

private theorem flushHeld_plain (out : Array Ir.Inline) (h : Option (String × Resolved))
    (hout : out.all plainCite = true) : (flushHeld out h).all plainCite = true := by
  cases h with
  | none => exact hout
  | some ph => exact emitLink_plain _ _ _ (emit_plain _ _ hout)

private theorem runStep_plain (p : CitePunct) (st : RunAcc) (o : Option Resolved)
    (h : st.acc.out.all plainCite = true) : (runStep p st o).acc.out.all plainCite = true := by
  cases o with
  | none => exact emit_plain _ _ (flushHeld_plain _ _ h)
  | some r =>
    simp only [runStep]
    split
    · exact h
    · exact emitLink_plain _ _ _ (emit_plain _ _ (flushHeld_plain _ _ h))

private theorem compressRuns_plain (p : CitePunct) (parts : Array (Option Resolved)) :
    (compressRuns p parts).out.all plainCite = true := by
  unfold compressRuns
  refine flushHeld_plain _ _ ?_
  exact Array.foldl_induction (motive := fun _ (a : RunAcc) => a.acc.out.all plainCite = true)
    (by simp) (fun _ b hb => runStep_plain p b _ hb)

/-- The renderer emits text and links over text only. -/
theorem renderCite_plain (p : CitePunct) (f : Ir.CiteForm)
    (parts : Array (Option Resolved)) :
    (renderCite p f parts).all plainCite = true := by
  unfold renderCite
  split
  · exact emit_plain _ _ (by simp)
  split
  · exact emit_plain _ _ (by simp)
  split
  · simp
  · refine finish_plain _ _ _ _ ?_
    split
    · exact compressRuns_plain p _
    · exact Array.foldl_induction (motive := fun _ (a : CiteAcc) => a.out.all plainCite = true)
        (by simp) (fun _ b hb => citeStep_plain p f _ _ b _ hb)

/-- A rendered citation adds nothing to the pending census. -/
private theorem renderCite_pending (p : CitePunct) (f : Ir.CiteForm)
    (parts : Array (Option Resolved)) (acc : Array Ir.Unresolved) :
    Ir.foldInlineList Ir.pendingStep acc (renderCite p f parts).toList = acc :=
  foldInlineList_plain acc _ fun x hx =>
    Array.all_eq_true_iff_forall_mem.mp (renderCite_plain p f parts) x
      (Array.mem_def.mpr hx)

mutual

/-- Resolution's census, inline face: whatever a rewritten node adds to the
pending census is not a citation — the citation arm emits plain content
(`renderCite_pending`), every other node keeps its own leaf. -/
theorem resolveInline_pending (p : CitePunct) (find : Resolver) (x : Ir.Inline) :
    ∀ (acc : Array Ir.Unresolved) (q : Ir.Unresolved),
      q ∈ Ir.foldInlineList Ir.pendingStep acc (resolveInline p find #[] x).toList →
      q ∈ acc ∨ q.isCite = false := by
  match x with
  | .styled _ body | .colored _ _ body | .role _ body | .link _ body
  | .decorated kind body | .step _ _ body | .footnote _ body =>
    intro acc q h
    simp only [resolveInline, Array.toList_push, List.nil_append,
      Ir.foldInlineList, Ir.foldInline, Ir.pendingStep, Ir.pendingLeaf,
      Array.append_empty] at h
    exact resolveInlines_pending p find body.toList acc q h
  | .alt _ _ active otherwise =>
    intro acc q h
    simp only [resolveInline, Array.toList_push, List.nil_append,
      Ir.foldInlineList, Ir.foldInline, Ir.pendingStep, Ir.pendingLeaf,
      Array.append_empty] at h
    rcases resolveInlines_pending p find otherwise.toList _ q h with h' | hc
    · exact resolveInlines_pending p find active.toList acc q h'
    · exact .inr hc
  | .cite form keys =>
    intro acc q h
    simp only [resolveInline, Array.empty_append, renderCite_pending] at h
    exact .inl h
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

theorem resolveInlines_pending (p : CitePunct) (find : Resolver) (xs : List Ir.Inline) :
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

mutual

/-- Resolution's census, block face, generalised over the output prefix:
whatever the rewritten block adds to the census beyond what the prefix
already contributed is not a citation. -/
theorem resolveBlock_pending (p : CitePunct) (find : Resolver) (items : Array Ir.BibItem)
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
  | .link _ body | .spaced _ body | .step _ _ body | .only _ body | .nav _ body | .note body =>
    intro out acc q h
    simp only [resolveBlock, Ir.foldBlockList_push, Ir.foldBlock] at h
    exact resolveBlocks_pending p find items body.toList #[] _ q h
  | .alt _ _ active otherwise =>
    intro out acc q h
    simp only [resolveBlock, Ir.foldBlockList_push, Ir.foldBlock] at h
    rcases resolveBlocks_pending p find items otherwise.toList #[] _ q h with h' | hc
    · exact resolveBlocks_pending p find items active.toList #[] _ q h'
    · exact .inr hc
  | .titled _ title body | .frame title _ _ _ body =>
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
  | .bibliography _ _ _ | .verbatim _ _ _ | .setPalette _ | .setTokens _ | .pagebreak
  | .rule _ _ _ | .picture _ =>
    intro out acc q h
    simp only [resolveBlock, Ir.foldBlockList_push, Ir.foldBlock] at h
    exact .inl h

theorem resolveBlocks_pending (p : CitePunct) (find : Resolver) (items : Array Ir.BibItem)
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

theorem resolveItems_pending (p : CitePunct) (find : Resolver) (items : Array Ir.BibItem)
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

theorem resolveCols_pending (p : CitePunct) (find : Resolver) (items : Array Ir.BibItem)
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
theorem resolveDoc_no_cite (p : CitePunct) (find : Resolver) (items : Array Ir.BibItem)
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
theorem apply_no_cite (sources : Array (String × String)) (doc : Ir.Doc) :
    ∀ u ∈ Ir.pendingNodes (apply sources doc).1, u.isCite = false := by
  intro u hu
  unfold apply at hu
  rcases h : analyse sources doc with ⟨p, find, items, diags⟩
  rw [h] at hu
  exact resolveDoc_no_cite p find items doc u hu


end LeanTex.Core.Bib
