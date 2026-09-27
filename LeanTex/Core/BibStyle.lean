import LeanTex.Core.Bib
import LeanTex.Core.Ir

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
value. -/
structure CitePunct where
  numbers : Bool := false
  «open» : String := "("
  close : String := ")"
  sep : String := ";"
  aysep : String := ","
  yysep : String := ","
  notesep : String := ", "
  deriving Repr, BEq, Inhabited

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

/-- One declaration over the punctuation and natbib's `\bibstyle` door, the
door a bibliography style's own punctuation comes through at
`\begin{document}`: `nobibstyle` closes it and `bibstyle` reopens it
(natbib's option names), a keyword updates the punctuation, and anything
else leaves both as they were — natbib reads an unknown keyword as
nothing. -/
def CitePunct.step (st : CitePunct × Bool) (d : String) : CitePunct × Bool :=
  if d == "nobibstyle" then (st.1, false)
  else if d == "bibstyle" then (st.1, true)
  else match citeKeywords.lookup d with
    | some f => (f st.1, st.2)
    | none => st

/-- How the reference list is ordered: `citation` keeps first-citation
order (the "unsrt" in `unsrtnat`); `authorYear` sorts by the label names,
then year, then key — the tiebreak that keeps the comparison total when
two entries share authors and year. -/
inductive SortOrder where
  | citation
  | authorYear
  deriving Repr, BEq, Inhabited

/-- One field of a reference-list entry, rendered by kind: the field kind
owes its own dressing (the `In` before a booktitle, the `pages` word, the
`12(3):45–67` join), so a per-type template never exists — an entry type
contributes only an *order* over these kinds. `title` carries its one
per-type property (plainnat.bst: `format.btitle` emphasizes a book title
and leaves its case; `format.title` sets an article title plain in
sentence case), a parameter of the field, not a template of the type. -/
inductive Field where
  | authors
  /-- Emphasized titles keep their case; plain titles take sentence case
  (plainnat.bst FUNCTION {format.btitle} vs {format.title}). -/
  | title (emph : Bool)
  /-- The journal name, emphasized (plainnat.bst FUNCTION {article}). -/
  | journal
  /-- `12(3):45–67`: volume, parenthesized number, `:pages` (plainnat.bst
  FUNCTION {format.vol.num.pages}). -/
  | volumePages
  /-- `In *Booktitle*` (plainnat.bst FUNCTION {format.in.ed.booktitle}). -/
  | booktitle
  /-- `pages 45–67` spelled out (plainnat.bst FUNCTION {format.pages}). -/
  | pages
  | publisher
  | address
  /-- `Third edition` as written plus the word (plainnat.bst FUNCTION
  {format.edition}). -/
  | edition
  | howpublished
  /-- `PhD thesis, School` (plainnat.bst FUNCTION {phdthesis}). -/
  | school
  /-- `Technical report number, Institution` (plainnat.bst FUNCTION
  {format.tr.number}). -/
  | reportNumber
  | institution
  | note
  /-- `month year` when the month is there (plainnat.bst FUNCTION
  {format.date}). -/
  | year
  /-- `doi: value`, linked to `https://doi.org/value` (plainnat.bst
  FUNCTION {format.doi}). -/
  | doi
  /-- `URL value`, linked (plainnat.bst FUNCTION {format.url}). -/
  | url
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
  /-- The punctuation natbib's `\bibstyle@<name>` row gives the style
  (natbib.sty): a `\bibpunct` that sets every value, so an open door
  replaces whatever was declared before it. -/
  punct : CitePunct
  sort : SortOrder
  /-- Sentences of fields per entry kind: fields inside a sentence join
  with `, `, sentences close with `.` — the shared punctuation model every
  type renders through. -/
  order : String → Array (Array Field)
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
the author field through `labelNames`, or the key itself when no author
is there — visible, never silently empty. -/
def citeAuthors (e : Entry) : String :=
  match e.field? "author" with
  | some a => labelNames a
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
position in the reference list. -/
structure Resolved where
  key : String
  position : Nat
  entry : Entry
  deriving Repr

/-- The full author list natbib's starred forms print (`\citet*`), or the
key when no author is there, as `citeAuthors` does. -/
def citeFullAuthors (e : Entry) : String :=
  match e.field? "author" with
  | some a => fullNames a
  | none => e.key

/-- What one key prints: its names and year, its names alone, or its year
alone — natbib.sty's `\NAT@ctype` 0, 1 and 2. -/
private inductive CitePart where
  | both
  | names
  | year
  deriving BEq

/-- The loop's state between keys: the output so far, the separator the
last key left for the next (natbib.sty `\@citea`), the last key's names —
a key repeating them prints only its year — and whether the last key
printed a year, which is what closes a textual citation's bracket. -/
private structure CiteAcc where
  out : Array Ir.Inline := #[]
  citea : String := ""
  last : Option String := none
  dated : Bool := false

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
    | .alt | .alp | .author | .year | .num => false
  { numeric := p.numbers || f.cmd == .num
    wrap := match f.cmd with
      | .paren | .alp | .yearPar | .num | .text => true
      | .auto => p.numbers
      | .textual | .alt | .author | .year => false
    part := match f.cmd with
      | .author => .names
      | .year | .yearPar => .year
      | .textual | .paren | .auto | .alt | .alp | .num | .text => .both
    op := if brackets then p.open else ""
    cl := if brackets then p.close else "" }

/-- One key under natbib's loop (natbib.sty `\NAT@citex`, `\NAT@citexnum`
in numbers mode): the separator the previous key left, this key's piece
linked to its entry, and the separator it leaves. natbib capitalizes names
only in author-year mode, and a key repeating the previous key's names
prints only its year (`yysep`). An unresolvable key prints `?` in its
place with the separators a resolved one would have. -/
private def citeStep (p : CitePunct) (f : Ir.CiteForm) (s : Switches) (acc : CiteAcc) :
    Option Resolved → CiteAcc
  | none => { out := emit acc.out (acc.citea ++ "?"), citea := p.sep ++ " " }
  | some r =>
    let names := if f.full then citeFullAuthors r.entry else citeAuthors r.entry
    let names := if f.up && !s.numeric then upFirst names else names
    let year := citeYear r.entry
    let mark := if s.numeric then toString r.position else year
    let pre := if f.pre.isEmpty then "" else f.pre ++ " "
    let same := acc.last == some names
    -- (what precedes the linked piece, the piece, the separator left behind)
    let t : String × String × String := match s.part with
      | .names => (acc.citea, names, p.sep ++ " ")
      | .year => (acc.citea, year, p.sep ++ " ")
      | .both =>
        if s.wrap then
          if s.numeric then (acc.citea, mark, p.sep ++ " ")
          else if same then (p.yysep ++ " ", year, p.sep ++ " ")
          else (acc.citea, s!"{names}{p.aysep} {year}", p.sep ++ " ")
        else
          (if same then p.yysep ++ " " ++ (if s.numeric then pre else "")
            else acc.citea ++ names ++ " " ++ s.op ++ pre, mark, s.cl ++ p.sep ++ " ")
    { out := emitLink (emit acc.out t.1) (anchorOf r.key) t.2.1
      citea := t.2.2
      last := some names
      dated := true }

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

/-- A whole citation under natbib's punctuation, per its command (natbib.sty's
command table): `\citep` wraps its keys in the brackets with `sep` between
them (`[Doe, 2024; Roe, 2020]`, `[1, 2]`), `\citet` brackets each year
(`Doe [2024]`), the `alt`/`alp` forms drop the brackets, `\citeauthor` and
`\citeyear` print one part, `\citenum` the list position in either mode,
and `\citetext` its note between the brackets. The output is text and
links over text only — no `.cite`, no `.ref` — which is `renderCite_plain`,
the leaf fact `apply_no_cite` rests on. -/
def renderCite (p : CitePunct) (f : Ir.CiteForm) (parts : Array (Option Resolved)) :
    Array Ir.Inline :=
  if f.cmd == .text then emit #[] (p.open ++ f.pre ++ p.close)
  else finish p f (switches p f) (parts.foldl (citeStep p f (switches p f)) {})

/-- An en dash between page numbers: `45--67` and `45-67` both print
`45–67`, the range dash `.bib` files spell both ways. `text` already
turns `--` into an en dash; a single `-` between digits is promoted here. -/
private def pageRange (v : String) : String :=
  String.intercalate "–" (((text v).splitOn "-").filter (!·.isEmpty))

/-- One field of one entry, by kind: THE field renderer — every entry type
renders through this one function, and what varies per type is only the
order that calls it. An absent field renders empty and its sentence slot
closes over it. -/
def renderField (nf : NameFormat) (e : Entry) : Field → Array Ir.Inline
  | .authors =>
    match e.field? "author" with
    | some a => #[.text (nf.renderList a)]
    | none =>
      -- plainnat falls back to editors before giving up (format.authors
      -- then format.editors in FUNCTION {book}).
      match e.field? "editor" with
      | some ed => #[.text (nf.renderList ed ++ ", editors")]
      | none => #[]
  | .title emph =>
    match e.field? "title" with
    | some t =>
      if emph then #[.styled .emph #[.text (text t)]]
      else #[.text (text (sentenceCase t))]
    | none => #[]
  | .journal =>
    match e.field? "journal" with
    | some j => #[.styled .emph #[.text (text j)]]
    | none => #[]
  | .volumePages =>
    let vol := (e.field? "volume").map text
    let num := (e.field? "number").map text
    let pg := (e.field? "pages").map pageRange
    match vol, num, pg with
    | none, none, none => #[]
    | _, _, _ =>
      let v := vol.getD ""
      let n := match num with | some n => s!"({n})" | none => ""
      let p := match pg with | some p => s!":{p}" | none => ""
      #[.text (v ++ n ++ p)]
  | .booktitle =>
    match e.field? "booktitle" with
    | some b => #[.text "In ", .styled .emph #[.text (text b)]]
    | none => #[]
  | .pages =>
    match e.field? "pages" with
    | some p => #[.text s!"pages {pageRange p}"]
    | none => #[]
  | .publisher =>
    match e.field? "publisher" with
    | some p => #[.text (text p)]
    | none => #[]
  | .address =>
    match e.field? "address" with
    | some a => #[.text (text a)]
    | none => #[]
  | .edition =>
    match e.field? "edition" with
    | some ed => #[.text (text ed ++ " edition")]
    | none => #[]
  | .howpublished =>
    match e.field? "howpublished" with
    | some h => #[.text (text h)]
    | none => #[]
  | .school =>
    match e.field? "school" with
    | some s => #[.text s!"PhD thesis, {text s}"]
    | none => #[.text "PhD thesis"]
  | .reportNumber =>
    match e.field? "number" with
    | some n => #[.text s!"Technical report {text n}"]
    | none => #[.text "Technical report"]
  | .institution =>
    match e.field? "institution" with
    | some i => #[.text (text i)]
    | none => #[]
  | .note =>
    match e.field? "note" with
    | some n => #[.text (text n)]
    | none => #[]
  | .year =>
    match e.field? "year" with
    | some y =>
      match e.field? "month" with
      | some m => #[.text (text m ++ " " ++ text y)]
      | none => #[.text (text y)]
    | none => #[]
  | .doi =>
    match e.field? "doi" with
    | some d => #[.text "doi: ", .link ("https://doi.org/" ++ text d) #[.text (text d)]]
    | none => #[]
  | .url =>
    match e.field? "url" with
    | some u => #[.text "URL ", .link (text u) #[.text (text u)]]
    | none => #[]

/-- The sentences of fields each entry kind contributes — the whole of what
an entry type is under this decomposition. The six orders transcribe
plainnat.bst's FUNCTION {article}, {inproceedings}, {book}, {misc},
{phdthesis}, {techreport}; an unknown kind takes `misc`'s order, the
catch-all `.bst` files also route through. -/
def standardOrder (kind : String) : Array (Array Field) :=
  match kind with
  | "article" =>
    #[#[.authors], #[.title false],
      #[.journal, .volumePages, .year], #[.doi, .url], #[.note]]
  | "inproceedings" | "conference" =>
    #[#[.authors], #[.title false],
      #[.booktitle, .pages, .year], #[.doi, .url], #[.note]]
  | "book" =>
    #[#[.authors], #[.title true],
      #[.publisher, .address, .edition, .year], #[.note]]
  | "phdthesis" =>
    #[#[.authors], #[.title true], #[.school, .address, .year], #[.note]]
  | "techreport" =>
    #[#[.authors], #[.title false],
      #[.reportNumber, .institution, .address, .year], #[.note]]
  | _ =>
    #[#[.authors], #[.title false],
      #[.howpublished, .year], #[.doi, .url], #[.note]]

/-- One reference-list entry through the shared punctuation model: fields
of a sentence join with `, `, each nonempty sentence closes with `.`, and
a sentence whose fields are all absent leaves nothing behind. -/
def renderEntry (nf : NameFormat) (order : Array (Array Field)) (e : Entry) :
    Array Ir.Inline := Id.run do
  let mut out : Array Ir.Inline := #[]
  for sentence in order do
    let mut sent : Array Ir.Inline := #[]
    let mut firstField := true
    for f in sentence do
      let r := renderField nf e f
      unless r.isEmpty do
        unless firstField do sent := sent.push (.text ", ")
        firstField := false
        sent := sent ++ r
    unless sent.isEmpty do
      unless out.isEmpty do out := out.push (.text " ")
      out := (out ++ sent).push (.text ".")
  return out

/-- natbib's `\bibstyle@plainnat` row, which `abbrvnat` and `unsrtnat`
share (natbib.sty: `\bibpunct{[}{]}{,}{a}{,}{,}`): author-year, square
brackets, a comma between citations. -/
def natPunct : CitePunct := { «open» := "[", close := "]", sep := "," }

/-- natbib's `\bibstyle@plain` row, which `abbrv` and `unsrt` share
(`\bibpunct{[}{]}{,}{n}{}{,}`): numbers in square brackets, LaTeX's own
`\cite` too (latex.ltx `\@cite`, `[1, 2]`). These styles write no
author-year label into a `\bibitem`, so natbib reads them in numbers mode
whatever was declared. -/
def latexPunct : CitePunct :=
  { numbers := true, «open» := "[", close := "]", sep := ",", aysep := "" }

/-- `unsrtnat`: the reference list in first-citation order (the "unsrt"),
the standard field orders, full names, natbib's author-year row — what
`unsrtnat.bst` is, as one record. -/
def Style.unsrtnat : Style where
  punct := natPunct
  sort := .citation
  order := standardOrder
  names := {}

/-- `plainnat`: the same fields and names, the list sorted by author then
year (natbib manual §4: plainnat is the author-year companion of plain). -/
def Style.plainnat : Style where
  punct := natPunct
  sort := .authorYear
  order := standardOrder
  names := {}

/-- `plain`: what the record model buys — plain.bst is numbers over an
author-sorted list, zero new code, only another pairing of the axes. -/
def Style.plain : Style where
  punct := latexPunct
  sort := .authorYear
  order := standardOrder
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
natbib's `\bibstyle` door stays open, the declared style's row replaces
them all at `\begin{document}`, and a style that writes no author-year
labels puts natbib in numbers mode whatever was declared (natbib.sty
reading a `\bibitem` without one). A document that declares no style has
no row to apply. -/
def CitePunct.ofDoc (natbib : Option (Array String)) (style : Option Style) : CitePunct :=
  match natbib with
  | none => latexPunct
  | some decls =>
    let (p, door) := decls.foldl CitePunct.step ({}, true)
    match style with
    | none => p
    | some s =>
      let p := if door then s.punct else p
      if s.punct.numbers then { p with numbers := true } else p

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

/-- First-citation order: the keys the document cites, in order of first
appearance, each once — the sequence citation-order lists are sorted by
and numeric labels index into. A leaf projection of `Ir.foldDoc`, the one
collect traversal, over every region `resolveDoc` rewrites. -/
def citedKeys (doc : Ir.Doc) : Array String :=
  Ir.foldDoc
    (fun out x => match x with
      | .cite _ keys =>
        keys.foldl (fun out k => if out.contains k then out else out.push k) out
      | _ => out) #[] doc

/-- The comparison a sort order names, over entries carrying their
first-citation position. Citation order compares the positions, which are
distinct by construction; author-year compares the label names, then the
year, then — the tiebreak totality forces — the key, so two entries by the
same authors in the same year still have one order. -/
def SortOrder.compare (so : SortOrder) (a b : Resolved) : Ordering :=
  match so with
  | .citation => Ord.compare a.position b.position
  | .authorYear =>
    (Ord.compare (citeAuthors a.entry).toLower (citeAuthors b.entry).toLower).then
      ((Ord.compare (citeYear a.entry) (citeYear b.entry)).then
        (Ord.compare a.key b.key))

/-- Insertion sort by the order's comparison: stable, and small enough to
prove things about — the list is the cited entries, dozens at most. -/
def sortResolved (so : SortOrder) (xs : List Resolved) : List Resolved :=
  match xs with
  | [] => []
  | x :: rest => insertResolved so x (sortResolved so rest)
where
  insertResolved (so : SortOrder) (x : Resolved) : List Resolved → List Resolved
    | [] => [x]
    | y :: rest =>
      match so.compare x y with
      | .gt => y :: insertResolved so x rest
      | _ => x :: y :: rest

/-- What one key renders as, everywhere it is cited: its entry at its
1-based position in the reference list. -/
def Resolver := String → Option Resolved

/-- The reference list a style builds from the cited entries: sorted by
the style's order, positions assigned by list index — so the numeric
marker IS the sort position, the fact `\cite` marks rest on. -/
def resolveEntries (style : Style) (cited : Array String)
    (find : String → Option Entry) : Array Resolved :=
  -- First-citation positions (1-based, in cited order) feed the sort;
  -- the final position is the index in the sorted list.
  let hits := cited.foldl (fun acc k =>
    match find k with
    | some e => acc.push { key := k, position := acc.size + 1, entry := e }
    | none => acc) #[]
  let sorted := sortResolved style.sort hits.toList
  (sorted.toArray.mapIdx fun i r => { r with position := i + 1 })

/-- The items a `\bibliography` block ships: each resolved entry formatted
per the style, marked by its position in numbers mode and by nothing in
author-year mode — natbib's `\@biblabel` is the number there and an
empty hanging label here. -/
def bibItems (p : CitePunct) (style : Style) (resolved : Array Resolved) :
    Array Ir.BibItem :=
  resolved.map fun r =>
    { key := r.key
      marker := if p.numbers then some (toString r.position) else none
      content := renderEntry style.names (style.order r.entry.kind) r.entry }

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
  simp [resolveEntries] at hi ⊢

/-- Insertion keeps every element: what goes in comes out, nothing else.
The membership half of "the emitted list is a permutation of the cited
set". -/
theorem insertResolved_mem (so : SortOrder) (x : Resolved) (ys : List Resolved)
    (z : Resolved) :
    z ∈ sortResolved.insertResolved so x ys ↔ (z = x ∨ z ∈ ys) := by
  induction ys with
  | nil => simp [sortResolved.insertResolved]
  | cons y rest ih =>
    rw [sortResolved.insertResolved]
    split
    · simp only [List.mem_cons, ih, or_left_comm]
    · simp only [List.mem_cons]

/-- The sorted list holds exactly the input's elements. -/
theorem sortResolved_mem (so : SortOrder) (xs : List Resolved) (z : Resolved) :
    z ∈ sortResolved so xs ↔ z ∈ xs := by
  induction xs with
  | nil => simp [sortResolved]
  | cons x rest ih =>
    rw [sortResolved, insertResolved_mem, ih, List.mem_cons]

/-- The sorted list is exactly as long as the input: with `sortResolved_mem`
this is the counting half of the permutation claim. -/
theorem sortResolved_length (so : SortOrder) (xs : List Resolved) :
    (sortResolved so xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    rw [sortResolved, insertResolved_length, ih, List.length_cons]
where
  insertResolved_length (so : SortOrder) (x : Resolved) (ys : List Resolved) :
      (sortResolved.insertResolved so x ys).length = ys.length + 1 := by
    induction ys with
    | nil => rfl
    | cons y rest ih =>
      rw [sortResolved.insertResolved]
      split
      · simp [ih]
      · rfl

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
  induction xs with
  | nil => exact .nil
  | cons x rest ih => exact insert_sorted x (sortResolved .citation rest) ih
where
  le_of_not_gt (a b : Resolved) (h : SortOrder.citation.compare a b ≠ .gt) :
      a.position ≤ b.position := by
    simp [SortOrder.compare, Nat.compare_eq_gt] at h
    omega
  not_gt_of_le (a b : Resolved) (h : a.position ≤ b.position) :
      SortOrder.citation.compare a b ≠ .gt := by
    simp [SortOrder.compare, Nat.compare_eq_gt]
    omega
  insert_sorted (x : Resolved) (ys : List Resolved)
      (hs : ys.Pairwise (fun a b => SortOrder.citation.compare a b ≠ .gt)) :
      (sortResolved.insertResolved .citation x ys).Pairwise
        (fun a b => SortOrder.citation.compare a b ≠ .gt) := by
    induction ys with
    | nil => exact .cons (by simp) .nil
    | cons y rest ih =>
      rw [sortResolved.insertResolved]
      rcases hs with - | ⟨hy, hrest⟩
      split
      · rename_i hgt
        refine .cons ?_ (ih hrest)
        intro z hz
        rw [insertResolved_mem] at hz
        rcases hz with rfl | hz
        · exact not_gt_of_le y z (Nat.le_of_lt (by
            simp [SortOrder.compare, Nat.compare_eq_gt] at hgt
            omega))
        · exact hy z hz
      · rename_i hng
        refine .cons ?_ (.cons hy hrest)
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hng
        · exact not_gt_of_le x z (Nat.le_trans
            (le_of_not_gt x y hng) (le_of_not_gt y z (hy z hz)))

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
  | .underline body => out.push (.underline (resolveInlines p find #[] body.toList))
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
  | .strut h => out.push (.strut h)
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
  | .underline body => citeFreeList body.toList
  | .step _ _ body => citeFreeList body.toList
  | .alt _ _ active otherwise =>
    citeFreeList active.toList && citeFreeList otherwise.toList
  | .footnote _ body => citeFreeList body.toList
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _
  | .label _ | .ref _ _ _ _
  | .fill | .strut _ | .pageNumber | .pageCount | .linebreak _ => true

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
    | .underline body | .step _ _ body | .footnote _ body => simp [resolveInline]
    | .alt _ _ _ _ => simp [resolveInline]
    | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _
    | .label _ | .ref _ _ _ _
    | .fill | .strut _ | .pageNumber | .pageCount | .linebreak _ =>
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
  | .underline body =>
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
  | .fill | .strut _ | .pageNumber | .pageCount | .linebreak _ =>
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

mutual

/-- The block half of the rewrite: citations resolve wherever inline
content stands, and each `\bibliography` marker takes the items the style
built. -/
-- conserves: none — resolution rewrites citation marks and fills the
-- reference list; `resolveInline_id` carries the off-citation identity.
private def resolveBlock (p : CitePunct) (find : Resolver)
    (items : Array Ir.BibItem) (out : Array Ir.Block) (b : Ir.Block) :
    Array Ir.Block :=
  match b with
  | .bibliography src declared _ => out.push (.bibliography src declared items)
  | .para content => out.push (.para (resolveArr p find content))
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
  | .table cols pl pr rows rules =>
    out.push (.table cols pl pr
      (rows.map fun row => row.map (resolveArr p find)) rules)
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
        unless entries.any (·.key == e.key) do
          entries := entries.push e
  let declared ← do
    match Ir.bibStyleName doc with
    | none => pure none
    | some name =>
      match Style.named name with
      | some s => pure (some s)
      | none =>
        diags := diags.push (Diag.of .W0353 s!"bibliography style '{name}' is not \
          one the engine knows; the reference list is set as 'unsrtnat'"
          (help := "styles known: unsrtnat, unsrt, plainnat, plain, abbrvnat, abbrv"))
        pure (some Style.unsrtnat)
  let style := declared.getD Style.unsrtnat
  let p := CitePunct.ofDoc doc.natbib declared
  let cited := citedKeys doc
  let findEntry (k : String) : Option Entry := (entries.find? (·.key == k)).map id
  unless requested.isEmpty do
    for k in cited do
      if (findEntry k).isNone then
        diags := diags.push (Diag.of .W0351 s!"citation '{k}' has no entry in the \
          bibliography; it shows as '?'"
          (help := s!"add an entry with key '{k}' to the .bib file, or fix the \
            spelling in \\cite")
          (subject := some k))
  let resolved := resolveEntries style cited findEntry
  let find : Resolver := fun k => resolved.find? (·.key == k)
  return (p, find, bibItems p style resolved, diags)

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

private theorem citeStep_plain (p : CitePunct) (f : Ir.CiteForm) (s : Switches)
    (acc : CiteAcc) (o : Option Resolved) (h : acc.out.all plainCite = true) :
    (citeStep p f s acc o).out.all plainCite = true := by
  cases o with
  | none => exact emit_plain _ _ h
  | some r => exact emitLink_plain _ _ _ (emit_plain _ _ h)

private theorem finish_plain (p : CitePunct) (f : Ir.CiteForm) (s : Switches)
    (acc : CiteAcc) (h : acc.out.all plainCite = true) :
    (finish p f s acc).all plainCite = true := by
  refine emit_plain _ _ ?_
  rw [Array.all_append, emit_plain _ _ (by simp), h]; rfl

/-- The renderer emits text and links over text only. -/
theorem renderCite_plain (p : CitePunct) (f : Ir.CiteForm)
    (parts : Array (Option Resolved)) :
    (renderCite p f parts).all plainCite = true := by
  unfold renderCite
  split
  · exact emit_plain _ _ (by simp)
  · refine finish_plain _ _ _ _ ?_
    exact Array.foldl_induction (motive := fun _ (a : CiteAcc) => a.out.all plainCite = true)
      (by simp) (fun _ b hb => citeStep_plain p f _ b _ hb)

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
  | .underline body | .step _ _ body | .footnote _ body =>
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
  | .fill | .strut _ | .pageNumber | .pageCount | .linebreak _ =>
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
  | .para content | .framefoot content | .logo content =>
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
  | .spaced _ body | .step _ _ body | .only _ body | .nav _ body | .note body =>
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
  | .table _ _ _ rows _ =>
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
