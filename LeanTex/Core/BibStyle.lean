import LeanTex.Core.Bib
import LeanTex.Core.Ir

/-! A bibliography style, decomposed the way biblatex decomposed `.bst`
files: four independent pure choices — how a citation renders inline, how
the reference list is ordered, which fields each entry type contributes in
what order, and how a name is written. `unsrtnat` is one record of the
four; `plainnat` is another over the same field orders; a style the engine
does not know falls back to a record, never to a separate code path. The
formats themselves transcribe plainnat.bst (Daly, natbib's companion
style), which `unsrtnat.bst` shares verbatim minus the SORT pass. -/

namespace LeanTex.Core.Bib

open LeanTex.Core

/-- How a citation renders inline (natbib manual §2.3): numeric prints
`[3]` for `\citep` and `Author et al. [3]` for `\citet`; author-year
prints `(Author et al., 2024)` and `Author et al. (2024)`. Closed: a new
citation style is one arm in `renderCite`, not a rewrite. -/
inductive CiteStyle where
  | numeric
  | authorYear
  deriving Repr, BEq, Inhabited

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
names inline, so both shipped styles share the defaults; `initials` and
`lastFirst` are the axes abbrv-shaped and alpha-shaped styles would set. -/
structure NameFormat where
  lastFirst : Bool := false
  initials : Bool := false
  /-- Truncate a list longer than this to its first name and `et al.`;
  `none` keeps every name, as plainnat does. -/
  etAlAfter : Option Nat := none
  deriving Repr, BEq, Inhabited

/-- A bibliography style: four independent choices composed. `unsrtnat` and
`plainnat` are records of this type; so is the fallback an unknown
`\bibliographystyle` gets (W0353) — a record, not a code path. -/
structure Style where
  cite : CiteStyle
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
link to. The key is author text from the `.bib`; the typed HTML tree
escapes it on the way into the attribute (`escapeAttr`), so no spelling of
a key can break out of the `href`. -/
def anchorOf (key : String) : String := "#ref-" ++ key

/-- One resolved citation, ready to render: the entry with its 1-based
position in the reference list. -/
structure Resolved where
  key : String
  position : Nat
  entry : Entry
  deriving Repr

/-- The inline body of one resolved key under the style: numeric prints the
position, author-year the names and year (natbib manual §2.3). Each piece
links to the entry's item. `textual` is `\citet`'s form. -/
def renderCiteOne (style : CiteStyle) (textual : Bool) (r : Resolved) :
    Array Ir.Inline :=
  let anchor := anchorOf r.key
  match style, textual with
  | .numeric, false => #[.link anchor #[.text (toString r.position)]]
  | .numeric, true =>
    #[.text (citeAuthors r.entry ++ " ["),
      .link anchor #[.text (toString r.position)], .text "]"]
  | .authorYear, false =>
    #[.link anchor #[.text s!"{citeAuthors r.entry}, {citeYear r.entry}"]]
  | .authorYear, true =>
    #[.text (citeAuthors r.entry ++ " ("),
      .link anchor #[.text (citeYear r.entry)], .text ")"]

/-- A whole citation under the style: numeric `\citep` wraps its keys in
one bracket group `[1, 2]`; author-year `\citep` parenthesizes with `; `
between entries; the textual forms join with `; ` and no wrapper (natbib
manual §2.3: `\citet{jon90,jam91}` → `Jones et al. (1990); James et al.
(1991)`). An unresolvable key prints `?` in place, LaTeX's own spelling
for an undefined citation — the caller says why with W0351. -/
def renderCite (style : CiteStyle) (textual : Bool)
    (parts : Array (Option Resolved)) : Array Ir.Inline := Id.run do
  let one (p : Option Resolved) : Array Ir.Inline :=
    match p with
    | some r => renderCiteOne style textual r
    | none => #[.text "?"]
  let sep := match style, textual with
    | .numeric, false => ", "
    | _, _ => "; "
  let mut out : Array Ir.Inline := #[]
  match style, textual with
  | .numeric, false => out := out.push (.text "[")
  | .authorYear, false => out := out.push (.text "(")
  | _, _ => pure ()
  let mut firstPart := true
  for p in parts do
    unless firstPart do out := out.push (.text sep)
    firstPart := false
    out := out ++ one p
  match style, textual with
  | .numeric, false => out := out.push (.text "]")
  | .authorYear, false => out := out.push (.text ")")
  | _, _ => pure ()
  return out

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

/-- `unsrtnat`: numeric citations, the reference list in first-citation
order (the "unsrt"), the standard field orders, full names — what
`unsrtnat.bst` is, as one record. -/
def Style.unsrtnat : Style where
  cite := .numeric
  sort := .citation
  order := standardOrder
  names := {}

/-- `plainnat`: author-year citations over the same field orders and
names, the list sorted by author then year (natbib manual §4: plainnat is
the author-year companion of plain). -/
def Style.plainnat : Style where
  cite := .authorYear
  sort := .authorYear
  order := standardOrder
  names := {}

/-- `plain`: what the record model buys — plain.bst is numeric citations
over an author-sorted list, a third style that is zero new code, only a
third pairing of the same two axes. -/
def Style.plain : Style where
  cite := .numeric
  sort := .authorYear
  order := standardOrder
  names := {}

/-- The style a `\bibliographystyle` name selects. `none` is W0353's cue;
the caller falls back to `unsrtnat` — a record, so the fallback loses the
name, never the machinery. -/
def Style.named (name : String) : Option Style :=
  match name with
  | "unsrtnat" | "unsrt" => some .unsrtnat
  | "plainnat" => some .plainnat
  | "plain" => some .plain
  | _ => none

end LeanTex.Core.Bib
