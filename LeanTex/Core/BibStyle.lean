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
import LeanTex.Core.TexText

/-! A bibliography style decomposed into independent pure choices: inline
citations, list order, each entry type's fields, and name format. -/

namespace LeanTex.Core.Bib

open LeanTex.Core

/-- How the reference list is ordered: first-citation order, or plain.bst's or
alpha.bst's sort key. -/
public inductive SortOrder where
  | citation
  | plain
  | alpha
  | authorYear
  | bbl (template : String) (opts : BblOptions)
  deriving Repr, BEq, Inhabited

/-- One formatted piece of a reference-list entry, after plainnat.bst's
`format.*` functions. -/
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
  /-- The `key` field where the named field is empty (FUNCTION {format.key}). -/
  | keyIf (name : String)
  /-- An article's reference to its listed parent (FUNCTION
  {format.article.crossref}); `natbib` cites it with `\citet`. -/
  | articleCrossref (natbib : Bool)
  /-- A book's or chapter's reference to its listed parent (FUNCTION
  {format.book.crossref}). -/
  | bookCrossref (natbib : Bool)
  /-- A contribution's reference to its listed parent (FUNCTION
  {format.incoll.inproc.crossref}). -/
  | incollCrossref (natbib : Bool)
  deriving Repr, BEq

/-- One step of an entry type's function: a piece's `output`, or a block or
sentence boundary, conditional ones taken when a named field is present. -/
public inductive Step where
  | out (f : Field)
  | newBlock
  | newSentence
  | newBlockIf (fields : List String)
  | newSentenceIf (fields : List String)
  deriving Repr, BEq

/-- How one name is written, by the inline citation style
and the entry format alike. -/
public structure NameFormat where
  lastFirst : Bool := false
  /-- Abbreviate first names to initials, plain.bst's `{f.~}` designator. -/
  initials : Bool := false
  /-- Truncate a list longer than this to its first name and
  `et al.`; `none` keeps every name. -/
  etAlAfter : Option Nat := none
  deriving Repr, BEq, Inhabited

/-- A bibliography style: four independent choices composed. -/
public structure Style where
  /-- Whether the style's `\bibitem`s carry natbib's author-year labels. -/
  labels : Bool
  sort : SortOrder
  /-- The steps an entry's type writes, the entry deciding
  the style function's branches. -/
  steps : Entry → Array Step
  names : NameFormat
  /-- Whether the style's month macros are its own
  abbreviations rather than the full names. -/
  shortMonths : Bool := false
  /-- alpha.bst's labels in place of the list position. -/
  alphabetic : Bool := false

/-- One name as the format writes it, in TeX. -/
public def NameFormat.render (nf : NameFormat) (n : Name) : String :=
  let first := if nf.initials then Bib.initials n.first else n.first
  let jr := if n.jr.isEmpty then "" else s!", {n.jr}"
  if nf.lastFirst then
    let tail := String.intercalate " " ([n.von, first].filter (!·.isEmpty))
    if tail.isEmpty then n.last ++ jr else s!"{n.last}, {tail}" ++ jr
  else
    String.intercalate " " ([first, n.von, n.last].filter (!·.isEmpty)) ++ jr

/-- An author value as the reference list writes it, in TeX. -/
public def NameFormat.renderTeX (nf : NameFormat) (v : String) : String :=
  let ns := (splitNames v).toList
  let ns := match nf.etAlAfter with
    | some k => if ns.length > k then ns.take 1 ++ ["others"] else ns
    | none => ns
  andJoin (ns.map fun s => if s == "others" then "others" else nf.render (parseName s))

/-- An author value as plain text. -/
public def NameFormat.renderList (nf : NameFormat) (v : String) : String :=
  let ns := (splitNames v).toList
  let ns := match nf.etAlAfter with
    | some k => if ns.length > k then ns.take 1 ++ ["others"] else ns
    | none => ns
  andJoin (ns.map fun s =>
    if s == "others" then "others" else text (nf.render (parseName s)))

/-- The year a date field names in a label, with a range's
differing end year after an en dash. -/
private def dateYears (dv : DateValue) : String :=
  let yr (d : Date) : String := (if d.year < 0 then "−" else "") ++ toString d.year.natAbs
  match dv.start, dv.stop with
  | some a, some (some b) => if b.year == a.year then yr a else s!"{yr a}–{yr b}"
  | some a, some none => s!"{yr a}–"
  | none, some (some b) => s!"–{yr b}"
  | some a, none => yr a
  | none, _ => ""

/-- The year an entry's label and inline citation print: its
`year`, else its date's year. -/
private def citeYear (e : Entry) : String :=
  match e.field? "year" with
  | some y => text y
  | none =>
    match e.field? "date" with
    | some d => match DateValue.parse d with
      | some dv => dateYears dv
      | none => text d
    | none => "n.d."

/-- An organization without the `"The "` a label or sort drops. -/
private def chopThe (v : String) : String :=
  if v.startsWith "The " then (v.drop 4).toString else v

/-- The names a label is built from, in TeX. -/
private def labelSource (e : Entry) (biblatex : Bool) (useprefix : Bool := false) : String :=
  let names (v : String) : String := labelNamesTeX v 2 true
  if biblatex then
    match labelNameList e with
    | some (_, l) => citeNamesTeX { useprefix } l {}
    | none => (e.field? "title").getD e.key
  else
    let key := (e.value? "key").getD ((e.key.take 3).toString)
    let org := (e.value? "organization").map fun o => ((text (chopThe o)).take 3).toString
    let first (fs : List (Option String)) : String := (fs.findSome? id).getD key
    let au := (e.value? "author").map names
    let ed := (e.value? "editor").map names
    match e.kind with
    | "book" | "inbook" => first [au, ed]
    | "proceedings" => first [ed, e.value? "key", org]
    | "manual" => first [au, e.value? "key", org]
    | _ => first [au]

/-- The label names a citation prints, never silently empty. -/
private def citeAuthors (e : Entry) (biblatex : Bool := false) (useprefix : Bool := false) :
    String :=
  Ir.smartPunct (text (labelSource e biblatex useprefix))

/-- The anchor an entry's reference-list item carries and
its citations link to. -/
public def anchorOf (key : String) : String :=
  let a := Ir.bibAnchor key
  "#" ++ a

/-- One resolved citation, ready to render: the entry, its 1-based list
position, and its disambiguating letter. -/
public structure Resolved where
  key : String
  position : Nat
  entry : Entry
  extra : String := ""
  /-- The mark a `thebibliography` entry's optional label
  sets in numbers mode. -/
  label : Option String := none
  /-- biblatex's labelname as its citations print it,
  uniqueness applied, in TeX. -/
  citeNames : Option String := none
  /-- biblatex's citation text for an entry no name list labels. -/
  citeLabel : Option (Array Ir.Inline) := none
  /-- The TeX the style's label is spelt in, where `label` holds its text. -/
  labelTeX : Option String := none
  /-- What a citation prints for the names, where their TeX
  holds a control word. -/
  namesInk : Option (Array Ir.Inline) := none
  /-- biblatex's shorthand as an author-year citation prints it, where its TeX
  holds a control word. -/
  shortInk : Option (Array Ir.Inline) := none
  /-- biblatex's grouping key for the extradate letter: the
  names its citations show. -/
  extraKey : Option String := none
  /-- biblatex's `namehash`: the names its citations show, whole. -/
  nameHash : Option String := none
  /-- biblatex's labelname field and the names its `uniquelist` shows. -/
  labelUl : Option (String × Nat) := none
  /-- biblatex's count of sort-list names the sort key reads. -/
  sortShown : Option Nat := none
  /-- biblatex's `shorthand`, printed in place of the label. -/
  shorthand : Option String := none
  /-- biblatex's label year, and whether it reads as numerals. -/
  labelYear : Option (String × Bool) := none
  /-- biblatex's `skipbib`: cited and numbered, never listed. -/
  skipbib : Bool := false
  /-- biblatex's `skiplab`: no number and no letter. -/
  skiplab : Bool := false
  /-- The entry as its `.bib` writes it, where the list's definitions differ
  from its sort keys'; `none` where they are one. -/
  raw : Option Entry := none
  /-- What the entry's field citations print, per field and form. -/
  fieldInk : Array ((Ir.CiteField × Bool) × Array Ir.Inline) := #[]
  /-- The boundary pictures its citation ink sets. -/
  inkPictures : Array (String × Ir.PicSrc) := #[]
  deriving Repr

/-- The entry a sort key and alpha's label read: as its `.bib` writes it. -/
public def Resolved.sortEntry (r : Resolved) : Entry := r.raw.getD r.entry

/-- The anchor an entry's citations link to: its list entry's, where a list sets the entry. -/
public def Resolved.anchor? (r : Resolved) : Option String :=
  if r.skipbib then none else some (anchorOf r.key)

/-- The full author list natbib's starred forms print, or the key. -/
private def citeFullAuthors (e : Entry) : String :=
  match e.value? "author" with
  | some a => Ir.smartPunct (fullNames a)
  | none => e.key

/-- What one key prints: names and year, names alone, or year alone. -/
private inductive CitePart where
  | both
  | names
  | year
  deriving BEq

/-- The citation loop's state between keys. -/
private structure CiteAcc where
  out : Array Ir.Inline := #[]
  citea : String := ""
  last : Option String := none
  lastYear : Option String := none
  dated : Bool := false
  /-- The keys read so far. -/
  index : Nat := 0
  /-- The groups begun so far; a biblatex numeric textual citation's keys share
  one per list of names. -/
  groups : Nat := 0
  /-- The last key's `namehash`. -/
  lastHash : Option String := none

mutual

/-- Inline content carrying no citation, anywhere in its tree. -/
private def citeFreeOne : Ir.Inline → Bool
  | .cite _ _ => false
  | .cited _ _ ink => citeFreeList ink.toList
  | .styled _ body => citeFreeList body.toList
  | .colored _ _ body => citeFreeList body.toList
  | .located _ body => citeFreeList body.toList
  | .role _ body => citeFreeList body.toList
  | .link _ body => citeFreeList body.toList
  | .decorated _ body | .boxed _ body => citeFreeList body.toList
  | .onSteps _ body => citeFreeList body.toList
  | .altSteps _ active otherwise =>
    citeFreeList active.toList && citeFreeList otherwise.toList
  | .footnote _ body => citeFreeList body.toList
  | .image _ _ (.citing _) => false
  | .image _ _ .undeclared | .image _ _ .decorative | .image _ _ (.described _) => true
  | .text _ | .math _ _ | .formula _ _ _ | .icon _ _
  | .label _ | .ref _ _ _ _
  | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _ | .pageNumber | .pageCount | .linebreak _ => true

private def citeFreeList : List Ir.Inline → Bool
  | [] => true
  | x :: rest => citeFreeOne x && citeFreeList rest

end

private def emit (out : Array Ir.Inline) (s : String) : Array Ir.Inline :=
  if s.isEmpty then out else out.push (.text s)

private def emitLink (p : CitePunct) (out : Array Ir.Inline) (anchor : Option String)
    (s : String) : Array Ir.Inline :=
  match anchor with
  | some a => out.push (.link a (match p.ink with
    | some (c, n) => #[.colored c n #[.text s]]
    | none => #[.text s]))
  | none => emit out s

/-- A key's piece, linked to its entry where a list sets it, after what precedes it. -/
private def linkPiece (p : CitePunct) (out : Array Ir.Inline) (anchor : Option String)
    (before piece : Array Ir.Inline) : Array Ir.Inline :=
  if piece.isEmpty then
    if citeFreeList before.toList then out ++ before else emit out (Ir.plainText before)
  else if citeFreeList before.toList && citeFreeList piece.toList then
    match anchor with
    | some a => (out ++ before).push (.link a (match p.ink with
      | some (c, n) => #[.colored c n piece]
      | none => piece))
    | none => out ++ before ++ piece
  else emitLink p (emit out (Ir.plainText before)) anchor (Ir.plainText piece)

/-- The first letter capitalized over inline content, natbib's `\NAT@Up`. -/
private def upFirstInk (xs : Array Ir.Inline) : Array Ir.Inline :=
  if let some (Ir.Inline.text t) := xs[0]? then xs.modify 0 fun _ => .text t.capitalize else xs

/-- What natbib's command table sets for a command. -/
private structure Switches where
  numeric : Bool
  wrap : Bool
  part : CitePart
  op : String
  cl : String

private def switches (p : CitePunct) (f : Ir.CiteForm) : Switches :=
  let brackets := match f.cmd with
    | .textual | .paren | .auto | .yearPar | .text => true
    | .alt | .alp | .author | .year | .num | .nocite | .bracket _ | .noteSep | .field _ => false
  { numeric := p.numbers || f.cmd == .num
    wrap := match f.cmd with
      | .paren | .alp | .yearPar | .num | .text => true
      | .auto => p.numbers
      | .textual | .alt | .author | .year | .nocite | .bracket _ | .noteSep | .field _ => false
    part := match f.cmd with
      | .author => .names
      | .year | .yearPar => .year
      | .textual | .paren | .auto | .alt | .alp | .num | .text | .nocite | .bracket _ | .noteSep
      | .field _ => .both
    op := if brackets then p.open else ""
    cl := if brackets then p.close else "" }

/-- The separator a textual citation's key `k` of `total`
leaves for the next. -/
private def textSep (p : CitePunct) (f : Ir.CiteForm) (total k : Nat) : String :=
  if p.biblatex && f.cmd == .textual then
    if k + 2 == total then (if total ≥ 3 then ", and " else " and ") else ", "
  else p.sep ++ " "

/-- Whether a citation groups its keys by their names, as a biblatex numeric
textual citation does. -/
private def groupsKeys (p : CitePunct) (f : Ir.CiteForm) (s : Switches) : Bool :=
  p.biblatex && s.numeric && f.cmd == .textual

/-- A citation's groups: one per key, a grouping citation's key joining the last
key's group when their `namehash` agree. -/
private def citeGroups (p : CitePunct) (f : Ir.CiteForm) (s : Switches)
    (parts : Array (Option Resolved)) : Nat :=
  if groupsKeys p f s then
    (parts.foldl (init := (0, (none : Option String))) fun (n, last) o =>
      match o with
      | some r => if r.nameHash.isSome && r.nameHash == last then (n, last) else (n + 1, r.nameHash)
      | none => (n + 1, none)).1
  else parts.size

/-- One key under natbib's loop: the separator the previous key left, this key's
linked piece, and the separator it leaves. -/
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
    let names := if up then names.capitalize else names
    let titled := if f.full then none else match r.namesInk with
      | some inl => some (if up then upFirstInk inl else inl)
      | none => if r.citeNames.isSome then none else r.citeLabel
    let txt (s : String) : Array Ir.Inline := if s.isEmpty then #[] else #[.text s]
    let linked (after : String) : Array Ir.Inline := match titled with
      | some inl =>
        let tail := txt after
        inl ++ tail
      | none => #[.text (names ++ after)]
    let lead (before after : String) : Array Ir.Inline := match titled with
      | some inl =>
        let tail := txt after
        txt before ++ inl ++ tail
      | none => txt (before ++ names ++ after)
    let (bare, numerals) := r.labelYear.getD (citeYear r.entry, true)
    let inParens := (s.wrap && !s.op.isEmpty) || f.cmd == .textual
    let letter := if p.numbers || r.extra.isEmpty then ""
      else if numerals then r.extra
      else if inParens then "[" ++ r.extra ++ "]" else "(" ++ r.extra ++ ")"
    let year := bare ++ letter
    let sh := if p.biblatex && !s.numeric then r.shorthand.map (Ir.smartPunct ∘ text) else none
    let mark := if s.numeric then r.label.getD (toString r.position) else sh.getD year
    let shInk : Option (Array Ir.Inline) :=
      sh.map fun h => r.shortInk.getD #[.text h]
    let markInk : Array Ir.Inline := if s.numeric then #[.text mark] else shInk.getD #[.text mark]
    let pre := if f.pre.isEmpty then "" else f.pre ++ " "
    let same := !p.biblatex && acc.last == some names
    let sameYear := same && acc.lastYear == some bare && !letter.isEmpty
    let joins := groupsKeys p f s && r.nameHash.isSome && acc.lastHash == r.nameHash
    let tsep := textSep p f total (if joins then acc.groups - 1 else acc.groups)
    let t : Array Ir.Inline × Array Ir.Inline × String :=
      if joins then (txt (p.sep ++ " "), markInk, s.cl ++ tsep) else
      match s.part with
      -- biblatex's `\citeauthor` prints nothing for an entry no name list labels.
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
    { out := linkPiece p acc.out r.anchor? t.1 t.2.1
      citea := t.2.2
      last := some names
      lastYear := some bare
      dated := true
      index := acc.index + 1
      groups := if joins then acc.groups else acc.groups + 1
      lastHash := r.nameHash }

/-- The brackets around the loop's output, with the pre- and post-notes. -/
private def finish (p : CitePunct) (f : Ir.CiteForm) (s : Switches) (pagination : Option String)
    (acc : CiteAcc) : Array Ir.Inline :=
  let post := if f.post.isEmpty then ""
    else p.notesep ++ (if p.biblatex then bblPostnote pagination f.post else f.post)
  let (lead, trail) :=
    if s.wrap then (s.op ++ (if f.pre.isEmpty then "" else f.pre ++ " "), post ++ s.cl)
    else ("", (if s.numeric && s.part != .both then "" else post) ++
      (if acc.dated then s.cl else ""))
  emit (emit #[] lead ++ acc.out) trail

/-- natbib's `sort`: a citation's keys in reference-list
order, unnumbered marks after them. -/
private def sortParts (parts : Array (Option Resolved)) : Array (Option Resolved) :=
  let numbered (o : Option Resolved) : Bool := o.any (·.label.isNone)
  let known := (parts.filterMap fun o => if numbered o then o else none).toList.mergeSort
    fun a b => decide (a.position ≤ b.position)
  let unknown := parts.filter (!numbered ·)
  (known.map some).toArray ++ unknown

/-- `compress`'s state between keys. -/
private structure RunAcc where
  acc : CiteAcc := {}
  last : Option Nat := none
  held : Option (String × Resolved) := none

/-- The held number, printed. -/
private def flushHeld (p : CitePunct) (out : Array Ir.Inline) :
    Option (String × Resolved) → Array Ir.Inline
  | some (pre, r) => emitLink p (emit out pre) r.anchor? (toString r.position)
  | none => out

/-- One key under `compress`: a number one past the last extends the run and is
held back; anything else prints the held number, then itself. -/
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
          out := emitLink p (emit (flushHeld p st.acc.out st.held) st.acc.citea) r.anchor?
            (r.label.getD (toString r.position))
          citea := p.sep ++ " ", dated := true }
        last := if r.label.isNone then some r.position else none }

/-- natbib's `compress` over a numbered citation: a run of three or more joins
its ends by an en dash. -/
private def compressRuns (p : CitePunct) (parts : Array (Option Resolved)) : CiteAcc :=
  let st := parts.foldl (runStep p) {}
  { st.acc with out := flushHeld p st.acc.out st.held }

/-- What a field citation prints for one key's entry, `?`
where it holds no content. -/
private def fieldPiece (w : Ir.CiteField) (full : Bool) (acc : Array Ir.Inline) :
    Option Resolved → Array Ir.Inline
  | some r =>
    let ink := ((r.fieldInk.find? (·.1 == (w, full))).map (·.2)).getD #[]
    if ink.isEmpty || !citeFreeList ink.toList then emit acc "?"
    else if w == .title || w == .date then
      match r.anchor? with
      | some a => acc.push (.link a ink)
      | none => acc ++ ink
    else acc ++ ink
  | none => emit acc "?"

/-- One key of a field citation: the separator before it, then its piece. -/
private def fieldStep (p : CitePunct) (w : Ir.CiteField) (full : Bool) (acc : Array Ir.Inline)
    (o : Option Resolved) : Array Ir.Inline :=
  fieldPiece w full (if acc.isEmpty then acc else emit acc (p.sep ++ " ")) o

/-- A whole citation under natbib's punctuation, per its command. -/
public def renderCite (p : CitePunct) (f : Ir.CiteForm) (parts : Array (Option Resolved)) :
    Array Ir.Inline :=
  if let .bracket o := f.cmd then emit #[] (if o then p.open else p.close)
  else if f.cmd == .noteSep then emit #[] p.notesep
  else if let .field w := f.cmd then
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

/-- BibTeX's `n.dashify`: a lone `-` between page numbers
becomes the en dash. -/
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

/-- Whether a stored value holds anything but white space, BibTeX's `empty$` false. -/
private def Entry.has (e : Entry) (name : String) : Bool := (e.value? name).isSome

/-- The reference list's writer: the diagnostics its field readings report, and
the texts read so far. -/
private abbrev RenderM := StateM (FieldReport × FieldCache)

/-- A field's TeX text through the reading in force, once per text. -/
private def conv (cv : FieldText) (s : String) : RenderM (Array Ir.Inline) := do
  let (ds, cache) ← get
  let ((out, ds'), cache) := cache.read cv s
  set (ds ++ ds', cache)
  pure out

/-- plain.bst's `tie.or.space.connect`: a value shorter than
three characters ties to its word. -/
private def tieOrSpace (cv : FieldText) (word v : String) : RenderM (Array Ir.Inline) := do
  let gap := if (text v).length < 3 then "\u00a0" else " "
  pure (#[.text (word ++ gap)] ++ (← conv cv v))

/-- plain.bst's `format.pages`: `pages` for a range or a
list, `page` for one. -/
private def formatPages (cv : FieldText) (p : String) : RenderM (Array Ir.Inline) :=
  if p.any fun c => c == '-' || c == ',' || c == '+' then tieOrSpace cv "pages" (dashify p)
  else tieOrSpace cv "page" p

/-- An editor list as plain.bst writes it (FUNCTION {format.editors}). -/
private def editorsTeX (nf : NameFormat) (ed : String) : String :=
  nf.renderTeX ed ++ if (splitNames ed).size > 1 then ", editors" else ", editor"

/-- plain.bst's `format.crossref.editor`. -/
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

/-- A cross-reference's citation of its parent: plainnat's
`\citet`, plain's `\cite`. -/
private def crossrefCite (natbib : Bool) (key : String) : Ir.Inline :=
  .cite { cmd := if natbib then .textual else .auto } #[key]

/-- Whether the parent's editor list stands for the parent. -/
private def editorStands (e : Entry) : Bool :=
  e.has "editor" && e.field? "editor" != e.field? "author"

/-- One piece of one entry, the one renderer every entry type goes through;
`mid` says whether it continues a sentence. -/
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

/-- The entry functions of plainnat.bst, which unsrtnat.bst
and abbrvnat.bst share. -/
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

/-- The entry functions of plain.bst, which unsrt.bst,
abbrv.bst and alpha.bst share. -/
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

/-- The output state plainnat.bst threads through an entry. -/
private inductive OutState where
  | beforeAll
  | mid
  | afterBlock
  | afterSentence
  deriving BEq

/-- Inline content with each citation and reference read as the key it names. -/
private def sourceText (xs : Array Ir.Inline) : Array Ir.Inline :=
  Ir.mapInlines (fun x => match x with
    | .cite _ keys => .text (keys.back?.getD "")
    | .ref k _ _ _ => .text k
    | x => x) xs

/-- BibTeX's `add.period$`: a period unless the entry
already ends with `.`, `?` or `!`. -/
private def addPeriod (out : Array Ir.Inline) : Array Ir.Inline :=
  match (Ir.plainText (sourceText out)).toList.getLast? with
  | none => out
  | some c => if c == '.' || c == '?' || c == '!' then out else out.push (.text ".")

/-- One reference-list entry as plainnat.bst's `output` writes it, with its
field readings' reports. -/
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
    return Ir.mergeTexts (addPeriod out)
  let (out, ds, cache) := run.run ({}, cache)
  ((out, ds), cache)

public def renderEntryWith (cv : FieldText) (nf : NameFormat) (steps : Array Step) (e : Entry)
    (extra : String := "") : Array Ir.Inline × FieldReport :=
  (renderEntryCached cv nf steps e extra {}).1

public def renderEntry (nf : NameFormat) (steps : Array Step) (e : Entry) (extra : String := "") :
    Array Ir.Inline :=
  (renderEntryWith plainField nf steps e extra).1

/-- `unsrtnat`: first-citation order, the standard field
orders, full names, author-year labels. -/
public def Style.unsrtnat : Style where
  labels := true
  sort := .citation
  steps := plainnatSteps
  names := {}

/-- `plainnat`: `unsrtnat` with the list sorted by author then year. -/
public def Style.plainnat : Style where
  labels := true
  sort := .authorYear
  steps := plainnatSteps
  names := {}

/-- `plain`: numbers over a list sorted by names, year and title. -/
public def Style.plain : Style where
  labels := false
  sort := .plain
  steps := plainSteps
  names := {}

/-- `alpha`: `plain` under alpha.bst's labels, sorted by label. -/
public def Style.alpha : Style :=
  { Style.plain with sort := .alpha, alphabetic := true }

/-- `unsrt`: `plain` in first-citation order, as unsrt.bst is. -/
public def Style.unsrt : Style :=
  { Style.plain with sort := .citation }

/-- The abbrv styles' name format: initials, first names first. -/
public def abbrvNames : NameFormat := { initials := true }

/-- `abbrvnat`: `plainnat` with abbreviated first names. -/
public def Style.abbrvnat : Style :=
  { Style.plainnat with names := abbrvNames, shortMonths := true }

/-- `abbrv`: `plain` with abbreviated first names. -/
public def Style.abbrv : Style :=
  { Style.plain with names := abbrvNames, shortMonths := true }

/-- The styles a `\bibliographystyle` name selects, by name. -/
public def Style.byName : List (String × Style) :=
  [("unsrtnat", .unsrtnat), ("unsrt", .unsrt), ("plainnat", .plainnat), ("plain", .plain),
   ("abbrvnat", .abbrvnat), ("abbrv", .abbrv), ("alpha", .alpha)]

/-- The style a `\bibliographystyle` name selects; `none` for an unknown name. -/
public def Style.named (name : String) : Option Style := Style.byName.lookup name

/-- The month names abbrv.bst and abbrvnat.bst define. -/
private def shortMonthNames : Array String :=
  #["Jan.", "Feb.", "Mar.", "Apr.", "May", "June", "July", "Aug.", "Sept.", "Oct.", "Nov.", "Dec."]

/-- A key appended to an ordered set of keys. -/
private def addKey (acc : Array String × Std.HashSet String) (k : String) :
    Array String × Std.HashSet String :=
  if acc.2.contains k then acc else (acc.1.push k, acc.2.insert k)

/-- The keys the document cites, in order of first appearance, each once, among
the citations `keep` admits. -/
private def citedKeys (doc : Ir.Doc) (keep : Ir.CiteForm → Bool := fun _ => true) : Array String :=
  (Ir.foldDoc
    (fun acc x => match x with
      | .cite f keys => if keep f then keys.foldl addKey acc else acc
      | .image _ _ alt => alt.cites.foldl (fun acc (f, keys) =>
          if keep f then keys.foldl addKey acc else acc) acc
      | _ => acc) (#[], {}) doc).1

/-- `\nocite{*}`: every `.bib` entry but an `@xdata` one enters the list where
it stands, after the keys cited before it. -/
private def expandStar (entries : Array Entry) (cited : Array String) : Array String :=
  (cited.foldl (fun acc k =>
    if k == "*" then entries.foldl (fun acc e =>
      if e.kind == "xdata" then acc else addKey acc e.key) acc
    else addKey acc k) (#[], {})).1

/-- BibTeX's `sortify`: `purify$`, lowercased. -/
private def sortify (v : String) : String := (purify v).toLower

/-- plain.bst's `sort.format.names`. -/
private def sortNames (v : String) : String :=
  let ns := splitNames v
  String.intercalate "   " (ns.toList.zipIdx.map fun (s, i) =>
    if i + 1 == ns.size && s == "others" then "et al"
    else
      let n := parseName s
      sortify ((if n.von.isEmpty then "" else n.von ++ " ") ++ n.last ++
        (if n.first.isEmpty then "" else "  " ++ n.first) ++
        (if n.jr.isEmpty then "" else "  " ++ n.jr)))

/-- plain.bst's `sort.format.title`: a leading `The `, `An `
or `A ` dropped, sortified. -/
private def sortTitle (v : String) : String :=
  let chop (w t : String) : String := if t.startsWith w then (t.drop w.length).toString else t
  sortify (chop "A " (chop "An " (chop "The " v)))

/-- The names plain.bst's `presort` reads by entry type. -/
private def sortWho (e : Entry) : String :=
  let key := ((e.value? "key").map sortify).getD ""
  let org := (e.value? "organization").map fun o => sortify (chopThe o)
  let au := (e.value? "author").map sortNames
  let ed := (e.value? "editor").map sortNames
  let first (fs : List (Option String)) : String := (fs.findSome? id).getD key
  match e.kind with
  | "book" | "inbook" => first [au, ed]
  | "proceedings" => first [ed, org]
  | "manual" => first [au, org]
  | _ => first [au]

/-- plain.bst's sort key: the names, the year and the title;
the cite key breaks a tie. -/
private def plainKey (r : Resolved) : String × String :=
  (sortWho r.sortEntry ++ "    " ++ sortify ((r.sortEntry.field? "year").getD "") ++ "    " ++
    sortTitle ((r.sortEntry.field? "title").getD ""), r.key)

/-- alpha.bst's `format.lab.names`. -/
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

/-- alpha.bst's label stem by entry type (`calc.label`). -/
private def alphaWho (e : Entry) (key : String) : String :=
  let k := (e.value? "key").map (textPrefix · 3)
  let org := (e.value? "organization").map fun o => textPrefix (chopThe o) 3
  let first (fs : List (Option String)) : String :=
    ((fs ++ [k]).findSome? id).getD ((key.take 3).toString)
  let au := (e.value? "author").map alphaNames
  let ed := (e.value? "editor").map alphaNames
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
characters, sortified. -/
private def alphaSortLabel (r : Resolved) : String :=
  sortify (alphaWho r.sortEntry r.key ++ yearTail r.sortEntry 4)

/-- alpha.bst's sort key: the sort label, then plain.bst's. -/
private def alphaKey (r : Resolved) : String × String :=
  (alphaSortLabel r ++ "    " ++ (plainKey r).1, r.key)

/-- plainnat.bst's `sort.format.names`. -/
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

/-- plainnat.bst's sort key: the names by type, the year and the cite key. -/
private def plainnatKey (r : Resolved) : String × String :=
  let e := r.sortEntry
  let year := (e.field? "year").getD ""
  let key := ((e.value? "key").map sortify).getD ""
  let org := (e.value? "organization").map fun o => sortify (chopThe o)
  let au := (e.value? "author").map (sortNamesNat · year)
  let ed := (e.value? "editor").map (sortNamesNat · year)
  let first (fs : List (Option String)) : String := (fs.findSome? id).getD key
  let who := match e.kind with
    | "book" | "inbook" => first [au, ed]
    | "proceedings" => first [ed, org]
    | "manual" => first [au, org]
    | _ => first [au]
  (who ++ "    " ++ sortify year ++ "    " ++ r.key, r.key)

/-- Lexicographic order on two keys: the sort strings by
collation, the cite keys as written. -/
private def pairCompare (a b : Collate.Key × String) : Ordering :=
  (a.1.compare b.1).then (Ord.compare a.2 b.2)

/-- A BibTeX key with its sort string read for collation, once per entry. -/
private def collated (key : Resolved → String × String) (r : Resolved) : Collate.Key × String :=
  let (k, c) := key r
  (Collate.key k, c)

/-- One sortset's value under a biblatex template: a string compared by
collation, or a number. -/
private inductive SortVal where
  | str (k : Collate.Key)
  | int (n : Int)

private def SortVal.compare : SortVal → SortVal → Ordering
  | .str a, .str b => a.compare b
  | .int a, .int b => Ord.compare a b
  | .int _, .str _ => .lt
  | .str _, .int _ => .gt

/-- What a template's sortset reads. -/
private inductive SortSet where
  | presort
  | sortkey
  | names
  | titles
  | year
  | yearOr9999
  | volume
  deriving BEq

private def bblTemplate : String → List SortSet × Bool
  | "nyt" => ([.presort, .sortkey, .names, .year, .titles, .volume], false)
  | "nyvt" => ([.presort, .sortkey, .names, .year, .volume, .titles], false)
  | "ynt" => ([.presort, .sortkey, .yearOr9999, .names, .titles], false)
  | "ydnt" => ([.presort, .sortkey, .yearOr9999, .names, .titles], true)
  | _ => ([.presort, .sortkey, .names, .titles, .year, .volume], false)

/-- A literal field as biber sorts it (`normalise_string_sort`). -/
private def sortText (v : String) : String :=
  " ".intercalate ((sortPlainText v).splitOn " " |>.filter (!·.isEmpty))

/-- A name's parts as biber's sorting name key reads them. -/
private def namePartsForSort (up : Bool) (n : Name) : List (String × String) :=
  (if up then [("prefix", n.von), ("family", n.last)] else [("family", n.last)]) ++
    [("given", n.first), ("suffix", n.jr)] ++ (if up then [] else [("prefix", n.von)])

/-- The name lists a biblatex list sorts by, each value read once. -/
private def sortNameLists (es : List Entry) : Std.HashMap String (Array Name) :=
  es.foldl (init := {}) fun m e =>
    ["author", "editor", "translator", "sortname"].foldl (init := m) fun m f =>
      match e.field? f with
      | none => m
      | some v =>
        if m.contains v then m
        else m.insert v (((splitNames v).filter (· != "others")).map parseNameBiber)

/-- The longest each name part is written across the names a
list sorts (biber's `np_length`). -/
private def namePartLengths (lists : Std.HashMap String (Array Name)) : Std.HashMap String Nat :=
  lists.fold (init := {}) fun m _ ns =>
    ns.foldl (init := m) fun m n =>
      [("prefix", n.von), ("family", n.last), ("given", n.first), ("suffix", n.jr)].foldl
        (init := m) fun m (part, t) =>
          let len := (Nfc.normalize (sortText t)).length
          if len > m.getD part 0 then m.insert part len else m

/-- A name list's sort string, each part padded to the list's longest. -/
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

/-- A sortset's integer as biber's sort compares it, past
every number where the value is none. -/
private def sortInt (v : String) : Int := ((text v).trimAscii.toString.toInt?).getD 2000000000

/-- A roman numeral's value as biber reads an integer field for sorting. -/
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

/-- An integer field's sort value: a roman numeral as its
value, else as `sortInt` reads it. -/
private def sortIntField (v : String) : Int :=
  let t := (text v).trimAscii.toString
  match romanValue t with
  | some n => n
  | none => sortInt t

/-- The tailoring file a biblatex list sorts by. -/
public def bblSortFile (o : BblOptions) : String :=
  Collate.localeFile (Collate.biberLocale
    (if o.sortlocale == "auto" then o.babelMain.getD "english" else o.sortlocale))

/-- The tailoring a biblatex list sorts by; the default table where the file is
none or of another script. -/
private def bblTailoring (o : BblOptions) : Collate.Tailoring :=
  (Collate.tailoringFor (bblSortFile o)).getD {}

/-- An entry's biblatex sort key under a template. -/
private def bblSortKey (template : String) (o : BblOptions) (tl : Collate.Tailoring)
    (lists : Std.HashMap String (Array Name)) (lens : Std.HashMap String Nat)
    (r : Resolved) : Array SortVal := Id.run do
  let e := r.sortEntry
  let oe := o.forEntry e
  let str (s : String) : SortVal := .str (Collate.keyWith tl s)
  let titles : SortVal := str (sortText (((e.value? "sorttitle").orElse fun _ => e.value? "title").getD ""))
  let names : SortVal :=
    let used := [("sortname", true), ("author", oe.useauthor), ("editor", oe.useeditor),
      ("translator", oe.usetranslator)]
    match used.findSome? fun (f, use) => if use then e.value? f else none with
    | some v =>
      let names := (lists.get? v).getD
        (((splitNames v).filter (· != "others")).map parseNameBiber)
      str (nameSortString lens oe.useprefix r.sortShown names)
    | none => titles
  let yearOf : Option Int := match (e.value? "sortyear") with
    | some y => some (sortIntField y)
    | none => match e.dateParts #[] "" with
      | .parsed dv => some ((dv.start.map (·.year)).getD 2000000000)
      | .legacy y _ => some (sortIntField y)
      | .written _ => some 2000000000
      | .none => none
  let volume : SortVal := .int ((e.value? "volume").map sortIntField |>.getD 0)
  let (sets, descending) := bblTemplate template
  let mut out : Array SortVal := #[]
  let mut final : Option String := none
  for set in sets do
    match final with
    | some k => out := out.push (if set == .year || set == .yearOr9999 || set == .volume then
        .int (sortInt k) else str k)
    | none =>
      match set with
      | .presort => out := out.push (str (sortText ((e.value? "presort").getD "mm")))
      | .sortkey =>
        match e.value? "sortkey" with
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
first-citation position. -/
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

/-- The list sorted by the order's comparison: a stable merge sort over keys
computed once per entry. -/
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

/-- What one key renders as everywhere it is cited. -/
@[expose] public def Resolver := String → Option Resolved

/-- The label two entries must share to take letters. -/
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

/-- The letter of the `i`-th entry among those sharing a label: `a` … `z`, then
`aa`, `ab`, … as biblatex's `\mknumalph`. -/
private def extraLetter (i : Nat) : String := Id.run do
  -- bijective base 26 over the 1-based index: 1 is `a`, 26 `z`, 27 `aa`
  let mut n := i + 1
  let mut out : List Char := []
  for _ in [0:i + 2] do
    if n == 0 then break
    out := Char.ofNat ('a'.toNat + (n - 1) % 26) :: out
    n := (n - 1) / 26
  return String.ofList out

/-- The letters plainnat.bst's `forward.pass` and `reverse.pass` give entries
sharing a label, in list order. -/
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

/-- alpha.bst's labels over the sorted list. -/
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
    { r with label := some (Ir.smartPunctInWord (text tex) ++ letter), labelTeX := some (tex ++ letter) }

/-- What biber reads of a biblatex list before it sorts and labels it, each
entry under its own options. -/
private def bblAnnotate (o : BblOptions) (months : Array String) (rs : Array Resolved) :
    Array Resolved :=
  let uo := o.unique'
  let opts := rs.map fun r => o.forEntry r.entry
  let lists := (rs.zip opts).map fun (r, oe) => oe.labelName r.entry
  let us := uniqueness uo (lists.map fun l => (l.map (·.2)).getD {})
  ((rs.zip opts).zip (lists.zip us)).map fun ((r, oe), l, u) =>
    let sortList := [("sortname", true), ("author", oe.useauthor), ("editor", oe.useeditor),
      ("translator", oe.usetranslator)].findSome? fun (f, use) =>
        if use then (r.entry.value? f).map fun v =>
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
      shorthand := r.entry.value? "shorthand"
      labelYear := some (bblLabelYear months r.entry)
      skipbib := oe.skipbib
      skiplab := oe.skiplab }

/-- biblatex's numeric labels: an entry's number counts the
numbered listed entries before it. -/
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

/-- The reference list a style builds from the cited entries: sorted, positions
assigned by list index. -/
public def resolveEntries (style : Style) (cited : Array String)
    (find : String → Option Entry) (biblatex : Bool := false)
    (bbl : Option (BblOptions × Bool) := none) (months : Array String := Locale.en.months)
    (findRaw : String → Option Entry := fun _ => none) : Array Resolved :=
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

/-- The mark an item carries: in numbers mode its label,
else its position; none in author-year mode. -/
public def itemMarker (p : CitePunct) (r : Resolved) : Option String :=
  if p.numbers then some (r.label.getD (toString r.position)) else none

/-- The items a `\bibliography` block ships, each with what
reading its fields reported. -/
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

/-- The entries a biblatex list prints: all but those under `skipbib`. -/
public def bblListed (resolved : Array Resolved) : Array Resolved :=
  resolved.filter (!·.skipbib)

/-- The items biblatex's standard styles set, with each item's field reports and
the fields its driver read. -/
public def bblItems (o : BblOptions) (cvOf : String → FieldText) (p : CitePunct)
    (resolved : Array Resolved) (months : Array String := Locale.en.months) :
    Array ((Ir.BibItem × FieldReport) × List String) :=
  let listed := bblListed resolved
  let renders := (listed.foldl (init := ((#[] : Array (Array Ir.Inline × FieldReport × List String)),
      (none : Option String), ({} : FieldCache))) fun (acc, prev, cache) r =>
    let names := bblHeadNames o r.entry
    let dash := o.style == .authoryear && o.dashed && names.isSome && names == prev
    let (out, cache) := renderBbl o (cvOf r.key) r.entry
      (if o.style == .authoryear then r.extra else "") dash r.labelUl months cache
    (acc.push out, names, cache)).1
  listed.mapIdx fun i r =>
    let rd := renders[i]?.getD (#[], {}, [])
    (({ key := r.key, marker := itemMarker p r, content := rd.1 }, rd.2.1), rd.2.2)

public def bibItems (p : CitePunct) (style : Style) (resolved : Array Resolved) :
    Array Ir.BibItem :=
  (bibItemsWith (fun _ => plainField) p style resolved).map (·.1)

public theorem bibItems_marker_exact (cvOf : String → FieldText) (p : CitePunct) (style : Style)
    (resolved : Array Resolved) (h : p.numbers = true) (i : Nat) (hi : i < resolved.size) :
    (bibItemsWith cvOf p style resolved)[i]?.bind (·.1.marker) =
      some (resolved[i].label.getD (toString resolved[i].position)) := by
  simp [bibItemsWith, itemMarker, Array.getElem?_mapIdx, Array.getElem?_eq_getElem hi, h]

public theorem bblItems_marker_exact (o : BblOptions) (cvOf : String → FieldText)
    (p : CitePunct) (resolved : Array Resolved) (months : Array String) (h : p.numbers = true)
    (i : Nat) (hi : i < (bblListed resolved).size) :
    (bblItems o cvOf p resolved months)[i]?.bind (·.1.1.marker) =
      some ((bblListed resolved)[i].label.getD (toString (bblListed resolved)[i].position)) := by
  simp [bblItems, itemMarker, Array.getElem?_mapIdx, Array.getElem?_eq_getElem hi, h]

public theorem positions_exact (style : Style) (cited : Array String)
    (find : String → Option Entry) (biblatex : Bool) (bbl : Option (BblOptions × Bool))
    (months : Array String) (findRaw : String → Option Entry)
    (i : Nat) (hi : i < (resolveEntries style cited find biblatex bbl months findRaw).size) :
    (resolveEntries style cited find biblatex bbl months findRaw)[i].position = i + 1 := by
  unfold resolveEntries at hi ⊢
  rcases bbl with _ | ⟨o, _ | _⟩ <;>
    simp only [numericLabels] at hi ⊢ <;>
    split <;> (try split) <;> simp [alphaMarks, extraLabels] at hi ⊢

public theorem sortResolved_mem (so : SortOrder) (xs : List Resolved) (z : Resolved) :
    z ∈ sortResolved so xs ↔ z ∈ xs := by
  cases so <;> simp [sortResolved, sortByKey]

public theorem sortResolved_length (so : SortOrder) (xs : List Resolved) :
    (sortResolved so xs).length = xs.length := by
  cases so <;> simp [sortResolved, sortByKey]

public theorem compare_citation_asymm (a b : Resolved)
    (h : SortOrder.citation.compare a b = .gt) :
    SortOrder.citation.compare b a ≠ .gt := by
  simp [SortOrder.compare, Nat.compare_eq_gt] at h ⊢
  omega

public theorem sortResolved_sorted_citation (xs : List Resolved) :
    (sortResolved .citation xs).Pairwise
      (fun a b => SortOrder.citation.compare a b ≠ .gt) := by
  have h := List.pairwise_mergeSort (le := fun (a b : Resolved) => decide (a.position ≤ b.position))
    (fun a b c hab hbc => by simp at hab hbc ⊢; omega)
    (fun a b => by simp; omega) xs
  refine h.imp fun {a b} hab => ?_
  simp [SortOrder.compare, Nat.compare_eq_gt] at hab ⊢
  omega

/-- A run of an alternative set: a citation its style's text. -/
private def resolveRun (p : CitePunct) (find : Resolver) : Ir.AltRun → Ir.AltRun
  | .cite form keys _ => .cite form keys (some (Ir.plainText (renderCite p form (keys.map find))))
  | .text t => .text t

/-- An alternative's citations set: each its style's text. -/
private def resolveAlt (p : CitePunct) (find : Resolver) : Ir.Alt → Ir.Alt
  | .citing runs => .citing (runs.map (resolveRun p find))
  | .undeclared => .undeclared
  | .decorative => .decorative
  | .described t => .described t

private theorem pendingKeys_resolveAlt (p : CitePunct) (find : Resolver) (a : Ir.Alt) :
    (resolveAlt p find a).pendingKeys = #[] := by
  cases a with
  | citing runs =>
    have hr : ∀ r, (resolveRun p find r).pending = #[] := by
      intro r; cases r <;> rfl
    rcases runs with ⟨l⟩
    simp only [resolveAlt, Ir.Alt.pendingKeys]
    apply Array.toList_inj.mp
    simp [hr]
  | undeclared | decorative | described _ => rfl

mutual

/-- The citation rewrite: every `.cite` node becomes its rendering under the
document's punctuation, beside the citation it renders; a `\nocite` sets nothing. -/
-- conserves: none — resolution rewrites citation marks
private def resolveInline (p : CitePunct) (find : Resolver)
    (out : Array Ir.Inline) : Ir.Inline → Array Ir.Inline
  | .cite form keys =>
    if form.cmd == .nocite then out
    else out.push (.cited form keys (renderCite p form (keys.map find)))
  | .cited form keys ink => out.push (.cited form keys (resolveInlines p find #[] ink.toList))
  | .styled st body => out.push (.styled st (resolveInlines p find #[] body.toList))
  | .colored c nm body => out.push (.colored c nm (resolveInlines p find #[] body.toList))
  | .located nm body => out.push (.located nm (resolveInlines p find #[] body.toList))
  | .role nm body => out.push (.role nm (resolveInlines p find #[] body.toList))
  | .link u body => out.push (.link u (resolveInlines p find #[] body.toList))
  | .decorated kind body =>
    out.push (.decorated kind (resolveInlines p find #[] body.toList))
  | .boxed b body =>
    out.push (.boxed b (resolveInlines p find #[] body.toList))
  | .onSteps spec body => out.push (.onSteps spec (resolveInlines p find #[] body.toList))
  | .altSteps spec active otherwise =>
    out.push (.altSteps spec (resolveInlines p find #[] active.toList)
      (resolveInlines p find #[] otherwise.toList))
  | .footnote n body => out.push (.footnote n (resolveInlines p find #[] body.toList))
  | .text s => out.push (.text s)
  | .math d src => out.push (.math d src)
  | .formula d src body => out.push (.formula d src body)
  | .image src size alt => out.push (.image src size (resolveAlt p find alt))
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
    | .cite _ _ => simp only [resolveInline]; split <;> simp
    | .styled _ body | .colored _ _ body | .located _ body | .role _ body | .link _ body
    | .decorated kind body | .boxed _ body | .onSteps _ body | .footnote _ body | .cited _ _ body =>
      simp [resolveInline]
    | .altSteps _ _ _ => simp [resolveInline]
    | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _
    | .label _ | .ref _ _ _ _
    | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _ | .pageNumber | .pageCount | .linebreak _ =>
      simp [resolveInline]

mutual

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
  | .cited f ks ink =>
    rw [citeFreeOne] at h
    rw [resolveInline, resolveInlines_id p find ink.toList h]
  | .decorated kind body =>
    rw [citeFreeOne] at h
    rw [resolveInline, resolveInlines_id p find body.toList h]
  | .boxed b body =>
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
  | .image src size alt =>
    cases alt with
    | citing _ => simp [citeFreeOne] at h
    | undeclared | decorative | described _ => rw [resolveInline]; rfl
  | .text _ | .math _ _ | .formula _ _ _ | .icon _ _
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

/-- Whether a paragraph holds only `\nocite`s and spaces,
which TeX never begins. -/
private def nociteOnly (content : Array Ir.Inline) : Bool :=
  content.any (fun x => match x with | .cite f _ => f.cmd == .nocite | _ => false) &&
    content.all fun x => match x with
      | .cite f _ => f.cmd == .nocite
      | .text s => s.all Char.isWhitespace
      | _ => false

mutual

/-- The block half of the rewrite: citations resolve, each `\bibliography`
marker takes the style's items, and a paragraph of `\nocite`s is dropped. -/
-- conserves: none — resolution rewrites citations and fills the reference list
private def resolveBlock (p : CitePunct) (find : Resolver)
    (items : Array Ir.BibItem) (out : Array Ir.Block) (b : Ir.Block) :
    Array Ir.Block :=
  match b with
  | .bibliography src declared _ =>
    out.push (.bibliography src declared
      (items.map fun it => { it with content := resolveArr p find it.content }))
  | .contents spec entries =>
    out.push (.contents spec (entries.map fun e => { e with title := resolveArr p find e.title }))
  | .para content =>
    if nociteOnly content then out else out.push (.para (resolveArr p find content))
  | .equation n content =>
    out.push (.equation (resolveArr p find n) (resolveArr p find content))
  | .section l st num title => out.push (.section l st num (resolveArr p find title))
  | .abstract body => out.push (.abstract (resolveBlocks p find items #[] body.toList))
  | .list ordered s its => out.push (.list ordered s (resolveItems p find items #[] its.toList))
  | .center body => out.push (.center (resolveBlocks p find items #[] body.toList))
  | .ragged s body => out.push (.ragged s (resolveBlocks p find items #[] body.toList))
  | .quote q body => out.push (.quote q (resolveBlocks p find items #[] body.toList))
  | .lines ls => out.push (.lines (ls.map fun l => { l with content := resolveArr p find l.content }))
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
    out.push (.table cols pl pr (resolveRows p find items #[] rows.toList) rules spans)
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
  | .picture pic => out.push (.picture { pic with alt := resolveAlt p find pic.alt })
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

private def resolveRows (p : CitePunct) (find : Resolver)
    (items : Array Ir.BibItem) (out : Array (Array (Array Ir.Block)))
    (rows : List (Array (Array Ir.Block))) : Array (Array (Array Ir.Block)) :=
  match rows with
  | [] => out
  | row :: rest =>
    resolveRows p find items (out.push (resolveItems p find items #[] row.toList)) rest
termination_by structural rows

end

/-- The citation rewrite over the whole document, body and furniture regions. -/
public def resolveDoc (p : CitePunct) (find : Resolver) (items : Array Ir.BibItem)
    (doc : Ir.Doc) : Ir.Doc :=
  Ir.mapDoc (resolveArr p find)
    (fun bs => resolveBlocks p find items #[] bs.toList) doc

/-- Whether a block survives bibliography resolution: all but a paragraph of
only nonprinting citations. -/
public def keepsBlock : Ir.Block → Bool
  | .para content => !nociteOnly content
  | .bibliography .. | .contents .. | .equation .. | .section .. | .abstract .. | .list ..
  | .center .. | .ragged .. | .quote .. | .lines .. | .titled .. | .disclosure .. | .role .. | .link ..
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
    cases hk : keepsBlock b <;> simp [hk]; omega

/-- Metadata of surviving top-level blocks, reindexed to the output document. -/
public def remapSources {α : Type} (doc : Ir.Doc) (sites : Array (Nat × α)) :
    Array (Nat × α) :=
  sites.filterMap fun (i, source) =>
    if doc.body[i]?.any keepsBlock then
      some (((doc.body.toList.take i).filter keepsBlock).length, source)
    else none

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

/-- natbib's author-year label in a `\bibitem`'s optional
argument: the names and the year. -/
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

/-- The entry a `thebibliography` item cites as in author-year mode. -/
private def ownEntry (key : String) (label : Option (String × String)) : Entry :=
  let fields := match label with
    | some (names, year) =>
      let names := if names.endsWith " et al." then (names.dropEnd 7).toString ++ " and others"
        else names
      #[("author", names), ("year", year)]
    | none => #[]
  { (default : Entry) with key, fields }

/-- A document's own `thebibliography` list resolved, its
entries in source order. -/
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
    -- A hand-written label sets flush left, as latex.ltx's `\@lbibitem` sets it.
    items := items.push
      { it with marker := if p.numbers then some (label.getD (toString n)) else none
                labelFlush := p.numbers && it.marker.isSome }
  return (p, resolved, items)

/-- A field's `\cite` read as biblatex's author-year styles
read it, as the bare citation. -/
private def bareCites (xs : Array Ir.Inline) : Array Ir.Inline :=
  Ir.mapInlines (fun x => match x with
    | .cite f keys => if f.cmd == .auto then .cite { f with cmd := .alp } keys else .cite f keys
    | x => x) xs

/-- The field citations a document makes: each key, the field, and whether the
star asks the full title. -/
private def citeFieldUses (doc : Ir.Doc) : Array (String × Ir.CiteField × Bool) :=
  Ir.foldDoc (fun acc x => match x with
    | .cite f keys => match f.cmd with
      | .field w => keys.foldl (fun acc k => acc.push (k, w, f.full)) acc
      | _ => acc
    | _ => acc) #[] doc

/-- What a field citation prints under a BibTeX style, which defines none. -/
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

/-- One run of the reference list over a sequence of citations. -/
private structure ListRun where
  cited : Array String
  db : Database
  resolved : Array Resolved
  rendered : Array (Ir.BibItem × FieldReport)
  readSets : Array (List String)

/-- The keys the set entries' own fields cite, in list order, each once, with
the first entry citing it. -/
private def fieldCites (rendered : Array (Ir.BibItem × FieldReport)) : Array (String × String) :=
  (rendered.foldl (init := ((#[] : Array (String × String)), (∅ : Std.HashSet String)))
    fun acc (it, _) => Ir.foldInlines (fun (out, seen) x => match x with
      | .cite _ keys => keys.foldl (init := (out, seen)) fun (out, seen) k =>
          if seen.contains k then (out, seen) else (out.push (k, it.key), seen.insert k)
      | _ => (out, seen)) acc it.content).1

/-- The keys of `uncited` that `named` does not hold, when
it holds one at least. -/
private def spend (uncited : List String) (named : Std.HashSet String) :
    Option { rest : List String // rest.length < uncited.length } :=
  if h : uncited.filter (named.contains ·) = [] then none
  else some ⟨uncited.filter (!named.contains ·), by
    rw [List.length_filter_lt_length_iff_exists]
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ h
    exact ⟨x, (List.mem_filter.mp hx).1, by simp [(List.mem_filter.mp hx).2]⟩⟩

/-- The keys a list run's set entries cite in their fields
that `seen` does not hold, each once. -/
private def freshCites (canon : String → String) (r : ListRun) (seen : Std.HashSet String) :
    Array String :=
  ((fieldCites r.rendered).foldl (init := ((#[] : Array String), seen))
    fun (out, seen) (k, _) =>
      let k := canon k
      if seen.contains k then (out, seen) else (out.push k, seen.insert k)).1

/-- Where the field citations of `frontier`'s entries lead, round by round. -/
private def discoverFieldCites (run : Array String → ListRun) (canon : String → String)
    (uncited : List String) (frontier found : Array String) (foundSet : Std.HashSet String) :
    Array String × Std.HashSet String :=
  let fresh := freshCites canon (run frontier) foundSet
  let foundSet := fresh.foldl (·.insert ·) foundSet
  match spend uncited foundSet with
  | none => (found ++ fresh, foundSet)
  | some ⟨rest, _⟩ => discoverFieldCites run canon rest fresh (found ++ fresh) foundSet
termination_by uncited.length

/-- The list completed with the entries its fields cite, as the next BibTeX or
biber run lists them. -/
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

/-- An entry's fields as BibTeX sets them, white space runs one space, in name order, one empty$
reads as missing left out. -/
private def setFields (e : Entry) : List (String × String) :=
  let one (v : String) : String :=
    " ".intercalate ((v.splitOn " ").flatMap (·.splitOn "\n") |>.flatMap (·.splitOn "\t")
      |>.flatMap (·.splitOn "\r") |>.filter (!·.isEmpty))
  ((e.fields.toList.map fun (k, v) => (k, one v)).filter (!·.2.isEmpty)).mergeSort
    fun a b => a.1 ≤ b.1

/-- Whether a repeated entry sets what the first does, its fields in any order. -/
private def sameEntry (a b : Entry) : Bool := a.kind == b.kind && setFields a == setFields b

/-- The document's citations and reference lists resolved
against its `.bib` sources. -/
private def analyse (sources : Array (String × String)) (doc : Ir.Doc) (rd : FieldReading)
    (sites : Array Ir.CiteSite) (absent : Array String) :
    CitePunct × Resolver × Array Ir.BibItem × Array Diag × Array (String × Ir.PicSrc) × Nat :=
    Id.run do
  let requested := Ir.bibRefs doc
  let declared := (Ir.bibStyleName doc).map fun name => (name, Style.named name)
  -- The month macros are the style's, in the document's language where the style is English.
  let months := if (declared.bind (·.2)).any (·.shortMonths) && doc.info.locale.tag == "en"
    then shortMonthNames else doc.info.locale.months
  let mut diags : Array Diag := #[]
  let mut entries : Array Entry := #[]
  let mut origin : Std.HashMap String String := {}
  let mut seen : Std.HashSet String := {}
  let mut firstAt : Std.HashMap String (String × Entry) := {}
  -- Each later entry of a key whose fields differ from the first's: the key, its place, the first's.
  let mut repeats : Array (String × Span × String) := #[]
  let mut preambles : Array String := #[]
  -- One `@string` store for the list's files, read in turn.
  let mut store := monthMacros months
  let mut undefined : Std.HashMap String (Array String) := {}
  for src in requested do
    match sources.find? (·.1 == src) with
    | none => pure ()  -- the driver's missing-file diagnostic already fired
    | some (_, text) =>
      let parsed := parse text store (biber := (CitePunct.ofDoc doc.citeSetup none true).biblatex)
      store := parsed.macros
      for (k, n) in parsed.undefined do
        unless (undefined.getD k #[]).contains n do
          undefined := undefined.insert k ((undefined.getD k #[]).push n)
      preambles := preambles ++ parsed.preambles
      for (pos, msg) in parsed.errors do
        diags := diags.push (Diag.of .W0352
          (Diag.say .W0352 .entry (obj := some (some .file, sourceName src)))
          (some ⟨sourceName src, pos⟩) (detail := some msg))
      for e in parsed.entries do
        if seen.contains e.key then
          if let some (f, first) := firstAt.get? e.key then
            unless sameEntry first e do
              repeats := repeats.push (e.key, ⟨sourceName src, e.pos⟩, s!"{sourceName f}:{first.pos.line}")
        else
          entries := entries.push e
          seen := seen.insert e.key
          origin := origin.insert e.key src
          firstAt := firstAt.insert e.key (src, e)
  let declared ← do
    match declared with
    | none => pure none
    | some (_, some s) => pure (some s)
    | some (name, none) =>
        diags := diags.push (Diag.of .W0353 (Diag.say .W0353 .style name)
          (help := s!"styles known: {", ".intercalate (Style.byName.map (·.1))}"))
        pure (some Style.unsrtnat)
  let p := CitePunct.ofDoc doc.citeSetup ((Ir.bibStyleName doc).bind (natbibRows.lookup ·))
    (declared.all (·.labels))
  let p := { p with ink := (doc.styles.find? "cite").bind (·.color) }
  -- biblatex sorts by the load's `sorting`: nty for numeric styles and nyt for author-year.
  let bbl := (BblOptions.ofDecls doc.citeSetup).map ({ · with mainLang := doc.info.locale.tag })
  let style := declared.getD Style.unsrtnat
  let sorting := (doc.citeSetup.bind (CiteDecl.last? · .sorting)).getD "nty"
  let style := match bbl with
    | some o => { style with sort := match sorting with
        | "none" => .citation
        | t => .bbl (if CiteDecl.sortingTemplates.contains t then t
            else if o.style == .authoryear then "nyt" else "nty") o }
    | none => if p.biblatex && style.sort != .citation then
        { style with sort := .bbl (if p.numbers then "nty" else "nyt") {} } else style
  let p := { p with useprefix := bbl.any (·.useprefix) }
  let proc : Processor := if p.biblatex then .biber else .bibtex
  -- An entry's `ids` are other keys it is cited by.
  let keys : Std.HashSet String := entries.foldl (·.insert ·.key) {}
  let aliases : Std.HashMap String String := entries.foldl (init := {}) fun m e =>
    (e.refsBy "ids").foldl (init := m) fun m a =>
      if keys.contains a || m.contains a then m else m.insert a e.key
  let canon (k : String) : String := aliases.getD k k
  let cited := expandStar entries ((citedKeys doc).map canon)
  let shown := (citedKeys doc (·.cmd != .nocite)).foldl (·.insert ·) (∅ : Std.HashSet String)
  -- Each `@set` member is listed as its own entry; the set is cited as its first member.
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
  -- The list is typeset under its `@preamble` definitions and sorted without them.
  let macros := preambleMacros preambles
  let typeset := if macros.isEmpty then entries else
    entries.map fun e => { e with fields := e.fields.map fun (f, v) => (f, expandMacros macros v) }
  let positions : Std.HashMap String Pos := entries.foldl (fun m e => m.insert e.key e.pos) {}
  let spanOf (k : String) : Span :=
    ⟨sourceName ((origin.get? k).getD ""), (positions.get? k).getD {}⟩
  let cv (k : String) : FieldText := rd (spanOf k)
  let own := Ir.ownBibItemsBlocks doc.body
  let prepared := Database.prepare proc months typeset
  let rawPrepared := if macros.isEmpty then prepared else Database.prepare proc months entries
  -- The TeX a label or a citation's names are spelt in, set as the entry's fields are.
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
  -- A key named twice loses the later entry where the list reads the key: cited, listed, or
  -- lending its fields by crossref or xdata.
  let reads : Std.HashSet String := Id.run do
    let mut seen : Std.HashSet String := {}
    let mut todo : Array String := cited ++ db.list
    for _ in [0:todo.size + entries.size + 1] do
      match todo.back? with
      | none => break
      | some k =>
        todo := todo.pop
        unless seen.contains k do
          seen := seen.insert k
          if let some e := prepared.own.get? k then
            todo := todo ++ ((e.refsBy "crossref" ++ e.refsBy "xdata").filter (!seen.contains ·)).toArray
    return seen
  for (k, at_, first) in repeats do
    if reads.contains k then
      diags := diags.push (Diag.of .W0450 (Diag.say .W0450 .entry k) (some at_)
        (help := "one entry per key: delete this one or give it a key of its own")
        (subject := some ("bibkey:" ++ k)) (detail := some s!"the first at {first}"))
  let findEntry (k : String) : Option Entry := db.entries.get? k
  let (p, resolved, rendered, readSets) :=
    if own.isEmpty then (p, run.resolved, run.rendered, run.readSets)
    else
      let (p, resolved, items) := ownList p own
      (p, resolved, items.map (·, ({} : FieldReport)), #[])
  let labelled (r : Resolved) : Resolved :=
    let r := match bbl with
      | some o => if r.citeNames.isSome then r else
        let (l, pics) := bblCiteLabel o (cv r.key) months r.entry
        if l.isEmpty then r
        else { r with citeLabel := some l, inkPictures := r.inkPictures ++ pics }
      | none => r
    let namesTeX := if p.biblatex then r.citeNames else some (labelSource r.entry false p.useprefix)
    { r with namesInk := namesTeX.bind (inkOf r.key), shortInk := r.shorthand.bind (inkOf r.key) }
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
      let ink := resolveArr p labelFind ink
      m.insert (canon k) { r with fieldInk := r.fieldInk.push ((w, full), ink)
                                  inkPictures := r.inkPictures ++ pics }
  let find : Resolver := fun k => byCite.get? (canon k)
  -- An entry's own citations resolve as the body's do.
  let bare := bbl.any (·.cite == .authoryear)
  let items := rendered.map fun (it, _) =>
    { it with content := resolveArr p find (if bare then bareCites it.content else it.content) }
  -- An entry's declared language tags its text, as biblatex's `autolang=hyphen`.
  let items := items.map fun it =>
    match (db.own.get? it.key).bind fun e =>
        (e.field? "langid").orElse fun _ => e.field? "hyphenation" with
    | some l =>
      let tag := Locale.babelTagOf (text l).trimAscii.toString
      if tag.isEmpty || tag == doc.info.locale.tag then it
      else { it with content := #[.styled (.lang tag) it.content] }
    | none => it
  -- The list's notes number where the list stands, after the notes before it.
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
  let mut reported : Std.HashSet String := {}
  for (it, ds) in rendered do
    let span : Option Span := (origin.get? it.key).map fun src =>
      ⟨sourceName src, ((findEntry it.key).map (·.pos)).getD {}⟩
    for d in ds.diags do
      let d := { d with span := span.orElse fun _ => d.span }
      let d := if d.kind != .W0429 then d else match findEntry it.key with
        | some e => nameUnread (entries.find? (·.key == it.key)) e d
        | none => d
      let site := s!"{d.code}\u0000{d.message}\u0000{d.detail}\u0000{Diag.spanKey d.span}\u0000{d.subject}"
      unless reported.contains site do
        reported := reported.insert site
        diags := diags.push d
  -- A field the style prints nowhere for an entry declaring it is named once (N0029).
  let styleName := match bbl with
    | some o => if o.style == BblStyle.authoryear then "biblatex's authoryear style"
      else "biblatex's numeric style"
    | none => s!"the bibliography style '{(Ir.bibStyleName doc).getD "unsrtnat"}'"
  let written : Std.HashMap String Entry := entries.foldl (fun m e => m.insert e.key e) {}
  -- premise: biblatexFieldCoverageChecks — the drivers read every printed field
  let listedReads := if bbl.isSome then (bblListed resolved).zip readSets else resolved.zip readSets
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
    diags := diags.push (Diag.of .N0029 (Diag.say .N0029 .field f)
      (detail := some s!"{styleName} prints it for no {types} entry: {shown}")
      (subject := some ("bibfield:" ++ f)))
  -- A reference a listed entry's reading left unresolved is named (W0425).
  for r in db.broken do
    let k := r.holder
    let m := r.target
    let fld := r.field
    let xf := r.source
    let atEntry : Option Span := (origin.get? k).map fun src => ⟨sourceName src, (positions.get? k).getD {}⟩
    let near := entries.find? fun e => e.key != m && e.key.toLower == m.toLower
    let via := if xf.isEmpty then fld else s!"{fld} takes {xf}"
    let (fault, help) : String × String := match r.fault with
      | .missing =>
        ("no such entry",
         match near with
          | some e => s!"the entry '{e.key}' differs only in case; biber matches keys exactly: \
            write '{if xf.isEmpty then s!"{fld} = \{{e.key}}" else e.key}'"
          | none => s!"add an entry with key '{m}' to the .bib file, or fix the spelling in '{fld}'")
      | .unread =>
        (s!"'{m}' stands before '{k}', which BibTeX reads in one pass",
         s!"move '{m}' after the entries that cross-reference it, or cite '{m}' as well")
      | .notData =>
        ("not an @xdata entry",
         s!"make '{m}' an @xdata entry, or name the data '{k}' needs in '{fld}'")
      | .cycle path =>
        (s!"a cycle, where biber stops: {" → ".intercalate (path.toList.map (s!"'{·}'"))}",
         s!"remove the reference to '{m}' from the {fld} of '{k}'")
      | .noField _ =>
        (s!"'{m}' holds no {xf}",
         s!"add '{xf}' to '{m}', or write the {fld} of '{k}' out")
      | .noPosition _ n =>
        (s!"the {xf} of '{m}' holds no item {n}",
         s!"name an item '{m}' holds, or write the {fld} of '{k}' out")
      | .shapes _ =>
        (s!"{xf} is a field of another kind",
         s!"take a field of the kind '{fld}' is, or write the {fld} of '{k}' out")
      | .malformed =>
        ("it names no field to take",
         s!"write it 'xdata=<key>-<field>', or write the {fld} of '{k}' out")
    diags := diags.push (Diag.of .W0425
      (Diag.say .W0425 .reference (Diag.Name.of m) (some (some .entry, k))) atEntry (help := help)
      (subject := some (if xf.isEmpty then s!"bibref:{m}" else s!"bibref:{m}-{xf}"))
      (detail := some s!"{via}: {fault}"))
  -- A value naming an undefined macro prints the name where BibTeX prints nothing (W0426).
  for k in db.list do
    for n in undefined.getD k #[] do
      let atEntry : Option Span := (origin.get? k).map fun src => ⟨sourceName src, (positions.get? k).getD {}⟩
      diags := diags.push (Diag.of .W0426
        (Diag.say .W0426 .string (Diag.Name.of n) (some (some .entry, k))) atEntry
        (help := s!"define it before its first use: '@string\{{n} = \"...\"}', in the .bib \
          file named first")
        (subject := some s!"bibstring:{n}"))
  if bbl.isSome then
    for r in bblListed resolved do
      let mine := (db.own.get? r.key).getD r.entry
      if let some rel := mine.field? "related" then
        diags := diags.push (Diag.of .W0423
          (Diag.say .W0423 .field "related" (some (some .entry, r.key)))
          ((origin.get? r.key).map fun src => ⟨sourceName src, mine.pos⟩)
          (detail := some s!"biblatex sets '{text rel}' after it")
          (subject := some ("bibrelated:" ++ r.key)))
  -- premise: biblatexOracleChecks — the strings and dates set are english.lbx's
  if let some o := (if requested.isEmpty then none else bbl) then
    let main := (o.language.filter fun l => !["autodetect", "auto"].contains l).orElse
      fun _ => o.babelMain
    let help := "load biblatex with 'language=english' and 'autolang=hyphen' to word the \
      list in English, as biblatex then does"
    let mut worded : Array String := #[]
    if let some m := main then
      if m != "english" then
        worded := worded.push m
        diags := diags.push (Diag.of .W0421
          (Diag.say .W0421 .language "English" (some (none, m)))
          (subject := some ("bibstrings:" ++ m ++ if o.language.any (· != "autodetect") then ":language" else ""))
          (help := help))
    if ["other", "other*", "langname"].contains o.autolang then
      for k in db.list do
        let lang := (db.own.get? k).bind fun e =>
          (e.field? "langid").orElse fun _ => e.field? "hyphenation"
        if let some l := lang.map (text · |>.trimAscii.toString) then
          if !l.isEmpty && l != "english" && some l != main && !worded.contains l then
            worded := worded.push l
            diags := diags.push (Diag.of .W0421
              (Diag.say .W0421 .language "English" (some (none, l)))
              (detail := some s!"autolang={o.autolang}, langid '{l}'")
              (subject := some ("bibstrings:" ++ l ++ ":autolang")) (help := help))
  -- premise: biblatexLocaleSortChecks — carried tailorings sort as biber does
  if let some o := (if requested.isEmpty then none else bbl) then
    let file := bblSortFile o
    if Collate.outsideRows file then
      diags := diags.push (Diag.of .W0427 (Diag.say .W0427 .collation file)
        (help := "load biblatex with 'sortlocale=en_US' to sort the list by the default collation")
        (subject := some ("bibsort:" ++ file)))
  for k in cited do
    if let some ms := sets.get? k then
      diags := diags.push (Diag.of .W0422
        (Diag.say .W0422 .entryType "@set" (some (some .entry, k)))
        (((origin.get? k).map fun src => ⟨sourceName src, ((db.own.get? k).map (·.pos)).getD {}⟩))
        (subject := some ("bibset:" ++ k)) (detail := some s!"{ms.size} members"))
  -- A date biber cannot read prints as written, named (W0420).
  for r in resolved do
    let mine := (db.own.get? r.key).getD r.entry
    let atEntry : Option Span := (origin.get? r.key).map fun src => ⟨sourceName src, mine.pos⟩
    for f in ["date", "urldate", "eventdate", "origdate"] do
      if let some v := mine.value? f then
        if (DateValue.parse v).isNone then
          diags := diags.push (Diag.of .W0420
            (Diag.say .W0420 .date (Diag.Name.value (text v)) (some (some .entry, r.key))) atEntry
            (detail := if f == "date" then none else some s!"field {f}")
            (help := s!"write it as YYYY, YYYY-MM or YYYY-MM-DD, a range with '/': \
              '{f} = \{2020-03}'")
            (subject := some s!"bibdate:{r.key}:{f}"))
    if proc == .biber then
      if let some m := mine.value? "month" then
        if (monthNumber months m).isNone then
          diags := diags.push (Diag.of .W0420
            (Diag.say .W0420 .date (Diag.Name.value (text m)) (some (some .entry, r.key))) atEntry
            (detail := some "field month")
            (help := "write it as a number, 1 to 12, or as a month's name: 'month = {3}'")
            (subject := some s!"bibdate:{r.key}:month"))
  let citedBy : Std.HashMap String String := (fieldCites rendered).foldl (init := {})
    fun m (k, by_) => if m.contains (canon k) then m else m.insert (canon k) by_
  -- premise: Tests.BibEdges.missingChecks — a list every file of which the driver named absent is
  -- those files' loss, its citations' marks with it
  let unread := own.isEmpty && !requested.isEmpty && requested.all absent.contains
  let siteOf : Std.HashMap (String × Bool) Ir.CiteSite := sites.foldl (init := {}) fun m c =>
    if m.contains (c.key, c.nocite) then m else m.insert (c.key, c.nocite) c
  unless (requested.isEmpty && own.isEmpty) || unread do
    for k in cited do
      if (find k).isNone then
        let shownHere := shown.contains k
        let site := siteOf.get? (k, !shownHere)
        -- A key a field alone cites is spelled in TeX, as the field is read.
        let surface := if shownHere || !citedBy.contains k then
            (site.map (·.surface)).getD doc.surface
          else .tex
        let md := surface != .tex
        let cmd := if shownHere || citedBy.contains k then "cite" else "nocite"
        let atEntry : Option Span := if shownHere || !citedBy.contains k then site.map (·.span) else
          (citedBy.get? k).bind fun e => (origin.get? e).map fun src =>
            ⟨sourceName src, (positions.get? e).getD {}⟩
        -- The fix is spelled in the surface the citation was written in, its own command's name.
        let written := (site.bind (·.span.pos.command)).filter (·.startsWith "\\")
        let spelling := if md then s!"@{k}" else written.getD s!"\\{cmd}"
        diags := diags.push (Diag.of .W0351
          (if md then Diag.say .W0351 .citation k else Diag.tex .citation [k]) atEntry
          (help := if own.isEmpty then s!"add an entry with key '{k}' to the .bib file, \
            or fix the spelling in {spelling}"
            else s!"add \\bibitem\{{k}} to the reference list, or fix the spelling in {spelling}")
          (subject := some k))
  let pictures := resolved.foldl (init := rendered.foldl (init := #[]) fun acc (_, rep) =>
      acc ++ rep.pictures) fun acc r =>
    match find r.key with
    | some r' => acc ++ r'.inkPictures
    | none => acc
  return (p, find, items, diags, pictures, afterInk - base)

/-- A loss the reference list reports at a site after the run has named it,
demoted to a note with no help. -/
public def demoteRepeated (prior ds : Array Diag) : Array Diag :=
  let key (d : Diag) : Option String := d.subject.map fun s =>
    s!"{d.code}\u0000{s}\u0000{Diag.outputKey d.output}"
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

/-- The document without the heading its markdown metadata sets over the list at its end, where the
list lists nothing, as Pandoc's citation processing sets none (`CiteDecl.Word.sectionTitle`). -/
private def untitled (doc : Ir.Doc) (items : Array Ir.BibItem) : Ir.Doc :=
  if !items.isEmpty || !(doc.citeSetup.getD #[]).contains (.word .sectionTitle) then doc else
  let last := doc.body.zipIdx.foldl (init := none) fun acc (b, i) =>
    if b matches .bibliography .. then some i else acc
  match last with
  | some (k + 1) =>
    if doc.body[k]? matches some (.section ..) then { doc with body := doc.body.eraseIdxIfInBounds k }
    else doc
  | _ => doc

/-- The document's citations and reference lists resolved against its `.bib`
sources, every field read through `rd`. -/
public def apply (sources : Array (String × String)) (doc : Ir.Doc)
    (rd : FieldReading) (sites : Array Ir.CiteSite := #[]) (absent : Array String := #[]) :
    Ir.Doc × Array Diag :=
  match analyse sources doc rd sites absent with
  | (p, find, items, diags, pictures, notes) =>
    (((resolveDoc p find items (untitled doc items)).addPictures pictures).withListNotes notes, diags)

/-- The keys of the references the document's reference lists hold, each once in
list order; `pending` keeps only those no label answered. -/
public def listRefKeys (doc : Ir.Doc) (pending : Bool) : Array String :=
  Ir.foldBlocks (fun out b => match b with
    | .bibliography _ _ items => items.foldl (init := out) fun out it =>
        Ir.foldInlines (fun out x => match x with
          | .ref key _ _ target =>
            if (pending && target.isSome) || out.contains key then out else out.push key
          | _ => out) out it.content
    | _ => out) (fun out _ => out) #[] doc.body

/-- A reference list's references resolved against the document's labels. -/
public def resolveListRefs (table : Ir.RefTable) (doc : Ir.Doc) : Ir.Doc :=
  if (Ir.bibRefs doc).isEmpty || !Ir.foldDoc (fun b x => b || x matches .ref ..) false doc
  then doc
  else { doc with body := Ir.resolveRefs doc.info.locale table doc.body }

/-- Where W0349 names a key: the body's first site, else a
reference list's command. -/
public def refSpanOf (bodySpan : String → Option Span) (listSpan : Option Span)
    (listed : Array String) (key : String) : Option Span :=
  (bodySpan key).orElse fun _ => if listed.contains key then listSpan else none

/-- Whether an inline is a citation link's body: its mark's
text, or that text in the declared ink. -/
private def plainMark : Ir.Inline → Bool
  | .text _ => true
  | .colored _ _ b => b.all fun x => match x with | .text _ => true | _ => false
  | _ => false

/-- Whether an inline is a node the citation renderer emits
for a label citation. -/
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

private theorem emitLink_plain (p : CitePunct) (out : Array Ir.Inline) (anchor : Option String)
    (s : String) (h : out.all plainCite = true) : (emitLink p out anchor s).all plainCite = true := by
  cases anchor with
  | none => exact emit_plain out s h
  | some a =>
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

private theorem citeFree_census (x : Ir.Inline) (h : citeFreeOne x = true) :
    ∀ (acc : Array Ir.Unresolved) (q : Ir.Unresolved),
      q ∈ Ir.foldInline Ir.pendingStep acc x → q ∈ acc ∨ q.isCite = false := by
  match x with
  | .styled _ body | .colored _ _ body | .located _ body | .role _ body | .link _ body
  | .decorated _ body | .boxed _ body | .onSteps _ body | .footnote _ body | .cited _ _ body =>
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
  | .image _ _ alt =>
    intro acc q hq
    cases alt with
    | citing _ => simp [citeFreeOne] at h
    | undeclared | decorative | described _ =>
      simp only [Ir.foldInline, Ir.pendingStep, Ir.pendingLeaf, Ir.Alt.pendingKeys, Array.map_empty,
        Array.append_empty] at hq
      exact .inl hq
  | .text _ | .math _ _ | .formula _ _ _ | .icon _ _ | .label _
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

private theorem linkPiece_citeFree (p : CitePunct) (out : Array Ir.Inline)
    (anchor : Option String) (before piece : Array Ir.Inline) (h : citeFreeList out.toList = true) :
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
    cases anchor with
    | some a =>
      simp only
      rw [Array.toList_push, Array.toList_append]
      refine citeFreeList_append _ _ (citeFreeList_append _ _ h hg.1) ?_
      cases p.ink <;> simp [citeFreeList, citeFreeOne, hg.2]
    | none =>
      simp only
      rw [Array.toList_append, Array.toList_append]
      exact citeFreeList_append _ _ (citeFreeList_append _ _ h hg.1) hg.2
  · cases anchor with
    | some a =>
      rw [emitLink, Array.toList_push]
      refine citeFreeList_append _ _ (emit_citeFree _ _ h) ?_
      cases p.ink <;> simp [citeFreeList, citeFreeOne]
    | none => exact emit_citeFree _ _ (emit_citeFree _ _ h)

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
      · split
        · rw [Array.toList_push]
          refine citeFreeList_append _ _ hsep ?_
          simp [citeFreeList, citeFreeOne, hink.2]
        · rw [Array.toList_append]
          exact citeFreeList_append _ _ hsep (by simpa using hink.2)
      · rw [Array.toList_append]
        exact citeFreeList_append _ _ hsep (by simpa using hink.2)

private theorem renderCite_citeFree (p : CitePunct) (f : Ir.CiteForm)
    (parts : Array (Option Resolved)) :
    citeFreeList (renderCite p f parts).toList = true := by
  unfold renderCite
  split
  · exact citeFree_of_plain _ (emit_plain _ _ (by simp))
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

private theorem renderCite_pending (p : CitePunct) (f : Ir.CiteForm)
    (parts : Array (Option Resolved)) (acc : Array Ir.Unresolved) (q : Ir.Unresolved)
    (h : q ∈ Ir.foldInlineList Ir.pendingStep acc (renderCite p f parts).toList) :
    q ∈ acc ∨ q.isCite = false :=
  citeFreeList_census _ (renderCite_citeFree p f parts) acc q h

mutual

private theorem resolveInline_pending (p : CitePunct) (find : Resolver) (x : Ir.Inline) :
    ∀ (acc : Array Ir.Unresolved) (q : Ir.Unresolved),
      q ∈ Ir.foldInlineList Ir.pendingStep acc (resolveInline p find #[] x).toList →
      q ∈ acc ∨ q.isCite = false := by
  match x with
  | .styled _ body | .colored _ _ body | .located _ body | .role _ body | .link _ body
  | .decorated kind body | .boxed _ body | .onSteps _ body | .footnote _ body | .cited _ _ body =>
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
    simp only [resolveInline] at h
    split at h
    · exact .inl (by simpa [Ir.foldInlineList] using h)
    · simp only [Array.toList_push, List.nil_append, Ir.foldInlineList, Ir.foldInline,
        Ir.pendingStep, Ir.pendingLeaf, Array.append_empty] at h
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
  | .image src size alt =>
    intro acc q h
    simp only [resolveInline, Array.toList_push, List.nil_append,
      Ir.foldInlineList, Ir.foldInline, Ir.pendingStep, Ir.pendingLeaf, pendingKeys_resolveAlt,
      Array.map_empty, Array.append_empty] at h
    exact .inl h
  | .text _ | .math _ _ | .formula _ _ _ | .icon _ _ | .label _
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

private theorem laidLines_pending (p : CitePunct) (find : Resolver) :
    ∀ (lines : List Ir.LaidLine) (acc : Array Ir.Unresolved) (q : Ir.Unresolved),
      q ∈ Ir.foldLaidLines Ir.pendingStep acc (lines.map fun l =>
        { l with content := resolveArr p find l.content }) →
      q ∈ acc ∨ q.isCite = false := by
  intro lines
  induction lines with
  | nil => intro acc q h; exact .inl h
  | cons l rest ih =>
    intro acc q h
    rw [List.map_cons, Ir.foldLaidLines] at h
    rcases ih _ q h with h' | hc
    · exact resolveInlines_pending p find l.content.toList acc q h'
    · exact .inr hc

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

private theorem contentsEntries_pending (p : CitePunct) (find : Resolver) :
    ∀ (entries : List Ir.ContentsEntry) (acc : Array Ir.Unresolved) (q : Ir.Unresolved),
      q ∈ Ir.foldContentsEntries Ir.pendingStep acc
        (entries.map fun e => { e with title := resolveArr p find e.title }) →
      q ∈ acc ∨ q.isCite = false := by
  intro entries
  induction entries with
  | nil => intro acc q h; exact .inl h
  | cons e rest ih =>
    intro acc q h
    rw [List.map_cons, Ir.foldContentsEntries] at h
    rcases ih _ q h with h' | hc
    · exact resolveInlines_pending p find e.title.toList acc q h'
    · exact .inr hc

mutual

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
  | .abstract body | .center body | .ragged _ body | .quote _ body | .role _ body
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
  | .list _ _ its =>
    intro out acc q h
    simp only [resolveBlock, Ir.foldBlockList_push, Ir.foldBlock] at h
    exact resolveItems_pending p find items its.toList #[] _ q h
  | .columns cols =>
    intro out acc q h
    simp only [resolveBlock, Ir.foldBlockList_push, Ir.foldBlock] at h
    exact resolveCols_pending p find items cols.toList #[] _ q h
  | .table _ _ _ rows _ _ =>
    intro out acc q h
    simp only [resolveBlock, Ir.foldBlockList_push, Ir.foldBlock] at h
    exact resolveRows_pending p find items rows.toList #[] _ q h
  | .algorithm _ _ lines =>
    intro out acc q h
    simp only [resolveBlock, Ir.foldBlockList_push, Ir.foldBlock, Array.toList_map] at h
    exact algLines_pending p find lines.toList _ q h
  | .lines ls =>
    intro out acc q h
    simp only [resolveBlock, Ir.foldBlockList_push, Ir.foldBlock, Array.toList_map] at h
    exact laidLines_pending p find ls.toList _ q h
  | .bibliography _ _ _ =>
    intro out acc q h
    simp only [resolveBlock, Ir.foldBlockList_push, Ir.foldBlock, Array.toList_map] at h
    exact bibItems_pending p find items.toList _ q h
  | .contents _ entries =>
    intro out acc q h
    simp only [resolveBlock, Ir.foldBlockList_push, Ir.foldBlock, Array.toList_map] at h
    exact contentsEntries_pending p find entries.toList _ q h
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

private theorem resolveRows_pending (p : CitePunct) (find : Resolver) (items : Array Ir.BibItem)
    (rows : List (Array (Array Ir.Block))) :
    ∀ (out : Array (Array (Array Ir.Block))) (acc : Array Ir.Unresolved) (q : Ir.Unresolved),
      q ∈ Ir.foldTableRows (fun a _ => a) Ir.pendingStep acc
        (resolveRows p find items out rows).toList →
      q ∈ Ir.foldTableRows (fun a _ => a) Ir.pendingStep acc out.toList ∨ q.isCite = false := by
  match rows with
  | [] => intro out acc q h; exact .inl h
  | row :: rest =>
    intro out acc q h
    rw [resolveRows] at h
    rcases resolveRows_pending p find items rest _ acc q h with h' | hc
    · simp only [Array.toList_push, Ir.foldTableRows_append, Ir.foldTableRows] at h'
      exact resolveItems_pending p find items row.toList #[] _ q h'
    · exact .inr hc

end

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

public theorem apply_no_cite (sources : Array (String × String)) (doc : Ir.Doc)
    (rd : FieldReading) {sites : Array Ir.CiteSite} {absent : Array String} :
    ∀ u ∈ Ir.pendingNodes (apply sources doc rd sites absent).1, u.isCite = false := by
  intro u hu
  unfold apply at hu
  rcases h : analyse sources doc rd sites absent with ⟨p, find, items, diags, pictures, notes⟩
  rw [h, Ir.pendingNodes_withListNotes, Ir.pendingNodes_addPictures] at hu
  exact resolveDoc_no_cite p find items _ u hu


end LeanTex.Core.Bib
