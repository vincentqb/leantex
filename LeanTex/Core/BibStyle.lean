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

/-! ## Resolution

`apply` is the pure half of the `\bibliography` effect: the driver reads
the named `.bib` file beside the document (`Ir.bibRefs` is the request) and
hands its text here; everything after — parsing, ordering, numbering,
formatting, the rewrite of every citation — is a function of the document
and that text. -/

/-- First-citation order: the keys the document cites, in order of first
appearance, each once — the sequence citation-order lists are sorted by
and numeric labels index into. A leaf projection of `Ir.foldBlocks`, the
one collect traversal. -/
def citedKeys (doc : Ir.Doc) : Array String :=
  Ir.foldBlocks (fun out _ => out)
    (fun out x => match x with
      | .cite _ keys =>
        keys.foldl (fun out k => if out.contains k then out else out.push k) out
      | _ => out) #[] doc.body

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
per the style, its marker the style's own (the position for numeric,
nothing for author-year — those lists mark no entries). -/
def bibItems (style : Style) (resolved : Array Resolved) : Array Ir.BibItem :=
  resolved.map fun r =>
    { key := r.key
      marker := match style.cite with
        | .numeric => some (toString r.position)
        | .authorYear => none
      content := renderEntry style.names (style.order r.entry.kind) r.entry }

/-! ### The theorems the four-axis shape earns

Each axis being a pure function is what makes these statable; a
transcribed `.bst` has none of them. -/

/-- Numbering is the sort position: in a numeric style, the marker of the
reference list's `i`-th entry is its 1-based index in the sorted list —
the fact every `\cite` mark rests on, `positions_exact` below being the
half that says the positions the marks look up are those same indices.
Floats state the same vocabulary in `Ir.numberFloats_exact` — a label is
the index of first appearance in a sequence, `List.range'` both times —
but over a different data shape (a counter threaded through a tree walk,
not a `mapIdx` over a sorted list). Deliberately not unified: a shared
"consecutive assignment" lemma would leave each proof's hard part — here a
one-line `simp`, there the tree induction — untouched. -/
theorem bibItems_marker_exact (style : Style) (resolved : Array Resolved)
    (h : style.cite = .numeric) (i : Nat) (hi : i < resolved.size) :
    (bibItems style resolved)[i]?.bind (·.marker) =
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

/-- The citation rewrite: every `.cite` node becomes the style's inlines
(`renderCite`), everything else passes through with its body walked. The
one edit is the citation; `resolveInline_id` below is the machine-checked
form of that sentence. -/
-- conserves: none — resolution rewrites citation marks into the style's
-- rendering; `resolveInline_id` states the walk's identity off citations.
private def resolveInline (style : CiteStyle) (find : Resolver)
    (out : Array Ir.Inline) : Ir.Inline → Array Ir.Inline
  | .cite textual keys =>
    let rendered := renderCite style textual (keys.map find)
    out ++ rendered
  | .styled st body => out.push (.styled st (resolveInlines style find #[] body.toList))
  | .colored c nm body => out.push (.colored c nm (resolveInlines style find #[] body.toList))
  | .role nm body => out.push (.role nm (resolveInlines style find #[] body.toList))
  | .link u body => out.push (.link u (resolveInlines style find #[] body.toList))
  | .underline body => out.push (.underline (resolveInlines style find #[] body.toList))
  | .step n last body => out.push (.step n last (resolveInlines style find #[] body.toList))
  | .text s => out.push (.text s)
  | .math d src => out.push (.math d src)
  | .formula d src body => out.push (.formula d src body)
  | .image src size alt => out.push (.image src size alt)
  | .icon c label => out.push (.icon c label)
  | .label k => out.push (.label k)
  | .ref k paren text anchor => out.push (.ref k paren text anchor)
  | .fill => out.push .fill
  | .strut h => out.push (.strut h)
  | .pageNumber => out.push .pageNumber
  | .pageCount => out.push .pageCount
  | .linebreak e => out.push (.linebreak e)

private def resolveInlines (style : CiteStyle) (find : Resolver)
    (out : Array Ir.Inline) : List Ir.Inline → Array Ir.Inline
  | [] => out
  | x :: rest => resolveInlines style find (resolveInline style find out x) rest

end

private def resolveArr (style : CiteStyle) (find : Resolver)
    (xs : Array Ir.Inline) : Array Ir.Inline :=
  resolveInlines style find #[] xs.toList

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
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _
  | .label _ | .ref _ _ _ _
  | .fill | .strut _ | .pageNumber | .pageCount | .linebreak _ => true

def citeFreeList : List Ir.Inline → Bool
  | [] => true
  | x :: rest => citeFreeOne x && citeFreeList rest

end

private theorem resolveInlines_acc (style : CiteStyle) (find : Resolver)
    (out : Array Ir.Inline) (xs : List Ir.Inline) :
    resolveInlines style find out xs = out ++ resolveInlines style find #[] xs := by
  induction xs generalizing out with
  | nil => simp [resolveInlines]
  | cons x rest ih =>
    rw [resolveInlines, resolveInlines, ih (resolveInline style find out x),
      ih (resolveInline style find #[] x), resolveInline_acc, ← Array.append_assoc]
where
  resolveInline_acc (style : CiteStyle) (find : Resolver)
      (out : Array Ir.Inline) (x : Ir.Inline) :
      resolveInline style find out x = out ++ resolveInline style find #[] x := by
    match x with
    | .cite t keys => simp [resolveInline]
    | .styled _ body | .colored _ _ body | .role _ body | .link _ body
    | .underline body | .step _ _ body => simp [resolveInline]
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
theorem resolveInline_id (style : CiteStyle) (find : Resolver)
    (out : Array Ir.Inline) (x : Ir.Inline) (h : citeFreeOne x = true) :
    resolveInline style find out x = out.push x := by
  match x with
  | .styled st body =>
    rw [citeFreeOne] at h
    rw [resolveInline, resolveInlines_id style find body.toList h]
  | .colored c nm body =>
    rw [citeFreeOne] at h
    rw [resolveInline, resolveInlines_id style find body.toList h]
  | .role nm body =>
    rw [citeFreeOne] at h
    rw [resolveInline, resolveInlines_id style find body.toList h]
  | .link u body =>
    rw [citeFreeOne] at h
    rw [resolveInline, resolveInlines_id style find body.toList h]
  | .underline body =>
    rw [citeFreeOne] at h
    rw [resolveInline, resolveInlines_id style find body.toList h]
  | .step n last body =>
    rw [citeFreeOne] at h
    rw [resolveInline, resolveInlines_id style find body.toList h]
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _
  | .label _ | .ref _ _ _ _
  | .fill | .strut _ | .pageNumber | .pageCount | .linebreak _ =>
    rw [resolveInline]

theorem resolveInlines_id (style : CiteStyle) (find : Resolver)
    (xs : List Ir.Inline) (h : citeFreeList xs = true) :
    resolveInlines style find #[] xs = xs.toArray := by
  match xs with
  | [] => rw [resolveInlines]
  | x :: rest =>
    rw [citeFreeList, Bool.and_eq_true] at h
    rw [resolveInlines, resolveInline_id style find #[] x h.1,
      resolveInlines_acc, resolveInlines_id style find rest h.2]
    simp

end

mutual

/-- The block half of the rewrite: citations resolve wherever inline
content stands, and each `\bibliography` marker takes the items the style
built. -/
-- conserves: none — resolution rewrites citation marks and fills the
-- reference list; `resolveInline_id` carries the off-citation identity.
private def resolveBlock (style : Style) (find : Resolver)
    (items : Array Ir.BibItem) (out : Array Ir.Block) (b : Ir.Block) :
    Array Ir.Block :=
  match b with
  | .bibliography src declared _ => out.push (.bibliography src declared items)
  | .para content => out.push (.para (resolveArr style.cite find content))
  | .equation n content => out.push (.equation n (resolveArr style.cite find content))
  | .section l st num title => out.push (.section l st num (resolveArr style.cite find title))
  | .abstract body => out.push (.abstract (resolveBlocks style find items #[] body.toList))
  | .list ordered its => out.push (.list ordered (resolveItems style find items #[] its.toList))
  | .center body => out.push (.center (resolveBlocks style find items #[] body.toList))
  | .quote body => out.push (.quote (resolveBlocks style find items #[] body.toList))
  | .titled kind title body =>
    out.push (.titled kind (resolveArr style.cite find title)
      (resolveBlocks style find items #[] body.toList))
  | .role nm body => out.push (.role nm (resolveBlocks style find items #[] body.toList))
  | .spaced g body => out.push (.spaced g (resolveBlocks style find items #[] body.toList))
  | .columns cols => out.push (.columns (resolveCols style find items #[] cols.toList))
  | .step n last body =>
    out.push (.step n last (resolveBlocks style find items #[] body.toList))
  | .only t body => out.push (.only t (resolveBlocks style find items #[] body.toList))
  | .nav spec body => out.push (.nav spec (resolveBlocks style find items #[] body.toList))
  | .note body => out.push (.note (resolveBlocks style find items #[] body.toList))
  | .frame title standout va body =>
    out.push (.frame (resolveArr style.cite find title) standout va
      (resolveBlocks style find items #[] body.toList))
  | .framefoot content => out.push (.framefoot (resolveArr style.cite find content))
  | .float k n ca body caption =>
    out.push (.float k n ca (resolveBlocks style find items #[] body.toList)
      (resolveArr style.cite find caption))
  | .table cols pl pr rows rules =>
    out.push (.table cols pl pr
      (rows.map fun row => row.map (resolveArr style.cite find)) rules)
  | .logo content => out.push (.logo (resolveArr style.cite find content))
  | .verbatim c s => out.push (.verbatim c s)
  | .setPalette p => out.push (.setPalette p)
  | .setTokens tk => out.push (.setTokens tk)
  | .pagebreak => out.push .pagebreak
  | .rule c nm th => out.push (.rule c nm th)
  | .picture pic => out.push (.picture pic)
termination_by structural b

private def resolveBlocks (style : Style) (find : Resolver)
    (items : Array Ir.BibItem) (out : Array Ir.Block) (bs : List Ir.Block) :
    Array Ir.Block :=
  match bs with
  | [] => out
  | b :: rest => resolveBlocks style find items (resolveBlock style find items out b) rest
termination_by structural bs

private def resolveItems (style : Style) (find : Resolver)
    (items : Array Ir.BibItem) (out : Array (Array Ir.Block))
    (its : List (Array Ir.Block)) : Array (Array Ir.Block) :=
  match its with
  | [] => out
  | item :: rest =>
    resolveItems style find items
      (out.push (resolveBlocks style find items #[] item.toList)) rest
termination_by structural its

private def resolveCols (style : Style) (find : Resolver)
    (items : Array Ir.BibItem) (out : Array (Option Nat × Array Ir.Block))
    (cs : List (Option Nat × Array Ir.Block)) :
    Array (Option Nat × Array Ir.Block) :=
  match cs with
  | [] => out
  | (w, body) :: rest =>
    resolveCols style find items
      (out.push (w, resolveBlocks style find items #[] body.toList)) rest
termination_by structural cs

end

/-- Resolve the document's citations and reference lists against its
`.bib` sources — the pure half of the `\bibliography` effect. `sources`
maps each requested name (`Ir.bibRefs`) to the file text the driver read;
a name the driver could not read is simply absent, its diagnostic already
fired. Emits W0352 for each malformed `.bib` entry (skipped, the rest
kept), W0353 when the declared style is unknown (the fallback record
formats the list and says so), and W0351 for each cited key no entry
answers (its citation shows `?`, LaTeX's own rendering). A document with
no `\bibliography` marker is returned untouched: there is nothing to
resolve against, and the unresolved citations' marks say so on the page. -/
def apply (sources : Array (String × String)) (doc : Ir.Doc) :
    Ir.Doc × Array Diag := Id.run do
  let requested := Ir.bibRefs doc
  if requested.isEmpty then return (doc, #[])
  let mut diags : Array Diag := #[]
  let mut entries : Array Entry := #[]
  for src in requested do
    match sources.find? (·.1 == src) with
    | none => pure ()  -- the driver's missing-file diagnostic already fired
    | some (_, text) =>
      let parsed := parse text
      for (pos, msg) in parsed.errors do
        diags := diags.push (Diag.of .W0352 s!"malformed .bib entry: {msg}; \
          the entry is skipped and the rest of '{src}' is kept"
          (some ⟨src, pos⟩))
      for e in parsed.entries do
        unless entries.any (·.key == e.key) do
          entries := entries.push e
  let style ← do
    match Ir.bibStyleName doc with
    | none => pure Style.unsrtnat
    | some name =>
      match Style.named name with
      | some s => pure s
      | none =>
        diags := diags.push (Diag.of .W0353 s!"bibliography style '{name}' is not \
          one the engine knows; the reference list is set as 'unsrtnat'"
          (help := "styles known: unsrtnat, unsrt, plainnat, plain"))
        pure Style.unsrtnat
  let cited := citedKeys doc
  let findEntry (k : String) : Option Entry := (entries.find? (·.key == k)).map id
  for k in cited do
    if (findEntry k).isNone then
      diags := diags.push (Diag.of .W0351 s!"citation '{k}' has no entry in the \
        bibliography; it shows as '?'"
        (help := s!"add an entry with key '{k}' to the .bib file, or fix the \
          spelling in \\cite"))
  let resolved := resolveEntries style cited findEntry
  let find : Resolver := fun k => resolved.find? (·.key == k)
  let items := bibItems style resolved
  let body := resolveBlocks style find items #[] doc.body.toList
  return ({ doc with body }, diags)

end LeanTex.Core.Bib
