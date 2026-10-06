import LeanTex.Core.BibStyle
import LeanTex.Core.Pending

/-! Ordinary bibliography clients can choose the citation and entry style,
resolve references and transport source metadata. The resolution gate composes
those contracts with references and images. Scanners, formatting state and
resolver step lemmas belong to their implementation modules. -/

open LeanTex.Core

namespace Tests.BibPendingInterface

example : Repr Bib.CitePunct := inferInstance
example : BEq Bib.CitePunct := inferInstance
example : Inhabited Bib.CitePunct := inferInstance
example : Repr Bib.SortOrder := inferInstance
example : BEq Bib.SortOrder := inferInstance
example : Inhabited Bib.SortOrder := inferInstance
example : Repr Bib.NameFormat := inferInstance
example : BEq Bib.NameFormat := inferInstance
example : Inhabited Bib.NameFormat := inferInstance
example : Repr Bib.Resolved := inferInstance

example (ink : Option (Ir.Color × Option String)) : Bib.CitePunct :=
  { numbers := true, «open» := "[", close := "]", sep := ",",
    aysep := ",", yysep := ",", notesep := ", ", sort := true,
    compress := true, biblatex := false, ink }

example (p : Bib.CitePunct) : Bool × String × Option (Ir.Color × Option String) :=
  (p.numbers, p.notesep, p.ink)

example : String → Bool := Bib.CitePunct.reads
example : String → Array String := Bib.citeItems
example : List (String × List String) := Bib.natbibOptions
example : List (String × Bib.CitePunct) := Bib.natbibRows
example : Array Bib.CitePunct := #[Bib.natPunct, Bib.latexPunct]
example : Option (Array String) → Option Bib.CitePunct → Bool → Bib.CitePunct :=
  Bib.CitePunct.ofDoc

example : Repr Bib.Field := inferInstance
example : Repr Bib.Step := inferInstance
example : Array Bib.Step :=
  #[.out .authors, .newBlock, .out .title, .newSentence,
    .newBlockIf ["journal"], .out .journal,
    .newSentenceIf ["year"], .out .date, .out (.field "note")]

example (steps : Bib.Entry → Array Bib.Step) : Bib.Style :=
  { labels := true, sort := .authorYear, steps,
    names := { lastFirst := false, initials := true, etAlAfter := some 3 } }

example (style : Bib.Style) (entry : Bib.Entry) :
    Bool × Bib.SortOrder × Array Bib.Step × Bib.NameFormat :=
  (style.labels, style.sort, style.steps entry, style.names)

example : Bib.NameFormat → Bib.Name → String := Bib.NameFormat.render
example : Bib.NameFormat → String → String := Bib.NameFormat.renderList
example : Bib.NameFormat := Bib.abbrvNames
example : Bib.Entry → Array Bib.Step := Bib.plainnatSteps
example : String → Option Bib.Style := Bib.Style.named
example : Array Bib.Style :=
  #[Bib.Style.unsrtnat, Bib.Style.plainnat, Bib.Style.plain, Bib.Style.unsrt,
    Bib.Style.abbrvnat, Bib.Style.abbrv]

example (key : String) (entry : Bib.Entry) : Bib.Resolved :=
  { key, entry, position := 1, extra := "", label := none }

example (r : Bib.Resolved) :
    String × Nat × Bib.Entry × String × Option String :=
  (r.key, r.position, r.entry, r.extra, r.label)

example (r : Bib.Resolved) : Bib.Resolver :=
  fun key => if key == r.key then some r else none

example (find : Bib.Resolver) (key : String) : Option Bib.Resolved := find key

example : String → String := Bib.anchorOf
example : String → Array Ir.Inline := Bib.fieldInlines
example : Bib.CitePunct → Ir.CiteForm → Array (Option Bib.Resolved) → Array Ir.Inline :=
  Bib.renderCite
example : Bib.NameFormat → Array Bib.Step → Bib.Entry → String → Array Ir.Inline :=
  fun names steps entry extra => Bib.renderEntry names steps entry extra
example : Bib.SortOrder → Bib.Resolved → Bib.Resolved → Ordering := Bib.SortOrder.compare
example : Bib.SortOrder → List Bib.Resolved → List Bib.Resolved := Bib.sortResolved
example : Bib.Style → Array String → (String → Option Bib.Entry) → Bool →
    Array Bib.Resolved :=
  fun style cited find biblatex => Bib.resolveEntries style cited find biblatex
example : Bib.CitePunct → Bib.Style → Array Bib.Resolved → Array Ir.BibItem := Bib.bibItems
example : Bib.CitePunct → Bib.Resolver → Array Ir.BibItem → Ir.Doc → Ir.Doc := Bib.resolveDoc
example : Array (String × String) → Ir.Doc → Ir.Doc × Array Diag := Bib.apply
example : Ir.Block → Bool := Bib.keepsBlock
example {α : Type} : Ir.Doc → Array (Nat × α) → Array (Nat × α) := Bib.remapSources

example (p : Bib.CitePunct) (style : Bib.Style) (resolved : Array Bib.Resolved)
    (h : p.numbers = true) (i : Nat) (hi : i < resolved.size) :
    (Bib.bibItems p style resolved)[i]?.bind (·.marker) =
      some (toString resolved[i].position) :=
  Bib.bibItems_marker_exact p style resolved h i hi

example (style : Bib.Style) (cited : Array String)
    (find : String → Option Bib.Entry) (i : Nat)
    (hi : i < (Bib.resolveEntries style cited find).size) :
    (Bib.resolveEntries style cited find)[i].position = i + 1 :=
  Bib.positions_exact style cited find i hi

example (order : Bib.SortOrder) (xs : List Bib.Resolved) (r : Bib.Resolved) :
    r ∈ Bib.sortResolved order xs ↔ r ∈ xs := Bib.sortResolved_mem order xs r
example (order : Bib.SortOrder) (xs : List Bib.Resolved) :
    (Bib.sortResolved order xs).length = xs.length := Bib.sortResolved_length order xs
example (a b : Bib.Resolved) (h : Bib.SortOrder.citation.compare a b = .gt) :
    Bib.SortOrder.citation.compare b a ≠ .gt := Bib.compare_citation_asymm a b h
example (xs : List Bib.Resolved) :
    (Bib.sortResolved .citation xs).Pairwise
      (fun a b => Bib.SortOrder.citation.compare a b ≠ .gt) :=
  Bib.sortResolved_sorted_citation xs

example {α : Type} (doc : Ir.Doc) (sites : Array (Nat × α)) (i : Nat)
    (source : α) (b : Ir.Block) (hs : (i, source) ∈ sites)
    (hb : doc.body[i]? = some b) (hk : Bib.keepsBlock b = true)
    (p : Bib.CitePunct) (find : Bib.Resolver) (items : Array Ir.BibItem) :
    ((Bib.resolveDoc p find items
        { doc with body := (doc.body.toList.take i).toArray }).body.size, source) ∈
      Bib.remapSources doc sites :=
  Bib.remapSources_projects doc sites i source b hs hb hk p find items

example (p : Bib.CitePunct) (find : Bib.Resolver) (items : Array Ir.BibItem)
    (doc : Ir.Doc) :
    ∀ u ∈ Ir.pendingNodes (Bib.resolveDoc p find items doc), u.isCite = false :=
  Bib.resolveDoc_no_cite p find items doc

example (sources : Array (String × String)) (doc : Ir.Doc) :
    ∀ u ∈ Ir.pendingNodes (Bib.apply sources doc).1, u.isCite = false :=
  Bib.apply_no_cite sources doc

example (table : Ir.RefTable) (spanOf : String → Option Span)
    (sources : Array (String × String)) (doc : Ir.Doc)
    (fetched : Array (Image.Request × Image.Fetch))
    (hcov : fetched.map (·.1) = Ir.imageRequests (Bib.apply sources doc).1) :
    ∀ p ∈ Ir.pending (Bib.apply sources doc).1 (Image.fulfilRequests fetched).1,
      ∃ d ∈ Ir.refDiags table spanOf (Bib.apply sources doc).1 ++
        (Image.fulfilRequests fetched).2, d.mentions p = true :=
  pending_named table spanOf sources doc fetched hcov

example : True := by
  fail_if_success have := Bib.citeKeywords
  fail_if_success have := Bib.citeKeys
  fail_if_success have := Bib.stripGroup
  fail_if_success have := Bib.keyValue?
  fail_if_success have := Bib.CitePunct.step
  trivial

example : True := by
  fail_if_success have := Bib.citeYear
  fail_if_success have := Bib.citeAuthors
  fail_if_success have := Bib.citeFullAuthors
  fail_if_success have := Bib.CitePart
  fail_if_success have := Bib.CiteAcc
  fail_if_success have := Bib.Switches
  fail_if_success have := Bib.RunAcc
  fail_if_success have := Bib.compressRuns
  trivial

example : True := by
  fail_if_success have := Bib.mathSpans
  fail_if_success have := Bib.formulaOf
  fail_if_success have := Bib.Entry.has
  fail_if_success have := Bib.renderField
  fail_if_success have := Bib.OutState
  fail_if_success have := Bib.addPeriod
  trivial

example : True := by
  fail_if_success have := Bib.addKey
  fail_if_success have := Bib.citedKeys
  fail_if_success have := Bib.expandStar
  fail_if_success have := Bib.ayKey
  fail_if_success have := Bib.ayCompare
  fail_if_success have := Bib.biblatexKey
  fail_if_success have := Bib.biblatexCompare
  fail_if_success have := Bib.sortByKey
  fail_if_success have := Bib.labelOf
  fail_if_success have := Bib.extraLetter
  fail_if_success have := Bib.extraLabels
  trivial

example : True := by
  fail_if_success have := Bib.citeFreeOne
  fail_if_success have := Bib.citeFreeList
  fail_if_success have := Bib.nociteOnly
  fail_if_success have := Bib.natbibLabel?
  fail_if_success have := Bib.ownEntry
  fail_if_success have := Bib.ownList
  fail_if_success have := Bib.analyse
  trivial

example : True := by
  fail_if_success have := Bib.resolveInline
  fail_if_success have := Bib.resolveInlines
  fail_if_success have := Bib.resolveBlock
  fail_if_success have := Bib.resolveBlocks
  fail_if_success have := Bib.resolveItems
  fail_if_success have := Bib.resolveCols
  fail_if_success have := Bib.resolveInline_id
  fail_if_success have := Bib.resolveInlines_id
  fail_if_success have := Bib.renderCite_plain
  fail_if_success have := Bib.resolveInline_pending
  fail_if_success have := Bib.resolveInlines_pending
  fail_if_success have := Bib.resolveBlock_pending
  fail_if_success have := Bib.resolveBlocks_pending
  fail_if_success have := Bib.resolveItems_pending
  fail_if_success have := Bib.resolveCols_pending
  trivial

end Tests.BibPendingInterface
