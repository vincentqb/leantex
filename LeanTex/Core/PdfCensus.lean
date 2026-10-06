import LeanTex.Core.PdfRead

namespace LeanTex.Core.PdfCensus

open LeanTex.Core.PdfRead

/-! # The read-side census of a PDF

What a PDF file *carries*, read from its bytes by the engine's own reader
(`PdfRead.objects`) — never from the writer's intent. The distinction is
the reason this module exists: a copied foreign page can bring a font the
writer never saw, so "every font is embedded" is a fact of the file, and
a census computed from the writer's inputs would say "embedded" for the
very file that was not. `Check.Shipped.fontsEmbedded` reads this census;
so will every profile violation (`pdf/a-4`, `pdf/ua-2`) once its contract
lands.

The module imports the reader and nothing else — not the writer, whose
spellings it must never be allowed to assume (the pre-commit hook holds
that line). Copied graphs are classified like any dictionary and never
certified: a form XObject's resources are counted, not vouched for.

Wave 1 states theorems over `fontsEmbedded` alone; the other
classifications ship as data for the contracts that will read them. -/

/-- What a dictionary is, by its `/Type` and `/Subtype`. -/
inductive Kind where
  | catalog
  | pages
  | page
  /-- A font dictionary of any subtype (composite, simple, Type 3). -/
  | font
  | fontDescriptor
  | image
  | form
  | annot (subtype : String)
  | outlines
  /-- An outline item has no `/Type`: `/Title` beside `/Parent` names it. -/
  | outlineItem
  | metadata
  | objStm
  | xref
  | other
  deriving DecidableEq, Repr, Inhabited

private def nameOf (o : Obj) (k : String) : Option String :=
  match o.get? k with
  | some (.name n) => some n
  | _ => none

/-- The font subtypes ISO 32000-2 §9.5–9.7 name. -/
def fontSubtypes : List String :=
  ["Type0", "Type1", "MMType1", "TrueType", "Type3", "CIDFontType0", "CIDFontType2"]

def kindOf (o : Obj) : Kind :=
  match nameOf o "Type", nameOf o "Subtype" with
  | some "Catalog", _ => .catalog
  | some "Pages", _ => .pages
  | some "Page", _ => .page
  | some "Font", _ => .font
  | some "FontDescriptor", _ => .fontDescriptor
  | some "XObject", some "Image" => .image
  | _, some "Image" => .image
  | some "XObject", some "Form" => .form
  | _, some "Form" => .form
  | some "Annot", some s => .annot s
  | _, some "Link" => .annot "Link"
  | some "Outlines", _ => .outlines
  | some "Metadata", _ => .metadata
  | some "ObjStm", _ => .objStm
  | some "XRef", _ => .xref
  | _, some s =>
    if fontSubtypes.contains s then .font else .other
  | none, none =>
    if (o.get? "Title").isSome && (o.get? "Parent").isSome then .outlineItem else .other
  | _, _ => .other

/-- Without a subtype, only an explicit `/Type /Font` can enter the
font census. This states the classifier's own rule, independently of a
producer's dictionary layout. -/
theorem kindOf_no_subtype_not_font (o : Obj)
    (ht : o.get? "Type" ≠ some (.name "Font"))
    (hs : o.get? "Subtype" = none) :
    kindOf o ≠ .font := by
  have hsub : nameOf o "Subtype" = none := by simp [nameOf, hs]
  unfold kindOf
  rw [hsub]
  split <;> simp_all [nameOf]
  all_goals split at * <;> simp_all
  all_goals split <;> simp_all

theorem kindOf_catalog_exact (o : Obj)
    (h : o.get? "Type" = some (.name "Catalog")) :
    kindOf o = .catalog := by
  simp [kindOf, nameOf, h]

theorem kindOf_pages_exact (o : Obj)
    (h : o.get? "Type" = some (.name "Pages")) :
    kindOf o = .pages := by
  simp [kindOf, nameOf, h]

theorem kindOf_page_exact (o : Obj)
    (h : o.get? "Type" = some (.name "Page")) :
    kindOf o = .page := by
  simp [kindOf, nameOf, h]

/-- The value behind a reference, one hop; a direct value unchanged; an
unlisted reference is the null object (§7.3.10). -/
def deref (es : Array Entry) (o : Obj) : Obj :=
  match o with
  | .ref n _ => ((es.find? (·.num == n)).map (·.val)).getD .null
  | _ => o

/-- The font dictionaries the file carries, copied graphs included. -/
def fontEntries (es : Array Entry) : Array Entry :=
  es.filter fun e => kindOf e.val == .font

/-- Is this font dictionary's program in the file? A composite font
delegates to its descendant, which is a font dictionary of its own and
judged on its own row; a Type 3 font's glyphs are content streams in the
file by definition (§9.6.4); every other subtype needs a descriptor
carrying `FontFile`, `FontFile2`, or `FontFile3` (§9.9) — the standard
fourteen without one are exactly what a viewer substitutes. -/
def fontEmbedded (es : Array Entry) (e : Entry) : Bool :=
  match nameOf e.val "Subtype" with
  | some "Type0" => true
  | some "Type3" => true
  | _ =>
    let fd := deref es ((e.val.get? "FontDescriptor").getD .null)
    (fd.get? "FontFile").isSome || (fd.get? "FontFile2").isSome ||
      (fd.get? "FontFile3").isSome

/-- The filter names a stream declares, one or a chain (§7.4). -/
def filtersOf (o : Obj) : Array String :=
  match o.get? "Filter" with
  | some (.name f) => #[f]
  | some (.arr xs) => xs.filterMap fun x => match x with
    | .name f => some f
    | _ => none
  | _ => #[]

/-- A colour-space spelling: a family name, or the first element of an
array (`[/Indexed …]`, `[/ICCBased n 0 R]`). -/
def colorSpaceOf (o : Obj) : Option String :=
  match o.get? "ColorSpace" with
  | some (.name n) => some n
  | some (.arr xs) => match xs[0]? with
    | some (Obj.name n) => some n
    | _ => none
  | _ => none

private def sortedUnique (xs : Array String) : Array String :=
  ((xs.qsort (· < ·)).foldl (fun acc x =>
    if acc.back? == some x then acc else acc.push x) #[])

private def strOf (o : Obj) : Option String :=
  match o with
  | .str raw =>
    -- A literal string's bytes between its parentheses; hex strings and
    -- escapes are left as spelled — a language tag has neither.
    if raw.size ≥ 2 && raw[0]? == some 40 then
      some (String.fromUTF8! (raw.extract 1 (raw.size - 1)))
    else some (String.fromUTF8! raw)
  | _ => none

/-- The census of one file. Counts are of dictionaries the cross-reference
lists, whatever wrote them; `fontsEmbedded` is the one field an assertion
reads today. -/
structure Census where
  /-- The trailer's `/Size`, when declared. -/
  size : Option Nat
  objects : Nat
  pages : Nat
  fonts : Nat
  type0Fonts : Nat
  fontsEmbedded : Bool
  images : Nat
  smasks : Nat
  forms : Nat
  linkAnnots : Nat
  outlineItems : Nat
  lang : Option String
  /-- Every filter name any stream declares, sorted, once each. -/
  filters : Array String
  /-- Every colour-space family an image declares, sorted, once each. -/
  colorSpaces : Array String
  markInfo : Bool
  structTreeRoot : Bool
  outputIntents : Nat
  /-- The trailer names an `/Info` dictionary. -/
  info : Bool
  /-- The page boxes beyond `/MediaBox` any page declares, sorted, once each. -/
  boxes : Array String
  deriving Repr

def catalogOf (es : Array Entry) (trailer : Obj) : Obj :=
  match trailer.get? "Root" with
  | some r => deref es r
  | none => ((es.find? fun e => kindOf e.val == .catalog).map (·.val)).getD .null

def ofEntries (trailer : Obj) (es : Array Entry) : Census :=
  let kinds := es.map fun e => kindOf e.val
  let count (k : Kind) : Nat := (kinds.filter (· == k)).size
  -- Annotations are counted through each page's `/Annots` (§12.5.1),
  -- where a writer may inline them as direct dictionaries.
  let catalog := catalogOf es trailer
  let images := es.filter fun e => kindOf e.val == .image
  let pages := es.filter fun e => kindOf e.val == .page
  {
    size := ((trailer.get? "Size").bind Obj.int?).map (·.toNat)
    objects := es.size
    pages := pages.size
    fonts := (fontEntries es).size
    type0Fonts := ((fontEntries es).filter fun e => nameOf e.val "Subtype" == some "Type0").size
    fontsEmbedded := (fontEntries es).all (fontEmbedded es)
    images := images.size
    smasks := (images.filter fun e => (e.val.get? "SMask").isSome).size
    forms := count .form
    linkAnnots := pages.foldl (fun acc e =>
      match deref es ((e.val.get? "Annots").getD .null) with
      | .arr xs => acc + (xs.filter fun a => kindOf (deref es a) == .annot "Link").size
      | _ => acc) 0
    outlineItems := count .outlineItem
    lang := (catalog.get? "Lang").bind strOf
    filters := sortedUnique (es.foldl (fun acc e =>
      if e.stream.isSome then acc ++ filtersOf e.val else acc) #[])
    colorSpaces := sortedUnique (images.filterMap fun e => colorSpaceOf e.val)
    markInfo := match deref es ((catalog.get? "MarkInfo").getD .null) with
      | .dict _ => true
      | _ => false
    structTreeRoot := (catalog.get? "StructTreeRoot").isSome
    outputIntents := match deref es ((catalog.get? "OutputIntents").getD .null) with
      | .arr xs => xs.size
      | _ => 0
    info := (trailer.get? "Info").isSome
    boxes := sortedUnique (pages.foldl (fun acc e =>
      ["CropBox", "BleedBox", "TrimBox", "ArtBox"].foldl (fun acc k =>
        if (e.val.get? k).isSome then acc.push k else acc) acc) #[])
  }

/-- **`census_fontsEmbedded_exact`** (the `_exact` statement): the census
says every font is embedded exactly when every font dictionary the file
carries — the writer's and any copied graph's alike — has its program in
the file by `fontEmbedded`'s rule. Nothing about the writer's inputs
enters: the judge is the file. -/
theorem census_fontsEmbedded_exact (trailer : Obj) (es : Array Entry) :
    (ofEntries trailer es).fontsEmbedded = true ↔
      ∀ e ∈ fontEntries es, fontEmbedded es e = true := by
  simp only [ofEntries, Array.all_eq_true_iff_forall_mem]

/-- Every object the file lists lies below the trailer's `/Size`: the
cross-reference covers its own declared range (§7.5.8.2). `objectsOf`
refuses a file where it does not, so this is `true` of every census the
engine hands back; stated as a function for the fixture sweep to read. -/
def xrefCovers (c : Census) (es : Array Entry) : Bool :=
  match c.size with
  | some n => es.all (·.num < n)
  | none => true

/-- The census of a file's bytes: the cross-reference followed, every
object fetched and checked (`objects_num_covers`), the dictionaries
classified. A file the reader cannot follow is a named refusal — which an
assertion over the census then reports, never swallows. -/
def census (b : ByteArray) : Except String Census := do
  unless b[0]? == some 37 && b[1]? == some 80 && b[2]? == some 68 && b[3]? == some 70 do
    throw "not a PDF file (no %PDF header)"
  let x ← readXref b
  let es ← objectsOf b x
  return ofEntries (x.trailer.getD (.dict #[])) es.val

end LeanTex.Core.PdfCensus
