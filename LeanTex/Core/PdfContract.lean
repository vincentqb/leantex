module

public import LeanTex.Core.PdfCensus
public import LeanTex.Core.Ir

namespace LeanTex.Core.PdfContract

open LeanTex.Core.PdfCensus (Census)
open LeanTex.Core.Ir (OutputContract)

/-! What a declared PDF conformance profile demands of the file, as values, judged over the
read-side census of the built bytes. -/

/-- A stream filter as the allowlist names it; `none` is the unfiltered stream and `other` a filter
the engine has no constructor for. -/
public inductive Filter where
  | flate
  | dct
  | none
  | other (name : String)
  deriving DecidableEq, Repr, Inhabited

/-- A filter by its PDF name (ISO 32000-2 Table 6). -/
public def Filter.ofName : String → Filter
  | "FlateDecode" => .flate
  | "DCTDecode" => .dct
  | n => .other n

/-- The trailer's `/Info` dictionary: kept, or forbidden (PDF/A-4 6.1.3). -/
public inductive InfoPolicy where
  | full
  | absent
  deriving DecidableEq, Repr, Inhabited

public def InfoPolicy.meet : InfoPolicy → InfoPolicy → InfoPolicy
  | .absent, _ => .absent
  | .full, .absent => .absent
  | .full, .full => .full

/-- `a ≤ b`: every demand of `a` is one of `b`. -/
public def InfoPolicy.le (a b : InfoPolicy) : Prop := a = .full ∨ b = .absent

public instance : DecidableRel InfoPolicy.le := fun a b => inferInstanceAs (Decidable (a = .full ∨ b = .absent))

/-- The colour kind of an output intent's destination profile. -/
public inductive IccKind where
  | rgb
  | cmyk
  | gray
  deriving DecidableEq, Repr, Inhabited

/-- How device colour is given meaning: no demand, an output intent of a kind (PDF/A-4 6.2.4.3),
or a conflict no file can satisfy. -/
public inductive ColourPolicy where
  | device
  | intent (kind : IccKind)
  | conflict
  deriving DecidableEq, Repr, Inhabited

public def ColourPolicy.meet : ColourPolicy → ColourPolicy → ColourPolicy
  | .device, b => b
  | .intent k, .device => .intent k
  | .intent k, .intent k' => if k = k' then .intent k else .conflict
  | .intent _, .conflict => .conflict
  | .conflict, _ => .conflict

public def ColourPolicy.le (a b : ColourPolicy) : Prop := a = .device ∨ a = b ∨ b = .conflict

public instance : DecidableRel ColourPolicy.le := fun a b =>
  inferInstanceAs (Decidable (a = .device ∨ a = b ∨ b = .conflict))

/-- The `/S` of an output intent: PDF/A's or PDF/X's. -/
public inductive IntentSubtype where
  | gtsPdfA1
  | gtsPdfX
  deriving DecidableEq, Repr, Inhabited

/-- The output intents the file must carry: one, or both subtypes sharing one destination profile
(PDF/A-4 6.2.3). -/
public inductive IntentReq where
  | one (subtype : IntentSubtype)
  | both
  deriving DecidableEq, Repr, Inhabited

public def IntentReq.meet : IntentReq → IntentReq → IntentReq
  | .one a, .one b => if a = b then .one a else .both
  | .one _, .both => .both
  | .both, _ => .both

/-- Lifted to the optional field: no intent demanded is the bottom. -/
public def IntentReq.meetOpt : Option IntentReq → Option IntentReq → Option IntentReq
  | none, b => b
  | some a, none => some a
  | some a, some b => some (a.meet b)

public def IntentReq.leOpt (a b : Option IntentReq) : Prop := a = none ∨ a = b ∨ b = some .both

public instance : DecidableRel IntentReq.leOpt := fun a b =>
  inferInstanceAs (Decidable (a = none ∨ a = b ∨ b = some .both))

/-- Page boxes: no demand, or exactly one of `/TrimBox` and `/ArtBox` on every page (PDF/X-4's rule,
assumed for X-6). -/
public inductive BoxPolicy where
  | any
  | trimXorArt
  deriving DecidableEq, Repr, Inhabited

public def BoxPolicy.meet : BoxPolicy → BoxPolicy → BoxPolicy
  | .any, b => b
  | .trimXorArt, _ => .trimXorArt

public def BoxPolicy.le (a b : BoxPolicy) : Prop := a = .any ∨ a = b

public instance : DecidableRel BoxPolicy.le := fun a b => inferInstanceAs (Decidable (a = .any ∨ a = b))

/-- An XMP identification block a claim writes, one per ISO profile. -/
public inductive XmpId where
  | pdfa
  | pdfua
  | pdfx
  deriving DecidableEq, Repr, Inhabited

/-- The profile name the id claims. -/
public def XmpId.profile : XmpId → String
  | .pdfa => "pdf/a-4"
  | .pdfua => "pdf/ua-2"
  | .pdfx => "pdf/x-6"

public def XmpId.schema : XmpId → String
  | .pdfa => "http://www.aiim.org/pdfa/ns/id/"
  | .pdfua => "http://www.aiim.org/pdfua/ns/id/"
  | .pdfx => "http://www.npes.org/pdfx/ns/id/"

/-- `pdfaid:part`, `pdfuaid:part`, `pdfxid:GTS_PDFXVersion`. -/
public def XmpId.part : XmpId → String
  | .pdfa => "4"
  | .pdfua => "2"
  | .pdfx => "PDF/X-6"

/-- `pdfaid:rev`, `pdfuaid:rev`; X has no revision key. -/
public def XmpId.rev : XmpId → Option String
  | .pdfa => some "2020"
  | .pdfua => some "2024"
  | .pdfx => none

/-- The demands of a profile set on the PDF file, values only. -/
public structure Contract where
  infoDict : InfoPolicy
  /-- The filters the file may declare on a stream; the meet intersects. -/
  filters : Array Filter
  colour : ColourPolicy
  intent : Option IntentReq
  /-- `/MarkInfo /Marked true` and a `/StructTreeRoot` (PDF/UA-2 6.2, 8.2.1). -/
  tagged : Bool
  /-- Every in-document destination a structure destination (PDF/UA-2 8.4). -/
  structDests : Bool
  /-- `/Tabs` on every page carrying annotations (PDF/UA-2 8.9.3.3). -/
  tabs : Bool
  /-- A non-empty catalog `/Lang` (PDF/UA-2 8.4.4). -/
  needsLang : Bool
  /-- A `dc:title` in the metadata stream (PDF/UA-2 8.11.1). -/
  needsTitle : Bool
  boxes : BoxPolicy
  /-- The identification blocks the claim would write; the meet unites. -/
  ids : Array XmpId
  deriving DecidableEq, Repr, Inhabited

/-- Fieldwise stricter: `absent` wins, filters intersect, Bool demands
disjoin, ids unite, boxes and colour and intent take their own meets. -/
public def Contract.meet (a b : Contract) : Contract := {
  infoDict := a.infoDict.meet b.infoDict
  filters := a.filters.filter fun f => decide (f ∈ b.filters)
  colour := a.colour.meet b.colour
  intent := IntentReq.meetOpt a.intent b.intent
  tagged := a.tagged || b.tagged
  structDests := a.structDests || b.structDests
  tabs := a.tabs || b.tabs
  needsLang := a.needsLang || b.needsLang
  needsTitle := a.needsTitle || b.needsTitle
  boxes := a.boxes.meet b.boxes
  ids := a.ids ++ b.ids.filter fun i => decide (i ∉ a.ids) }

/-- `a ≤ b`: every demand of `a` is a demand of `b`. -/
@[expose] public def Contract.le (a b : Contract) : Prop :=
  a.infoDict.le b.infoDict ∧
  (∀ f ∈ b.filters, f ∈ a.filters) ∧
  a.colour.le b.colour ∧
  IntentReq.leOpt a.intent b.intent ∧
  (a.tagged = true → b.tagged = true) ∧
  (a.structDests = true → b.structDests = true) ∧
  (a.tabs = true → b.tabs = true) ∧
  (a.needsLang = true → b.needsLang = true) ∧
  (a.needsTitle = true → b.needsTitle = true) ∧
  a.boxes.le b.boxes ∧
  (∀ i ∈ a.ids, i ∈ b.ids)

public instance : DecidableRel Contract.le := fun a b => by
  unfold Contract.le
  infer_instance

/-- Two contracts with the same demands: scalar fields equal, set-valued fields equal as sets. -/
public def Contract.same (a b : Contract) : Prop :=
  a.infoDict = b.infoDict ∧ a.colour = b.colour ∧ a.intent = b.intent ∧
  a.tagged = b.tagged ∧ a.structDests = b.structDests ∧ a.tabs = b.tabs ∧
  a.needsLang = b.needsLang ∧ a.needsTitle = b.needsTitle ∧ a.boxes = b.boxes ∧
  (∀ f, f ∈ a.filters ↔ f ∈ b.filters) ∧ (∀ i, i ∈ a.ids ↔ i ∈ b.ids)

private def tableSix : Array Filter :=
  #[.flate, .dct, .none, .other "ASCIIHexDecode", .other "ASCII85Decode",
    .other "RunLengthDecode", .other "CCITTFaxDecode", .other "JBIG2Decode",
    .other "JPXDecode"]

/-- No profile: nothing demanded or claimed, every filter ISO 32000-2 Table 6 names allowed. -/
public def plain : Contract := {
  infoDict := .full
  filters := tableSix ++ #[.other "LZWDecode", .other "Crypt"]
  colour := .device
  intent := none
  tagged := false
  structDests := false
  tabs := false
  needsLang := false
  needsTitle := false
  boxes := .any
  ids := #[] }

/-- PDF/A-4 (ISO 19005-4:2020): no `/Info`, Table 6 filters, device colour under an RGB output
intent, and the `pdfaid` identification. -/
public def archive : Contract := {
  infoDict := .absent
  filters := tableSix
  colour := .intent .rgb
  intent := some (.one .gtsPdfA1)
  tagged := false
  structDests := false
  tabs := false
  needsLang := false
  needsTitle := false
  boxes := .any
  ids := #[.pdfa] }

/-- PDF/UA-2 (ISO 14289-2:2024): tagged with structure destinations, `/Tabs` on annotated pages, a
language and a title. -/
public def accessible : Contract := {
  infoDict := .full
  filters := tableSix
  colour := .device
  intent := none
  tagged := true
  structDests := true
  tabs := true
  needsLang := true
  needsTitle := true
  boxes := .any
  ids := #[.pdfua] }

/-- PDF/X-6 (ISO 15930-9:2020): a `GTS_PDFX` intent (CMYK by default), Trim-xor-Art boxes (assumed
from PDF/X-4), and the `pdfxid` identification. -/
public def print : Contract := {
  infoDict := .full
  filters := tableSix
  colour := .intent .cmyk
  intent := some (.one .gtsPdfX)
  tagged := false
  structDests := false
  tabs := false
  needsLang := false
  needsTitle := false
  boxes := .trimXorArt
  ids := #[.pdfx] }

/-- The Brotli extension to ISO 32000-2: `plain` with `BrotliDecode` allowed, no claim. -/
public def brotli : Contract := { plain with filters := plain.filters.push (.other "BrotliDecode") }

/-- One violated rule, as the assertion reports it: the clause the rule
comes from, and the census fact that broke it. -/
public structure Violation where
  rule : String
  actual : String
  deriving DecidableEq, Repr, Inhabited

public def Violation.render (v : Violation) : String := s!"{v.actual} ({v.rule})"

namespace Rule

/-- PDF/A-4 6.1.3: the trailer names an `/Info` dictionary. -/
private def info (c : Contract) (x : Census) : Array Violation :=
  match c.infoDict, x.info with
  | .absent, true => #[⟨"6.1.3-4", "trailer /Info dictionary present"⟩]
  | .absent, false => #[]
  | .full, _ => #[]

/-- PDF/A-4 6.1.7: a filter outside the allowlist, copied graphs included. -/
private def filters (c : Contract) (x : Census) : Array Violation :=
  x.filters.filterMap fun f =>
    if Filter.ofName f ∈ c.filters then none
    else some ⟨"6.1.7", s!"stream filter /{f} outside the profile's filters"⟩

/-- PDF/A-4 6.2.4.3: an intent demanded and none in the catalog. -/
private def intent (c : Contract) (x : Census) : Array Violation :=
  match c.intent with
  | none => #[]
  | some _ =>
    if x.outputIntents = 0 then
      #[⟨"6.2.4.3", "no output intent: device colour has no device-independent meaning"⟩]
    else #[]

/-- Whether an image's device space has meaning under an intent of this kind (PDF/A-4 6.2.4.3-4). -/
private def spaceHolds (k : IccKind) (intents : Nat) : String → Bool
  | "DeviceGray" => intents > 0
  | "DeviceRGB" => k == .rgb && intents > 0
  | "DeviceCMYK" => k == .cmyk && intents > 0
  | _ => true

private def isDevice (s : String) : Bool :=
  s == "DeviceGray" || s == "DeviceRGB" || s == "DeviceCMYK"

/-- PDF/A-4 6.2.4.3 over the image colour spaces the census classifies. -/
private def spaces (c : Contract) (x : Census) : Array Violation :=
  x.colorSpaces.filterMap fun s =>
    match c.colour with
    | .device => none
    | .intent k =>
      if spaceHolds k x.outputIntents s then none
      else some ⟨"6.2.4.3", s!"image colour space /{s} with no matching output intent"⟩
    | .conflict =>
      if isDevice s then some ⟨"6.2.4.3", s!"image colour space /{s} with no matching output intent"⟩
      else none

/-- PDF/A-4 6.2.9: transparency, an image `/SMask`, with no intent. -/
private def smask (c : Contract) (x : Census) : Array Violation :=
  match c.intent with
  | none => #[]
  | some _ =>
    if x.smasks > 0 && x.outputIntents == 0 then
      #[⟨"6.2.9-2", s!"{x.smasks} soft-masked image(s) with no output intent"⟩]
    else #[]

/-- PDF/UA-2 8.2.1 and 6.2: the structure tree and the mark. -/
private def tagged (c : Contract) (x : Census) : Array Violation :=
  if c.tagged then
    (if x.structTreeRoot then #[] else #[⟨"8.2.1-1", "no structure tree"⟩]) ++
    (if x.markInfo then #[] else #[⟨"6.2-1", "no MarkInfo"⟩])
  else #[]

private def langMissing (x : Census) : Bool :=
  match x.lang with
  | some l => l.isEmpty
  | none => true

/-- PDF/UA-2 8.4.4: a non-empty catalog `/Lang`. -/
private def lang (c : Contract) (x : Census) : Array Violation :=
  if c.needsLang && langMissing x then #[⟨"8.4.4-1", "no /Lang"⟩] else #[]

/-- PDF/UA-2 8.11.1: a `dc:title`. -/
private def title (c : Contract) (t : Option String) : Array Violation :=
  if c.needsTitle && t.isNone then #[⟨"8.11.1-1", "no title"⟩] else #[]

/-- PDF/X Trim-xor-Art over the file's box set. -/
private def boxes (c : Contract) (x : Census) : Array Violation :=
  match c.boxes with
  | .any => #[]
  | .trimXorArt =>
    match x.boxes.contains "TrimBox", x.boxes.contains "ArtBox" with
    | true, true => #[⟨"trim-xor-art", "pages declare both /TrimBox and /ArtBox"⟩]
    | false, false => #[⟨"trim-xor-art", "no page declares /TrimBox or /ArtBox"⟩]
    | true, false => #[]
    | false, true => #[]

end Rule

/-- Every rule of the contract the census breaks, in rule order; empty when the file satisfies it
as far as the census sees. -/
public def violations (c : Contract) (x : Census) (title : Option String) : Array Violation :=
  Rule.info c x ++ Rule.filters c x ++ Rule.intent c x ++ Rule.spaces c x ++
    Rule.smask c x ++ Rule.tagged c x ++ Rule.lang c x ++ Rule.title c title ++
    Rule.boxes c x

/-- The registered conformance names, as `\output{ profiles = … }` spells
them. -/
public def Profile.names : List String := ["pdf/a-4", "pdf/ua-2", "pdf/x-6"]

/-- The contract a name denotes. -/
public def Profile.contract? : String → Option Contract
  | "pdf/a-4" => some archive
  | "pdf/ua-2" => some accessible
  | "pdf/x-6" => some print
  | _ => none

public theorem Profile.names_covers :
    (∀ n ∈ Profile.names, (Profile.contract? n).isSome) ∧
    (∀ n, (Profile.contract? n).isSome → n ∈ Profile.names) := by
  refine ⟨by decide, fun n h => ?_⟩
  unfold Profile.contract? at h
  split at h <;> simp_all [Profile.names]

/-- The backend-neutral demands a profile folds into the output contract: PDF/UA-2 requires image
alternatives, PDF/A-4 sRGB colour. -/
public def Profile.implies : String → OutputContract
  | "pdf/a-4" => { color := .srgb }
  | "pdf/ua-2" => { alternatives := .required }
  | _ => {}

/-- The contract of a declared set, the meet of each name's contract; an unregistered name or
conflicting intents are refused. -/
public def Contract.ofProfiles (names : Array String) : Except Violation Contract := do
  let mut c := plain
  for n in names do
    match Profile.contract? n with
    | some k => c := c.meet k
    | none => throw ⟨"profile", s!"'{n}' is not a registered conformance profile"⟩
  if c.colour = .conflict then
    throw ⟨"6.2.4.3",
      "the declared profiles demand output intents of different colour kinds; one file carries one destination profile"⟩
  return c

public theorem InfoPolicy.meet_comm (a b : InfoPolicy) : a.meet b = b.meet a := by
  cases a <;> cases b <;> rfl

public theorem ColourPolicy.meet_comm (a b : ColourPolicy) : a.meet b = b.meet a := by
  cases a <;> cases b <;> simp only [ColourPolicy.meet]
  rename_i k k'
  by_cases h : k = k'
  · subst h; simp
  · simp [h, Ne.symm h]

public theorem IntentReq.meet_comm (a b : IntentReq) : a.meet b = b.meet a := by
  cases a <;> cases b <;> simp only [IntentReq.meet]
  rename_i k k'
  by_cases h : k = k'
  · subst h; simp
  · simp [h, Ne.symm h]

public theorem IntentReq.meetOpt_comm (a b : Option IntentReq) : meetOpt a b = meetOpt b a := by
  cases a <;> cases b <;> simp only [meetOpt]
  rw [IntentReq.meet_comm]

public theorem BoxPolicy.meet_comm (a b : BoxPolicy) : a.meet b = b.meet a := by
  cases a <;> cases b <;> rfl

public theorem meet_comm (a b : Contract) : (a.meet b).same (b.meet a) := by
  refine ⟨InfoPolicy.meet_comm .., ColourPolicy.meet_comm .., IntentReq.meetOpt_comm ..,
    Bool.or_comm .., Bool.or_comm .., Bool.or_comm .., Bool.or_comm .., Bool.or_comm ..,
    BoxPolicy.meet_comm .., fun f => ?_, fun i => ?_⟩
  · simp only [Contract.meet, Array.mem_filter, decide_eq_true_eq]
    exact and_comm
  · simp only [Contract.meet, Array.mem_append, Array.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (h | ⟨h, _⟩)
      · by_cases hb : i ∈ b.ids
        · exact Or.inl hb
        · exact Or.inr ⟨h, hb⟩
      · exact Or.inl h
    · rintro (h | ⟨h, _⟩)
      · by_cases ha : i ∈ a.ids
        · exact Or.inl ha
        · exact Or.inr ⟨h, ha⟩
      · exact Or.inl h

public theorem InfoPolicy.meet_idem (a : InfoPolicy) : a.meet a = a := by cases a <;> rfl

public theorem ColourPolicy.meet_idem (a : ColourPolicy) : a.meet a = a := by
  cases a <;> simp [ColourPolicy.meet]

public theorem IntentReq.meet_idem (a : IntentReq) : a.meet a = a := by
  cases a <;> simp [IntentReq.meet]

public theorem IntentReq.meetOpt_idem (a : Option IntentReq) : meetOpt a a = a := by
  cases a <;> simp [meetOpt, IntentReq.meet_idem]

public theorem BoxPolicy.meet_idem (a : BoxPolicy) : a.meet a = a := by cases a <;> rfl

public theorem meet_idem (a : Contract) : a.meet a = a := by
  simp only [Contract.meet, InfoPolicy.meet_idem, ColourPolicy.meet_idem, IntentReq.meetOpt_idem,
    Bool.or_self, BoxPolicy.meet_idem]
  have hf : (a.filters.filter fun f => decide (f ∈ a.filters)) = a.filters :=
    Array.filter_eq_self.2 fun f hf => decide_eq_true hf
  have hi : (a.ids.filter fun i => decide (i ∉ a.ids)) = #[] :=
    Array.filter_eq_empty_iff.2 fun i hi => by simp [hi]
  rw [hf, hi, Array.append_empty]

public theorem InfoPolicy.le_meet (a b : InfoPolicy) : a.le (a.meet b) := by
  cases a <;> cases b <;> simp [InfoPolicy.le, InfoPolicy.meet]

public theorem ColourPolicy.le_meet (a b : ColourPolicy) : a.le (a.meet b) := by
  cases a <;> cases b <;> simp only [ColourPolicy.le, ColourPolicy.meet] <;> try simp
  rename_i k k'
  by_cases h : k = k' <;> simp [h]

public theorem IntentReq.leOpt_meet (a b : Option IntentReq) : leOpt a (meetOpt a b) := by
  cases a <;> cases b <;> simp only [leOpt, meetOpt] <;> try simp
  rename_i k k'
  cases k <;> cases k' <;> simp [IntentReq.meet]
  all_goals (rename_i s s'; cases s <;> cases s' <;> simp)

public theorem BoxPolicy.le_meet (a b : BoxPolicy) : a.le (a.meet b) := by
  cases a <;> cases b <;> simp [BoxPolicy.le, BoxPolicy.meet]

public theorem le_meet_left (a b : Contract) : a.le (a.meet b) := by
  refine ⟨InfoPolicy.le_meet .., fun f hf => ?_, ColourPolicy.le_meet .., IntentReq.leOpt_meet ..,
    fun h => by simp [Contract.meet, h], fun h => by simp [Contract.meet, h],
    fun h => by simp [Contract.meet, h], fun h => by simp [Contract.meet, h],
    fun h => by simp [Contract.meet, h], BoxPolicy.le_meet .., fun i hi => ?_⟩
  · exact (Array.mem_filter.1 hf).1
  · simp [Contract.meet, hi]

public theorem meet_covers (a b : Contract) : a.le (a.meet b) ∧ b.le (a.meet b) := by
  refine ⟨le_meet_left a b, ?_⟩
  have hl := le_meet_left b a
  have hs := meet_comm b a
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hs
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11⟩ := hl
  refine ⟨h1 ▸ l1, fun f hf => l2 f ((h10 f).2 hf), h2 ▸ l3, h3 ▸ l4,
    fun h => h4 ▸ l5 h, fun h => h5 ▸ l6 h, fun h => h6 ▸ l7 h, fun h => h7 ▸ l8 h,
    fun h => h8 ▸ l9 h, h9 ▸ l10, fun i hi => (h11 i).1 (l11 i hi)⟩

public theorem filters_meet_set_eq (a b : Contract) (f : Filter) :
    f ∈ (a.meet b).filters ↔ f ∈ a.filters ∧ f ∈ b.filters := by
  simp [Contract.meet]

namespace Rule

private theorem info_mono {a b : Contract} (h : a.infoDict.le b.infoDict) (x : Census)
    (hb : info b x = #[]) : info a x = #[] := by
  unfold InfoPolicy.le at h
  unfold info at *
  rcases h with h | h
  · rw [h]
  · rw [h] at hb
    split <;> simp_all

private theorem filters_mono {a b : Contract} (h : ∀ f ∈ b.filters, f ∈ a.filters) (x : Census)
    (hb : filters b x = #[]) : filters a x = #[] := by
  unfold filters at *
  rw [Array.filterMap_eq_empty_iff] at *
  intro f hf
  have := hb f hf
  split at this
  · next hin => simp [h _ hin]
  · simp at this

private theorem intent_mono {a b : Contract} (h : IntentReq.leOpt a.intent b.intent) (x : Census)
    (hb : intent b x = #[]) : intent a x = #[] := by
  unfold IntentReq.leOpt at h
  unfold intent at *
  rcases h with h | h | h
  · rw [h]
  · rw [h]; exact hb
  · rw [h] at hb
    split
    · rfl
    · simp only at hb
      split at hb
      · simp at hb
      · simp_all

private theorem smask_mono {a b : Contract} (h : IntentReq.leOpt a.intent b.intent) (x : Census)
    (hb : smask b x = #[]) : smask a x = #[] := by
  unfold IntentReq.leOpt at h
  unfold smask at *
  rcases h with h | h | h
  · rw [h]
  · rw [h]; exact hb
  · rw [h] at hb
    split
    · rfl
    · simp only at hb
      split at hb
      · simp at hb
      · simp_all

private theorem spaces_mono {a b : Contract} (h : a.colour.le b.colour) (x : Census)
    (hb : spaces b x = #[]) : spaces a x = #[] := by
  unfold ColourPolicy.le at h
  unfold spaces at *
  rw [Array.filterMap_eq_empty_iff] at *
  intro s hs
  have hbs := hb s hs
  rcases h with h | h | h
  · rw [h]
  · rw [h]; exact hbs
  · rw [h] at hbs
    simp only at hbs
    split
    · rfl
    · next _ k _ =>
      split at hbs
      · simp at hbs
      · next hd =>
        have hk : spaceHolds k x.outputIntents s = true := by
          unfold spaceHolds
          unfold isDevice at hd
          split <;> simp_all
        simp [hk]
    · exact hbs

private theorem tagged_mono {a b : Contract} (h : a.tagged = true → b.tagged = true) (x : Census)
    (hb : tagged b x = #[]) : tagged a x = #[] := by
  unfold tagged at *
  cases ha : a.tagged
  · simp
  · rw [h ha] at hb
    simpa using hb

private theorem lang_mono {a b : Contract} (h : a.needsLang = true → b.needsLang = true) (x : Census)
    (hb : lang b x = #[]) : lang a x = #[] := by
  unfold lang at *
  cases ha : a.needsLang
  · simp
  · rw [h ha] at hb
    simpa using hb

private theorem title_mono {a b : Contract} (h : a.needsTitle = true → b.needsTitle = true)
    (t : Option String) (hb : title b t = #[]) : title a t = #[] := by
  unfold title at *
  cases ha : a.needsTitle
  · simp
  · rw [h ha] at hb
    simpa using hb

private theorem boxes_mono {a b : Contract} (h : a.boxes.le b.boxes) (x : Census)
    (hb : boxes b x = #[]) : boxes a x = #[] := by
  unfold BoxPolicy.le at h
  unfold boxes at *
  rcases h with h | h
  · rw [h]
  · rw [h]; exact hb

end Rule

public theorem violations_monotone {a b : Contract} (h : a.le b) (x : Census) (t : Option String)
    (hb : violations b x t = #[]) : violations a x t = #[] := by
  obtain ⟨h1, h2, h3, h4, h5, _, _, h8, h9, h10, _⟩ := h
  unfold violations at *
  simp only [Array.append_eq_empty_iff] at *
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, b7⟩, b8⟩, b9⟩ := hb
  exact ⟨⟨⟨⟨⟨⟨⟨⟨Rule.info_mono h1 x b1, Rule.filters_mono h2 x b2⟩, Rule.intent_mono h4 x b3⟩,
    Rule.spaces_mono h3 x b4⟩, Rule.smask_mono h4 x b5⟩, Rule.tagged_mono h5 x b6⟩,
    Rule.lang_mono h8 x b7⟩, Rule.title_mono h9 t b8⟩, Rule.boxes_mono h10 x b9⟩

public theorem needsTitle_accounts (c : Contract) (x : Census) (h : c.needsTitle = true) :
    violations c x none ≠ #[] := by
  unfold violations
  simp [Rule.title, h]

public theorem ofProfiles_plain : Contract.ofProfiles #[] = .ok plain := by rfl

end LeanTex.Core.PdfContract
