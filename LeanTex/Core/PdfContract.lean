module

public import LeanTex.Core.PdfCensus
public import LeanTex.Core.Ir

namespace LeanTex.Core.PdfContract

open LeanTex.Core.PdfCensus (Census)
open LeanTex.Core.Ir (OutputContract)

/-! # The PDF conformance contract

What a declared conformance profile *demands* of the file, as values —
the `ClassRecord` discipline: a profile is a record, never a module with
its own writer. A document declares a *set* of profile names
(`\output{ profiles = pdf/a-4, pdf/ua-2 }`); each name is one `Contract`,
the set is their `meet` (fieldwise stricter), and the writer will read the
meet, never a name. Until the writer does, nothing here changes a byte:
this module judges.

Judging is `violations : Contract → Census → Option String → Array
Violation` over the read-side census of the bytes just built
(`PdfCensus.census`) — never over the writer's intent, so a copied foreign
page is judged like anything else. Each rule reads a census field; a rule
the census cannot yet see is not judged and is named below, never
approximated from what the writer meant:

- device colour painted by content-stream operators (`rg`, `k`) — the
  census classifies image colour spaces only, so the colour rule judges
  the presence of an output intent and the image spaces;
- an output intent's own profile kind, a page `/Group /CS`, a `Default*`
  resource space, an `/Indexed` base space — all read as absent;
- `/Tabs` on annotated pages, whether a destination is a structure
  destination, and whether every non-real content operator is marked as an
  artifact (PDF/UA-2 8.2.2) — none is a census field;
- page boxes are censused for the file, not per page, so Trim-xor-Art is
  judged on the file's set;
- the `/Info` dictionary's keys (PDF/A-4 6.1.3-5) — its presence is the one
  violation, and the one fix removes both.

The title is the one fact judged from the document rather than the
bytes: the census does not parse XMP, and `dc:title` is the writer's
projection of `Meta.title`.

This module imports the census and the IR and never the writer: a
contract that could see the writer's spellings would be a contract on
intent (the pre-commit hook holds that line, as it does for the census). -/

/-- A stream filter, as the allowlist names it. `none` is the unfiltered
stream — a census never reports it, so it is a member of the domain for
`meet` and never the subject of a violation. `other` carries a name the
engine has no constructor for: Table 6 filters it never emits, and
extension filters (`BrotliDecode`). -/
public inductive Filter where
  | flate
  | dct
  | none
  | other (name : String)
  deriving DecidableEq, Repr, Inhabited

/-- The census spells filters by their PDF name (ISO 32000-2 Table 6). -/
public def Filter.ofName : String → Filter
  | "FlateDecode" => .flate
  | "DCTDecode" => .dct
  | n => .other n

/-- The trailer's `/Info` dictionary: kept (`full`, today's file) or
forbidden (`absent`: PDF/A-4 6.1.3 — a document information dictionary is
deprecated in PDF 2.0, and A-4 refuses it unless the catalog has
`/PieceInfo`). -/
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

/-- How device colour is given meaning: `device` (no demand — today's
file), `intent k` (a device space needs an output intent whose profile is
of kind `k`, or a matching `Default*` space: PDF/A-4 6.2.4.3), `conflict`
(two profiles demand intents of different kinds; one file carries one
destination profile, so no device space can be satisfied — the top of the
order, reached only by a `meet` that `ofProfiles` then refuses). -/
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

/-- What output intents the file must carry: one, or both subtypes sharing
one destination profile (PDF/A-4 6.2.3: when several intents exist, every
`DestOutputProfile` is the same indirect object). -/
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

/-- Page boxes: `any` (today's file: bleed emits Trim, Bleed and Art
together, no bleed emits none), `trimXorArt` (PDF/X: every page carries
exactly one of `/TrimBox` and `/ArtBox` — carried from ISO 15930-7 as a
hypothesis for X-6, flagged on `print`). -/
public inductive BoxPolicy where
  | any
  | trimXorArt
  deriving DecidableEq, Repr, Inhabited

public def BoxPolicy.meet : BoxPolicy → BoxPolicy → BoxPolicy
  | .any, b => b
  | .trimXorArt, _ => .trimXorArt

public def BoxPolicy.le (a b : BoxPolicy) : Prop := a = .any ∨ a = b

public instance : DecidableRel BoxPolicy.le := fun a b => inferInstanceAs (Decidable (a = .any ∨ a = b))

/-- An XMP identification block a claim writes: the three the ISO profiles
define, each with its fixed schema. A finite enumeration, so the union in
`meet` is by equality and its set statement is clean; the schema strings
are functions of the constructor, never data a meet could disagree on. -/
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

/-- The demands of a profile set on the PDF file, values only. The name a
profile was declared under is a key of `Profile.contract?`, not a demand —
the meet of two names is not a name — so it is not a field. -/
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

/-- `a ≤ b`: every demand of `a` is a demand of `b` — `b` forbids at least
what `a` forbids (its filter allowlist is inside `a`'s), and claims at
least what `a` claims. A decidable record predicate. -/
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

/-- Two contracts with the same demands: every scalar field equal, the
two set-valued fields equal as sets. Array order is not a demand. -/
public def Contract.same (a b : Contract) : Prop :=
  a.infoDict = b.infoDict ∧ a.colour = b.colour ∧ a.intent = b.intent ∧
  a.tagged = b.tagged ∧ a.structDests = b.structDests ∧ a.tabs = b.tabs ∧
  a.needsLang = b.needsLang ∧ a.needsTitle = b.needsTitle ∧ a.boxes = b.boxes ∧
  (∀ f, f ∈ a.filters ↔ f ∈ b.filters) ∧ (∀ i, i ∈ a.ids ↔ i ∈ b.ids)

/-- ISO 32000-2 Table 6 minus `LZWDecode`, the set PDF/A-4 6.1.7 permits;
`Crypt` is left out with encryption (A-4 6.1.3 forbids `/Encrypt`).
Spelled as the engine's constructors where it has them and by name where
it never emits the filter. -/
private def tableSix : Array Filter :=
  #[.flate, .dct, .none, .other "ASCIIHexDecode", .other "ASCII85Decode",
    .other "RunLengthDecode", .other "CCITTFaxDecode", .other "JBIG2Decode",
    .other "JPXDecode"]

/-- Today's file: nothing demanded, nothing claimed; every filter PDF 2.0
itself names (Table 6 whole, `Crypt` included) — a file under no profile
may carry what the standard allows, copied graphs included. The bottom of
the profile order, and `ofProfiles`' starting point; the Brotli extension
permits one filter more and so sits below it, which is why an extension
will have to start the fold rather than join it. -/
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

/-- PDF/A-4 (ISO 19005-4:2020): no `/Info`, Table 6 filters, device colour
under an RGB output intent — the engine's working space is sRGB, so the
destination profile it will carry is RGB (the CMYK model then needs a
`DefaultCMYK` resource space, the colour plan's work) — the `GTS_PDFA1`
intent, the `pdfaid` identification. No tagging demand: A-4 has no
conformance levels and leaves structure to PDF/UA. -/
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

/-- PDF/UA-2 (ISO 14289-2:2024): tagged with structure destinations,
`/Tabs` on annotated pages, a language and a title; no Info, colour or box
demand of its own. The filter set is the base standard's Table 6 — UA-2
adds no filter rule (hypothesis). Declarable today and failing honestly on
the census until the structure slices land. -/
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

/-- PDF/X-6 (ISO 15930-9:2020): a `GTS_PDFX` printer intent — its kind is
CMYK here as the default press profile's, until the `intent =` key names
a document's own — Trim-xor-Art boxes (hypothesis carried from X-4, not
yet read from the X-6 text or a validator), the `pdfxid` identification.
Declarable and failing honestly until the print slice emits its intent. -/
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

/-- The Brotli extension (PDF Association, extension to ISO 32000-2):
`plain` plus `BrotliDecode` in the allowlist, no claim. Experimental —
reachable only through `extensions =`, which this grammar does not yet
have; the constant exists so `meet` has its full domain and so any
profile's meet removes the filter. -/
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

/-- PDF/A-4 6.2.4.3: an intent demanded and none in the catalog. Every
content stream paints in device colour (the initial colour space is
DeviceGray, ISO 32000-2 §8.4.1), which an output intent alone gives
meaning to — the operators themselves are not censused. -/
private def intent (c : Contract) (x : Census) : Array Violation :=
  match c.intent with
  | none => #[]
  | some _ =>
    if x.outputIntents = 0 then
      #[⟨"6.2.4.3", "no output intent: device colour has no device-independent meaning"⟩]
    else #[]

/-- Does an image's device space have meaning under this kind of intent?
Gray needs any intent (PDF/A-4 6.2.4.3-4), RGB an RGB one, CMYK a CMYK one;
a non-device family (ICCBased, Indexed — whose base the census does not
read) asks nothing. -/
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

/-- PDF/A-4 6.2.9: transparency (an image `/SMask`) with no intent; a page
`/Group /CS` would also satisfy the rule and is not censused. -/
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

/-- Every rule of the contract the census breaks, in rule order. Empty
means the file satisfies the contract as far as the census sees. -/
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

/-- Every registered name denotes a contract, and only registered names do
(`_covers`): the grammar's list and the table are one. -/
public theorem Profile.names_covers :
    (∀ n ∈ Profile.names, (Profile.contract? n).isSome) ∧
    (∀ n, (Profile.contract? n).isSome → n ∈ Profile.names) := by
  refine ⟨by decide, fun n h => ?_⟩
  unfold Profile.contract? at h
  split at h <;> simp_all [Profile.names]

/-- The backend-neutral demands a profile folds into the output contract
at elaboration: PDF/UA-2 requires an alternative for every image
(`alternatives = required`); PDF/A-4 gives colour a device-independent
meaning (`color = srgb`). Everything else a profile demands is a PDF-side
fact and lives in its `Contract`. -/
public def Profile.implies : String → OutputContract
  | "pdf/a-4" => { color := .srgb }
  | "pdf/ua-2" => { alternatives := .required }
  | _ => {}

/-- The contract of a declared set: the meet of each name's contract from
`plain`. An unregistered name is refused (the grammar refuses it first),
and so is a set whose intents cannot share one destination profile. -/
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

/-! ## The algebra -/

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

/-- **`meet_comm`** (`_exact` on every scalar field, `_set_eq` on the two
set-valued ones): the order two profiles are declared in is not a demand. -/
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

/-- **`meet_idem`** (`_exact`): declaring a profile twice is declaring it
once — `profiles = pdf/a-4, pdf/a-4` demands what `pdf/a-4` demands, as a
record equality: the filter intersection keeps every element, the id union
adds none. -/
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

/-- `a ≤ a ⊓ b`: the meet demands everything `a` does. -/
public theorem le_meet_left (a b : Contract) : a.le (a.meet b) := by
  refine ⟨InfoPolicy.le_meet .., fun f hf => ?_, ColourPolicy.le_meet .., IntentReq.leOpt_meet ..,
    fun h => by simp [Contract.meet, h], fun h => by simp [Contract.meet, h],
    fun h => by simp [Contract.meet, h], fun h => by simp [Contract.meet, h],
    fun h => by simp [Contract.meet, h], BoxPolicy.le_meet .., fun i hi => ?_⟩
  · exact (Array.mem_filter.1 hf).1
  · simp [Contract.meet, hi]

/-- **`meet_covers`** (`_covers`): the meet of two contracts demands
everything either demands — a file passing the meet passes each, once
`violations_monotone` is read with it. The right half is the left half
read through `meet_comm`, spelled out because `same` is not `le`. -/
public theorem meet_covers (a b : Contract) : a.le (a.meet b) ∧ b.le (a.meet b) := by
  refine ⟨le_meet_left a b, ?_⟩
  have hl := le_meet_left b a
  have hs := meet_comm b a
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hs
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11⟩ := hl
  refine ⟨h1 ▸ l1, fun f hf => l2 f ((h10 f).2 hf), h2 ▸ l3, h3 ▸ l4,
    fun h => h4 ▸ l5 h, fun h => h5 ▸ l6 h, fun h => h6 ▸ l7 h, fun h => h7 ▸ l8 h,
    fun h => h8 ▸ l9 h, h9 ▸ l10, fun i hi => (h11 i).1 (l11 i hi)⟩

/-- **`filters_meet_set_eq`** (`_set_eq`): the meet's allowlist is the
intersection. -/
public theorem filters_meet_set_eq (a b : Contract) (f : Filter) :
    f ∈ (a.meet b).filters ↔ f ∈ a.filters ∧ f ∈ b.filters := by
  simp [Contract.meet]

/-! ### Monotonicity, one rule at a time -/

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

/-- **`violations_monotone`** (`_monotone`): a file that satisfies the
stricter contract satisfies the weaker — so a file passing a declared
set's meet passes each member (`meet_covers`), and "PDF/A-4 + PDF/UA-2
compose" is a theorem, not a sentence. -/
public theorem violations_monotone {a b : Contract} (h : a.le b) (x : Census) (t : Option String)
    (hb : violations b x t = #[]) : violations a x t = #[] := by
  obtain ⟨h1, h2, h3, h4, h5, _, _, h8, h9, h10, _⟩ := h
  unfold violations at *
  simp only [Array.append_eq_empty_iff] at *
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, b7⟩, b8⟩, b9⟩ := hb
  exact ⟨⟨⟨⟨⟨⟨⟨⟨Rule.info_mono h1 x b1, Rule.filters_mono h2 x b2⟩, Rule.intent_mono h4 x b3⟩,
    Rule.spaces_mono h3 x b4⟩, Rule.smask_mono h4 x b5⟩, Rule.tagged_mono h5 x b6⟩,
    Rule.lang_mono h8 x b7⟩, Rule.title_mono h9 t b8⟩, Rule.boxes_mono h10 x b9⟩

/-- **`needsTitle_accounts`** (`_accounts`): a contract that demands a title
and a document with none is a named violation, never a silent pass. -/
public theorem needsTitle_accounts (c : Contract) (x : Census) (h : c.needsTitle = true) :
    violations c x none ≠ #[] := by
  unfold violations
  simp [Rule.title, h]

/-- The empty set demands today's file (`_exact`). -/
public theorem ofProfiles_plain : Contract.ofProfiles #[] = .ok plain := by rfl

end LeanTex.Core.PdfContract
