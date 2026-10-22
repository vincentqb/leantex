module

public import LeanTex.Core.MdParse
public import LeanTex.Core.Jtex

public section

namespace LeanTex.Core.MystTemplate

/-! A MyST template's `template.yml` (jtex v1) read and checked, and a document's front matter
extended into the `doc` a template reads, as myst-templates 1.x does both, every departure named. -/

open LeanTex.Core.Md (Yaml)
open LeanTex.Core.Jtex (Value)

/-- A YAML node as the JSON value myst-templates reads it: YAML 1.2's core booleans, null and
integers, every other scalar a string. -/
def valueOf : Yaml → Value
  | .scalar s =>
    match s with
    | "true" | "True" | "TRUE" => .bool true
    | "false" | "False" | "FALSE" => .bool false
    | "null" | "Null" | "NULL" | "~" => .null
    | _ => match s.toInt? with
      | some n => .num n
      | none => .str s
  | .seq items => .arr (items.attach.toList.map fun ⟨y, _⟩ => valueOf y)
  | .map fields => .obj (fields.attach.toList.map fun ⟨p, _⟩ => (p.1, valueOf p.2))
decreasing_by
  all_goals
    rename_i h
    have := Array.sizeOf_lt_of_mem h
    try cases p
    simp_all
    omega

/-- Whether a value is set: neither null nor absent. -/
def defined : Value → Bool
  | .undef | .null => false
  | _ => true

/-- An option's, part's or doc field's condition: the option it reads, and the value it wants. -/
structure Condition where
  id : String
  value : Option Value
  deriving Repr, BEq, Inhabited

/-- The kinds of a template option. -/
inductive OptionType where
  | boolean
  | string
  | number
  | choice
  | file
  deriving Repr, BEq, Inhabited

/-- One declared option. -/
structure OptionDef where
  id : String
  kind : OptionType
  required : Bool := false
  default : Option Value := none
  choices : List String := []
  maxChars : Option Nat := none
  min : Option Int := none
  max : Option Int := none
  integer : Bool := false
  multiple : Bool := false
  condition : Option Condition := none
  deriving Repr, Inhabited

/-- One declared part. -/
structure PartDef where
  id : String
  required : Bool := false
  asList : Bool := false
  maxChars : Option Nat := none
  maxWords : Option Nat := none
  condition : Option Condition := none
  deriving Repr, Inhabited

/-- One front matter field the template reads. -/
structure DocDef where
  id : String
  required : Bool := false
  condition : Option Condition := none
  deriving Repr, Inhabited

/-- A template's declaration: its options, parts and doc fields, the packages its source loads,
the files it ships, and the bibliography style it sets. -/
structure TemplateYml where
  options : Array OptionDef := #[]
  parts : Array PartDef := #[]
  doc : Array DocDef := #[]
  packages : Array String := #[]
  files : Array String := #[]
  bibliography : Option String := none
  deriving Repr, Inhabited

/-- What a template's declaration or its use leaves unmet, each a loss the document is still set
through: the declaration's own faults, then an option, part or doc field missing, unknown or
outside its declared bounds, and an undated or misdated document. -/
inductive Issue where
  | malformed (path : String) (what : String)
  | optionMissing (id : String)
  | optionUnknown (id : String)
  | optionInvalid (id : String) (what : String)
  | partMissing (id : String)
  | partUnknown (id : String)
  | partTooLong (id : String) (limit : Nat) (words : Bool)
  | docMissing (id : String)
  | frontInvalid (path : String) (what : String)
  | undated
  | dateUnread (spelling : String)
  deriving Repr, BEq, Inhabited

/-- myst-frontmatter's site keys, the parts it knows among them. -/
def siteKeys : List String :=
  ["title", "subtitle", "short_title", "description", "thumbnail", "thumbnailOptimized", "banner",
   "bannerOptimized", "tags", "authors", "reviewers", "editors", "contributors", "venue", "github",
   "keywords", "affiliations", "funding", "copyright", "options", "parts", "social", "abstract",
   "summary", "keypoints", "dedication", "epigraph", "data_availability", "acknowledgments"]

/-- myst-frontmatter's keys a project and a page both take. -/
def projectAndPageKeys : List String :=
  ["date", "doi", "identifiers", "open_access", "license", "binder", "source", "subject", "volume",
   "issue", "first_page", "last_page", "oxa", "numbering", "bibliography", "math", "abbreviations",
   "exports", "downloads", "settings", "edit_url", "source_url", "arxiv", "pmid", "pmcid", "zenodo"] ++
    siteKeys

/-- The page front matter keys a doc field may name, myst-frontmatter's PAGE_FRONTMATTER_KEYS. -/
def frontmatterKeys : List String :=
  projectAndPageKeys ++ ["label", "kernelspec", "jupytext", "tags", "site", "enumerator",
    "content_includes_title", "skip_execution", "execute"]

/-- myst-frontmatter's aliases, each spelling with the key it stands for. -/
def aliases : List (String × String) :=
  [("author", "authors"), ("reviewer", "reviewers"), ("editor", "editors"),
   ("contributor", "contributors"), ("affiliation", "affiliations"), ("export", "exports"),
   ("download", "downloads"), ("jupyter", "thebe"), ("part", "parts"), ("ack", "acknowledgments"),
   ("acknowledgements", "acknowledgments"), ("acknowledgment", "acknowledgments"),
   ("acknowledgement", "acknowledgments"), ("availability", "data_availability"),
   ("dataAvailability", "data_availability"), ("data-availability", "data_availability"),
   ("quote", "epigraph"), ("plain_language_summary", "summary"),
   ("plain-language-summary", "summary"), ("plainLanguageSummary", "summary"),
   ("lay_summary", "summary"), ("lay-summary", "summary"), ("keyPoints", "keypoints"),
   ("key_points", "keypoints"), ("key-points", "keypoints"), ("image", "thumbnail"),
   ("identifier", "identifiers"), ("socials", "social")]

/-- The keys myst reserves beside a template's options: an export's own and its aliases, and every
project front matter key and alias. -/
def reservedKeys : List String :=
  ["format", "template", "output", "zip", "id", "name", "renderer", "articles", "top_level",
   "sub_articles", "article", "sub_article"] ++ projectAndPageKeys ++
    ["id", "references", "requirements", "resources", "static_files", "thebe", "toc"] ++
    aliases.map (·.1)

private def boolAt (path : String) (y : Option Yaml) (out : Array Issue) : Bool × Array Issue :=
  match y.map valueOf with
  | none => (false, out)
  | some (.bool b) => (b, out)
  | some _ => (false, out.push (.malformed path "a boolean"))

private def natAt (path : String) (y : Option Yaml) (out : Array Issue) : Option Nat × Array Issue :=
  match y.map valueOf with
  | none => (none, out)
  | some (.num n) => if n ≥ 0 then (some n.toNat, out) else (none, out.push (.malformed path "a count"))
  | some _ => (none, out.push (.malformed path "a count"))

private def intAt (path : String) (y : Option Yaml) (out : Array Issue) : Option Int × Array Issue :=
  match y.map valueOf with
  | none => (none, out)
  | some (.num n) => (some n, out)
  | some _ => (none, out.push (.malformed path "a number"))

private def conditionAt (path : String) (y : Option Yaml) (out : Array Issue) :
    Option Condition × Array Issue :=
  match y with
  | none => (none, out)
  | some c => match (c.get? "id").bind (·.text?) with
    | some id => (some { id, value := (c.get? "value").map valueOf }, out)
    | none => (none, out.push (.malformed path "a condition naming its option's id"))

private def items (y : Option Yaml) : Array Yaml :=
  match y with
  | some (.seq xs) => xs
  | _ => #[]

private def texts (y : Option Yaml) : Array String :=
  match y with
  | some (.seq xs) => xs.filterMap (·.text?)
  | some (.scalar s) => #[s]
  | _ => #[]

/-- A value as an option of `d` takes it: a boolean, a string within its length, an integer
within its bounds, one of its choices, or a file path; the reason where it is none. -/
def checkValue (d : OptionDef) (v : Value) : Except String Value :=
  match d.kind, v with
  | .boolean, .bool b => .ok (.bool b)
  | .boolean, _ => .error "a boolean"
  | .string, .str s =>
    match d.maxChars with
    | some m => if m == 0 || Jtex.utf16Len s ≤ m then .ok (.str s) else .error s!"at most {m} characters"
    | none => .ok (.str s)
  -- the YAML reader loses a scalar's quotes, so an unquoted number stands for a string too
  | .string, .num n => .ok (.str (toString n))
  | .string, _ => .error "a string"
  | .number, .num n =>
    if d.min.any (n < ·) then .error s!"at least {d.min.getD 0}"
    else if d.max.any (n > ·) then .error s!"at most {d.max.getD 0}"
    else .ok (.num n)
  | .number, _ => .error "a number"
  | .choice, .str s =>
    if d.choices.contains s then .ok (.str s) else .error s!"one of {", ".intercalate d.choices}"
  | .choice, _ => .error s!"one of {", ".intercalate d.choices}"
  | .file, .str s => .ok (.str s)
  | .file, _ => .error "a file path"

/-- A value as `d` takes it, a list item by item where it takes several, its invalid items dropped,
a lone value a list of one. -/
def checkOption (d : OptionDef) (v : Value) : Except String Value :=
  if !d.multiple then checkValue d v else
  match v with
  | .arr xs => .ok (.arr (xs.filterMap fun x => (checkValue d x).toOption))
  | v => (checkValue d v).map fun x => .arr [x]

private def optionDef (y : Yaml) (k : Nat) (out : Array Issue) : Option OptionDef × Array Issue :=
  let path := s!"options.{k}"
  match (y.get? "id").bind (·.text?), (y.get? "type").bind (·.text?) with
  | some id, some ty =>
    let type? : Option OptionType := match ty with
      | "boolean" => some .boolean
      | "string" => some .string
      | "number" => some .number
      | "choice" => some .choice
      | "file" => some .file
      | _ => none
    match type? with
    | none => (none, out.push (.malformed path s!"an option type, not '{ty}'"))
    | some type =>
      if reservedKeys.contains id then (none, out.push (.malformed path s!"an id myst does not reserve, not '{id}'")) else
      if type == .choice && (y.get? "choices").isNone then (none, out.push (.malformed path "its choices")) else
      let (required, out) := boolAt s!"{path}.required" (y.get? "required") out
      let (integer, out) := boolAt s!"{path}.integer" (y.get? "integer") out
      let (multiple, out) := boolAt s!"{path}.multiple" (y.get? "multiple") out
      let (maxChars, out) := natAt s!"{path}.max_chars" (y.get? "max_chars") out
      let (lo, out) := intAt s!"{path}.min" (y.get? "min") out
      let (hi, out) := intAt s!"{path}.max" (y.get? "max") out
      let (lo, hi) := match lo, hi with
        | some a, some b => if b < a then (some b, some a) else (some a, some b)
        | a, b => (a, b)
      let (condition, out) := conditionAt s!"{path}.condition" (y.get? "condition") out
      let d : OptionDef :=
        { id := id, kind := type, required := required, choices := (texts (y.get? "choices")).toList,
          maxChars := maxChars, min := lo, max := hi, integer := integer, multiple := multiple,
          condition := condition }
      match ((y.get? "default").map valueOf).filter defined with
      | none => (some d, out)
      | some v => match checkOption d v with
        | .ok v => (some { d with default := some v }, out)
        | .error e => (some d, out.push (.malformed s!"{path}.default" e))
  | _, _ => (none, out.push (.malformed path "an option with its id and type"))

private def partDef (y : Yaml) (k : Nat) (out : Array Issue) : Option PartDef × Array Issue :=
  let path := s!"parts.{k}"
  match (y.get? "id").bind (·.text?) with
  | none => (none, out.push (.malformed path "a part with its id"))
  | some id =>
    let (required, out) := boolAt s!"{path}.required" (y.get? "required") out
    let (asList, out) := boolAt s!"{path}.as_list" (y.get? "as_list") out
    let (maxChars, out) := natAt s!"{path}.max_chars" (y.get? "max_chars") out
    let (maxWords, out) := natAt s!"{path}.max_words" (y.get? "max_words") out
    let (condition, out) := conditionAt s!"{path}.condition" (y.get? "condition") out
    (some { id, required, asList, maxChars, maxWords, condition }, out)

private def docDef (y : Yaml) (k : Nat) (out : Array Issue) : Option DocDef × Array Issue :=
  let path := s!"doc.{k}"
  match (y.get? "id").bind (·.text?) with
  | none => (none, out.push (.malformed path "a doc field with its id"))
  | some id =>
    if !frontmatterKeys.contains id then (none, out.push (.malformed path s!"a front matter key, not '{id}'")) else
    let (required, out) := boolAt s!"{path}.required" (y.get? "required") out
    let (condition, out) := conditionAt s!"{path}.condition" (y.get? "condition") out
    (some { id, required, condition }, out)

/-- A `template.yml` read: its definitions, and each fault in it, a faulty definition dropped. -/
def read (y : Yaml) : TemplateYml × Array Issue := Id.run do
  let mut out : Array Issue := #[]
  match ((y.get? "myst").orElse fun _ => y.get? "jtex").bind (·.text?) with
  | some "v1" => pure ()
  | _ => out := out.push (.malformed "myst" "the jtex version v1")
  let mut t : TemplateYml := {}
  for (o, k) in (items (y.get? "options")).zipIdx do
    let (d, o') := optionDef o k out
    out := o'
    if let some d := d then t := { t with options := t.options.push d }
  for (p, k) in (items (y.get? "parts")).zipIdx do
    let (d, o') := partDef p k out
    out := o'
    if let some d := d then t := { t with parts := t.parts.push d }
  for (p, k) in (items (y.get? "doc")).zipIdx do
    let (d, o') := docDef p k out
    out := o'
    if let some d := d then t := { t with doc := t.doc.push d }
  t := { t with
    packages := texts (y.get? "packages"), files := texts (y.get? "files"),
    bibliography := (((y.get? "style").bind (·.get? "bibliography")).bind (·.text?)).filter
      fun b => b == "natbib" || b == "biblatex" }
  -- every condition names a declared option, and a value that option takes
  let conds := (t.options.map (fun d => (d.id, d.condition))) ++ (t.parts.map (fun d => (d.id, d.condition))) ++
    (t.doc.map (fun d => (d.id, d.condition)))
  for (id, c) in conds do
    if let some c := c then
      match t.options.find? (·.id == c.id) with
      | some od =>
        if od.id == id then out := out.push (.malformed s!"{id}.condition" "an option other than itself")
        else if let some v := c.value then
          if (checkOption od v).toBool == false then
            out := out.push (.malformed s!"{id}.condition" s!"a value option '{c.id}' takes")
      | none => if c.id != id then out := out.push (.malformed s!"{id}.condition" s!"a declared option, not '{c.id}'")
  return (t, out)

/-- Whether a condition holds over the given options: always without one, else its option given
and, where it names a value, that value. -/
def conditionMet (c : Option Condition) (given : List (String × Value)) : Bool :=
  match c with
  | none => true
  | some c => match given.find? (·.1 == c.id) with
    | none => false
    | some (_, v) => c.value.all (· == v)

private def isRequired (required : Bool) (default : Option Value) : Bool :=
  required && default.isNone

/-- The options a template renders with, from the given ones: each whose condition holds, given or
by a set default, checked; the issues name a missing required one, an unknown one and an invalid
one, each dropped. -/
def options (t : TemplateYml) (given : List (String × Value)) : List (String × Value) × Array Issue :=
  Id.run do
  let live := t.options.filter (conditionMet ·.condition given)
  let mut out : Array Issue := #[]
  for d in live do
    if isRequired d.required d.default && !(given.any fun (k, v) => k == d.id && defined v) then
      out := out.push (.optionMissing d.id)
  for (k, _) in given do
    unless live.any (·.id == k) || reservedKeys.contains k do out := out.push (.optionUnknown k)
  let mut res : Array (String × Value) := #[]
  for d in live do
    let v := (given.find? (·.1 == d.id)).map (·.2) |>.filter defined
    -- myst-templates fills a default only where it is truthy, so a false or empty default stays unset
    match v.orElse fun _ => d.default.filter (·.truthy) with
    | none => pure ()
    | some v => match checkOption d v with
      | .ok v => res := res.push (d.id, v)
      | .error e => out := out.push (.optionInvalid d.id e)
  return (res.toList, out)

/-- A part's given text: one block, or a list of them where the part is read as a list. -/
inductive PartText where
  | one (s : String)
  | many (items : Array String)
  deriving Repr, BEq, Inhabited

/-- The limits one text of part `d` exceeds, in UTF-16 units as JavaScript counts and in words split
at single spaces as myst-templates splits them; an empty text exceeds none. -/
def tooLong (d : PartDef) (s : String) : Array Issue :=
  if s.isEmpty then #[] else
  (match d.maxChars with
    | some m => if Jtex.utf16Len s > m then #[Issue.partTooLong d.id m false] else #[]
    | none => #[]) ++
  (match d.maxWords with
    | some w => if (s.splitOn " ").length > w then #[Issue.partTooLong d.id w true] else #[]
    | none => #[])

/-- The parts a template renders with, from the given ones, under the rendered options: each whose
condition holds, as one text or a list; the issues name a missing required one, an unknown one,
and one over its declared length, which is kept. -/
def parts (t : TemplateYml) (given : List (String × PartText)) (opts : List (String × Value)) :
    List (String × PartText) × Array Issue := Id.run do
  let live := t.parts.filter (conditionMet ·.condition opts)
  let mut out : Array Issue := #[]
  for d in live do
    if d.required && !(given.any (·.1 == d.id)) then out := out.push (.partMissing d.id)
  for (k, _) in given do
    unless live.any (·.id == k) do out := out.push (.partUnknown k)
  let mut res : Array (String × PartText) := #[]
  for d in live do
    if let some (_, p) := given.find? (·.1 == d.id) then
      let p := match d.asList, p with
        | true, .one s => PartText.many #[s]
        | false, .many xs => .one ("\n\n".intercalate xs.toList)
        | _, p => p
      let each := match p with
        | .one s => #[s]
        | .many xs => xs
      for s in each do
        out := out ++ tooLong d s
      res := res.push (d.id, p)
  return (res.toList, out)

/-- The required doc fields, under the rendered options, the front matter leaves unset. -/
def docIssues (t : TemplateYml) (frontmatter : List (String × Value)) (opts : List (String × Value)) :
    Array Issue :=
  (t.doc.filter fun d => conditionMet d.condition opts && d.required &&
    !(frontmatter.any fun (k, v) => k == d.id && defined v)).map (.docMissing ·.id)

/-- The letters indices take: A to Z, then AA to ZZ and on. -/
def letter (index : Nat) : String :=
  -- myst-templates' table reads Q U R S for Q R S T; this one does not, a departure at the 18th to 20th
  let alpha := "ABCDEFGHIJKLMNOPQRSTUVWXYZ".toList
  let c := alpha.getD (index % 26) 'A'
  String.ofList (List.replicate (index / 26 + 1) c)

private def textOf : Value → Option String
  | .str s => some s
  | .num n => some (toString n)
  | _ => none

/-- A text's pieces apart at any of `seps`, trimmed, the empty ones dropped. -/
private def splitAt (seps : List Char) (s : String) : List String :=
  ((s.split fun c => seps.contains c).toList.map fun t => t.toString.trimAscii.toString).filter (!·.isEmpty)

/-- A value as a list: a list itself, a text apart at `seps`, nothing for none, else alone. -/
private def listOf (seps : List Char) : Value → List Value
  | .arr xs => xs
  | .str s => (splitAt seps s).map Value.str
  | .undef | .null => []
  | v => [v]

/-- A date's day, month and year as myst-templates prints them from an ISO date, the year alone
the first of January as JavaScript reads it; none for a calendar date that does not exist. -/
def dateParts (s : String) : Option (String × String × String) :=
  let s := s.trimAscii.toString
  let body := ((s.splitOn "T").head?.getD s)
  let year (y : String) := y.length == 4 && y.all Char.isDigit
  let days (y m : Nat) : Nat :=
    if m == 2 then (if y % 4 == 0 && (y % 100 != 0 || y % 400 == 0) then 29 else 28)
    else if [4, 6, 9, 11].contains m then 30 else 31
  match body.splitOn "-" with
  | [y] => if year y then some ("1", "1", y) else none
  | [y, m] => m.toNat?.bind fun mn =>
    if year y && 1 ≤ mn && mn ≤ 12 then some ("1", toString mn, y) else none
  | [y, m, d] => match m.toNat?, d.toNat?, y.toNat? with
    | some mn, some dn, some yn =>
      if year y && 1 ≤ mn && mn ≤ 12 && 1 ≤ dn && dn ≤ days yn mn then
        some (toString dn, toString mn, y)
      else none
    | _, _, _ => none
  | _ => none

/-- Affiliations as myst-frontmatter stashes them, in the order first met: a declared one or an
author's by its `id` or `ref`, a name standing for the one of that id or a new one of that name,
an object without an id taking a generated one unless one of the same content stands. -/
structure Stash where
  items : Array (String × List (String × Value)) := #[]
  generated : Nat := 0

/-- An affiliation stashed, with the id it stands under. -/
def Stash.add (st : Stash) (v : Value) : Stash × Option String :=
  match v with
  | .str s =>
    if st.items.any (·.1 == s) then (st, some s)
    else ({ st with items := st.items.push (s, [("id", .str s), ("name", .str s)]) }, some s)
  | .obj fs =>
    let get (k : String) := (fs.find? (·.1 == k)).bind (textOf ·.2)
    let fs := fs.map fun (k, x) => (if k == "institution" && !fs.any (·.1 == "name") then "name" else k, x)
    match (get "id").orElse fun _ => get "ref" with
    | some id =>
      let fs := if fs.any (·.1 == "name") then fs else fs ++ [("name", .str id)]
      let fs := ("id", .str id) :: fs.filter fun (k, _) => k != "id" && k != "ref"
      if st.items.any (·.1 == id) then (st, some id) else ({ st with items := st.items.push (id, fs) }, some id)
    | none =>
      match st.items.find? (fun (_, g) => g.filter (·.1 != "id") == fs) with
      | some (id, _) => (st, some id)
      | none =>
        let id := s!"affiliations-generated-uid-{st.generated}"
        ({ items := st.items.push (id, ("id", .str id) :: fs), generated := st.generated + 1 }, some id)
  | _ => (st, none)

/-- An author's name as myst-frontmatter formats it: a text, or a mapping's `literal`, else its
given and family names apart by a space. -/
private def nameOf : Value → String
  | .str s => s
  | .obj fs =>
    let get (k : String) := ((fs.find? (·.1 == k)).bind (textOf ·.2)).getD ""
    if get "literal" != "" then get "literal" else
      " ".intercalate ([get "given", get "family"].filter (!·.isEmpty))
  | _ => ""

/-- A front matter as the `doc` a template reads, as extendFrontmatter makes it: its authors and
the affiliations they name indexed and lettered, the date's fields and a lone `.bib` as `bibtex`;
an undated document gets no date, never the clock's. -/
def extend (fm : List (String × Value)) : Value × Array Issue := Id.run do
  let fm := fm.map fun (k, v) => (((aliases.find? (·.1 == k)).map (·.2)).getD k, v)
  let get (k : String) : Value := ((fm.find? (·.1 == k)).map (·.2)).getD .undef
  let mut issues : Array Issue := #[]
  -- the declared affiliations first, then each author's, as myst-frontmatter stashes them
  let mut st : Stash := {}
  for a in listOf [';'] (get "affiliations") do
    st := (st.add a).1
  let mut authorsIn : Array (List (String × Value) × List String) := #[]
  for (au, k) in (listOf [';'] (get "authors")).zipIdx do
    let fs := match au with
      | .str s => [("name", Value.str s)]
      | .obj fs => fs
      | _ => []
    let mut ids : Array String := #[]
    for a in listOf [';'] (((fs.find? fun (k, _) => k == "affiliations" || k == "affiliation").map (·.2)).getD .undef) do
      let (st', id) := st.add a
      st := st'
      if let some id := id then ids := ids.push id
    let fs := fs.filter fun (k, _) => k != "affiliation"
    let fs := fs.map fun (key, x) => if key == "name" then (key, Value.str (nameOf x)) else (key, x)
    -- myst-frontmatter refuses a corresponding author without an email, setting it false
    let unmailed := (fs.find? (·.1 == "corresponding")).any (·.2.truthy) &&
      !(fs.any fun (key, x) => key == "email" && x.truthy)
    if unmailed then issues := issues.push (.frontInvalid s!"authors.{k}.corresponding" "an email beside it")
    let fs := if !unmailed then fs else
      fs.map fun (key, x) => if key == "corresponding" then (key, Value.bool false) else (key, x)
    authorsIn := authorsIn.push (fs, ids.toList)
  let mut named : Array String := #[]
  for (_, ids) in authorsIn do
    for id in ids do
      unless named.contains id do named := named.push id
  let collab (fs : List (String × Value)) : Bool :=
    (fs.find? (·.1 == "collaboration")).any (·.2.truthy)
  let indexed (pick : Bool) : Array (String × Value) := Id.run do
    let mut res : Array (String × Value) := #[]
    for id in named do
      if let some (_, fs) := st.items.find? (·.1 == id) then
        if collab fs == pick then
          let i := res.size
          res := res.push (id, .obj (fs ++ [("value", .obj fs), ("index", .num (i + 1)),
            ("letter", .str (letter i))]))
    return res
  let affs := indexed false
  let collabs := indexed true
  let mut corresponding : Nat := 0
  let mut authorValues : Array Value := #[]
  for ((au, ids), i) in authorsIn.zipIdx do
    let pickAll (from_ : Array (String × Value)) : Value :=
      match ids.filterMap fun id => (from_.find? (·.1 == id)).map (·.2) with
      | [] => .undef
      | xs => .arr xs
    let corr : Value := match (au.find? (·.1 == "corresponding")).map (·.2) with
      | some (Value.bool false) => .obj [("value", .bool false)]
      | some v => if v.truthy then
          .obj [("value", v), ("index", .num (corresponding + 1)), ("letter", .str (letter corresponding))]
        else .undef
      | none => .undef
    if (corr.get "index").truthy then corresponding := corresponding + 1
    let name := ((au.find? (·.1 == "name")).bind (textOf ·.2)).getD ""
    let words := name.splitOn " "
    let rest := au.filter fun (k, _) => !["affiliations", "corresponding"].contains k
    authorValues := authorValues.push (.obj (rest ++ [("index", .num (i + 1)), ("letter", .str (letter i)),
      ("corresponding", corr), ("affiliations", pickAll affs), ("collaborations", pickAll collabs),
      ("given_name", .str (words.headD "")), ("surname", .str (" ".intercalate words.tail))]))
  let date : Value ← match get "date" with
    | .undef | .null => issues := issues.push .undated; pure .undef
    | v => match (textOf v).bind dateParts with
      | some (d, m, y) => pure (.obj [("day", .str d), ("month", .str m), ("year", .str y)])
      | none => issues := issues.push (.dateUnread ((textOf v).getD "")); pure .undef
  let bib := listOf [','] (get "bibliography")
  let bibtex : Value := match bib with
    | [.str b] => if b.endsWith ".bib" then .str b else .undef
    | _ => .undef
  let own := fm.filter fun (k, _) =>
    !["date", "authors", "affiliations", "collaborations", "bibliography", "bibtex", "keywords"].contains k
  return (.obj (own ++ [("date", date), ("authors", .arr authorValues.toList),
    ("affiliations", .arr (affs.toList.map (·.2))), ("collaborations", .arr (collabs.toList.map (·.2))),
    ("keywords", match get "keywords" with
      | .undef => .undef
      | v => .arr (listOf [',', ';'] v)),
    ("bibliography", if bib.isEmpty then .undef else .arr bib), ("bibtex", bibtex)]), issues)

end LeanTex.Core.MystTemplate
