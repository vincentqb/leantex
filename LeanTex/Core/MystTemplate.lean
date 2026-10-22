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
  | undated
  | dateUnread (spelling : String)
  deriving Repr, BEq, Inhabited

/-- The export keys myst reserves beside a template's options. -/
def reservedKeys : List String :=
  ["id", "format", "template", "output", "zip", "toc", "articles", "sub_articles", "renderer"]

/-- The page front matter keys a doc field may name. -/
def frontmatterKeys : List String :=
  ["title", "subtitle", "short_title", "description", "authors", "contributors", "affiliations",
   "date", "doi", "arxiv", "open_access", "license", "github", "binder", "source", "subject",
   "venue", "volume", "issue", "keywords", "first_page", "last_page", "bibliography", "math",
   "abbreviations", "numbering", "funding", "copyright", "references", "thumbnail", "banner",
   "tags", "parts", "label", "site", "exports", "downloads", "settings", "enumerator", "kernelspec",
   "jupytext", "options", "id", "identifiers", "edit_url", "requirements", "resources", "keypoints"]

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
    | some m => if s.length ≤ m then .ok (.str s) else .error s!"at most {m} characters"
    | none => .ok (.str s)
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

/-- A value as `d` takes it, a list item by item where it takes several, a lone value a list of one. -/
def checkOption (d : OptionDef) (v : Value) : Except String Value :=
  if !d.multiple then checkValue d v else
  match v with
  | .arr xs => (xs.mapM (checkValue d)).map .arr
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
      match (y.get? "default").map valueOf with
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
  if (y.get? "myst").isNone && (y.get? "jtex").isNone then
    out := out.push (.malformed "myst" "the jtex version the template declares")
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
    bibliography := ((y.get? "style").bind (·.get? "bibliography")).bind (·.text?) }
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
  let mut res : List (String × Value) := []
  for d in live do
    let v := (given.find? (·.1 == d.id)).map (·.2) |>.filter defined
    -- myst-templates fills a default only where it is truthy, so a false or empty default stays unset
    match v.orElse fun _ => d.default.filter (·.truthy) with
    | none => pure ()
    | some v => match checkOption d v with
      | .ok v => res := res ++ [(d.id, v)]
      | .error e => out := out.push (.optionInvalid d.id e)
  return (res, out)

/-- A part's given text: one block, or a list of them where the part is read as a list. -/
inductive PartText where
  | one (s : String)
  | many (items : Array String)
  deriving Repr, BEq, Inhabited

/-- Whether one text of part `d` exceeds its declared length, in UTF-16 units as JavaScript counts
or in words split at single spaces as myst-templates splits them. -/
def tooLong (d : PartDef) (s : String) : Option Issue :=
  match d.maxChars, d.maxWords with
  | some m, _ => if Jtex.utf16Len s > m then some (.partTooLong d.id m false) else
      d.maxWords.bind fun w => if (s.splitOn " ").length > w then some (.partTooLong d.id w true) else none
  | none, some w => if (s.splitOn " ").length > w then some (.partTooLong d.id w true) else none
  | none, none => none

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
  let mut res : List (String × PartText) := []
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
        if let some i := tooLong d s then out := out.push i
      res := res ++ [(d.id, p)]
  return (res, out)

/-- The required doc fields, under the rendered options, the front matter leaves unset. -/
def docIssues (t : TemplateYml) (frontmatter : List (String × Value)) (opts : List (String × Value)) :
    Array Issue :=
  (t.doc.filter fun d => conditionMet d.condition opts && d.required &&
    !(frontmatter.any fun (k, v) => k == d.id && defined v)).map (.docMissing ·.id)

/-- The letters indices take: A to Z, then AA to ZZ and on. -/
def letter (index : Nat) : String :=
  -- myst-templates' table repeats U for T; this one does not, a departure from the 20th on
  let alpha := "ABCDEFGHIJKLMNOPQRSTUVWXYZ".toList
  let c := alpha.getD (index % 26) 'A'
  String.ofList (List.replicate (index / 26 + 1) c)

private def fieldsOf : Value → List (String × Value)
  | .obj fs => fs
  | _ => []

private def textOf : Value → Option String
  | .str s => some s
  | .num n => some (toString n)
  | _ => none

/-- A date's day, month and year as myst-templates prints them from an ISO date, the year alone
the first of January as JavaScript reads it. -/
def dateParts (s : String) : Option (String × String × String) :=
  let s := s.trimAscii.toString
  let body := ((s.splitOn "T").head?.getD s)
  match body.splitOn "-" with
  | [y] => if y.length == 4 && y.all Char.isDigit then some ("1", "1", y) else none
  | [y, m] => m.toNat?.bind fun mn =>
    if y.length == 4 && y.all Char.isDigit && 1 ≤ mn && mn ≤ 12 then some ("1", toString mn, y) else none
  | [y, m, d] => match m.toNat?, d.toNat? with
    | some mn, some dn =>
      if y.length == 4 && y.all Char.isDigit && 1 ≤ mn && mn ≤ 12 && 1 ≤ dn && dn ≤ 31 then
        some (toString dn, toString mn, y)
      else none
    | _, _ => none
  | _ => none

/-- One affiliation as myst normalizes it: a mapping keeps its fields with its id or its name as
id, a bare name is its own id and name. -/
def affiliationOf : Value → Option (String × List (String × Value))
  | .str s => some (s, [("id", .str s), ("name", .str s)])
  | .obj fs =>
    (((fs.find? (·.1 == "id")).bind (textOf ·.2)).orElse fun _ =>
        (fs.find? (·.1 == "name")).bind (textOf ·.2)).map fun id =>
      (id, if fs.any (·.1 == "id") then fs else ("id", .str id) :: fs)
  | _ => none

/-- One author as myst normalizes it: a bare name its `name`, an affiliation or a list of them its
`affiliations` by id. -/
def authorOf (v : Value) : List (String × Value) :=
  let fs := match v with
    | .str s => [("name", Value.str s)]
    | .obj fs => fs
    | _ => []
  fs.map fun (k, x) =>
    if k == "affiliations" || k == "affiliation" then
      let xs : List Value := match x with
        | .arr xs => xs
        | x => [x]
      ("affiliations", Value.arr (xs.filterMap fun a => (affiliationOf a).map fun (id, _) => Value.str id))
    else (k, x)

/-- A front matter as the `doc` a template reads, as extendFrontmatter makes it: its authors and
the affiliations they name indexed and lettered, the date's fields and a lone `.bib` as `bibtex`;
an undated document gets no date, never the clock's. -/
def extend (fm : List (String × Value)) : Value × Array Issue := Id.run do
  let get (k : String) : Value := ((fm.find? (·.1 == k)).map (·.2)).getD .null
  let authorsIn : List Value := match get "authors", get "author" with
    | .arr xs, _ => xs
    | .null, .arr xs => xs
    | .null, .null => []
    | .null, x => [x]
    | x, _ => [x]
  let authors := authorsIn.map authorOf
  -- every affiliation declared, then each an author names that none declares
  let mut declared : List (String × List (String × Value)) := []
  for a in (match get "affiliations" with
      | .arr xs => xs
      | .null => []
      | x => [x]) do
    if let some p := affiliationOf a then declared := declared ++ [p]
  for au in authorsIn do
    for x in (match (fieldsOf (match au with | .obj _ => au | _ => .null)).find? (fun f => f.1 == "affiliations" || f.1 == "affiliation") with
        | some (_, .arr xs) => xs
        | some (_, x) => [x]
        | none => []) do
      if let some (id, fs) := affiliationOf x then
        unless declared.any (·.1 == id) do declared := declared ++ [(id, fs)]
  let mut named : List String := []
  for au in authors do
    for x in (match (au.find? (·.1 == "affiliations")).map (·.2) with
        | some (.arr xs) => xs
        | _ => []) do
      if let some id := textOf x then
        unless named.contains id do named := named ++ [id]
  let collab (fs : List (String × Value)) : Bool :=
    (fs.find? (·.1 == "collaboration")).any (·.2.truthy)
  let indexed (pick : Bool) : List (String × Value) := Id.run do
    let mut res : List (String × Value) := []
    for id in named do
      if let some (_, fs) := declared.find? (·.1 == id) then
        if collab fs == pick then
          let i := res.length
          res := res ++ [(id, .obj (fs ++ [("value", .obj fs), ("index", .num (i + 1)),
            ("letter", .str (letter i))]))]
    return res
  let affs := indexed false
  let collabs := indexed true
  let mut corresponding : Nat := 0
  let mut authorValues : List Value := []
  for (au, i) in authors.zipIdx do
    let ids := match (au.find? (·.1 == "affiliations")).map (·.2) with
      | some (.arr xs) => xs.filterMap textOf
      | _ => []
    let pickAll (from_ : List (String × Value)) : Value :=
      match ids.filterMap fun id => (from_.find? (·.1 == id)).map (·.2) with
      | [] => .null
      | xs => .arr xs
    let corr : Value := match (au.find? (·.1 == "corresponding")).map (·.2) with
      | some (Value.bool false) => .obj [("value", .bool false)]
      | some v => if v.truthy then
          .obj [("value", v), ("index", .num (corresponding + 1)), ("letter", .str (letter corresponding))]
        else .null
      | none => .null
    if (corr.get "index").truthy then corresponding := corresponding + 1
    let name := ((au.find? (·.1 == "name")).bind (textOf ·.2)).getD ""
    let words := name.splitOn " "
    let rest := au.filter fun (k, _) => !["affiliations", "corresponding"].contains k
    authorValues := authorValues ++ [.obj (rest ++ [("index", .num (i + 1)), ("letter", .str (letter i)),
      ("corresponding", corr), ("affiliations", pickAll affs), ("collaborations", pickAll collabs),
      ("given_name", .str (words.headD "")), ("surname", .str (" ".intercalate words.tail))])]
  let mut issues : Array Issue := #[]
  let date : Value ← match get "date" with
    | .null => issues := issues.push .undated; pure .null
    | v => match (textOf v).bind dateParts with
      | some (d, m, y) => pure (.obj [("day", .str d), ("month", .str m), ("year", .str y)])
      | none => issues := issues.push (.dateUnread ((textOf v).getD "")); pure .null
  let bib : List Value := match get "bibliography" with
    | .arr xs => xs
    | .null => []
    | x => [x]
  let bibtex : Value := match bib with
    | [.str b] => if b.endsWith ".bib" then .str b else .null
    | _ => .null
  let own := fm.filter fun (k, _) =>
    !["date", "authors", "author", "affiliations", "collaborations", "bibliography", "bibtex"].contains k
  return (.obj (own ++ [("date", date), ("authors", .arr authorValues),
    ("affiliations", .arr (affs.map (·.2))), ("collaborations", .arr (collabs.map (·.2))),
    ("bibliography", if bib.isEmpty then .null else .arr bib), ("bibtex", bibtex)]), issues)

end LeanTex.Core.MystTemplate
