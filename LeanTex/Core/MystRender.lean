module

public import LeanTex.Core.MystTemplate
public import LeanTex.Core.MdDesugar
public import LeanTex.Core.Surface

public section

namespace LeanTex.Core.MystRender

/-! A markdown document set through the MyST template its front matter declares: the template's
jtex source rendered over the document's front matter, its own text lexed as TeX, and the body and
parts spliced in as the raws the markdown reader gives them, never as TeX text. -/

open LeanTex.Core.Jtex (Value Piece)
open LeanTex.Core.MystTemplate
open LeanTex.Core.Md (MetaField MetaValue Yaml)

/-- A front matter field's value as a template reads it. -/
def valueOfMeta : MetaValue → Option Value
  | .scalar s => some (valueOf (.scalar s))
  | .list items => some (.arr (items.toList.map Value.str))
  | .tree y => some (valueOf y)
  | .unread => none

/-- A markdown document's template declaration: the path its export names, where, and the export's
options. -/
structure Declared where
  path : String
  pos : Pos
  options : List (String × Value)

/-- The first export of a pdf or tex format that names a template, from the front matter's
`exports` list or its lone `export`. -/
def declared (fields : Array MetaField) : Option Declared := Id.run do
  for f in fields do
    unless f.key == "exports" || f.key == "export" do continue
    let entries : List Value := match valueOfMeta f.value with
      | some (.arr xs) => xs
      | some (.obj fs) => [.obj fs]
      | _ => []
    for e in entries do
      match e with
      | .obj fs =>
        let fmt : Value := ((fs.find? (·.1 == "format")).map (·.2)).getD (.str "pdf")
        let tpl : Option Value := (fs.find? (·.1 == "template")).map (·.2)
        if let (Value.str fm, some (Value.str path)) := (fmt, tpl) then
          if fm == "pdf" || fm == "tex" then
            return some
              { path := path, pos := f.pos, options := fs.filter fun (k, _) => !reservedKeys.contains k }
      | _ => pure ()
  return none

/-- The template keys a document gives with no template declared to read them, each named. -/
def unreadDiags (file : String) (fields : Array MetaField) : Array Diag :=
  fields.filterMap fun f => if !Md.templateKeys.contains f.key then none else
    some (Diag.of .W0307 (Diag.say .W0307 .key f.key) (some ⟨file, f.pos⟩) none
      (detail := some "no template a pdf or tex export declares reads it") (subject := some ("md:meta:" ++ f.key)))

/-- A declared template set aside, the document set as itself, with why. -/
def lossDiag (file : String) (d : Declared) (why : String) : Diag :=
  Diag.of .W0392 (Diag.say .W0392 .key "exports") (some ⟨file, d.pos⟩) none
    (detail := some s!"{why}; the document sets without its template") (subject := some "md:template")

/-- Where a declared template stands under the document's directory: a relative path inside its
tree, a bare name under `templates/`; the reason where it is a URL or leaves the tree. -/
def resolve (path : String) : Except String String :=
  if (path.splitOn "://").length > 1 then .error "a remote template, which is never fetched"
  else if path.startsWith "/" then .error "a template outside the document's tree"
  else if (path.splitOn "/").any (· == "..") then .error "a template outside the document's tree"
  else if !(path.splitOn "/").any (·.startsWith ".") && (path.splitOn "/").length == 1 then
    .ok ("templates/" ++ path)
  else .ok path

/-- The engine name of a splice request: a word no source spells, since it holds a space. -/
def spliceName (name : String) : String := "template splice " ++ name

/-- The splice a request names, if it names one. -/
def spliceOf? (name : String) : Option String :=
  if name.startsWith "template splice " then some (name.drop 16).copy else none

/-- A token stream's positions moved down `lines` lines, as a run lexed apart from what precedes it
stands in its file. -/
private def shifted (lines : Nat) (toks : Array Lex.Token) : Array Lex.Token :=
  toks.map fun t => { t with pos := { t.pos with line := t.pos.line + lines } }

/-- The pieces as TeX tokens: each run of the template's text and its escaped values lexed, each
splice a `\markdownInput` of its engine name, which the input reader answers with its raws. -/
def tokens (file : String) (pieces : Array Piece) : Array Lex.Token × Array Diag := Id.run do
  let mut out : Array Lex.Token := #[]
  let mut ds : Array Diag := #[]
  let mut run := ""
  let mut line := 0
  let flush (run : String) (line : Nat) (out : Array Lex.Token) (ds : Array Diag) :
      Array Lex.Token × Array Diag × Nat :=
    let (toks, d) := Surface.texLex file run
    (out ++ shifted line toks, ds ++ d, line + (run.splitOn "\n").length - 1)
  for p in pieces do
    match p with
    | .text s => run := run ++ s
    | .value s => run := run ++ Jtex.escapeTex s
    | .splice n =>
      let (o, d, l) := flush run line out ds
      out := o; ds := d; line := l; run := ""
      let q : Pos := { line := line + 1 }
      out := out ++ #[{ tok := .ctrl "markdownInput", pos := q }, { tok := .lbrace, pos := q },
        { tok := .word (spliceName n), pos := q }, { tok := .rbrace, pos := q }]
  let (o, d, _) := flush run line out ds
  return (o, d)

/-- An issue as the diagnostic naming its loss. -/
def issueDiag (file : String) (pos : Pos) : Issue → Diag
  | .malformed path what => loss s!"template:{path}" s!"its template.yml wants {what} at {path}"
  | .optionMissing id => loss s!"template:option:{id}" s!"the template's required option '{id}' is not given"
  | .optionUnknown id => loss s!"template:option:{id}" s!"the template declares no option '{id}'"
  | .optionInvalid id what => loss s!"template:option:{id}" s!"the option '{id}' is not {what}"
  | .partMissing id => loss s!"template:part:{id}" s!"the template's required part '{id}' is not given"
  | .partUnknown id => loss s!"template:part:{id}" s!"the template declares no part '{id}'"
  | .partTooLong id n words => loss s!"template:part:{id}"
      s!"the part '{id}' runs over its {n} {if words then "words" else "characters"}"
  | .docMissing id => loss s!"template:doc:{id}" s!"the template's required field '{id}' is not given"
  | .frontInvalid path what => loss s!"template:front:{path}" s!"the front matter's {path} wants {what}"
  | .undated => loss "template:date" "the document gives no date, so the template sets none"
  | .dateUnread s => loss "template:date" s!"the date '{s}' is not one a template reads"
where
  loss (subject what : String) : Diag :=
    Diag.of .W0392 (Diag.say .W0392 .key "exports") (some ⟨file, pos⟩) none (detail := some what)
      (subject := some ("md:" ++ subject))

/-- What a template renders over: the front matter as `doc` (its bibliography left to the body's own
list), the export's options, each part the template declares and the front matter gives as a typed
splice, and CONTENT and IMPORTS splices; with the parts' texts. -/
def context (tpl : TemplateYml) (fields : Array MetaField) (d : Declared) :
    Value × List (String × String) × Array Issue := Id.run do
  let front : List (String × Value) := fields.toList.filterMap fun f =>
    if f.key == "exports" || f.key == "export" then none else (valueOfMeta f.value).map (f.key, ·)
  let given := ((front.find? (·.1 == "parts")).map (·.2)).getD (.obj [])
  let mut texts : List (String × String) := []
  let mut partsGiven : List (String × PartText) := []
  for pd in tpl.parts do
    let v : Value := if !(given.get pd.id matches .undef) then given.get pd.id else
      ((front.find? fun (p : String × Value) => p.1 == pd.id).map (·.2)).getD Value.undef
    match v with
    | .str s =>
      texts := texts ++ [(pd.id, s)]
      partsGiven := partsGiven ++ [(pd.id, PartText.one s)]
    | .arr xs =>
      let ss := xs.filterMap fun (x : Value) => if let .str s := x then some s else none
      texts := texts ++ (ss.zipIdx.map fun (s, k) => (s!"{pd.id}.{k}", s))
      partsGiven := partsGiven ++ [(pd.id, PartText.many ss.toArray)]
    | _ => pure ()
  let (opts, oi) := options tpl d.options
  let (parts, pi) := MystTemplate.parts tpl partsGiven opts
  let (doc, di) := extend (front.filter fun (k, _) => k != "parts")
  let doc := if let .obj fs := doc then Value.obj (fs.map fun ((k, v) : String × Value) =>
      if k == "bibliography" || k == "bibtex" then (k, Value.undef) else (k, v)) else doc
  let partValues := parts.map fun (id, p) => match p with
    | .one _ => (id, Value.splice id)
    | .many xs => (id, .arr ((List.range xs.size).map fun k => .splice s!"{id}.{k}"))
  let ctx : Value := .obj [("doc", doc), ("options", .obj opts), ("parts", .obj partValues),
    ("CONTENT", .splice "CONTENT"), ("IMPORTS", .splice "IMPORTS")]
  return (ctx, texts, oi ++ pi ++ docIssues tpl front opts ++ di)

/-- A markdown document set through its template: the template's raws, the splices' raws by name,
and what the template's reading names; none where the template does not render, with why. -/
def render (file tplFile : String) (yml tex : String) (fields : Array MetaField) (d : Declared)
    (body : Array Parse.Raw) : Except String (Array Parse.Raw × List (String × Array Parse.Raw)) × Array Diag :=
  let ymlTree := Md.yamlTree ((yml.splitOn "\n").toArray)
  match ymlTree with
  | none => (.error "its template.yml is outside the YAML the reader reads", #[])
  | some y =>
    let (tpl, ri) := read y
    let (ctx, texts, ci) := context tpl fields d
    let ds := (ri ++ ci).map (issueDiag file d.pos)
    match Jtex.render tex ctx with
    | .error e => (.error s!"its template.tex does not render: {e}", ds)
    | .ok pieces =>
      let (toks, lexDs) := tokens tplFile pieces
      let (raws, parseDs) := Surface.texParse tplFile toks
      let parts := texts.map fun (id, s) => (id, (Surface.read .markdown file s).1)
      (.ok (raws, ("CONTENT", body) :: ("IMPORTS", #[]) :: parts), ds ++ lexDs ++ parseDs)

end LeanTex.Core.MystRender
