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

/-- The front matter keys a template reads: those its source names under `doc.` or as a part, and
the ones extendFrontmatter reads to make its doc. -/
def keysRead (tex : String) : List String :=
  let named := ((tex.splitOn "doc.").drop 1).map fun t => (t.takeWhile fun c => c.isAlphanum || c == '_').toString
  let parts := ((tex.splitOn "parts.").drop 1).map fun t => (t.takeWhile fun c => c.isAlphanum || c == '_').toString
  named ++ parts ++ ["title", "authors", "author", "affiliations", "affiliation", "date", "keywords",
    "bibliography", "exports", "export", "parts"] ++ aliases.map (·.1)

/-- The template keys a document gives with no template declared to read them, each named. -/
def unreadDiags (file : String) (fields : Array MetaField) : Array Diag :=
  fields.filterMap fun f => if !Md.templateKeys.contains f.key then none else
    some (Diag.of .W0307 (Diag.say .W0307 .key f.key) (some ⟨file, f.pos⟩) none
      (detail := some "no template a pdf or tex export declares reads it") (subject := some ("md:meta:" ++ f.key)))

/-- A declared template set aside, the document set as itself, with why. -/
def lossDiag (file : String) (d : Declared) (why : String) : Diag :=
  Diag.of .W0392 (Diag.say .W0392 .directory (some (Diag.Name.of d.path))) (some ⟨file, d.pos⟩) none
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
    let d := d.map fun x => { x with span := x.span.map fun sp =>
      { sp with pos := { sp.pos with line := sp.pos.line + line } } }
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

/-- An issue as the diagnostic naming its loss, each its own noun and name so none hides another. -/
def issueDiag (file : String) (pos : Pos) : Issue → Diag
  | .malformed path what => loss .key path s!"template:{path}" s!"its template.yml wants {what} at {path}"
  | .optionMissing id => loss .option id s!"template:option:{id}" s!"the template's required option '{id}' is not given"
  | .optionUnknown id => loss .option id s!"template:option:{id}" s!"the template declares no option '{id}'"
  | .optionInvalid id what => loss .option id s!"template:option:{id}" s!"the option '{id}' is not {what}"
  | .partMissing id => loss .key id s!"template:part:{id}" s!"the template's required part '{id}' is not given"
  | .partUnknown id => loss .key id s!"template:part:{id}" s!"the template declares no part '{id}'"
  | .partTooLong id n words => loss .key id s!"template:part:{id}"
      s!"the part '{id}' runs over its {n} {if words then "words" else "characters"}"
  | .docMissing id => loss .key id s!"template:doc:{id}" s!"the template's required field '{id}' is not given"
  | .frontInvalid path what => loss .key path s!"template:front:{path}" s!"the front matter's {path} wants {what}"
  | .undated => loss .key "date" "template:date" "the document gives no date, so the template sets none"
  | .dateUnread v => loss .key "date" "template:date" s!"the date '{v}' is not one a template reads"
where
  loss (noun : Diag.Noun) (name subject what : String) : Diag :=
    Diag.of .W0392 (Diag.say .W0392 noun (some (Diag.Name.of name))) (some ⟨file, pos⟩) none
      (detail := some what) (subject := some ("md:" ++ subject))

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
      if pd.asList then
        texts := texts ++ (ss.zipIdx.map fun (s, k) => (s!"{pd.id}.{k}", s))
        partsGiven := partsGiven ++ [(pd.id, PartText.many ss.toArray)]
      else
        texts := texts ++ [(pd.id, "\n\n".intercalate ss)]
        partsGiven := partsGiven ++ [(pd.id, PartText.one ("\n\n".intercalate ss))]
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

/-- The bibliography commands a template sets its own list with, which the document's own list
stands in place of. -/
def bibliographyCtrls : List String := ["bibliography", "bibliographystyle", "printbibliography"]

/-- A template document's top-level raws with its body read as the template file's and its own
bibliography set aside, a `\graphicspath` after its class line resolving its images beside the
document and then in `dir`; whether it set a bibliography aside. -/
def placed (tplFile dir : String) (raws : Array Parse.Raw) : Array Parse.Raw × Bool := Id.run do
  let mut out : Array Parse.Raw := #[]
  let mut dropped := false
  for r in raws do
    match r with
    | .env "document" b p =>
      let mut body : Array Parse.Raw := #[]
      let mut skip := false
      for x in b do
        if skip then
          skip := false
          if x matches .group _ _ then continue
        match x with
        | .ctrl n _ =>
          if bibliographyCtrls.contains n then
            dropped := true
            skip := n != "printbibliography"
          else body := body.push x
        | _ => body := body.push x
      out := out.push (.env "document" #[.env (Parse.inputEnv tplFile) body p] p)
    | _ => out := out.push r
  -- graphicx reads the last \graphicspath, so the template's own, set after this one, still wins
  let gp : Array Parse.Raw := #[.ctrl "graphicspath" {}, .group #[.group #[.word "./" {}] {},
    .group #[.word (dir ++ "/") {}] {}] {}]
  let k := (out.findIdx? fun x => x matches .ctrl "documentclass" _).getD 0
  -- past the class line's optional run and its argument
  let mut j := k + 1
  let mut inOpt := false
  for _ in [k + 1:out.size] do
    match out[j]? with
    | some (.sym '[' _) => inOpt := true; j := j + 1
    | some (.sym ']' _) => inOpt := false; j := j + 1
    | some (.group _ _) =>
      j := j + 1
      unless inOpt do break
    | some _ => j := j + 1
    | none => break
  -- the preamble after the class line reads as the template file's, as its body does
  let docAt := (out.findIdx? fun x => x matches .env "document" _ _).getD out.size
  let pre := gp.append (out.extract j docAt)
  return ((out.extract 0 j).push (.env (Parse.inputEnv tplFile) pre {}) ++ out.extract docAt out.size, dropped)

/-- A markdown document set through its template: the template's raws, the splices' raws by name,
and what the template's reading names; none where the template does not render, with why. -/
def render (file tplFile dir : String) (yml tex : String) (fields : Array MetaField) (d : Declared)
    (body : Array Parse.Raw) : Except String (Array Parse.Raw × List (String × Array Parse.Raw)) × Array Diag :=
  let ymlTree := Md.yamlTree ((yml.splitOn "\n").toArray)
  match ymlTree with
  | none => (.error "its template.yml is outside the YAML the reader reads", #[])
  | some y =>
    let (tpl, ri) := read y
    let (ctx, texts, ci) := context tpl fields d
    -- the undated loss is the template's only where it reads the date
    let ci := if (tex.splitOn "doc.date").length > 1 then ci else ci.filter (· != .undated)
    let ds := (ri ++ ci).map (issueDiag file d.pos)
    match Jtex.render tex ctx with
    | .error e => (.error s!"its template.tex does not render: {e}", ds)
    | .ok pieces =>
      let (toks, lexDs) := tokens tplFile pieces
      let (raws, parseDs) := Surface.texParse tplFile toks
      let (raws, dropped) := placed tplFile dir raws
      let bibDs := if !dropped then #[] else
        #[Diag.of .W0392 (Diag.say .W0392 .bibliography none) (some ⟨file, d.pos⟩) none
          (detail := some "the template's own list set aside for the document's") (subject := some "md:template:bibliography")]
      let read := texts.map fun (id, s) => (id, Surface.fragment .markdown file s d.pos (cites := true))
      let parts := read.map fun (id, (rs, _)) => (id, rs)
      let partDs := read.foldl (init := #[]) fun acc (_, (_, ds)) => acc ++ ds
      let kept := #[Parse.Raw.env (Parse.keptInputEnv file) body d.pos]
      (.ok (raws, ("CONTENT", kept) :: ("IMPORTS", #[]) :: parts), ds ++ lexDs ++ parseDs ++ bibDs ++ partDs)

end LeanTex.Core.MystRender
