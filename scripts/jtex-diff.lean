/-
The jtex renderer against nunjucks under jtex's configuration, over each MyST template.tex in a
templates directory and contexts derived from the paths and literals it reads.
Usage: lake build LeanTex.Core.Jtex && lake env lean --run scripts/jtex-diff.lean --nunjucks DIR --templates DIR [--node NODE] | --selftest
-/
import LeanTex.Core.Jtex
import Lean.Data.Json

open LeanTex.Core.Jtex
open Lean (Json)

def die (msg : String) : IO α := do
  IO.eprintln s!"jtex-diff: {msg}"
  IO.Process.exit 2

/-- The constant bridge program: nunjucks configured as jtex configures it renders each case of
the batch, answering its text or its error. -/
def bridge : String := r#"const nunjucks = require(process.argv[2]);
const fs = require('fs');
const env = new nunjucks.Environment(null, {
  trimBlocks: true, autoescape: false,
  tags: { blockStart: '[#', blockEnd: '#]', variableStart: '[-', variableEnd: '-]',
    commentStart: '%#', commentEnd: '#%' },
}).addFilter('len', (a) => a.length);
const batch = JSON.parse(fs.readFileSync(process.argv[3], 'utf8'));
const out = batch.map((c) => {
  try { return { text: env.renderString(c.template, c.context) }; }
  catch (e) { return { error: String(e.message || e) }; }
});
process.stdout.write(JSON.stringify(out));
"#

/-- A value as the JSON nunjucks reads. -/
def toJson : Value → Json
  | .null => .null
  | .bool b => .bool b
  | .num n => .num (Lean.JsonNumber.fromInt n)
  | .str s => .str s
  | .arr items => .arr (items.attach.map fun ⟨v, _⟩ => toJson v).toArray
  | .obj fs => Json.mkObj (fs.attach.map fun ⟨p, _⟩ => (p.1, toJson p.2))
decreasing_by
  all_goals
    rename_i h
    have := List.sizeOf_lt_of_mem h
    try cases p
    simp_all
    omega

/-- The dotted paths a template reads under `root`, each with the string literals compared to it. -/
def pathsUnder (root : String) (src : String) : List (String × List String) := Id.run do
  let cs := src.toList.toArray
  let mut out : List (String × List String) := []
  let mut i := 0
  let word (c : Char) := c.isAlphanum || c == '_'
  while i < cs.size do
    let pre := root.toList
    if (i == 0 || !(cs[i - 1]?.any fun c => word c || c == '.')) &&
        (List.range pre.length).all (fun k => cs[i + k]? == pre[k]?) && cs[i + pre.length]? == some '.' then
      let mut j := i + pre.length + 1
      let mut name := ""
      while j < cs.size && (cs[j]?.any word) do
        name := name.push (cs[j]?.getD ' ')
        j := j + 1
      let rest := (String.ofList (cs.extract j (j + 40)).toList).trimAscii.toString
      let lit :=
        if rest.startsWith "==" || rest.startsWith "!=" then
          let r := (rest.drop 2).toString.trimAscii.toString
          match r.toList with
          | q :: tl => if q == '"' || q == '\'' then [String.ofList (tl.takeWhile (· != q))] else []
          | [] => []
        else []
      if !name.isEmpty then
        out := match out.find? (·.1 == name) with
          | some _ => out.map fun (n, ls) => if n == name then (n, ls ++ lit.filter (!ls.contains ·)) else (n, ls)
          | none => out ++ [(name, lit)]
      i := j
    else i := i + 1
  return out

/-- An invented author, `k` of the document's. -/
def author (k : Nat) (corresponding : Bool) : Value :=
  let names := #[("Kilo", "Lima"), ("Mike", "Oscar"), ("Papa", "Quebec")]
  let (g, s) := names.getD k ("Romeo", "Sierra")
  .obj [("name", .str s!"{g} {s}"), ("given_name", .str g), ("surname", .str s),
    ("email", .str s!"{g.toLower}@example.org"), ("orcid", .str "0000-0000-0000-0000"),
    ("corresponding", .bool corresponding), ("roles", .arr [.str "Writing"]),
    ("index", .num (k + 1)),
    ("affiliations", .arr [.obj [("value", .obj [("name", .str s!"Institute {k + 1}")]),
      ("index", .num (k % 2 + 1))]])]

/-- The invented document: bare, of one author, or rich. -/
def doc (kind : Nat) : Value :=
  if kind == 0 then .obj [("title", .str "A Bare Title"), ("authors", .arr [])] else
  if kind == 1 then .obj [("title", .str "A Single Title"), ("authors", .arr [author 0 false]),
    ("date", .obj [("year", .str "2001")]), ("keywords", .arr [])] else
  .obj [("title", .str "An Invented Title"), ("short_title", .str "Invented"),
    ("subtitle", .str "Of Placeholder Words"), ("description", .str "A description."),
    ("authors", .arr [author 0 true, author 1 false, author 2 false]),
    ("affiliations", .arr <| [1, 2].map fun (i : Nat) =>
      .obj [("value", .obj [("name", .str s!"Institute {i}"), ("department", .str "Department"),
        ("institution", .str s!"Institute {i}"), ("city", .str "Town"), ("country", .str "Land")]),
        ("index", .num i)]),
    ("date", .obj [("day", .str "3"), ("month", .str "4"), ("year", .str "2001")]),
    ("keywords", .arr [.str "alpha", .str "bravo"]),
    ("bibliography", .arr [.str "main.bib"])]

/-- The contexts one template is judged over: its options absent, all true, and each compared option
at each of its literals with the rest true, over the bare document without parts, the one-author
document with its parts as text, and the rich document with its parts as lists. -/
def contexts (src : String) : List Value :=
  let opts := pathsUnder "options" src
  let parts := pathsUnder "parts" src
  let optSets : List (List (String × Value)) :=
    [[], opts.map fun (n, _) => (n, .bool true)] ++
      ((opts.map (·.2.length)).foldl max 0 |> List.range).map fun k =>
        opts.map fun (n, ls) => (n, match ls[k]? with
          | some l => .str l
          | none => .bool true)
  let partSet (kind : Nat) : List (String × Value) := if kind == 0 then [] else
    parts.map fun (n, _) => (n, if kind == 1 then Value.str s!"The {n} part."
      else .arr [.str s!"One {n}.", .str s!"Two {n}."])
  optSets.flatMap fun os => [0, 1, 2].map fun kind =>
    .obj [("doc", doc kind), ("options", .obj os), ("parts", .obj (partSet kind)),
      ("CONTENT", .str "⟦CONTENT⟧"), ("IMPORTS", .str "⟦IMPORTS⟧")]

/-- The first line two texts differ at, with both lines. -/
def firstDiff (a b : String) : Option (Nat × String × String) :=
  let as := a.splitOn "\n"
  let bs := b.splitOn "\n"
  ((List.range (max as.length bs.length)).find? fun k => as[k]? != bs[k]?).map fun k =>
    (k + 1, as[k]?.getD "⟨end⟩", bs[k]?.getD "⟨end⟩")

def selftest : IO UInt32 := do
  let src := "[#- if options.style == \"two\" #]x[# endif #][- parts.abstract -][- options.flag -]"
  let ok := pathsUnder "options" src == [("style", ["two"]), ("flag", [])] &&
    pathsUnder "parts" src == [("abstract", [])] && (contexts src).length == 9 &&
    firstDiff "a\nb" "a\nc" == some (2, "b", "c") && firstDiff "a" "a" == none
  IO.println (if ok then "jtex-diff: selftest ok" else "jtex-diff: selftest FAILED")
  return if ok then 0 else 1

def main (args : List String) : IO UInt32 := do
  if args == ["--selftest"] then return ← selftest
  let rec parse : List String → Option String × Option String × String → Except String (Option String × Option String × String)
    | [], o => .ok o
    | "--nunjucks" :: d :: rest, (_, t, n) => parse rest (some d, t, n)
    | "--templates" :: d :: rest, (j, _, n) => parse rest (j, some d, n)
    | "--node" :: n :: rest, (j, t, _) => parse rest (j, t, n)
    | a :: _, _ => .error s!"an unknown argument '{a}'"
  let (nj, dir, node) ← match parse args (none, none, "node") with
    | .ok (some nj, some dir, node) => pure (nj, dir, node)
    | .ok _ => die "pass --nunjucks DIR and --templates DIR"
    | .error e => die e
  let mut files : Array System.FilePath := #[]
  for e in (← System.FilePath.readDir dir).qsort (·.fileName < ·.fileName) do
    let f := e.path / "template.tex"
    if ← f.pathExists then files := files.push f
  if files.isEmpty then die s!"no template.tex under {dir}"
  let mut cases : Array (String × String × Value) := #[]
  for f in files do
    let src ← IO.FS.readFile f
    for c in contexts src do
      cases := cases.push ((f.parent.bind (·.fileName)).getD f.toString, src, c)
  let reply ← IO.FS.withTempDir fun tmp => do
    let input := tmp / "batch.json"
    let script := tmp / "bridge.js"
    IO.FS.writeFile script bridge
    IO.FS.writeFile input (Json.arr (cases.map fun (_, t, c) =>
      Json.mkObj [("template", .str t), ("context", toJson c)])).compress
    let out ← IO.Process.output { cmd := node, args := #[script.toString, (System.FilePath.mk nj).toString, input.toString] }
    if out.exitCode != 0 then die s!"the bridge failed: {out.stderr}"
    match Json.parse out.stdout >>= fun j => j.getArr? with
    | .ok a => pure a
    | .error e => die s!"the bridge answered no batch: {e}"
  let mut agree := 0
  let mut differ : Std.HashMap String Nat := {}
  let mut shown : List String := []
  for ((name, src, ctx), k) in cases.zipIdx do
    let theirs := reply[k]?.getD .null
    let ours := (render src ctx ["CONTENT", "IMPORTS"]).map fun ps => String.join (ps.toList.map (·.spelled))
    let verdict : Option String := match ours, theirs.getObjValAs? String "text", theirs.getObjValAs? String "error" with
      | .ok o, .ok t, _ => (firstDiff o t).map fun (l, a, b) => s!"line {l}: ours {a.quote}, nunjucks {b.quote}"
      | .error e, .ok _, _ => some s!"ours refuses ({e}), nunjucks renders"
      | .ok _, _, .ok e => some s!"nunjucks refuses ({e}), ours renders"
      | .error _, _, .ok _ => none
      | _, _, _ => some "nunjucks answered neither text nor error"
    match verdict with
    | none => agree := agree + 1
    | some v =>
      differ := differ.insert name (differ.getD name 0 + 1)
      if !(shown.any (·.startsWith (name ++ ":"))) then shown := shown ++ [s!"{name}: {v}"]
  for line in shown do IO.println s!"  {line}"
  IO.println s!"jtex-diff: {agree} of {cases.size} renderings over {files.size} templates agree; {differ.size} templates differ"
  return if differ.isEmpty then 0 else 1
