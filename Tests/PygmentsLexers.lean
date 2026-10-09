import Tests.Support
import LeanTex.Core.Highlight
import Lean.Data.Json

open LeanTex.Core LeanTex.Core.Highlight
open Lean (Json)

namespace Tests

namespace PygmentsLexers

def root : System.FilePath := "testdata/highlight/snippets"
def recorded : System.FilePath := "testdata/highlight/pygments-tokens.json"

/-- A stream as the record spells it: start, type, text. -/
abbrev Spelled := Array (Nat × String × String)

def native (lexer : Lexer) (source : String) : Spelled :=
  let src := Src.ofString (source ++ "\n")
  (lex lexer src).map fun r =>
    (r.start, r.kind, String.ofList (src.chars.extract r.start r.stop).toList)

def spelled (tokens : Json) : Option Spelled := do
  let items ← tokens.getArr?.toOption
  items.mapM fun item => do
    let parts ← item.getArr?.toOption
    return (← (parts.getD 0 .null).getNat?.toOption, ← (parts.getD 1 .null).getStr?.toOption,
      ← (parts.getD 2 .null).getStr?.toOption)

/-- The snippet files, as the record names them. -/
def snippetPaths : IO (Array String) := do
  let mut out := #[]
  for d in (← root.readDir).qsort (·.fileName < ·.fileName) do
    for f in (← d.path.readDir).qsort (·.fileName < ·.fileName) do
      out := out.push f.path.toString
  return out

/-- The directory a snippet stands in names its listing language. -/
def aliasOf (path : String) : String :=
  ((path.splitOn "/").reverse.drop 1).headD ""

end PygmentsLexers

/-- The native lexers against Pygments' own streams for the invented
snippets, recorded by `scripts/highlight-diff.lean --record`: token for
token, start, type and text. The record covers every snippet and every
lexer, came from the Pygments and the Python the data was generated under,
and the mirror implements the rule structure that data was read beside. -/
def pygmentsLexerChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let json ← match Json.parse (← IO.FS.readFile PygmentsLexers.recorded) with
    | .ok j => pure j
    | .error e => do t s!"pygments lexers: the record does not parse: {e}" false; return
  let version := (json.getObjValAs? String "pygments").toOption.getD ""
  let python := (json.getObjValAs? String "python").toOption.getD ""
  t "pygments lexers: the record and the lexer data come from one Pygments under one Python"
    (version == PygmentsLexData.pygmentsVersion && python == PygmentsLexData.pythonVersion)
  t "pygments lexers: the mirror implements the generated rule structure"
    (mirrorsRules == PygmentsLexData.rulesDigest)
  let cases := ((json.getObjVal? "cases").toOption.bind (·.getArr?.toOption)).getD #[]
  let mut seen : Array String := #[]
  let mut lexers : Array Lexer := #[]
  for c in cases do
    let path := (c.getObjValAs? String "path").toOption.getD ""
    seen := seen.push path
    let alias := PygmentsLexers.aliasOf path
    let some lexer := Lexer.ofName? alias
      | do t s!"pygments lexers: {path} stands under no native lexer's name" false; continue
    unless lexers.contains lexer do lexers := lexers.push lexer
    let some want := (c.getObjVal? "tokens").toOption.bind PygmentsLexers.spelled
      | do t s!"pygments lexers: {path} has a malformed record" false; continue
    let raw ← try IO.FS.readFile path catch _ => pure ""
    t s!"pygments lexers: {path} is a snippet file" (← System.FilePath.pathExists path)
    let source := (ListingReply.Request.ofSource alias raw).source
    let got := PygmentsLexers.native lexer source
    let first := (List.range (max got.size want.size)).find? fun i => got[i]? != want[i]?
    t s!"pygments lexers: {path} reproduces its recorded stream (first difference: token {first})"
      (!want.isEmpty && first.isNone)
  let files ← PygmentsLexers.snippetPaths
  t "pygments lexers: every snippet is recorded, and only snippets are"
    (files.all seen.contains && seen.all files.contains)
  t "pygments lexers: every native lexer has a recorded snippet"
    (Lexer.all.all lexers.contains)
  t "pygments lexers: a Lean proof hole is Generic.Error, as Pygments' Lean 4 lexer types it"
    ((PygmentsLexers.native .lean4 "theorem t : p := sorry").any fun (_, k, text) =>
      k == Ty.genericError && text == "sorry")
  t "pygments lexers: a step that neither reads nor pops still ends, the fallback taking each scalar"
    (drive () (fun _ m => m) (Src.ofString "a\nb") ==
        #[⟨0, 1, Ty.error⟩, ⟨1, 2, Ty.whitespace⟩, ⟨2, 3, Ty.error⟩] &&
      drive () (fun _ m => m.push ()) (Src.ofString "ab") == #[⟨0, 1, Ty.error⟩, ⟨1, 2, Ty.error⟩])
  t "pygments lexers: the ASCII fast paths answer as the class tables do"
    ((List.range 128).all fun n => asciiAgrees (Char.ofNat n))
  t "pygments lexers: every alias selects its lexer, in any case, and no other"
    (Lexer.all.all fun l => l.aliases.all fun a =>
      Lexer.ofName? a == some l && Lexer.ofName? a.toUpper == some l &&
        Lexer.all.all fun l' => l' == l || !l'.aliases.contains a)
  t "pygments lexers: `lean` names Lean 4"
    (Lexer.ofName? "lean" == some .lean4 && Lexer.ofName? " Lean4 " == some .lean4)
  t "pygments lexers: a language with no native lexer selects none"
    ((["ruby", "c", "lean3", "pycon", "", "py thon"] : List String).all
      fun n => (Lexer.ofName? n).isNone)

end Tests
