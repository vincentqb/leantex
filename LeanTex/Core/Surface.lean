module

public import LeanTex.Core.Parse
public import LeanTex.Core.Lex
public import LeanTex.Core.MdDesugar
public import LeanTex.Core.CodeDoc

/-! # One door per surface

Each surface reads into the one surface AST through exactly one door. -/

namespace LeanTex.Core

namespace Surface

@[expose] public def texLex (file text : String) : Array Lex.Token × Array Diag := Lex.lex file text

@[expose] public def texParse (file : String) (toks : Array Lex.Token) : Array Parse.Raw × Array Diag :=
  Parse.parse file toks

/-- A surface's text as the surface AST, with the reader's own diagnostics. -/
@[expose] public def read : Ir.Surface → String → String → Array Parse.Raw × Array Diag
  | .tex, file, text =>
    let (toks, lexDs) := Lex.lex file text
    let (raws, parseDs) := Parse.parse file toks
    (raws, lexDs ++ parseDs)
  | .markdown, file, text => Md.read file text
  | .code lang, file, text => Code.read lang file text

/-- A code file's text as the surface AST, each statement its facts give set beside its
declaration's code as the file's directive orders its views. -/
@[expose] public def readCode (lang : Ir.CodeLang) (file text : String)
    (facts : Option LeanFacts.Facts) (place : Code.LinkPlace := {}) (refs : Option Code.Refs := none) :
    Array Parse.Raw × Array Diag :=
  Code.read lang file text facts place refs

public theorem read_tex_exact (file text : String) :
    read .tex file text =
      ((texParse file (texLex file text).1).1,
        (texLex file text).2 ++ (texParse file (texLex file text).1).2) := rfl

/-- An included file read through its surface's door, wrapped as
`Parse.inputEnv` at the including call's position, or as `Parse.nativeInputEnv` where the
compatibility pass and the document's own commands leave it alone. -/
@[expose] public def fragment (s : Ir.Surface) (path text : String) (pos : Pos)
    (cites : Bool := false) (native : Bool := false) (hybrid : Bool := false) :
    Array Parse.Raw × Array Diag :=
  let (sub, ds) := match s with
    | .markdown => Md.readIncluded path text cites hybrid
    | s => read s path text
  (#[.env (if native then Parse.nativeInputEnv path else Parse.inputEnv path) sub pos], ds)

end Surface

end LeanTex.Core
