module

public import LeanTex.Core.Parse
public import LeanTex.Core.Lex
public import LeanTex.Core.MdDesugar

/-! # One door per surface

Each surface reads into the one surface AST through exactly one door: tex
through its lexer and parser, markdown through its reader and desugaring. -/

namespace LeanTex.Core

namespace Surface

/-- The tex door's first stage, the lexer. -/
@[expose] public def texLex (file text : String) : Array Lex.Token × Array Diag := Lex.lex file text

/-- The tex door's second stage, the parser. -/
@[expose] public def texParse (file : String) (toks : Array Lex.Token) : Array Parse.Raw × Array Diag :=
  Parse.parse file toks

/-- A surface's text as the surface AST, with the reader's own diagnostics. -/
@[expose] public def read : Ir.Surface → String → String → Array Parse.Raw × Array Diag
  | .tex, file, text =>
    let (toks, lexDs) := Lex.lex file text
    let (raws, parseDs) := Parse.parse file toks
    (raws, lexDs ++ parseDs)
  | .markdown, file, text => Md.read file text

public theorem read_tex_exact (file text : String) :
    read .tex file text =
      ((texParse file (texLex file text).1).1,
        (texLex file text).2 ++ (texParse file (texLex file text).1).2) := rfl

/-- An included file read through its surface's door, wrapped as
`Parse.inputEnv` at the including call's position. -/
@[expose] public def fragment (s : Ir.Surface) (path text : String) (pos : Pos) :
    Array Parse.Raw × Array Diag :=
  let (sub, ds) := read s path text
  (#[.env (Parse.inputEnv path) sub pos], ds)

end Surface

end LeanTex.Core
