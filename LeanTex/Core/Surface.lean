module

public import LeanTex.Core.Parse
public import LeanTex.Core.Lex
public import LeanTex.Core.MdDesugar

/-! # One door per surface

The engine reads two surfaces, and each has exactly one door into the one
surface AST: tex through its lexer and parser, markdown through its reader
and desugaring. Everything past the door is blind to which surface wrote a
raw — one elaborator, one IR, every backend a projection of it — so the
door is the only place a surface may differ, and this module is the only
place it is spelled.

A file read for an include goes through the same door and comes back in the
one wrapper the elaborator knows a file by (`Parse.inputEnv`), so an
included file's diagnostics name the file and line that hold the construct.
The wrapper means nothing but the file's name: an include standing as its
block sequence elaborates exactly as the file alone does
(`Elab.elabBlocks_input_exact`), and a markdown file meets that statement's
hypotheses by construction (`Elab.markdownInput_blocks_exact`). The CLI
reaches the surfaces only through here (`surfaceDoorBypasses` in
`scripts/precommit.lean`). -/

namespace LeanTex.Core

/-- The surfaces a document or an included file can be written in. -/
public inductive Surface where
  | tex
  | md
  deriving Repr, BEq, DecidableEq

namespace Surface

/-- The surface a path's extension selects for a document: `.md` reads as
markdown, everything else as tex. -/
public def ofPath (file : String) : Surface :=
  if file.endsWith ".md" then .md else .tex

/-- The surface's short name, what a run reports its read phase as. -/
public def name : Surface → String
  | .tex => "tex"
  | .md => "md"

/-- A surface's text as the surface AST, with the reader's own diagnostics.
The tex door is the lexer then the parser; the markdown door is the reader
then the desugaring, which lowers into the AST without generating tex text
(`Md.desugar`). -/
@[expose] public def read : Surface → String → String → Array Parse.Raw × Array Diag
  | .tex, file, text =>
    let (toks, lexDs) := Lex.lex file text
    let (raws, parseDs) := Parse.parse file toks
    (raws, lexDs ++ parseDs)
  | .md, file, text => Md.read file text

/-- An included file through its surface's door, in the wrapper the
elaborator knows a file by, standing at the including call's position. -/
@[expose] public def fragment (s : Surface) (path text : String) (pos : Pos) :
    Array Parse.Raw × Array Diag :=
  let (sub, ds) := s.read path text
  (#[.env (Parse.inputEnv path) sub pos], ds)

end Surface

end LeanTex.Core
