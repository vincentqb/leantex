module

public import LeanTex.Core.Parse
public import LeanTex.Core.Lex
public import LeanTex.Core.MdDesugar

/-! # One door per surface

The engine reads two surfaces, and each has exactly one door into the one
surface AST: tex through its lexer and parser, markdown through its reader
and desugaring. Past the door the elaborator reads raws, never the surface
that wrote them; what a document's surface may still decide is its own
defaults — how its content sets, never what is set. The CLI reads a
surface only here (`surfaceDoorBypasses` in `scripts/precommit.lean`
holds it to that). Inside the core, three places read tex text the way the
tex door does without going through it: the elaborator's whole-document
entry (`Elab.run`, which tests elaborate a string with), a setting's tex
value (`Data.valParsed`), and the compatibility layer's synthesized source
(`Compat.synth`).

A file read for an include goes through the same door and comes back in the
one wrapper the elaborator knows a file by (`Parse.inputEnv`), so an
included file's diagnostics name the file and line that hold the construct.
The wrapper means nothing but the file's name: an include standing as its
block sequence elaborates exactly as the file alone does
(`Elab.elabBlocks_input_exact`; at any block accumulator, a frame's content
among them, `Elab.elabBlockScope_input_exact`), and a markdown file meets
that statement's hypotheses by construction once it has content
(`Elab.markdownInput_blocks_exact`). -/

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

/-- The tex door's first stage, the lexer, for a caller that reports each
stage on its own (the driver's `-v` phases). -/
@[expose] public def texLex (file text : String) : Array Lex.Token × Array Diag := Lex.lex file text

/-- The tex door's second stage, the parser. -/
@[expose] public def texParse (file : String) (toks : Array Lex.Token) : Array Parse.Raw × Array Diag :=
  Parse.parse file toks

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

/-- The tex door is its two stages, one after the other: a caller that
reports them apart reads what `read` reads. -/
public theorem read_tex_stages (file text : String) :
    read .tex file text =
      ((texParse file (texLex file text).1).1,
        (texLex file text).2 ++ (texParse file (texLex file text).1).2) := rfl

/-- An included file through its surface's door, in the wrapper the
elaborator knows a file by, standing at the including call's position. -/
@[expose] public def fragment (s : Surface) (path text : String) (pos : Pos) :
    Array Parse.Raw × Array Diag :=
  let (sub, ds) := s.read path text
  (#[.env (Parse.inputEnv path) sub pos], ds)

end Surface

end LeanTex.Core
