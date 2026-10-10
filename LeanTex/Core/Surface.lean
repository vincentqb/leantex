module

public import LeanTex.Core.Parse
public import LeanTex.Core.Lex
public import LeanTex.Core.MdDesugar

/-! # One door per surface

The engine reads two surfaces, and each has exactly one door into the one
surface AST: tex through its lexer and parser, markdown through its reader
and desugaring. Past the door the elaborator reads raws, never the surface
that wrote them; what a document's surface may still decide is its own
defaults — how its content sets, never what is set. The door is this
file's definition, and the hook holds the CLI to it: a CLI source reads a
surface only through `read`, `fragment` and the tex door's two stages
`texLex` and `texParse`, which compose to `read` (`read_tex_exact`), and a
core source lexes and parses tex text only inside a declared reader
(`surfaceDoorBypasses` and `coreTexReaders` in `scripts/precommit.lean`). The six declared readers
each read text the engine itself holds rather than a file: the elaborator's
whole-document entry (`Elab.run`, which tests elaborate a string with), a
style declaration's value (`Elab.applyStyle`), a setting's tex value
(`Data.valParsed`), the compatibility layer's synthesized source
(`Compat.synth`), a picture's macro definition (`Picture.readMacro`) and a
bibliography style's formula (`BibStyle.formulaOf`).

A file read for an include goes through the same door and comes back in the
one wrapper the elaborator knows a file by (`Parse.inputEnv`), so an
included file's diagnostics name the file and line that hold the construct.
The wrapper means nothing but the file's name: an include standing as its
block sequence, with only blank source around the call, elaborates exactly
as the file alone does (`Elab.elabBlocks_input_exact`), and a markdown file
meets that statement's hypotheses by construction once its desugaring is not
empty (`Elab.markdownInput_blocks_exact`). The same holds at any block
accumulator the elaborator opens, a frame's content among them, by a lemma
private to `InputContract` because the accumulator it speaks of is private
to the elaborator. -/

namespace LeanTex.Core

/-- The surfaces a document or an included file can be written in. -/
public inductive Surface where
  | tex
  | markdown
  deriving Repr, BEq, DecidableEq

namespace Surface

/-- The surface a path's extension selects for a document: `.md` reads as
markdown, everything else as tex. -/
public def ofPath (file : String) : Surface :=
  if file.endsWith ".md" then .markdown else .tex

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
  | .markdown, file, text => Md.read file text

/-- The tex door is its two stages, one after the other: a caller that
reports them apart reads what `read` reads. -/
public theorem read_tex_exact (file text : String) :
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
