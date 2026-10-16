module

public import LeanTex.Core.Ir

/-! natbib's citation punctuation, read where a document declares it. -/

namespace LeanTex.Core.Bib

open LeanTex.Core

/-- natbib's citation punctuation: the seven values `\bibpunct` sets, at
natbib's load defaults. -/
public structure CitePunct where
  numbers : Bool := false
  «open» : String := "("
  close : String := ")"
  sep : String := ";"
  aysep : String := ","
  yysep : String := ","
  notesep : String := ", "
  sort : Bool := false
  compress : Bool := false
  /-- The citations are biblatex's standard styles'. -/
  biblatex : Bool := false
  /-- biblatex's `useprefix`: a citation's names keep their von part. -/
  useprefix : Bool := false
  /-- The ink a citation's linked mark is set in. -/
  ink : Option (Ir.Color × Option Ir.ColorRef) := none
  deriving Repr, BEq, Inhabited

/-- natbib's `\bibstyle@plainnat` row: author-year, square
brackets, a comma between citations. -/
public def natPunct : CitePunct := { «open» := "[", close := "]", sep := "," }

/-- natbib's `\bibstyle@plain` row: numbers in square
brackets, LaTeX's own `\cite` too. -/
public def latexPunct : CitePunct :=
  { numbers := true, «open» := "[", close := "]", sep := ",", aysep := "" }

/-- natbib's `\bibstyle@<name>` rows. -/
public def natbibRows : List (String × CitePunct) :=
  let ay (o c sep aysep : String) : CitePunct :=
    { «open» := o, close := c, sep, aysep, yysep := "," }
  let num (o c : String) (yysep : String := ",") : CitePunct :=
    { numbers := true, «open» := o, close := c, sep := ",", aysep := "", yysep }
  [("chicago", ay "(" ")" ";" ","), ("named", ay "[" "]" ";" ","),
   ("agu", ay "[" "]" ";" ","), ("copernicus", ay "(" ")" ";" ","),
   ("egu", ay "(" ")" ";" ","), ("egs", ay "(" ")" ";" ","),
   ("agsm", ay "(" ")" "," ""), ("kluwer", ay "(" ")" "," ""),
   ("dcu", ay "(" ")" ";" ";"), ("aa", ay "(" ")" ";" ""),
   ("pass", ay "(" ")" ";" ","), ("anngeo", ay "(" ")" ";" ","),
   ("nlinproc", ay "(" ")" ";" ","),
   ("cospar", num "/" "/" (yysep := "")), ("esa", num "(Ref.\u00a0" ")" (yysep := "")),
   ("plain", latexPunct), ("alpha", latexPunct), ("abbrv", latexPunct), ("unsrt", latexPunct),
   ("plainnat", natPunct), ("abbrvnat", natPunct), ("unsrtnat", natPunct)]

/-- One of natbib's words over the punctuation and its `\bibstyle` door. -/
private def CitePunct.word (st : CitePunct × Bool) : CiteDecl.Word → CitePunct × Bool
  | .nobibstyle => (st.1, false)
  | .bibstyle => (st.1, true)
  | .sort => ({ st.1 with sort := true }, st.2)
  | .compress => ({ st.1 with compress := true }, st.2)
  | .biblatex => ({ st.1 with biblatex := true }, st.2)
  | .round => ({ st.1 with «open» := "(", close := ")" }, st.2)
  | .square => ({ st.1 with «open» := "[", close := "]" }, st.2)
  | .angle => ({ st.1 with «open» := "<", close := ">" }, st.2)
  | .curly => ({ st.1 with «open» := "{", close := "}" }, st.2)
  | .semicolon | .colon => ({ st.1 with sep := ";" }, st.2)
  | .comma => ({ st.1 with sep := "," }, st.2)
  | .authoryear => ({ st.1 with numbers := false }, st.2)
  | .numbers => ({ st.1 with numbers := true }, st.2)

/-- One declaration over the punctuation and natbib's `\bibstyle` door, a package option as the
words natbib executes for it. -/
private def CitePunct.step (st : CitePunct × Bool) : CiteDecl → CitePunct × Bool
  | .word w => CitePunct.word st w
  | .option o => o.words.foldl CitePunct.word st
  | .set .open v => ({ st.1 with «open» := v }, st.2)
  | .set .close v => ({ st.1 with close := v }, st.2)
  | .set .citesep v => ({ st.1 with sep := v }, st.2)
  | .set .aysep v => ({ st.1 with aysep := v }, st.2)
  | .set .yysep v => ({ st.1 with yysep := v }, st.2)
  | .set .notesep v => ({ st.1 with notesep := v }, st.2)
  | .set .citestyle name =>
    -- `\citestyle{name}`: the name's `\bibstyle@` row, or nothing for a name with none.
    match natbibRows.lookup name with
    | some r => ({ r with sort := st.1.sort, compress := st.1.compress,
                          biblatex := st.1.biblatex }, st.2)
    | none => st
  | .set _ _ => st

/-- The punctuation a document's citations draw with, by natbib's rule. -/
public def CitePunct.ofDoc (setup : Option (Array CiteDecl)) (row : Option CitePunct)
    (labels : Bool) : CitePunct :=
  match setup with
  | none => latexPunct
  | some decls =>
    let (p, door) := decls.foldl CitePunct.step ({}, true)
    let q := if door then row.getD p else p
    let q := { q with sort := p.sort, compress := p.compress, biblatex := p.biblatex }
    if labels then q else { q with numbers := true }

end LeanTex.Core.Bib
