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

/-- `\setcitestyle`'s keywords, each a row. -/
private def citeKeywords : List (String × (CitePunct → CitePunct)) :=
  [("round", fun p => { p with «open» := "(", close := ")" }),
   ("square", fun p => { p with «open» := "[", close := "]" }),
   ("angle", fun p => { p with «open» := "<", close := ">" }),
   ("curly", fun p => { p with «open» := "{", close := "}" }),
   ("semicolon", fun p => { p with sep := ";" }),
   ("colon", fun p => { p with sep := ";" }),
   ("comma", fun p => { p with sep := "," }),
   ("authoryear", fun p => { p with numbers := false }),
   ("numbers", fun p => { p with numbers := true })]

/-- `\setcitestyle`'s `key=value` declarations. -/
private def citeKeys : List (String × (CitePunct → String → CitePunct)) :=
  [("open", fun p v => { p with «open» := v }), ("close", fun p v => { p with close := v }),
   ("aysep", fun p v => { p with aysep := v }), ("yysep", fun p v => { p with yysep := v }),
   ("notesep", fun p v => { p with notesep := v }),
   ("citesep", fun p v => { p with sep := v })]

/-- A value as TeX reads a delimited argument: one outer
brace group stripped. -/
private def stripGroup (v : String) : String := Id.run do
  let cs := v.toList
  unless cs.head? == some '{' && cs.getLast? == some '}' do return v
  let mut depth : Int := 0
  let mut k := 0
  for c in cs do
    k := k + 1
    if c == '{' then depth := depth + 1
    else if c == '}' then
      depth := depth - 1
      if depth == 0 && k < cs.length then return v
  return String.ofList (cs.drop 1 |>.dropLast)

/-- A `key=value` declaration's key and value, when it is one. -/
private def keyValue? (d : String) : Option (String × String) :=
  match d.splitOn "=" with
  | k :: v :: rest => some (k, stripGroup (String.intercalate "=" (v :: rest)))
  | _ => none

/-- Whether natbib reads this declaration, compared exactly as written. -/
public def CitePunct.reads (d : String) : Bool :=
  d == "nobibstyle" || d == "bibstyle" || (citeKeywords.lookup d).isSome ||
    ((keyValue? d).bind fun (k, _) => citeKeys.lookup k).isSome

/-- One declaration over the punctuation and natbib's `\bibstyle` door. -/
private def CitePunct.step (st : CitePunct × Bool) (d : String) : CitePunct × Bool :=
  if d == "nobibstyle" then (st.1, false)
  else if d == "bibstyle" then (st.1, true)
  else if d == "sort" then ({ st.1 with sort := true }, st.2)
  else if d == "compress" then ({ st.1 with compress := true }, st.2)
  else if d == "biblatex" then ({ st.1 with biblatex := true }, st.2)
  else if let ["citestyle", name] := d.splitOn "=" then
    -- `\citestyle{name}`: the name's `\bibstyle@` row, or nothing for a name with none.
    match natbibRows.lookup name with
    | some r => ({ r with sort := st.1.sort, compress := st.1.compress,
                          biblatex := st.1.biblatex }, st.2)
    | none => st
  else match citeKeywords.lookup d, keyValue? d with
    | some f, _ => (f st.1, st.2)
    | none, some (k, v) =>
      match citeKeys.lookup k with
      | some f => (f st.1 v, st.2)
      | none => st
    | none, none => st

/-- The items of a `\setcitestyle` list, split at commas
outside braces, kept as written. -/
public def citeItems (src : String) : Array String := Id.run do
  let mut out : Array String := #[]
  let mut cur := ""
  let mut depth : Int := 0
  for c in src.toList do
    if c == ',' && depth == 0 then
      out := out.push cur
      cur := ""
    else
      if c == '{' then depth := depth + 1
      else if c == '}' then depth := depth - 1
      cur := cur.push c
  return (out.push cur).filter (!·.isEmpty)

/-- natbib's package options in its own declaration order, each as the
declarations it executes. -/
public def natbibOptions : List (String × List String) :=
  [("numbers", ["numbers", "square", "comma", "nobibstyle"]),
   ("authoryear", ["authoryear", "round", "semicolon", "bibstyle"]),
   ("round", ["round", "nobibstyle"]), ("square", ["square", "nobibstyle"]),
   ("angle", ["angle", "nobibstyle"]), ("curly", ["curly", "nobibstyle"]),
   ("comma", ["comma", "nobibstyle"]), ("semicolon", ["semicolon", "nobibstyle"]),
   ("colon", ["semicolon", "nobibstyle"]),
   ("nobibstyle", ["nobibstyle"]), ("bibstyle", ["bibstyle"]),
   ("sort", ["sort"]), ("compress", ["compress"]), ("sort&compress", ["sort", "compress"])]

/-- The punctuation a document's citations draw with, by natbib's rule. -/
public def CitePunct.ofDoc (natbib : Option (Array String)) (row : Option CitePunct)
    (labels : Bool) : CitePunct :=
  match natbib with
  | none => latexPunct
  | some decls =>
    let (p, door) := decls.foldl CitePunct.step ({}, true)
    let q := if door then row.getD p else p
    let q := { q with sort := p.sort, compress := p.compress, biblatex := p.biblatex }
    if labels then q else { q with numbers := true }

end LeanTex.Core.Bib
