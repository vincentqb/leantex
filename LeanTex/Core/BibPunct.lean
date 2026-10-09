module

public import LeanTex.Core.Ir

/-! natbib's citation punctuation, read where a document declares it — the
compatibility pass reads `\setcitestyle`, `\bibpunct` and natbib's load
options through it, and the bibliography resolution draws every citation
with what it settles to. A leaf of its own so that the compatibility pass
does not depend on the reference list's formatting. -/

namespace LeanTex.Core.Bib

open LeanTex.Core

/-- natbib's citation punctuation: the seven values `\bibpunct` sets
(natbib.sty `\NAT@open`, `\NAT@close`, `\NAT@sep`, the mode letter,
`\NAT@aysep`, `\NAT@yrsep`, `\NAT@cmt`), each at natbib's own load
value, and the load's `sort` and `compress` (`\NAT@sort`, `\NAT@cmprs`),
which order a citation's keys and join its runs of numbers — options no
`\bibpunct` or style row touches. -/
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
  /-- The citations are biblatex's (its standard styles' defaults, biblatex
  manual §3.1.2.1 and §3.9): the label names as biber's uniqueness reads
  them (`Resolved.citeNames`), no von part (`useprefix=false`), a textual
  citation's last key joined by `and`, and a key repeating the last key's
  names printed whole — but in a numeric textual citation, where it joins
  that key's bracket (`groupsKeys`). (Its bare author-year `\cite` is
  natbib's `\citealp`, a rename where it is read.) -/
  biblatex : Bool := false
  /-- biblatex's `useprefix`: a citation's names keep their von part
  (biblatex manual §3.1.2.1), as BibTeX's always do. -/
  useprefix : Bool := false
  /-- The ink a citation's linked mark is set in: the document's `cite` style
  colour (`Ir.Styles.linkInk`), hyperref's `citecolor` under `colorlinks`.
  Only the mark: the brackets and separators around it keep the running
  colour, as `\Hy@colorlink` leaves them. -/
  ink : Option (Ir.Color × Option String) := none
  deriving Repr, BEq, Inhabited

/-- natbib's `\bibstyle@plainnat` row, which `abbrvnat` and `unsrtnat`
share (natbib.sty: `\bibpunct{[}{]}{,}{a}{,}{,}`): author-year, square
brackets, a comma between citations. -/
public def natPunct : CitePunct := { «open» := "[", close := "]", sep := "," }

/-- natbib's `\bibstyle@plain` row, which `abbrv` and `unsrt` share
(`\bibpunct{[}{]}{,}{n}{}{,}`): numbers in square brackets, LaTeX's own
`\cite` too (latex.ltx `\@cite`, `[1, 2]`). -/
public def latexPunct : CitePunct :=
  { numbers := true, «open» := "[", close := "]", sep := ",", aysep := "" }

/-- natbib's `\bibstyle@<name>` rows (natbib.sty:206–234, and the `\let`
aliases beside them): the punctuation natbib gives a style by its name
while its `\bibstyle` door stays open, whether or not the engine formats
that style's list. A name with no row leaves natbib's declared punctuation
standing — natbib.sty reads an undefined `\bibstyle@<name>` as nothing —
which is what an `apalike` document cites with: `(Doe, 2024; Roe, 2020)`.
Each row is the six values its `\bibpunct` sets, the note separator at
`\bibpunct`'s default `, `; agu's `,~` year separator is the `,` natbib
sets (its `\unskip` takes the tie). natbib's `nature` row, superscript
numbers, has no entry: the engine sets no superscript citation, as it
refuses natbib's `super` option. -/
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

/-- `\setcitestyle`'s keywords (natbib.sty `\setcitestyle`, the package
options by the same names): each a row, read in the order written. -/
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

/-- `\setcitestyle`'s `key=value` declarations (natbib.sty `\setcitestyle`:
`open`, `close`, `aysep`, `yysep`, `notesep`, `citesep`), the values
`\bibpunct` sets by position. -/
private def citeKeys : List (String × (CitePunct → String → CitePunct)) :=
  [("open", fun p v => { p with «open» := v }), ("close", fun p v => { p with close := v }),
   ("aysep", fun p v => { p with aysep := v }), ("yysep", fun p v => { p with yysep := v }),
   ("notesep", fun p v => { p with notesep := v }),
   ("citesep", fun p v => { p with sep := v })]

/-- A value as TeX reads a delimited argument: one outer brace group is
stripped (`open={(}` is `(`), anything else is kept as written. -/
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

/-- Does natbib read this declaration — a keyword, a key it knows, or a
door word? Exactly as written: natbib compares whole items, so ` round`
after a comma and a space is a word it does not know. -/
public def CitePunct.reads (d : String) : Bool :=
  d == "nobibstyle" || d == "bibstyle" || (citeKeywords.lookup d).isSome ||
    ((keyValue? d).bind fun (k, _) => citeKeys.lookup k).isSome

/-- One declaration over the punctuation and natbib's `\bibstyle` door, the
door a bibliography style's own punctuation comes through at
`\begin{document}`: `nobibstyle` closes it and `bibstyle` reopens it
(natbib's option names), `sort` and `compress` set the load's two
citation options, a keyword or a `key=value` updates the punctuation, and
anything else leaves both as they were — natbib reads an unknown item as
nothing. -/
private def CitePunct.step (st : CitePunct × Bool) (d : String) : CitePunct × Bool :=
  if d == "nobibstyle" then (st.1, false)
  else if d == "bibstyle" then (st.1, true)
  else if d == "sort" then ({ st.1 with sort := true }, st.2)
  else if d == "compress" then ({ st.1 with compress := true }, st.2)
  else if d == "biblatex" then ({ st.1 with biblatex := true }, st.2)
  else if let ["citestyle", name] := d.splitOn "=" then
    -- `\citestyle{name}` (natbib.sty): the name's `\bibstyle@` row, or
    -- nothing for a name with none; the load's options stand.
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

/-- The items of a `\setcitestyle` list, split where natbib's `\@for` splits
them — at commas outside braces — and kept exactly as written. -/
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

/-- natbib's package options in its own declaration order (natbib.sty's
`\DeclareOption`s — `\ProcessOptions` runs them in this order, whatever
order a load lists them in), each as the declarations it executes in
`\setcitestyle`'s vocabulary: `numbers` is `numbers` with `square`, `comma`
and `nobibstyle` there. `sort`, `compress` and `sort&compress` set the two
citation options only a load declares (`CitePunct.step`). -/
public def natbibOptions : List (String × List String) :=
  [("numbers", ["numbers", "square", "comma", "nobibstyle"]),
   ("authoryear", ["authoryear", "round", "semicolon", "bibstyle"]),
   ("round", ["round", "nobibstyle"]), ("square", ["square", "nobibstyle"]),
   ("angle", ["angle", "nobibstyle"]), ("curly", ["curly", "nobibstyle"]),
   ("comma", ["comma", "nobibstyle"]), ("semicolon", ["semicolon", "nobibstyle"]),
   ("colon", ["semicolon", "nobibstyle"]),
   ("nobibstyle", ["nobibstyle"]), ("bibstyle", ["bibstyle"]),
   ("sort", ["sort"]), ("compress", ["compress"]), ("sort&compress", ["sort", "compress"])]

/-- The punctuation a document's citations draw with — natbib's rule. No
natbib is LaTeX's own `\cite` (`latexPunct`). With natbib, its
declarations replay over its load values (`CitePunct.step`); then, while
natbib's `\bibstyle` door stays open, the declared style's row
(`natbibRows`, by name) replaces them all at `\begin{document}` — a style
with no row leaves them standing — and a style whose `\bibitem`s carry no
author-year label (`labels`) puts natbib in numbers mode whatever was
declared (natbib.sty reading a `\bibitem` without one). A document that
declares no style has no row to apply. -/
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
