import Tests.Support

open LeanTex.Core LeanTex.Cli

/-- The symbols of the generated table that Fira Math, the shipped math face,
has no glyph for: each sets from a fallback face that has one, or is dropped
and named (E0405). A row of `MathSymData.rows` whose scalar the face lacks is
here, and every name here is such a row — both ways, so the list is the
face's coverage and not a guess about it. -/
def firaGaps : List String :=
  ["checkmark", "maltese", "ulcorner", "urcorner", "llcorner", "lrcorner", "vartriangleright",
   "vartriangleleft", "trianglerighteq", "trianglelefteq", "lhd", "unlhd", "rhd", "unrhd",
   "Join", "boxdot", "boxplus", "boxtimes", "blacklozenge", "boxminus", "Vdash", "Vvdash",
   "vDash", "circeq", "gtrapprox", "multimap", "triangleq", "lessapprox", "eqslantless",
   "eqslantgtr", "bigstar", "between", "blacktriangledown", "vartriangle", "blacktriangle",
   "triangledown", "eqcirc", "lesseqqgtr", "gtreqqless", "veebar", "barwedge", "doublebarwedge",
   "Subset", "Supset", "Cup", "doublecup", "Cap", "doublecap", "leftthreetimes",
   "rightthreetimes", "subseteqq", "supseteqq", "bumpeq", "Bumpeq", "pitchfork", "intercal",
   "circledcirc", "circledast", "circleddash", "lneq", "gneq", "precneqq", "succneqq",
   "precnapprox", "succnapprox", "lnapprox", "gnapprox", "diagup", "diagdown", "subsetneqq",
   "supsetneqq", "nvdash", "nVdash", "nvDash", "nVDash", "ntrianglerighteq", "ntrianglelefteq",
   "ntriangleleft", "ntriangleright", "divideontimes", "Finv", "Game", "ltimes", "rtimes",
   "succapprox", "precapprox", "digamma"]

/-- The index rows of one package whose call is exactly one math symbol,
`$\name$`: name ↦ verdict, in file order. -/
def symbolRows (text : String) : Array (String × String) := Id.run do
  let mut out : Array (String × String) := #[]
  for line in text.splitOn "\n" do
    let line := line.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then continue
    match (line.splitOn " ").filter (!·.isEmpty) with
    | [_, ann, call] =>
      if call.startsWith "$\\" && call.endsWith "$" then
        let name := String.ofList (call.toList.drop 2).dropLast
        if !name.isEmpty && name.all Char.isAlpha then out := out.push (name, ann)
    | _ => pure ()
  return out

/-- Every scalar a laid-out document inks, and its layout diagnostics. -/
def inkedScalars (fs : Font.FontSet) (src : String) : Array Char × Array Diag :=
  let out := layoutOf fs (elabStr src).1
  let ink := out.pages.flatMap fun p => p.lines.flatMap fun l => l.segs.flatMap fun s =>
    match s with
    | .run _ _ _ _ glyphs _ _ _ _ _ => glyphs.map (·.2)
    | _ => #[]
  (ink, out.diags)

mutual

/-- The MathML leaves of an emitted tree, in document order: each `mo`,
`mi` or `mn` with the text it carries. -/
def mathLeavesOne (acc : Array (String × String)) : Html.Node → Array (String × String)
  | .text _ => acc
  | .style _ => acc
  | .script _ _ => acc
  | .elem tag _ kids =>
    if tag == "mo" || tag == "mi" || tag == "mn" then acc.push (tag, nodeTextList "" kids.toList)
    else mathLeavesList acc kids.toList

def mathLeavesList (acc : Array (String × String)) : List Html.Node → Array (String × String)
  | [] => acc
  | k :: rest => mathLeavesList (mathLeavesOne acc k) rest

end

/-- The commands a source spells as one-symbol formulas, `$\name$`, in order. -/
def symbolCalls (src : String) : Array String :=
  ((src.splitOn "$\\").drop 1).toArray.filterMap fun piece =>
    let name := String.ofList (piece.toList.takeWhile Char.isAlpha)
    if !name.isEmpty && (piece.toList.drop name.length).head? == some '$' then some name
    else none

/-- The symbol table against its sources and the shipped math face.

The index side: `tests/compat-index/<pkg>.txt` carries one row per symbol
command the package declares (`MathSymData.<pkg>`, read off the package file
by the generator), and a row is `impl` exactly when the table sets the name
and `refuse:W0012` exactly when it refuses it — a missing row, a stray one or
a verdict the table contradicts fails. The table side: a name both the hand
rows and the generated rows carry is one atom, since `lookup` returns the
hand row and a disagreement would be a silent override; and a refused name
is unknown to the parser, which is what makes its W0012 the refusal it
declares. The face side: every generated scalar has a glyph in the shipped
math face or is one of `firaGaps`, and a gap reaches the page as a named
loss, never as silence. -/
def mathSymChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  for (pkg, documented) in [("amsfonts", MathSymData.amsfonts), ("amssymb", MathSymData.amssymb)] do
    let rows := symbolRows (← IO.FS.readFile s!"tests/compat-index/{pkg}.txt")
    for n in documented do
      let want := if MathSymData.refused.contains n then "refuse:W0012" else "impl"
      match (rows.filter (·.1 == n)).toList with
      | [(_, ann)] =>
        t s!"{pkg}.txt: \\{n} is '{ann}', and the table says '{want}'" (ann == want)
      | [] => failures ref s!"{pkg}.txt: \\{n} is declared by {pkg}.sty and has no row"
      | _ => failures ref s!"{pkg}.txt: \\{n} has more than one row"
    for (n, _) in rows do
      t s!"{pkg}.txt: \\{n} has a row but {pkg}.sty declares no such symbol"
        (documented.contains n)
  let gen := MathSymData.rows
  let hand := MathParse.ctrlAtom.take (MathParse.ctrlAtom.length - gen.length)
  t "the generated rows are the tail of ctrlAtom"
    (MathParse.ctrlAtom.drop hand.length == gen)
  for (n, cls, c) in gen do
    if let some (cls', c') := hand.lookup n then
      t s!"\\{n}: the hand row shadows a generated row that says otherwise"
        (cls == cls' && c == c')
  for n in MathSymData.refused do
    t s!"\\{n} is refused yet the parser knows it" (!MathParse.knownCtrl n)
  let fira ← match Font.parse (← IO.FS.readBinFile (testFonts ++ "/FiraMath-Regular.otf")) with
    | .ok f => pure f
    | .error e => throw (IO.userError s!"math symbols: FiraMath unparsable: {e}")
  let uncovered := gen.filter fun (_, _, c) => (fira.gid c).isNone
  for (n, _, c) in uncovered do
    t s!"Fira Math has no glyph for \\{n} (U+{String.ofList (Nat.toDigits 16 c.toNat)}), \
and firaGaps does not say so" (firaGaps.contains n)
  for n in firaGaps do
    t s!"firaGaps lists \\{n}, which Fira Math covers or the table does not set"
      (uncovered.any (·.1 == n))
  -- A gap on the page: the scalar is not inked and one E0405 accounts for
  -- it; a covered symbol inks its own scalar from the math face.
  let some fontData ← findFont
    | failures ref "math symbols: no corpus font"
  let .ok font := Font.parse fontData
    | failures ref "math symbols: corpus font unparsable"
  let fs ← mathSetOf (oneFaceOf font)
  match uncovered.find? fun (n, _, _) => n == "boxplus" with
  | some (_, _, c) =>
    let (ink, ds) := inkedScalars fs "$a \\boxplus b$"
    t "a symbol the math face lacks is not inked" (!ink.contains c)
    t "a symbol the math face lacks is named once (E0405)"
      ((ds.filter (·.code == "E0405")).size == 1)
  | none => failures ref "math symbols: \\boxplus is no longer a Fira Math gap; pick another probe"
  let (ink, ds) := inkedScalars fs "$a \\leqslant b$"
  t "a covered symbol inks its own scalar" (ink.contains '\u2A7D')
  t "a covered symbol raises no glyph loss"
    (!ds.any fun d => d.code == "E0405" || d.code == "W0009")
  -- The parity fixture's engine half, in HTML: the MathML leaves are the
  -- table's atoms in the source's order — each scalar, under the leaf its
  -- class maps to. The parity tier holds the PDF of the same source to
  -- lualatex's scalars, so the two artifacts agree through the one table.
  let src ← IO.FS.readFile "tests/parity/amssymb.tex"
  let calls := symbolCalls src
  let want := calls.filterMap fun n => (MathParse.ctrlAtom.lookup n).map fun (cls, c) =>
    (MathMl.leafTag cls c, String.ofList [c])
  t "the parity fixture spells every symbol it sets through the table"
    (!calls.isEmpty && want.size == calls.size)
  let (_, body, _) := HtmlDoc.emitTree {} (elabStr src).1
  t "the fixture's HTML sets each symbol as the table's leaf, in order"
    (mathLeavesList #[] body.toList == want)
