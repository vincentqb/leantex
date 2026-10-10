module

public import Tests.Support

public section

open LeanTex.Core LeanTex.Cli

/-- The table's atoms (each name's first row in `MathParse.ctrlAtom`, the one
`lookup` answers) that Fira Math, the shipped math face, has no glyph for:
each sets from a fallback face that has one, or is dropped and named
(E0405). An atom whose scalar the face lacks is here, and every name here
is such an atom — both ways, so the list is the face's coverage and not a
guess about it. -/
def firaGaps : List String :=
  ["star", "setminus", "Re", "Im", "wp", "top", "bot", "vdots", "ddots", "bigcup", "bigcap",
   "bigvee", "bigwedge", "bigoplus", "bigotimes", "amalg", "asymp", "bigodot", "bigsqcup",
   "bigtriangledown", "bigtriangleup", "biguplus", "bowtie", "dashv", "diamond", "diamondsuit",
   "flat", "frown", "heartsuit", "models", "natural", "preceq", "sharp", "smile", "succeq",
   "triangleleft", "triangleright", "vdash", "checkmark", "maltese", "ulcorner", "urcorner",
   "llcorner", "lrcorner", "vartriangleright", "vartriangleleft", "trianglerighteq",
   "trianglelefteq", "lhd", "unlhd", "rhd", "unrhd", "Join", "boxdot", "boxplus", "boxtimes",
   "blacklozenge", "boxminus", "Vdash", "Vvdash", "vDash", "circeq", "gtrapprox", "multimap",
   "triangleq", "lessapprox", "eqslantless", "eqslantgtr", "bigstar", "between",
   "blacktriangledown", "vartriangle", "blacktriangle", "triangledown", "eqcirc", "lesseqqgtr",
   "gtreqqless", "veebar", "barwedge", "doublebarwedge", "Subset", "Supset", "Cup", "doublecup",
   "Cap", "doublecap", "leftthreetimes", "rightthreetimes", "subseteqq", "supseteqq", "bumpeq",
   "Bumpeq", "pitchfork", "intercal", "circledcirc", "circledast", "circleddash", "lneq", "gneq",
   "precneqq", "succneqq", "precnapprox", "succnapprox", "lnapprox", "gnapprox", "diagup",
   "diagdown", "subsetneqq", "supsetneqq", "nvdash", "nVdash", "nvDash", "nVDash",
   "ntrianglerighteq", "ntrianglelefteq", "ntriangleleft", "ntriangleright", "divideontimes",
   "Finv", "Game", "ltimes", "rtimes", "succapprox", "precapprox", "digamma",
   "lmoustache", "rmoustache"]

/-- Hand rows of `MathParse.ctrlAtom` that shadow a generated row saying
otherwise: the hand row is what the engine sets, and the difference is a
decision recorded here, both ways — an undeclared disagreement fails, and
so does a declaration whose rows have come to agree. -/
def handDivergences : List (String × String) :=
  [("bullet", "the engine sets U+2219 BULLET OPERATOR, the binary operator; \
unicode-math sets U+2022 BULLET, its \\smblkcircle")]

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

/-- A kernel relation absent from a manual index still reaches both
surfaces as mathematics. Each long double arrow keeps its scalar and the
adjacent exponent, including in an alignment row. -/
def longArrowReportChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  for (name, scalar) in [("Longleftarrow", '⟸'), ("Longrightarrow", '⟹'),
      ("Longleftrightarrow", '⟺')] do
    for aligned in [false, true] do
      let formula := "x^2 \\" ++ name ++ " y"
      let body := if aligned then "\\begin{align*}a &= " ++ formula ++ "\\end{align*}"
        else "$" ++ formula ++ "$"
      let (doc, ds) := elabStr (dvDoc "\\usepackage{amsmath}" body)
      let out := layoutOf fonts doc
      let runs := (bodyLines out).flatMap (·.segs)
      let ink := runs.flatMap fun s => match s with
        | .run _ _ _ _ glyphs _ _ _ _ _ _ => glyphs.map (·.2.1)
        | _ => #[]
      let label := if aligned then "alignment" else "inline"
      t s!"long arrow: {name} ships its scalar in {label}" (ink.contains scalar)
      t s!"long arrow: {name} preserves the neighbouring exponent in {label}"
        (runs.any fun s => match s with
          | .run _ _ _ _ glyphs _ _ _ raise _ _ =>
            raise > 0 && glyphs.any (·.2.1 == '2')
          | _ => false)
      t s!"long arrow: {name} needs no recovery in {label}"
        (!(ds ++ out.diags).any fun d => d.code == "W0012" || d.code == "E0405")
      let (_, tree, _) := HtmlDoc.emitTree { fonts := some fonts } doc
      t s!"long arrow: {name} ships an HTML relation in {label}"
        ((mathLeavesList #[] tree.toList).contains ("mo", String.singleton scalar))

/-- The commands a source spells as one-symbol formulas, `$\name$`, in order. -/
def symbolCalls (src : String) : Array String :=
  ((src.splitOn "$\\").drop 1).toArray.filterMap fun piece =>
    let name := String.ofList (piece.toList.takeWhile Char.isAlpha)
    if !name.isEmpty && (piece.toList.drop name.length).head? == some '$' then some name
    else none

/-- The symbol table against its sources and the shipped math face.

The index side: `testdata/compat-index/<pkg>.txt` carries one row per symbol
command the package declares (`MathSymData.<pkg>`, read off the package file
by the generator), and a row is `impl` exactly when the table sets the name
and `refuse:W0012` exactly when it refuses it — a missing row, a stray one or
a verdict the table contradicts fails. The table side: a hand row that
shadows a generated one says the same or is a declared divergence, since
`lookup` returns the hand row and a disagreement would be a silent override;
no symbol row is a name the parser reads structurally, where the row would
be dead or would change what a script argument means; and a refused name is
unknown to the parser, which is what makes its W0012 the refusal it
declares. The face side: every atom the table sets has a glyph in the
shipped math face or is one of `firaGaps`, and a gap reaches the page as a
named loss, never as silence. -/
def mathSymChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  for (pkg, documented) in [("amsfonts", MathSymData.amsfonts), ("amssymb", MathSymData.amssymb)] do
    let rows := symbolRows (← IO.FS.readFile s!"testdata/compat-index/{pkg}.txt")
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
  let disagree := gen.filter fun (n, cls, c) => match hand.lookup n with
    | some (cls', c') => cls != cls' || c != c'
    | none => false
  for (n, _, _) in disagree do
    t s!"\\{n}: the hand row shadows a generated row that says otherwise, undeclared"
      (handDivergences.any (·.1 == n))
  for (n, _) in handDivergences do
    t s!"handDivergences lists \\{n}, but no hand row of that name shadows a generated row \
that says otherwise"
      (disagree.any (·.1 == n))
  for (n, _, _) in gen do
    t s!"\\{n} is a symbol row the parser reads structurally first"
      (!MathParse.structuralCtrl.contains n && (MathParse.alphaCtrl.lookup n).isNone &&
        (MathParse.accentCtrl.lookup n).isNone && (MathParse.ctrlSpace.lookup n).isNone &&
        (MathParse.ctrlWord.lookup n).isNone)
  for n in MathSymData.refused do
    t s!"\\{n} is refused yet the parser knows it" (!MathParse.knownCtrl n)
  let fira ← match Font.parse (← IO.FS.readBinFile (testFonts ++ "/FiraMath-Regular.otf")) with
    | .ok f => pure f
    | .error e => throw (IO.userError s!"math symbols: FiraMath unparsable: {e}")
  -- The atoms `lookup` answers: each name's first row.
  let effective := MathParse.ctrlAtom.foldl (fun acc r =>
    if acc.any (·.1 == r.1) then acc else acc.push r) #[]
  let uncovered := effective.filter fun (_, _, c) => (fira.gid c).isNone
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
  -- The parity fixtures' engine halves, in HTML: the MathML leaves are the
  -- table's atoms in the source's order — each scalar, under the leaf its
  -- class maps to. The parity tier holds the PDF of the same sources to
  -- lualatex's scalars, so the two artifacts agree through the one table.
  for fixture in ["amssymb", "mathsym"] do
    let src ← IO.FS.readFile s!"testdata/parity/{fixture}.tex"
    let calls := symbolCalls src
    let want := calls.filterMap fun n => (MathParse.ctrlAtom.lookup n).map fun (cls, c) =>
      (MathMl.leafTag cls c, String.ofList [c])
    t s!"parity fixture {fixture}: every symbol it sets is spelled through the table"
      (!calls.isEmpty && want.size == calls.size)
    let (_, body, _) := HtmlDoc.emitTree {} (elabStr src).1
    t s!"parity fixture {fixture}: the HTML sets each symbol as the table's leaf, in order"
      (mathLeavesList #[] body.toList == want)
  longArrowReportChecks ref fs
