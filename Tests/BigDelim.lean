import Tests.Support

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-- A math list's atoms, class and nucleus, in order. -/
def mathAtoms : Math.MList → List (Math.MathClass × Math.MNucleus)
  | .nil => []
  | .cons (.atom cls nuc _ _ _) rest => (cls, nuc) :: mathAtoms rest
  | .cons (.space _) rest => mathAtoms rest
  | .cons (.ink _ _) rest => mathAtoms rest

/-- The shipped glyphs set in `face`: each glyph's id, its run's size, and
its ink top and bottom about the line's baseline, from the face's outline
bounds at the run's size. -/
def faceGlyphInk (fs : Font.FontSet) (face : Nat) (out : Layout.Out) :
    Array (Char × Nat × Dim.Sp × Dim.Sp × Dim.Sp) := Id.run do
  let mut acc := #[]
  for l in bodyLines out do
    for s in l.segs do
      match s with
      | .run fi _ _ _ glyphs size _ _ raise _ _ =>
        if fi == face then
          for (g, c, _) in glyphs do
            if let some f := fs.fonts[fi]? then
              let (lo, hi) := (f.yExtent g).getD (0, 0)
              let upem : Int := f.unitsPerEm
              acc := acc.push (c, g, size, raise + hi * size / upem, raise + lo * size / upem)
      | .gap _ _ | .decoratedGap _ _ _ | .decoration _ _ _ _ _
      | .rule _ _ _ _ | .image _ _ _ | .poly _ _ => pure ()
  return acc

/-- A shipped line's reach above and below its baseline: every run's ink,
and each glyph-free construction's explicit bounds at its raise. -/
def lineReach (fs : Font.FontSet) (l : Layout.LineOut) : Dim.Sp × Dim.Sp :=
  l.segs.foldl (init := (0, 0)) fun (top, bot) s =>
    match s with
    | .run fi _ _ _ glyphs size metrics _ raise _ _ =>
      if glyphs.isEmpty then
        match metrics.math with
        | some m => (max top (raise + m.top), min bot (raise + m.bottom))
        | none => (max top raise, min bot raise)
      else
      glyphs.foldl (init := (top, bot)) fun (top, bot) (g, _, _) =>
        match fs.fonts[fi]? with
        | some f =>
          let (lo, hi) := (f.yExtent g).getD (0, 0)
          let upem : Int := f.unitsPerEm
          (max top (raise + hi * size / upem), min bot (raise + lo * size / upem))
        | none => (top, bot)
    | .gap _ _ | .decoratedGap _ _ _ | .decoration _ _ _ _ _
    | .rule _ _ _ _ | .image _ _ _ | .poly _ _ => (top, bot)

/-- amsmath's sized delimiters, `\big` through `\Bigg` in their four classes
(amsmath.sty `\bBigg@`: `\left` grown around a `\vcenter` of 1, 1.5, 2 and
2.5 times `\big@size`, which is 1.2 times the height and depth of the text
font's `(`). Each was the math parser's decline (W0012), which set the whole
formula as its source text; every row here failed there. -/
def bigDelimChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let doc (body : String) : String :=
    "\\documentclass{article}\n\\usepackage{amsmath}\n\\begin{document}\n" ++ body ++
      "\n\\end{document}"
  let atoms (body : String) : Option (List (Math.MathClass × Math.MNucleus)) :=
    (firstFormula (elabStr (doc body)).1).map mathAtoms
  let declines (body : String) : Bool :=
    (elabStr (doc body)).2.any (·.code == "W0012")
  -- ir tier: the class each spelling sets, and the size step it carries
  t "\\bigl and \\bigr open and close at the \\big step"
    ((atoms "$\\bigl(x\\bigr)$").map (·.map (·.1)) ==
      some [.opening, .ord, .closing] &&
     ((atoms "$\\bigl(x\\bigr)$").bind (·.head?)).map (·.2) == some (.big (some '(') 2) &&
     !declines "$\\bigl(x\\bigr)$")
  t "the four sizes step in halves of \\big@size"
    ((["big", "Big", "bigg", "Bigg"].map fun n =>
      ((atoms s!"$\\{n}l(x\\{n}r)$").bind (·.head?)).map (·.2)) ==
      [2, 3, 4, 5].map fun s => some (.big (some '(') s))
  t "\\bigm is a relation and \\big an ordinary atom"
    ((atoms "$a\\bigm|b$").map (·.map (·.1)) == some [.ord, .rel, .ord] &&
     (atoms "$\\big/$").map (·.map (·.1)) == some [.ord])
  t "a named delimiter and the empty one are read as \\left reads them"
    (((atoms "$\\Bigl\\langle x\\Bigr\\rangle$").bind (·.head?)).map (·.2) ==
      some (.big (some '\u27E8') 3) &&
     ((atoms "$\\bigl.x\\bigr|$").bind (·.head?)).map (·.2) == some (.big none 2) &&
     !declines "$\\bigl.x\\bigr|_{0}$")
  -- The page, against lualatex's \showbox of the same formulas under the
  -- test face (FiraMath, unicode-math, 10pt): in thousandths of the math
  -- size, the glyph each step selects (its ink, the variant) and the box's
  -- reach, which is its `\vcenter` wherever that stands past the glyph. ±1
  -- is \showbox's rounding.
  match ← serifFacesSet with
  | none => failures ref "big delimiters: the shipped serif faces did not load"
  | some fs =>
    let near (a b : Int) : Bool := (a - b).natAbs ≤ 1
    let permille (x size : Dim.Sp) : Int := x * 1000 / size
    let parens (body : String) :=
      (faceGlyphInk fs 4 (layoutOf fs (elabStr (doc body)).1)).toList.filter (·.1 == '(')
    let shipped := parens "$(\\bigl(\\Bigl(\\biggl(\\Biggl($"
    t "each step ships the variant lualatex selects"
      (shipped.length == 5 &&
       (shipped.zip [990, 1319, 1647, 2303, 2959]).all fun ((_, _, size, top, bot), h) =>
         near (permille (top - bot) size) h)
    let reach (body : String) : Option (Int × Int) :=
      let out := layoutOf fs (elabStr (doc body)).1
      match (bodyLines out)[0]?, (parens body).head? with
      | some l, some (_, _, size, _, _) =>
        let (top, bot) := lineReach fs l
        some (permille top size, permille (-bot) size)
      | _, _ => none
    t "the box reaches its \\vcenter, or its glyph where that stands past it"
      ((["\\bigl(", "\\Bigl(", "\\biggl(", "\\Biggl("].map fun d => reach s!"${d}$").zip
        [(940, 380), (1171, 611), (1468, 908), (1765, 1205)] |>.all fun (r, (a, b)) =>
          match r with
          | some (top, bot) => near top a && near bot b
          | none => false)
    t "a sized delimiter in a script is the text-size one, as lualatex sets it"
      (match (parens "$\\bigl($").head?, (parens "$x_{\\bigl(}$").head? with
       | some (_, g, s, t1, b1), some (_, g', s', t2, b2) =>
         g == g' && s == s' && t1 - b1 == t2 - b2
       | _, _ => false)
  -- HTML: MathML's stretch clamp at the PDF's own target (`Math.bigTarget`
  -- in em), which Chromium resolves to TeX's variant at every step in Latin
  -- Modern Math; the `\vcenter` itself (1.2 em at `\big`) set one variant
  -- too tall there.
  let html (body : String) : String := (HtmlDoc.emit {} (elabStr (doc body)).1).1
  t "the MathML stretches each to the PDF's target"
    (hasStr (html "$\\bigl(x$") "minsize=\"1.081em\" maxsize=\"1.081em\"" &&
     hasStr (html "$\\Bigl(x$") "minsize=\"1.621em\" maxsize=\"1.621em\"" &&
     hasStr (html "$\\biggl(x$") "minsize=\"2.162em\" maxsize=\"2.162em\"" &&
     hasStr (html "$\\Biggl(x$") "minsize=\"2.703em\" maxsize=\"2.703em\"")
