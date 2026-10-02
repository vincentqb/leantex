import Tests.Artifact

open LeanTex.Core

/-- Compare native layout and the actual PDF with an explicitly painted
control. Removing marked-content lines permits the control to omit an
unused alternative's structural leaves; text, colour and geometry remain.
The controls use a 100% colour mix for anonymous, quantized PDF paint,
including the bullet of a wholly covered item. -/
private def singletonWitness (ref : IO.Ref (List String)) (fonts : Font.FontSet)
    (pre label body control : String) (markers : List (String × Ir.Color)) : IO Unit := do
  let t := check ref
  let frame (s : String) := "\\begin{frame}\n" ++ s ++ "\n\\end{frame}\n"
  for mixed in [false, true] do
    let here := "overlay singleton " ++ label ++ if mixed then " mixed" else " alone"
    let source (s : String) := deck169 pre
      (if mixed then
        frame "ClockEarly\n\n\\uncover<2->{ClockLate}" ++ frame s ++ frame "AfterMarker"
       else frame s)
    let (doc, ds) := elabStr (source body)
    let (wantDoc, wantDs) := elabStr (source control)
    let out := layoutOf fonts doc
    let want := layoutOf fonts wantDoc
    t (here ++ ": diagnostics")
      ((ds ++ wantDs ++ out.diags ++ want.diags).all (·.severity == .note))
    let count := if mixed then 4 else 1
    t (here ++ ": page extent") (out.pages.size == count && want.pages.size == count)
    t (here ++ ": layout paint and placement") (shippedBodyGlyphs out == shippedBodyGlyphs want)
    let page := if mixed then 2 else 0
    let one := { out with pages := (out.pages.extract page (page + 1)) }
    let glyphs := shippedBodyGlyphs one
    let text := String.ofList (glyphs.toList.map (·.scalar))
    for (marker, color) in markers do
      t (here ++ ": one " ++ marker) ((text.splitOn marker).length == 2)
      let start := (List.range glyphs.size).find? fun i =>
        (glyphs.extract i (i + marker.length)).toList.map (·.scalar) == marker.toList
      t (here ++ ": paint " ++ marker) (match start with
        | some i => (glyphs.extract i (i + marker.length)).all (·.color == color)
        | none => false)
    let read (d : Ir.Doc) (o : Layout.Out) :=
      readArtifact (driverPdf fonts (Layout.Geom.ofPage d.page) d o)
    match read doc out, read wantDoc want with
    | .ok actual, .ok expected =>
      t (here ++ ": PDF page extent") (actual.size == count && expected.size == count)
      t (here ++ ": PDF paint streams")
        (actual.map (fun p => (p.media, stripMarkLines (String.fromUTF8! p.content))) ==
          expected.map (fun p => (p.media, stripMarkLines (String.fromUTF8! p.content))))
      t (here ++ ": PDF decoded text and placement")
        (actual.map (fun p => p.runs.map fun r => (r.text, r.x, r.y, r.w)) ==
          expected.map (fun p => p.runs.map fun r => (r.text, r.x, r.y, r.w)))
    | .error e, _ => t (here ++ ": PDF read: " ++ e) false
    | _, .error e => t (here ++ ": control PDF read: " ++ e) false

/-- A one-page frame still evaluates overlays at step one. Empty selectors
cover their payload once, active selectors preserve it, and alternation
ships only the selected branch, alone or between other frames. -/
def overlaySingletonChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let seed := (elabStr (deck169Frame "")).1
  let design := Ir.Design.ofDoc seed
  let hot : Ir.Color := { r := 0xAA, g := 0, b := 0 }
  let hex (c : Ir.Color) :=
    s!"#{Ir.Color.hexByte c.r}{Ir.Color.hexByte c.g}{Ir.Color.hexByte c.b}"
  let pre := "\\theme{default}\n\\palette[decorative]{ singlePlain = " ++
    hex design.cover.plain ++ ", singleHot = " ++ hex (design.cover.of hot) ++
    ", hot = " ++ hex hot ++ " }\n"
  let witness := singletonWitness ref fonts pre
  for spec in ["0", "0-0"] do
    let cover (s : String) := "\\uncover<" ++ spec ++ ">{" ++ s ++ "}"
    witness (spec ++ " inline") ("LeadMarker " ++ cover "ProbeMarker")
      "LeadMarker \\textcolor{singlePlain!100}{ProbeMarker}"
      [("LeadMarker", design.fg), ("ProbeMarker", design.cover.plain)]
    witness (spec ++ " block") (cover "ProbeMarker\n\nSecondMarker")
      "\\textcolor{singlePlain!100}{ProbeMarker}\n\n\\textcolor{singlePlain!100}{SecondMarker}"
      [("ProbeMarker", design.cover.plain), ("SecondMarker", design.cover.plain)]
    witness (spec ++ " coloured") (cover "\\hot{ProbeMarker}")
      "\\textcolor{singleHot!100}{ProbeMarker}" [("ProbeMarker", design.cover.of hot)]
    witness (spec ++ " item")
      ("\\begin{itemize}\n\\item<" ++ spec ++ "> ProbeMarker\n\\end{itemize}")
      "\\begin{itemize}\n\\item \\textcolor{singlePlain!100}{ProbeMarker}\n\\end{itemize}"
      [("ProbeMarker", design.cover.plain)]
    for (kind, nested) in
        [("outer", cover "\\uncover<1>{ProbeMarker}"),
         ("inner", "\\uncover<1>{" ++ cover "ProbeMarker" ++ "}"),
         ("both", cover (cover "\\hot{ProbeMarker}"))] do
      let colored := kind == "both"
      witness (spec ++ " nested " ++ kind) nested
        (if colored then "\\textcolor{singleHot!100}{ProbeMarker}" else "\\textcolor{singlePlain!100}{ProbeMarker}")
        [("ProbeMarker", if colored then design.cover.of hot else design.cover.plain)]
    witness (spec ++ " covered alt") (cover "\\alt<1>{ProbeMarker}{LostMarker}")
      "\\textcolor{singlePlain!100}{ProbeMarker}" [("ProbeMarker", design.cover.plain)]
    witness (spec ++ " alt covering")
      ("\\alt<" ++ spec ++ ">{LostMarker}{\\uncover<0>{ProbeMarker}}")
      "\\textcolor{singlePlain!100}{ProbeMarker}" [("ProbeMarker", design.cover.plain)]
  for (spec, active) in
      [("0", false), ("0-0", false), ("1", true), ("1-1", true),
       ("0-1", true), ("0-", true), ("1-", true), ("0,1", true)] do
    let selected := if active then "AmberMarker" else "BlueMarker"
    witness (spec ++ " alt inline")
      ("LeadMarker \\alt<" ++ spec ++ ">{AmberMarker}{BlueMarker}")
      ("LeadMarker " ++ selected) [("LeadMarker", design.fg), (selected, design.fg)]
    witness (spec ++ " alt block")
      ("\\alt<" ++ spec ++ ">{AmberMarker\n\nFirstMarker}{BlueMarker\n\nOtherMarker}")
      (selected ++ "\n\n" ++ if active then "FirstMarker" else "OtherMarker")
      [(selected, design.fg)]
    if active then
      witness (spec ++ " active inline")
        ("LeadMarker \\uncover<" ++ spec ++ ">{\\hot{ProbeMarker}}")
        "LeadMarker \\hot{ProbeMarker}" [("LeadMarker", design.fg), ("ProbeMarker", hot)]
      witness (spec ++ " active block")
        ("\\uncover<" ++ spec ++ ">{ProbeMarker\n\nSecondMarker}")
        "ProbeMarker\n\nSecondMarker" [("ProbeMarker", design.fg), ("SecondMarker", design.fg)]
  witness "ordinary identity" "LeadMarker \\hot{ProbeMarker}\n\nSecondMarker"
    "\\uncover<1>{LeadMarker \\hot{ProbeMarker}\n\nSecondMarker}"
    [("LeadMarker", design.fg), ("ProbeMarker", hot), ("SecondMarker", design.fg)]
