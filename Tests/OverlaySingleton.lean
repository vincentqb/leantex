module

public import Tests.Artifact

public section

open LeanTex.Core

/-- Compares native layout and the PDF with an explicitly painted control, marked-content lines
removed; `controlPre` declares what the control alone paints. -/
private def singletonWitness (ref : IO.Ref (List String)) (fonts : Font.FontSet)
    (base : String) (colours : List (String × String)) (label body control : String)
    (markers : List (String × Ir.Color)) (controlPre : String := "") : IO Unit := do
  let t := check ref
  let preOf (s : String) : String :=
    let painted := colours.filter fun (name, _) => hasStr s name
    base ++ if painted.isEmpty then "" else
      "\\palette[decorative]{ " ++ ", ".intercalate (painted.map fun (n, v) => n ++ " = " ++ v) ++
        " }\n"
  let frame (s : String) := "\\begin{frame}\n" ++ s ++ "\n\\end{frame}\n"
  for mixed in [false, true] do
    let here := "overlay singleton " ++ label ++ if mixed then " mixed" else " alone"
    let source (extra s : String) := deck169 (preOf (extra ++ s) ++ extra)
      (if mixed then
        frame "ClockEarly\n\n\\uncover<2->{ClockLate}" ++ frame s ++ frame "AfterMarker"
       else frame s)
    let (doc, ds) := elabStr (source "" body)
    let (wantDoc, wantDs) := elabStr (source controlPre control)
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

/-- A one-page frame evaluates overlays at step one: empty selectors cover once, active ones keep,
alternation ships the selected branch. -/
def overlaySingletonChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let seed := (elabStr (deck169Frame "")).1
  let design := Ir.Design.ofDoc seed
  let hot : Ir.Color := { r := 0xAA, g := 0, b := 0 }
  let base := "\\theme{default}\n\\palette{ covered = 38\\% }\n"
  let colours := [("singlePlain", design.inkCover.hex), ("singleHot", (design.cover.of hot).hex),
    ("hot", hot.hex)]
  let witness := singletonWitness ref fonts base colours
  let bullet := Ir.plainText (ListMark.marker false 1 1 fun c =>
    (fonts.body.gid c).isSome || (fonts.fallbackFor c).isSome)
  for spec in ["0", "0-0"] do
    let cover (s : String) := "\\uncover<" ++ spec ++ ">{" ++ s ++ "}"
    witness (spec ++ " inline") ("LeadMarker " ++ cover "ProbeMarker")
      "LeadMarker \\textcolor{singlePlain!100}{ProbeMarker}"
      [("LeadMarker", design.fg), ("ProbeMarker", design.inkCover)]
    witness (spec ++ " block") (cover "ProbeMarker\n\nSecondMarker")
      "\\textcolor{singlePlain!100}{ProbeMarker}\n\n\\textcolor{singlePlain!100}{SecondMarker}"
      [("ProbeMarker", design.inkCover), ("SecondMarker", design.inkCover)]
    witness (spec ++ " coloured") (cover "\\hot{ProbeMarker}")
      "\\textcolor{singleHot!100}{ProbeMarker}" [("ProbeMarker", design.cover.of hot)]
    -- The covered item's marker is covered with it; the control paints its marker so.
    singletonWitness ref fonts base colours (spec ++ " item")
      ("\\begin{itemize}\n\\item<" ++ spec ++ "> ProbeMarker\n\\end{itemize}")
      "\\begin{itemize}\n\\item \\textcolor{singlePlain!100}{ProbeMarker}\n\\end{itemize}"
      [("ProbeMarker", design.inkCover)]
      (controlPre := "\\style{itemize}{ marker = {\\textcolor{singlePlain!100}{" ++ bullet ++ "}} }\n")
    for (kind, nested) in
        [("outer", cover "\\uncover<1>{ProbeMarker}"),
         ("inner", "\\uncover<1>{" ++ cover "ProbeMarker" ++ "}"),
         ("both", cover (cover "\\hot{ProbeMarker}"))] do
      let colored := kind == "both"
      witness (spec ++ " nested " ++ kind) nested
        (if colored then "\\textcolor{singleHot!100}{ProbeMarker}" else "\\textcolor{singlePlain!100}{ProbeMarker}")
        [("ProbeMarker", if colored then design.cover.of hot else design.inkCover)]
    witness (spec ++ " covered alt") (cover "\\alt<1>{ProbeMarker}{LostMarker}")
      "\\textcolor{singlePlain!100}{ProbeMarker}" [("ProbeMarker", design.inkCover)]
    witness (spec ++ " alt covering")
      ("\\alt<" ++ spec ++ ">{LostMarker}{\\uncover<0>{ProbeMarker}}")
      "\\textcolor{singlePlain!100}{ProbeMarker}" [("ProbeMarker", design.inkCover)]
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
