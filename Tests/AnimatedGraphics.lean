import Tests.Support

open LeanTex.Core

namespace Tests

/-- The image boxes a reader receives, including the store entry whose
pixels or PDF form the writer embeds. A placeholder cannot pass this
check as a successfully lowered animation. -/
private def animatedImageSegs (out : Layout.Out) :
    Array (Option Nat × Dim.Sp × Dim.Sp) :=
  (allLines out).foldl (fun acc line =>
    line.segs.foldl (fun acc seg => match seg with
      | .image idx w h => acc.push (idx, w, h)
      | _ => acc) acc) #[]

private def graphicsInk (out : Layout.Out) : String :=
  (bodyLines out).foldl (fun s l => s ++ lineInk l) ""

private structure GraphicsPage where
  images : Array (Option Nat × Dim.Sp × Dim.Sp)
  ink : String
  tree : Array Html.Node
  diags : Array Diag

/-- Read the two artifacts after elaboration. Synthetic store entries
have distinct request identities and browser paths, so a source-only
lookup cannot accidentally satisfy a page-selection check. -/
private def graphicsPage (fonts : Font.FontSet) (imgs : Image.Store)
    (pre body : String) : GraphicsPage :=
  let (doc, diags) := elabStr (dvDoc pre body)
  let out := layoutOf fonts doc (imgs := imgs)
  let (_, tree, _) := HtmlDoc.emitTree { imgs } doc
  { images := animatedImageSegs out, ink := graphicsInk out, tree, diags }

private def graphicsPng (w h : Nat) : Option Image.Plan :=
  (Image.decode (mkPng (pngChunk "IHDR" (pngIhdr w h 8 2 0) ++
    pngChunk "IDAT" [1, 2, 3] ++ pngChunk "IEND" []))).toOption

private def graphicsSizingAttrs (p : GraphicsPage) : Array (Array (String × String)) :=
  (elemAttrsList (· == "img") #[] p.tree.toList).map fun (_, attrs) =>
    attrs.filter (·.1 != "src")

/-- An animation command owns four mandatory groups. Its frame rate,
source and range must never become paragraph ink; the tail must survive.
The witnesses are shipped layout and typed HTML, with an ordinary image
as the text/size control. The initial five artifact assertions failed on
a9116a2 before lowering existed. The PNG plans here isolate request
dispatch and sizing; multipage decoding and SVG fulfilment have their own
guards. Animation frames share dimensions, as the animate manual §6.1
sizes the widget from the first frame even when another poster is chosen. -/
def animatedGraphicsChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let info := graphicsPng 64 40
  t "animation regression has a decoded image" info.isSome
  let imgs : Image.Store := { entries := #[
    { src := "animation-probe", animated := true, href := "animation-probe.svg", info },
    { src := "animation-probe", href := "page-default.png", info },
    { src := "animation-probe", animated := true, page := .number 1,
      href := "poster-zero.svg", info },
    { src := "animation-probe", animated := true, page := .number 2,
      href := "poster-one.svg", info },
    { src := "animation-probe", animated := true, page := .last,
      href := "poster-last.svg", info },
    { src := "animation-probe", page := .number 1, href := "page-one.png", info },
    { src := "animation-probe", page := .number 2,
      href := "page-two.png", info := graphicsPng 48 96 },
    { src := "animation-probe", page := .number 3,
      href := "page-three.png", info := graphicsPng 80 20 }] }
  let source := dvDoc "" "Lead \\animategraphics[width=32pt,alt={Moving square}]\
    {17}{animation-probe}{}{} Tail"
  let control := dvDoc "" "Lead \\includegraphics[width=32pt,alt={Moving square}]\
    {animation-probe} Tail"
  let (doc, ds) := elabStr source
  let (plain, _) := elabStr control
  let out := layoutOf fonts doc (imgs := imgs)
  let expected := layoutOf fonts plain (imgs := imgs)
  t "animategraphics ships exactly one decoded image at its declared size"
    (animatedImageSegs out == #[(some 0, Dim.pt 32, Dim.pt 20)])
  t "animategraphics consumes fps and path and preserves the shipped tail"
    (graphicsInk out == graphicsInk expected && hasStr (graphicsInk out) "Tail")
  let (_, tree, _) := HtmlDoc.emitTree { imgs } doc
  let (_, plainTree, _) := HtmlDoc.emitTree { imgs } plain
  t "animategraphics emits exactly one typed HTML image"
    ((HtmlDoc.imgSrcsList #[] tree.toList).size == 1)
  t "animategraphics consumes all four groups in the typed HTML page"
    (shownTextList "" tree.toList == shownTextList "" plainTree.toList &&
      treeShownOccurs tree "Tail" == 1)
  t "animategraphics preserves its image alternative"
    ((elemAttrsList (· == "img") #[] tree.toList).any fun (_, attrs) =>
      attrs.contains ("alt", "Moving square"))

  let playback := ds.filter (·.subject == some "animategraphics:playback")
  t "animation names the static PDF, optional SVG companion, rate and controls"
    (playback.size == 1 && playback.all fun d =>
      d.code == "W0110" && d.severity == .warning &&
      hasStr d.message "static PDF poster without PDF JavaScript" &&
      hasStr d.message "HTML uses the companion SVG when present, otherwise the same static poster" &&
      hasStr d.message "SVG owns timing" && hasStr d.message "frame rate '17'" &&
      hasStr d.message "playback controls are not applied")
  t "animation sizes and alternatives add no unsupported-option warning"
    (ds.all fun d => d.severity == .note ||
      (d.code == "W0110" && d.subject == some "animategraphics:playback"))

  let opts (keys : String) := "[alt={Moving square}" ++
    (if keys.isEmpty then "" else "," ++ keys) ++ "]"
  let animate (keys first last : String) := "\\animategraphics" ++ opts keys ++
    "{17}{animation-probe}{" ++ first ++ "}{" ++ last ++ "}"
  let graphic (keys : String) := "\\includegraphics" ++ opts keys ++ "{animation-probe}"
  let page := graphicsPage fonts imgs
  let imageSrcs (p : GraphicsPage) := HtmlDoc.imgSrcsList #[] p.tree.toList
  let text (p : GraphicsPage) := shownTextList "" p.tree.toList
  let selected (p : GraphicsPage) (idx : Nat) (w h : Dim.Sp) : Bool :=
    p.images == #[(some idx, w, h)] &&
      imageSrcs p == #["assets/" ++ HtmlDoc.imageAssetName idx (imgs.entries[idx]!).href]

  -- animate manual §§5–6.1: first is the default; numbers count frames
  -- from zero. The exact identities also distinguish numeric zero from
  -- graphicx's numeric page one while both address the first PDF page.
  let posters : Array (String × Nat) := #[
    ("", 0), ("poster", 0), ("poster=first", 0), ("poster=0", 2),
    ("poster=1", 3), ("poster={1}", 3), ("poster=last", 4),
    ("poster=last,poster", 0), ("poster=none,poster=last", 4),
    ("every=1,type=pdf", 0), ("every=2,every=1,type=png,type=pdf", 0)]
  for (keys, idx) in posters do
    let sized := if keys.isEmpty then "width=32pt" else keys ++ ",width=32pt"
    let p := page "" ("Lead" ++ animate sized "" "" ++ "Tail")
    t s!"animation poster '{keys}' selects its own shipped image and HTML source"
      (selected p idx (Dim.pt 32) (Dim.pt 20))
    t s!"animation poster '{keys}' keeps exactly its named playback loss"
      (p.diags.all fun d => d.severity == .note ||
        (d.code == "W0110" && d.subject == some "animategraphics:playback"))

  -- graphicx.sty Gin/page and a synthetic three-page LuaLaTeX probe:
  -- default = first, numeric pages start at one, and page=0 / page=last
  -- are errors. Distinct dimensions witness that infoRequest? is used as
  -- well as findRequest? and the HTML source lookup.
  let pages : Array (String × Nat × Int × Int) := #[
    ("", 1, 64, 40), ("page=1", 5, 64, 40),
    ("page=2", 6, 48, 96), ("page={2}", 6, 48, 96),
    ("page=3", 7, 80, 20), ("page=3,page=2", 6, 48, 96)]
  for (keys, idx, w, h) in pages do
    let p := page "" ("Lead" ++ graphic keys ++ "Tail")
    t s!"graphicx '{keys}' selects its own dimensions and HTML source"
      (selected p idx (Dim.pt w) (Dim.pt h))
    t s!"graphicx '{keys}' is implemented without a warning"
      (p.diags.all (·.severity == .note))
  let localChoices := page "" (animate "poster=last,width=16pt" "" "" ++
    graphic "page=2,width=16pt" ++ graphic "width=16pt" ++ animate "width=16pt" "" "")
  t "page and animation choices are local to each command"
    (localChoices.images == #[
      (some 4, Dim.pt 16, Dim.pt 10), (some 6, Dim.pt 16, Dim.pt 32),
      (some 1, Dim.pt 16, Dim.pt 10), (some 0, Dim.pt 16, Dim.pt 10)])
  t "typed HTML keeps the four scoped requests in source order"
    (imageSrcs localChoices == #["assets/i4-poster-last.svg", "assets/i6-page-two.png",
      "assets/i1-page-default.png", "assets/i0-animation-probe.svg"])

  let sizes : Array (String × Int × Int) := #[
    ("width=32pt", 32, 20), ("height=10pt", 16, 10),
    ("totalheight=10pt", 16, 10), ("scale=0.5", 32, 20),
    ("width=40pt,height=40pt", 40, 40),
    ("width=40pt,height=40pt,keepaspectratio", 40, 25),
    ("width=40pt,height=40pt,keepaspectratio=true", 40, 25),
    ("width=40pt,height=40pt,keepaspectratio=false", 40, 40)]
  for (keys, w, h) in sizes do
    let p := page "" (animate keys "" "")
    let c := page "" (graphic keys)
    t s!"animation sizing '{keys}' preserves inherited size fields"
      (selected p 0 (Dim.pt w) (Dim.pt h) && graphicsSizingAttrs p == graphicsSizingAttrs c)
  let extra := page "" ("Lead" ++ animate "width=32pt" "" "" ++ "{Extra}Tail")
  let extraControl := page "" ("Lead" ++ graphic "width=32pt" ++ "{Extra}Tail")
  t "animation stops after its fourth group and preserves a following group"
    (extra.ink == extraControl.ink && text extra == text extraControl &&
      treeShownOccurs extra.tree "Extra" == 1)
  let spaced := page "" ("Lead\\animategraphics[width=32pt,alt={Moving square}]\n" ++
    "{17} \n {animation-probe} \n {} \n {}Tail")
  t "animation consumes groups separated by spaces and newlines"
    (selected spaced 0 (Dim.pt 32) (Dim.pt 20) &&
      !hasStr spaced.ink "17" && !hasStr spaced.ink "animation-probe" &&
      treeShownOccurs spaced.tree "Tail" == 1)

  let controlled := page "" (animate "poster=1,controls,autoplay,loop,palindrome,nomouse" "" "")
  t "animation controls are named once at the use without losing the selected poster"
    (selected controlled 3 (Dim.pt 64) (Dim.pt 40) &&
      (controlled.diags.filter (·.code == "W0110")).size == 1 &&
      controlled.diags.any fun d => d.subject == some "animategraphics:playback" &&
        ["controls", "autoplay", "loop", "palindrome", "nomouse"].all (hasStr d.message))
  let native := page "\\usepackage{animate}\n" (animate "" "" "")
  t "native animate loading still diagnoses playback at the command"
    (selected native 0 (Dim.pt 64) (Dim.pt 40) &&
      native.diags.any (·.code == "N0100") &&
      native.diags.all fun d => d.severity == .note ||
        (d.code == "W0110" && d.subject == some "animategraphics:playback"))
  let globalDefaults := page "\\usepackage[poster=last,controls]{animate}\n" (animate "" "" "")
  t "unsupported package defaults are named and do not masquerade as local selection"
    (globalDefaults.images == native.images && imageSrcs globalDefaults == imageSrcs native &&
      globalDefaults.diags.any (fun d => d.code == "W0110" &&
        d.subject == some "animate:package-options" &&
        hasStr d.message "poster=last,controls") &&
      globalDefaults.diags.all fun d => d.severity == .note ||
        (d.code == "W0110" &&
          (d.subject == some "animate:package-options" ||
            d.subject == some "animategraphics:playback")))
  let unknown := page "\\usepackage{animate}\n" "\\UnknownAnimationProbe{Kept}Tail"
  t "native animate does not silence arbitrary unknown commands or their arguments"
    (unknown.diags.any (·.code == "W0301") && hasStr unknown.ink "Kept" &&
      treeShownOccurs unknown.tree "Kept" == 1)

  -- Every refused source still owns all four groups. Nothing at that
  -- site becomes ink, and the following text is the unchanged control.
  let absent := page "" "LeadTail"
  let refusals : Array (String × String) := #[
    (animate "" "0" "2", "nonempty first/last"),
    (animate "" "" "2", "nonempty first/last"),
    (animate "" "1" "", "nonempty first/last"),
    (animate "" "9" "2", "numbered file sequences"),
    (animate "" "0000" "0009", "numbered file sequences"),
    (animate "poster=none" "" "", "poster=none"),
    (animate "timeline=frames.txt" "" "", "timeline=frames.txt"),
    (animate "every=2" "" "", "every=2"),
    (animate "type=png" "" "", "type=png")]
  for (call, why) in refusals do
    let p := page "" ("Lead" ++ call ++ "Tail")
    t s!"refused animation '{why}' consumes all groups without argument ink"
      (p.images.isEmpty && (imageSrcs p).isEmpty &&
        p.ink == absent.ink && text p == text absent)
    t s!"refused animation '{why}' carries one keyed loss and no error"
      ((p.diags.filter (·.code == "W0307")).size == 1 &&
        p.diags.any (fun d => d.code == "W0307" &&
          d.subject == some "animategraphics:source" && hasStr d.message why) &&
        p.diags.all fun d => d.severity == .note || d.code == "W0307")
  for keys in ["page=0", "page=-1", "page=1.5", "page=last", "page=bad"] do
    let p := page "" ("Lead" ++ graphic keys ++ "Tail")
    t s!"invalid graphicx '{keys}' is E0321 without a wrong page or argument ink"
      (p.diags.any (·.code == "E0321") && p.images.isEmpty &&
        (imageSrcs p).isEmpty && p.ink == absent.ink && text p == text absent)
  for keys in ["poster=-1", "poster=1.5", "poster=bad"] do
    let p := page "" ("Lead" ++ animate keys "" "" ++ "Tail")
    t s!"invalid animation '{keys}' consumes its arguments and names the bad value"
      (p.diags.any (·.code == "E0321") && p.images.isEmpty &&
        (imageSrcs p).isEmpty && p.ink == absent.ink && text p == text absent)
  for groups in ["", "{17}", "{17}{animation-probe}", "{17}{animation-probe}{}"] do
    let p := page "" ("Lead\\animategraphics[width=32pt]" ++ groups ++ "Tail")
    t s!"incomplete animation '{groups}' consumes supplied groups and preserves tail"
      (p.diags.any (·.code == "E0304") && p.images.isEmpty &&
        (imageSrcs p).isEmpty && p.ink == absent.ink && text p == text absent)

end Tests
