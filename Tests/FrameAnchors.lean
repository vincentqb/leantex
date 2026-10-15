module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests

/-- One titled deck stage of an emitted tree: its frame's anchor, its accessible name, the words its
title shows with no snap state (`shownTextList`), and its track's snap anchors. -/
private structure Stage where
  anchor : Option String
  name : Option String
  shown : String
  snaps : Array String

private def classesOf (attrs : Array (String × String)) : List String :=
  ((HtmlDoc.attrOf? attrs "class").getD "").splitOn " "

/-- A stage's record, its title the first `h2` its header carries. -/
private def stageOf (anchor : Option String) (attrs : Array (String × String))
    (kids : Array Html.Node) (snaps : Array String) : Option Stage :=
  let header := kids.filter fun k => k matches .elem "header" ..
  match elemNodesList (· == "h2") #[] header.toList with
  | #[] => none
  | hs => match hs[0]! with
    | .elem _ _ hk => some { anchor, name := HtmlDoc.attrOf? attrs "aria-label"
                             shown := shownTextList "" hk.toList, snaps }
    | _ => none

mutual

/-- Every titled stage of a tree in document order; hand-rolled because a stage's anchor rides its
track. -/
private def stagesOne (acc : Array Stage) : Html.Node → Array Stage
  | .elem tag attrs kids =>
    let cls := classesOf attrs
    if tag == "div" && cls.contains "slide-track" then
      let snaps := kids.filterMap fun k => match k with
        | .elem "div" a _ => if (classesOf a).contains "snap" then HtmlDoc.attrOf? a "id" else none
        | _ => none
      let stage := kids.findSome? fun k => match k with
        | .elem "section" a sk =>
          if (classesOf a).contains "slide" then stageOf (HtmlDoc.attrOf? attrs "id") a sk snaps
          else none
        | _ => none
      match stage with
      | some s => acc.push s
      | none => stagesList acc kids.toList
    else if tag == "section" && cls.contains "slide" then
      match stageOf (HtmlDoc.attrOf? attrs "id") attrs kids #[] with
      | some s => acc.push s
      | none => acc
    else stagesList acc kids.toList
  | .text _ | .style _ | .script _ _ => acc

private def stagesList (acc : Array Stage) : List Html.Node → Array Stage
  | [] => acc
  | k :: rest => stagesList (stagesOne acc k) rest

end

/-- Whether a frame's anchor and name read what its title shows: the shown words' slug (numbered as
`NameClaim.probe` ladders it), and a stepped frame's snaps its anchor and step. -/
private def stageFaithful (s : Stage) : Bool :=
  let words := HtmlDoc.squashSpace s.shown
  let base := Ir.slug #[.text s.shown]
  let numbered (got want sep : String) : Bool :=
    let rest := (got.drop (want ++ sep).length).toString
    got == want || (got.startsWith (want ++ sep) && !rest.isEmpty &&
      rest.all fun c => c.isDigit || c == ')')
  match s.anchor, s.name with
  | some a, some n =>
    !base.isEmpty && numbered a base "-" && numbered n words " (" &&
      s.snaps.toList.zipIdx.all fun (sid, k) => sid == s!"{a}-{k + 1}"
  | _, _ => false

/-- Every `id` a tree carries, in document order. -/
private def idsOf (nodes : Array Html.Node) : Array String :=
  nodes.flatMap (attrValuesOf (fun _ => true) "id")

/-- The alternative every image of a document carries, in document order. -/
private def imageAlts (doc : Ir.Doc) : Array Ir.Alt :=
  Ir.foldBlocks (fun acc _ => acc) (fun acc x => match x with
    | .image _ _ alt => acc.push alt
    | _ => acc) #[] doc.body

/-- A frame's anchor and accessible name are what its title shows at step 1, every assigned anchor
one id, over an invented deck and every corpus deck; captions and title metadata read the same page. -/
def frameAnchorChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let deck := deck169 "\\title{\\textcolor<2>{red}{Invented} Deck}"
    ("\\begin{frame}{\\alert<2>{Placement} of \\textcolor<1>{blue}{Boxes}}\nOne.\n\n" ++
     "\\pause\nTwo.\n\\end{frame}\n" ++
     "\\begin{frame}{\\alt<2>{Second}{First} Reading}\nA.\n\n\\pause\nB.\n\\end{frame}\n" ++
     "\\begin{frame}{Plain Title}\nBody.\n\\end{frame}\n" ++
     "\\begin{frame}{\\uncover<2>{Dimmed} Words}\nX.\n\n\\pause\nY.\n\\end{frame}\n" ++
     "\\begin{frame}{Plain Title}\nAgain.\n\\end{frame}\n" ++
     "\\begin{frame}{\\only<2>{Hidden }Shown}\nX.\n\n\\pause\nY.\n\\end{frame}\n" ++
     "\\begin{frame}{Figure}\n\\begin{figure}\n\\includegraphics{placeholder.png}\n" ++
     "\\caption{\\textcolor<2>{red}{Invented} picture}\n\\end{figure}\n\\end{frame}")
  let (doc, _) := elabStr deck
  let (_, body, _) := HtmlDoc.emitTree {} doc
  let stages := stagesList #[] body.toList
  t "frame anchors: each titled frame is anchored by what its first page shows"
    ((stages.extract 0 5).map (·.anchor) == #[some "placement-of-boxes", some "first-reading",
      some "plain-title", some "dimmed-words", some "plain-title-2"])
  t "frame anchors: each titled frame is named by what its first page shows"
    ((stages.extract 0 5).map (·.name) == #[some "Placement of Boxes", some "First Reading",
      some "Plain Title", some "Dimmed Words", some "Plain Title (2)"])
  t "frame anchors: a caption names the image it captions by what its first page shows"
    (imageAlts doc == #[.described "Invented picture"])
  t "frame anchors: the title metadata is what the title's first page shows"
    (doc.info.title == some "Invented Deck")
  t "frame anchors: a stepped frame's snaps are its anchor and their step"
    ((stages[0]?.map (·.snaps)) == some #["placement-of-boxes-1", "placement-of-boxes-2"])
  t "frame anchors: every stage of the invented deck is faithful to its title"
    (stages.all stageFaithful)
  let ids := idsOf body
  t "frame anchors: every id the invented deck carries is one element's"
    (ids.toList.eraseDups.length == ids.size)
  for name in goldenNames do
    let (fixture, _) ← goldenDoc name
    unless fixture.docClass.record.model == .frame do continue
    let (_, tree, _) := HtmlDoc.emitTree {} fixture
    let stages := stagesList #[] tree.toList
    let unfaithful := stages.filter (!stageFaithful ·)
    t s!"frame anchors: every titled stage of {name} is faithful to its title \
({unfaithful.map (·.anchor)})" unfaithful.isEmpty
    let ids := idsOf tree
    t s!"frame anchors: every id {name} carries is one element's"
      (ids.toList.eraseDups.length == ids.size)

end Tests
