module

public import LeanTex.Core.StageNames
public import LeanTex.Core.Outline

namespace LeanTex.Core.Ir

/-! A table of contents' entries, read off the document's headings once its body is known. -/

/-- How beamer's options set a section: as the current one or as another. -/
private def sectionShow (spec : ContentsSpec) (s1 : Nat) : ContentsShow :=
  if s1 == spec.current.1 then spec.sections.1 else spec.sections.2

/-- How beamer's options set a subsection: as the current one, as another of the current section,
or as one of another section. -/
private def subsectionShow (spec : ContentsSpec) (s1 s2 : Nat) : ContentsShow :=
  if s1 == spec.current.1 then
    if s2 == spec.current.2.1 then spec.subsections.1 else spec.subsections.2.1
  else spec.subsections.2.2

/-- How beamer's options set a subsubsection: as the current one, as another of the current
subsection, as one of the current section's other subsections, or as one of another section. -/
private def subsubsectionShow (spec : ContentsSpec) (s1 s2 s3 : Nat) : ContentsShow :=
  if s1 == spec.current.1 then
    if s2 == spec.current.2.1 then
      if s3 == spec.current.2.2 then spec.subsubsections.1 else spec.subsubsections.2.1
    else spec.subsubsections.2.2.1
  else spec.subsubsections.2.2.2

/-- Whether beamer's `sections=` lists section `s1`, every section where it names none. -/
private def listedSection (spec : ContentsSpec) (s1 : Nat) : Bool :=
  match spec.listed with
  | none => true
  | some ranges => ranges.any fun (a, b) => a ≤ s1 && (b.all (s1 ≤ ·))

/-- The stage each top-level block opens onto: a section page's route where the block is a section
standing on one, else the anchor of the next frame after it. -/
private def nextStages (doc : Doc) : Array (Option String) := Id.run do
  let frames := frameAnchors doc.body
  let routes := doc.sectionRoutes
  let mut next : Option String := none
  let mut out : List (Option String) := []
  for k in [0:doc.body.size] do
    let i := doc.body.size - 1 - k
    out := ((routes[i]?.join).orElse fun _ => next) :: out
    if let some (some fa) := frames[i]? then next := some fa.frame.id
  return out.toArray

/-- Whether a title has no words to list or link: only spaces, a tie's among them. -/
private def blankTitle (title : Array Inline) : Bool :=
  (plainText title).all fun c => c.isWhitespace || c == '\u00A0'

/-- A shaded entry's declared colours at the share it keeps over the page, mixed in sRGB as beamer's
`colormixin` mixes every colour inside it. -/
private def shadeDeclared (bg : Color) (xs : Array Inline) : Array Inline :=
  mapInlines id xs (finish := fun ys => ys.map fun x =>
    if let .colored c _ b := x then .colored (c.mix contentsShadeShare bg) none b else x)

/-- One entry, unless its options hide it, a shaded one's declared colours mixed over `bg`. -/
private def entryUnless (bg : Color) (look : ContentsShow) (e : ContentsEntry) :
    Option ContentsEntry :=
  if look == .hidden then none
  else if look == .shaded then some { e with shaded := true, title := shadeDeclared bg e.title }
  else some { e with shaded := false }

/-- The entries a deck's `\tableofcontents` lists, as beamerbasetoc.sty's: its unstarred titled
headings to the depth, unnumbered, a subsubsection's in `\footnotesize`, each opening the stage set
next, shown, shaded or hidden as the options set it about the heading in force. -/
public def deckContents (doc : Doc) (spec : ContentsSpec) : Array ContentsEntry := Id.run do
  let stages := nextStages doc
  let mut out : Array ContentsEntry := #[]
  let mut counts : Nat × Nat × Nat := (0, 0, 0)
  let mut paused := 0
  for h : i in [0:doc.body.size] do
    if let .section level starred _ title := doc.body[i] then
      let (s1, s2, s3) := counts
      counts := if level == .h2 then (s1 + 1, 0, 0) else if level == .h3 then (s1, s2 + 1, 0)
        else if level == .h4 then (s1, s2, s3 + 1) else counts
      let (s1, s2, s3) := counts
      let at? : Option (Nat × ContentsShow) := if level == .h2 then some (0, sectionShow spec s1)
        else if level == .h3 then some (1, subsectionShow spec s1 s2)
        else if level == .h4 then some (2, subsubsectionShow spec s1 s2 s3) else none
      if let some (depth, look) := at? then
        let look := if listedSection spec s1 then look else .hidden
        if !starred && !blankTitle title && depth < spec.depth then
          -- beamerbasetoc.sty pauses before an entry's hiding is decided.
          if (if depth == 0 then spec.pauses.1 else spec.pauses.2) then paused := paused + 1
          let shown := if depth == 2 then #[.styled (.size "footnotesize") (nameOf title)]
            else nameOf title
          if let some e := entryUnless (Design.ofPalette doc.palette).bg look
              { depth, number := none, title := shown, target := stages[i]?.join, shaded := false } then
            out := out.push (if paused ≤ 1 then e
              else { e with title := #[.onSteps { first := paused, last := none } e.title] })
  return out

/-- The rank a flow's contents list a heading at, LaTeX's section level: a section one, a
subsection two, a subsubsection three, a paragraph four. -/
private def contentsLevel : HeadingLevel → Option Nat
  | .h2 => some 1
  | .h3 => some 2
  | .h4 => some 3
  | .h5 => some 4
  | .h6 => some 5
  | .title | .h1 => none

/-- The entries a flow's `\tableofcontents` lists: its unstarred headings down to the depth, each by
its short title where it declared one, as article's, and opening its heading. -/
public def flowContents (doc : Doc) (spec : ContentsSpec) : Array ContentsEntry := Id.run do
  let anchors := flowAnchors doc.body
  let shorts := shortTitlesAt doc.shortTitles doc.body
  let mut out : Array ContentsEntry := #[]
  for h : i in [0:doc.body.size] do
    if let .section level starred num title := doc.body[i] then
      if let some rank := contentsLevel level then
        if !starred && rank ≤ spec.depth then
          let target := (anchors[i]?.join).map (·.id)
          let title := nameOf (listedTitleAt shorts i title)
          out := out.push { depth := rank - 1, number := num, target, shaded := false
                            title := if blankTitle title then #[] else title }
  return out

mutual

/-- A block with every table of contents in it replaced by what `f` makes of its options and
entries. -/
-- conserves: none — rewrites a table of contents, every other block kept.
private def rewriteContentsOne (f : ContentsSpec → Array ContentsEntry → Block) : Block → Block
  | .para content => .para content
  | .equation n content => .equation n content
  | .section l st num title => .section l st num title
  | .list o s items => .list o s (rewriteContentsItems f #[] items.toList)
  | .center body => .center (rewriteContentsList f #[] body.toList)
  | .ragged s body => .ragged s (rewriteContentsList f #[] body.toList)
  | .quote q body => .quote q (rewriteContentsList f #[] body.toList)
  | .lines ls => .lines ls
  | .abstract body => .abstract (rewriteContentsList f #[] body.toList)
  | .titled kind title body => .titled kind title (rewriteContentsList f #[] body.toList)
  | .disclosure summary expanded body =>
    .disclosure summary expanded (rewriteContentsList f #[] body.toList)
  | .role n body => .role n (rewriteContentsList f #[] body.toList)
  | .link target body => .link target (rewriteContentsList f #[] body.toList)
  | .spaced g body => .spaced g (rewriteContentsList f #[] body.toList)
  | .columns cols => .columns (rewriteContentsCols f #[] cols.toList)
  | .onSteps spec body => .onSteps spec (rewriteContentsList f #[] body.toList)
  | .altSteps spec firstPage otherPage =>
    .altSteps spec (rewriteContentsList f #[] firstPage.toList)
      (rewriteContentsList f #[] otherPage.toList)
  | .only targets body => .only targets (rewriteContentsList f #[] body.toList)
  | .nav spec body => .nav spec (rewriteContentsList f #[] body.toList)
  | .frame t s v br body => .frame t s v br (rewriteContentsList f #[] body.toList)
  | .note body => .note (rewriteContentsList f #[] body.toList)
  | .verbatim k s sp => .verbatim k s sp
  | .logo content => .logo content
  | .framefoot content => .framefoot content
  | .setPalette p => .setPalette p
  | .setTokens tk => .setTokens tk
  | .pagebreak => .pagebreak
  | .rule col nm th => .rule col nm th
  | .picture p => .picture p
  | .table cols pl pr rows rules spans => .table cols pl pr rows rules spans
  | .algorithm n sm lines => .algorithm n sm lines
  | .bibliography src style items => .bibliography src style items
  | .contents spec entries => f spec entries
  | .float kind num capAbove body caption =>
    .float kind num capAbove (rewriteContentsList f #[] body.toList) caption

private def rewriteContentsList (f : ContentsSpec → Array ContentsEntry → Block) (out : Array Block) :
    List Block → Array Block
  | [] => out
  | b :: rest => rewriteContentsList f (out.push (rewriteContentsOne f b)) rest

private def rewriteContentsItems (f : ContentsSpec → Array ContentsEntry → Block)
    (out : Array (Array Block)) : List (Array Block) → Array (Array Block)
  | [] => out
  | item :: rest => rewriteContentsItems f (out.push (rewriteContentsList f #[] item.toList)) rest

private def rewriteContentsCols (f : ContentsSpec → Array ContentsEntry → Block)
    (out : Array (BoxWidth × Array Block)) : List (BoxWidth × Array Block) →
      Array (BoxWidth × Array Block)
  | [] => out
  | (w, body) :: rest =>
    rewriteContentsCols f (out.push (w, rewriteContentsList f #[] body.toList)) rest

end

/-- The blocks with every table of contents replaced by what `f` makes of its options and entries. -/
public def rewriteContents (f : ContentsSpec → Array ContentsEntry → Block) (body : Array Block) :
    Array Block :=
  rewriteContentsList f #[] body.toList

/-- The document with each table of contents listing its headings, as a deck's or a flow's lists
them. -/
public def fillContents (doc : Doc) : Doc :=
  let deck := doc.docClass.record.model == .frame
  let fill := fun spec => if deck then deckContents doc spec else flowContents doc spec
  { doc with body := rewriteContents (fun spec _ => .contents spec (fill spec)) doc.body }

/-- A document whose body is one paragraph lists no contents: filling leaves its body. -/
public theorem fillContents_para (doc : Doc) (c : Array Inline) (h : doc.body = #[.para c]) :
    (fillContents doc).body = #[.para c] := by
  simp only [fillContents, rewriteContents, h]
  rfl

/-- The anchors the document prints the pages of, in flow order: each page reference's label's and
a flow's contents entries'. -/
public def pageTargets (doc : Doc) : Array String :=
  let flow := doc.docClass.record.model != .frame
  foldBlocks (fun out b =>
    if let .contents _ entries := b then
      (if flow then out ++ entries.filterMap (·.target) else out)
    else out)
    (fun out x => if let .ref _ form _ (some t) := x then (if form.paged then out.push t else out)
      else out) #[] doc.body

/-- A page reference showing the folio `folio` lands its label on, `??` where none. -/
private def pagedRef (folio : String → Option Nat) (x : Inline) : Inline :=
  if let .ref key form _ (some t) := x then
    if form.paged then .ref key form (((folio t).map toString).getD "??") (some t) else x
  else x

/-- The document with each page reference and flow contents entry carrying the folio `folio` lands
its anchor on. -/
public def fillPages (folio : String → Option Nat) (doc : Doc) : Doc :=
  let doc := mapDoc (mapInlines (pagedRef folio)) (mapBlocks (pagedRef folio)) doc
  if doc.docClass.record.model == .frame then doc else
  { doc with body := rewriteContents (fun spec entries =>
      .contents spec (entries.map fun e => { e with page := e.target.bind folio })) doc.body }

/-- Flat entries nested as their depths say, each under the last entry before it standing shallower,
never more than one level below it; `item` builds an entry over its nested entries. -/
public def nestContents {β : Type} (item : ContentsEntry → Array β → β)
    (entries : Array ContentsEntry) : Array β := Id.run do
  let mut out : Array β := #[]
  let mut open_ : Array (ContentsEntry × Array β) := #[]
  for e in entries do
    let keep := min e.depth open_.size
    for _ in [keep:open_.size] do
      if let some (pe, kids) := open_.back? then
        open_ := open_.pop
        let node := item pe kids
        open_ := match open_.back? with
          | some (qe, qs) => open_.pop.push (qe, qs.push node)
          | none => open_
        if open_.isEmpty then out := out.push node
    open_ := open_.push (e, #[])
  for _ in [0:open_.size] do
    if let some (pe, kids) := open_.back? then
      open_ := open_.pop
      let node := item pe kids
      open_ := match open_.back? with
        | some (qe, qs) => open_.pop.push (qe, qs.push node)
        | none => open_
      if open_.isEmpty then out := out.push node
  return out

/-- A table of contents as the list a reader without one reads: an item per entry, its number
before its title, nested as the entries are. -/
public def contentsList (entries : Array ContentsEntry) : Block :=
  let line (e : ContentsEntry) : Array Inline := match e.number with
    | some n => #[.text (n ++ " ")] ++ e.title
    | none => e.title
  .list false {} (nestContents (fun e kids =>
    if kids.isEmpty then #[.para (line e)] else #[.para (line e), .list false {} kids]) entries)

end LeanTex.Core.Ir
