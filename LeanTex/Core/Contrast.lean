module

public import LeanTex.Core.ContrastRatio
public import LeanTex.Core.Theme
import LeanTex.Core.Listing
import LeanTex.Core.Oklab
import Std.Data.HashMap
import Std.Data.HashSet

/-! WCAG 2.2 contrast judgement over the engine's colours: the document's contrast report,
the colour-scheme judge for web pages, and the palette contracts of the shipped bundles. -/

namespace LeanTex.Core.Contrast

open LeanTex.Core.Ir LeanTex.Core.Dim

/-- The authored expression and span of a color use or declaration,
matched by its palette, role and source value. -/
public abbrev ColorSite := Palette → Option String → Color → Option (String × Span)

/-- `4.62:1` from 4627: the human spelling of a milli ratio, for messages. -/
public def ratioString (milli : Nat) : String :=
  let frac := (milli % 1000) / 10
  s!"{milli / 1000}.{if frac < 10 then "0" else ""}{frac}:1"

/-- One coloured text occurrence, judged against the palette in force where it stands. -/
private structure Use where
  name : Option ColorRef
  color : Color
  large : Bool
  /-- The page under this use: its local ground, else the epoch's `bg`, else the light surface. -/
  surface : Color
  /-- What the diagnostic calls the surface; `none` reads "the page". -/
  groundName : Option String := none
  surfaceRole : Option Role := none
  /-- Exempt where it stood: covered, or declared decorative in its epoch. -/
  exempt : Bool
  /-- The palette in force at the use. -/
  pal : Palette
  /-- The coloured run the use stands in. -/
  site : Nat := 0
  /-- The highlighting style whose own colour a listing token carries. -/
  styleName : Option String := none
  /-- The surface under the use's mark and its role, read where a scheme ships no mark. -/
  under : Option (Color × Option Role) := none
  /-- The use stands on a box's literal ground, against which a scheme carries a literal ink. -/
  onLiteral : Bool := false
  deriving BEq

/-- The walk's fold state: the palette in force, the uses, and each design site's epochs. -/
private structure UseAcc where
  pal : Palette
  uses : Array Use := #[]
  /-- Every `.setPalette` snapshot met, in flow order. -/
  epochs : Array Palette := #[]
  /-- The epochs declared on a local ground, whose text stands on that ground, not the page. -/
  groundedEpochs : Array Nat := #[]
  titledPals : Array Palette := #[]
  /-- Epochs of numbered frames whose chrome footer actually ships. -/
  footPals : Array Palette := #[]
  /-- Epochs that shipped a titled block, per kind. -/
  blockPals : Array (TitledKind × Palette) := #[]
  standoutPals : Array Palette := #[]
  /-- Epochs that shipped a title page with a declared ground of its own. -/
  titlePagePals : Array Palette := #[]
  /-- Epochs that shipped a link, a code block, a summary, a deck's display or a focus-marked
  stage: where the HTML page draws a focus ring. -/
  focusPals : Array Palette := #[]
  pendingPals : Array Palette := #[]
  /-- The colours some handout page covers, each beside its epoch. -/
  coveredNames : Array (Palette × ColorRef) := #[]
  /-- The coloured runs met so far: the next run's site number. -/
  runs : Nat := 0

private def pushUnique [BEq α] (xs : Array α) (p : α) : Array α :=
  if xs.contains p then xs else xs.push p

/-- The walk past an element the page draws the focus ring on, under the palette in force. -/
private def UseAcc.focusable (acc : UseAcc) : UseAcc :=
  { acc with focusPals := pushUnique acc.focusPals acc.pal }

/-- The effective page of a palette: its `bg`, else the shipped light surface. -/
private def surfaceOf (pal : Palette) : Color :=
  (Design.at pal .light .page).getD Color.white

/-- The walk's text context; a size declaration sets a factor over `base`, never compounding. -/
private structure UseCx where
  base : Length
  size : Length
  /-- The document's size ladder, on which a named size resolves (`Ir.PageSpec.scale`). -/
  scale : List (String × Nat)
  /-- Inside overlay content some handout page covers. -/
  covering : Bool := false
  slides : Bool := false
  chromeFoot : Bool := false
  bold : Bool := false
  cur : Option (Option ColorRef × Color × Nat) := none
  /-- The local ground under this content when it is not the page. -/
  ground : Option Color := none
  /-- What the diagnostic calls the ground ("the frame-title bar"); `none`
  reads "the page". -/
  groundName : Option String := none
  groundRole : Option Role := none
  /-- A frame-entry ground lasts until the next palette declaration, even a repeated one. -/
  groundEpoch : Option Nat := none
  /-- A body's default ink follows a palette declaration, while its
  physical fill remains the enclosing surface. -/
  inkEpoch : Option Nat := none
  /-- The frame's default ink for a nested surface. -/
  inheritedInk : Option (ColorRef × Color) := none
  /-- The highlighting style of the listing this content is a token of. -/
  codeStyle : Option String := none
  /-- Whether the walk reads the design sites alone, passing over listing tokens. -/
  sitesOnly : Bool := false
  /-- The document's element styles, whose font templates' colours are uses. -/
  styles : Styles := {}
  /-- The ground under a mark this content stands on, and its role. -/
  markUnder : Option (Option Color × Option Role) := none
  /-- The literal ground of the box this content stands in, which its literal inks read on. -/
  literalGround : Option Color := none
  /-- Whether a focused stage standing on the page marks its focus in the focus role. -/
  stageFocus : Bool := false
  /-- Whether this content stands outside every frame. -/
  outside : Bool := false

private def UseCx.atEpoch (cx : UseCx) (pal : Palette) (epoch : Nat) : UseCx :=
  let cx := if cx.inkEpoch.any (· != epoch) then
    { cx with cur := some (some (.role .ink), Design.printInk pal,
        (cx.cur.map (·.2.2)).getD 0), inkEpoch := some epoch }
    else cx
  -- premise: listingPaletteAuditChecks — a body declaration replaces the entry ground
  if cx.groundEpoch.any (· != epoch) then
    { cx with ground := none, groundName := none, groundRole := none, groundEpoch := none
              inheritedInk := none }
  else cx

/-- The context under a local ground: text in the default ink judged there as the ink role's use,
a coloured run's ink as before. -/
private def UseCx.inkOnGround (cx : UseCx) (acc : UseAcc) : UseCx :=
  match cx.cur with
  | some _ => cx
  | none => { cx with cur := some (some (.role .ink), Design.printInk acc.pal, acc.runs) }

/-- The context inside a box command's box: on its ground where it declares one, the default ink
of block content following its palette declarations. -/
private def UseCx.onBox (cx : UseCx) (acc : UseAcc) (b : InlineBox) (blocks : Bool := false) :
    UseCx :=
  match b.ground with
  | none => cx
  | some (c, nm) =>
    let role := match nm with
      | some (.role r) => some r
      | _ => none
    let cx := cx.inkOnGround acc
    let cx := if blocks && cx.inkEpoch.isNone then { cx with inkEpoch := some acc.epochs.size }
      else cx
    { cx with ground := some c, groundName := (role.bind (·.row.noun)).getD "the box",
              groundRole := role, markUnder := some (cx.ground, cx.groundRole)
              literalGround := if nm.isNone then some c else none }

/-- Whether a use is large-scale text at the size its medium shows it; slide text always is. -/
private def UseCx.large (cx : UseCx) : Bool :=
  cx.slides || largeText cx.size cx.bold

private def UseCx.style (cx : UseCx) : Style → UseCx
  | .bold => { cx with bold := true }
  | .medium => { cx with bold := false }
  | .series w => { cx with bold := w.isBold }
  | .normal => { cx with bold := false }
  | .size n => match cx.scale.lookup n with
    | some _ => { cx with size := Ir.scaleStepIn cx.scale cx.base n }
    | none => cx
  | .fontSize size _ =>
    -- premise: contrastChecks — a font-relative size keeps the ordinary threshold
    match size.resolve (fun _ => none) with
    | .ok g =>
      { cx with size := if g.width.em == 0 && g.width.ex == 0 then g.width.sp else 0 }
    | .error _ => { cx with size := 0 }
  | _ => cx

private def UseAcc.use (acc : UseAcc) (cx : UseCx) (nm : Option ColorRef)
    (c : Color) : UseAcc :=
  let exempt := match nm with
    | some n => n == .role .covered || acc.pal.decorative.contains n
    | none => acc.pal.decorative.any (fun n => acc.pal.lookup n == some c)
  let styleName := match nm with
    | some (.role r) =>
      if r.code?.isSome && (Design.declared? acc.pal r).isNone then cx.codeStyle else none
    | _ => none
  let u : Use := { name := nm
                   color := c
                   large := cx.large
                   surface := cx.ground.getD (surfaceOf acc.pal)
                   groundName := cx.groundName
                   surfaceRole := if cx.ground.isSome then cx.groundRole else some .page
                   exempt := exempt
                   pal := acc.pal
                   site := match cx.cur with
                     | some (_, _, k) => k
                     | none => acc.runs
                   styleName
                   under := cx.markUnder.map fun (g, r) =>
                     (g.getD (surfaceOf acc.pal), if g.isSome then r else some .page)
                   onLiteral := cx.ground.isSome && cx.literalGround == cx.ground }
  let coveredNames := match nm with
    | some n => if cx.covering then pushUnique acc.coveredNames (acc.pal, n) else acc.coveredNames
    | none => acc.coveredNames
  { acc with uses := acc.uses.push u, coveredNames }

/-- Record pending overlay content: a step range past the first step covers on a handout page. -/
private def UseAcc.step (acc : UseAcc) (spec : Ir.OverlaySpec) : UseAcc :=
  if spec.maxStep ≥ 2 then
    { acc with pendingPals := pushUnique acc.pendingPals acc.pal }
  else acc

/-- The context a heading's title sets: bold, at its level's size on the document's ladder. -/
private def headingCx (scale : List (String × Nat)) (slides : Bool) (base : Length) :
    Ir.HeadingLevel → UseCx
  | 0 => { base, scale, size := Ir.titleSize scale base slides, bold := true }
  | l => { base, scale, size := Ir.headingSize scale base l, bold := true }

mutual

private def usesInlines (cx : UseCx) (acc : UseAcc) (xs : List Inline) :
    UseAcc :=
  match xs with
  | [] => acc
  | x :: rest => usesInlines cx (usesInline cx acc x) rest

private def usesInline (cx : UseCx) (acc : UseAcc) : Inline → UseAcc
  | .text s =>
    match cx.cur with
    | some (nm, c, _) =>
      if s.toList.any (fun ch => !ch.isWhitespace) then
        acc.use cx nm c
      else acc
    | none => acc
  | .math _ _ | .pageNumber | .pageCount =>
    match cx.cur with
    | some (nm, c, _) => acc.use cx nm c
    | none => acc
  | .ref _ _ _ _ =>
    let acc := { acc with focusPals := pushUnique acc.focusPals acc.pal }
    match cx.cur with
    | some (nm, c, _) => acc.use cx nm c
    | none => acc
  -- Judge only ink the formula uses: an inner switch may replace its inherited colour.
  | .formula _ _ body =>
    let ink := cx.cur.map fun (nm, c, _) => (c, nm)
    (Math.MList.inks ink #[] body).foldl (fun a (c, nm) =>
      { a.use { cx with cur := some (nm, c, a.runs) } nm c with runs := a.runs + 1 }) acc
  | .label _ => acc
  | .styled st body => usesInlines (cx.style st) acc body.toList
  | .colored c nm body =>
    usesInlines { cx with cur := some (nm, c, acc.runs) } { acc with runs := acc.runs + 1 }
      body.toList
  | .located _ body => usesInlines cx acc body.toList
  | .role _ body => usesInlines cx acc body.toList
  | .link _ body =>
    usesInlines cx { acc with focusPals := pushUnique acc.focusPals acc.pal } body.toList
  | .decorated kind body =>
    match kind with
    | .underline | .lineThrough => usesInlines cx acc body.toList
    -- marked text stands on its mark, a ground of its own
    | .highlight c nm =>
      let role := match nm with
        | some (.role r) => some r
        | _ => none
      let cx := cx.inkOnGround acc
      usesInlines { cx with ground := some c, groundName := (role.bind (·.row.noun)).getD "the mark",
                            groundRole := role, markUnder := some (cx.ground, cx.groundRole) }
        acc body.toList
  -- a box's content stands on the box's ground where it declares one
  | .boxed b body => usesInlines (cx.onBox acc b) acc body.toList
  | .onSteps spec body =>
    usesInlines { cx with covering := cx.covering || spec.maxStep ≥ 2 } (acc.step spec) body.toList
  -- An alternative is inked at full colour or not at all, so it makes no palette pending.
  | .altSteps _ active otherwise =>
    usesInlines cx (usesInlines cx acc active.toList) otherwise.toList
  | .footnote _ body =>
    usesInlines cx { acc with focusPals := pushUnique acc.focusPals acc.pal } body.toList
  | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _ | .linebreak _ => acc
  | .image _ _ _ => acc
  | .icon _ _ =>
    match cx.cur with
    | some (nm, c, _) => acc.use cx nm c
    | none => acc
  | .cite _ _ =>
    match cx.cur with
    | some (nm, c, _) => acc.use cx nm c
    | none => acc
  | .cited _ _ ink => usesInlines cx acc ink.toList

private def usesBlocks (cx : UseCx) (acc : UseAcc) (xs : List Block) :
    UseAcc :=
  match xs with
  | [] => acc
  | b :: rest =>
    let cx := cx.atEpoch acc.pal acc.epochs.size
    -- A section page or the run of content outside the frames is a stage of its own.
    let acc := if cx.stageFocus && cx.outside && !(b matches .frame ..) &&
        Ir.outsideUnder rest.head? b != .none then acc.focusable else acc
    usesBlocks cx (usesBlock { cx with outside := false } acc b) rest

private def usesBlock (cx : UseCx) (acc : UseAcc) : Block → UseAcc
  | .para content => usesInlines cx acc content.toList
  | .equation number content =>
    let acc := if cx.slides then acc.focusable else acc
    usesInlines cx (usesInlines cx acc content.toList) number.toList
  | .section level _ _ title =>
    let st := (cx.styles.find? level.element).getD {}
    let st := if level == 0 then Ir.titleHeadingStyle st else st
    let title := match st.font with
      | some tpl => Ir.fillTemplate tpl title
      | none => title
    let hc := { headingCx cx.scale cx.slides cx.base level with cur := cx.cur, styles := cx.styles }
    let (hc, acc) := if cx.slides && level == 1 then
      match Design.declared? acc.pal .sectionTitleInk with
      | some c => ({ hc with cur := some (some (.role .sectionTitleInk), c, acc.runs) },
          { acc with runs := acc.runs + 1 })
      | none => (hc, acc)
      else (hc, acc)
    usesInlines hc acc title.toList
  | .list _ _ items => usesItems cx acc items.toList
  | .center body =>
    let acc := if cx.slides && (Ir.displayContent? body).isSome then acc.focusable else acc
    usesBlocks cx acc body.toList
  | .ragged _ body => usesBlocks cx acc body.toList
  | .quote _ body => usesBlocks cx acc body.toList
  | .lines ls => ls.foldl (fun o l => usesInlines cx o l.content.toList) acc
  | .abstract body => usesBlocks cx acc body.toList
  | .titled kind title body =>
    let acc := if title.isEmpty then acc else
      { acc with blockPals := pushUnique acc.blockPals (kind, acc.pal) }
    let look := titledLook acc.pal kind
    let titleCx := { cx with
      bold := true
      cur := some (some (.role (Role.titleInk kind)), look.fg, acc.runs)
      ground := look.bar.or cx.ground
      groundName := (look.bar.map (fun _ => "the block-title bar")).or cx.groundName
      groundRole := if look.bar.isSome then some (Role.titleBar kind) else cx.groundRole }
    let d := Design.ofPalette acc.pal
    let bodyLook := d.titledBody kind
    let defaultInk := cx.inheritedInk.getD (.role .ink, d.fg)
    let inherited := cx.cur.getD (some defaultInk.1, defaultInk.2, acc.runs + 1)
    let parent : ColorPair := { fg := inherited.2.1, bg := cx.ground.getD (surfaceOf acc.pal) }
    let bodyCx := { cx with
      cur := some (if bodyLook.fg.isSome then some (.role (Role.bodyInk kind)) else inherited.1,
        (bodyLook.resolve parent).fg, acc.runs + 1)
      inkEpoch := some acc.epochs.size
      ground := bodyLook.bg.or cx.ground
      groundName := (bodyLook.bg.map (fun _ => "the block body")).or cx.groundName
      groundRole := if bodyLook.bg.isSome then some (Role.bodyGround kind) else cx.groundRole
      groundEpoch := if bodyLook.bg.isSome then none else cx.groundEpoch }
    let title := match Ir.blockTitleFont cx.styles kind with
      | some tpl => Ir.fillTemplate tpl title
      | none => title
    usesBlocks bodyCx
      (usesInlines titleCx { acc with runs := acc.runs + 2 } title.toList) body.toList
  | .disclosure summary _ body =>
    usesBlocks cx (usesInlines cx acc.focusable (Ir.disclosureSummary summary).toList) body.toList
  | .role _ body => usesBlocks cx acc body.toList
  | .link _ body => usesBlocks cx acc.focusable body.toList
  | .spaced _ body => usesBlocks cx acc body.toList
  | .columns cols => usesColumns cx acc cols.toList
  | .onSteps spec body =>
    usesBlocks { cx with covering := cx.covering || spec.maxStep ≥ 2 } (acc.step spec) body.toList
  | .altSteps _ active otherwise =>
    usesBlocks cx (usesBlocks cx acc active.toList) otherwise.toList
  -- Conditional content is judged whichever backend carries it.
  | .only _ body => usesBlocks cx acc body.toList
  | .nav _ body => usesBlocks cx acc body.toList
  | .frame title standout valign _ body =>
    let acc := if title.isEmpty || (Design.declared? acc.pal .frameTitleBar).isNone then acc
      else { acc with titledPals := pushUnique acc.titledPals acc.pal }
    let acc := if cx.stageFocus && !standout && !(valign matches .golden) then acc.focusable
      else acc
    let acc := if cx.chromeFoot && !standout && !(valign matches .golden) then
      { acc with footPals := pushUnique acc.footPals acc.pal }
      else acc
    let acc := if standout then
      { acc with standoutPals := pushUnique acc.standoutPals acc.pal }
      else acc
    let acc := if !standout && valign matches .golden &&
        (Design.ofPalette acc.pal).titlepage.isSome then
      { acc with titlePagePals := pushUnique acc.titlePagePals acc.pal }
      else acc
    let titleCx := cx.style (.size "large")
    let titleCx := { titleCx with
      bold := true
      ground := Design.declared? acc.pal .frameTitleBar
      groundName := (Design.declared? acc.pal .frameTitleBar).map
        (fun _ => "the frame-title bar")
      groundRole := (Design.declared? acc.pal .frameTitleBar).map fun _ => .frameTitleBar }
    let (titleCx, acc) := if titleCx.ground.isNone then
      match Design.declared? acc.pal .frameTitleInk with
      | some c => ({ titleCx with cur := some (some (.role .frameTitleInk), c, acc.runs) },
          { acc with runs := acc.runs + 1 })
      | none => (titleCx, acc)
      else (titleCx, acc)
    -- A standout frame's content sits on the inversion, never the page.
    let d := Design.ofPalette acc.pal
    let bodyCx := if standout then
        { cx with ground := some d.standout.bg
                  inheritedInk := some (.role .standoutInk, d.standout.fg)
                  groundName := some "the standout frame"
                  groundRole := some .standoutGround
                  groundEpoch := some acc.epochs.size }
      else match titleGroundOf acc.pal valign with
        | some ground =>
          { cx with ground := some ground, groundName := some "the title page"
                    groundRole := some .titlePageGround
                    inheritedInk := some (.role .titlePageInk, (d.titlepage.map (·.fg)).getD d.fg)
                    groundEpoch := some acc.epochs.size }
        | none => cx
    usesBlocks bodyCx (usesInlines titleCx acc title.toList) body.toList
  | .framefoot content =>
    usesInlines { cx with
      ground := (Design.ofPalette acc.pal).footline.bar
      groundName := (Design.ofPalette acc.pal).footline.bar.map (fun _ => "the footline")
      groundRole := (Design.ofPalette acc.pal).footline.bar.map fun _ => .footBand }
      acc content.toList
  | .setPalette p =>
    let grounded := if cx.ground.isSome then acc.groundedEpochs.push acc.epochs.size
      else acc.groundedEpochs
    { acc with pal := p, epochs := acc.epochs.push p, groundedEpochs := grounded }
  | .setTokens _ => acc
  | .table _ _ _ rows _ _ => usesRows cx acc rows.toList
  | .algorithm _ _ lines =>
    lines.foldl (fun o l =>
      let o := usesInlines cx o l.content.toList
      match l.comment with
      | some c => usesInlines cx o c.toList
      | none => o) acc
  | .float _ _ _ body caption =>
    usesBlocks cx (usesInlines cx acc caption.toList) body.toList
  | .bibliography _ _ items =>
    items.foldl (fun o item => usesInlines cx o item.content.toList) acc
  | .contents _ entries =>
    entries.foldl (fun o e => usesInlines cx o e.title.toList) acc
  | .verbatim covered source spec =>
    let acc := acc.focusable
    let acc := match spec.caption with
      | some (_, cap) => usesInlines cx acc cap.toList
      | none => acc
    if cx.sitesOnly then acc else
    let own := spec.groundIn acc.pal .print
    let ground := (own.map (·.1)).orElse fun _ =>
      cx.ground.orElse fun _ => some (Design.printPage acc.pal)
    let cur := match own with
      | some (g, _) =>
        let inherited := (cx.cur.map (·.2.1)).getD
          ((cx.inheritedInk.map (·.2)).getD (Design.printInk acc.pal))
        let name := if (Design.declared? acc.pal .codeInk).isSome then some (.role .codeInk)
          else cx.cur.bind (·.1)
        some (name, Listing.groundInk acc.pal g inherited, acc.runs)
      | none => cx.cur
    let codeCx := { cx.style spec.fontSize with
      ground, cur, groundName := (own.map fun _ => "the listing's ground").or cx.groundName
      groundRole := match own with
        | some (_, some (.role r)) => some r
        | some _ => none
        | none => cx.groundRole
      codeStyle := spec.style.map (·.name) }
    let lines := spec.tokenLines source
    let brushes := Listing.brushes acc.pal ground covered spec.style lines
    lines.foldl (fun acc line =>
      usesInlines codeCx acc
        ((Listing.paintLine acc.pal ground covered spec.style brushes
          line).flatMap fun r => Listing.paintRun r #[.text r.text]).toList) acc
  -- A picture's labels stand on its own fills, not the page; their contract is pending work.
  | .note _ | .rule _ _ _ | .logo _ | .picture _
  | .pagebreak => acc

private def usesItems (cx : UseCx) (acc : UseAcc) :
    List (Array Block) → UseAcc
  | [] => acc
  | item :: rest => usesItems cx (usesBlocks cx acc item.toList) rest

private def usesColumns (cx : UseCx) (acc : UseAcc) :
    List (BoxWidth × Array Block) → UseAcc
  | [] => acc
  | (w, body) :: rest =>
    usesColumns cx (usesBlocks (w.box.elim cx (cx.onBox acc · (blocks := true))) acc body.toList) rest

private def usesRows (cx : UseCx) (acc : UseAcc) :
    List (Array (Array Block)) → UseAcc
  | [] => acc
  | row :: rest => usesRows cx (usesItems cx acc row.toList) rest

end

/-- Whether the document is shown as a deck's stage (the frame page model). -/
public def stageOf (doc : Doc) : Bool := doc.docClass.record.model == .frame

/-- The body walk: every coloured use with its epoch, and the design sites each epoch ships. -/
private def docWalk (doc : Doc) (sitesOnly : Bool := false) : UseAcc :=
  let hasFrameFoot := doc.body.any fun b => match b with
    | .framefoot xs => !xs.isEmpty
    | _ => false
  let cx : UseCx :=
    { base := doc.page.fontSize, size := doc.page.fontSize, scale := doc.page.scale, sitesOnly
      styles := doc.styles
      slides := stageOf doc
      stageFocus := stageOf doc && doc.declaresFocus
      outside := stageOf doc
      chromeFoot := doc.docClass.record.chrome && doc.foot.isNone &&
        (doc.chrome.hasFooter || hasFrameFoot) }
  let walk := usesBlocks cx { pal := doc.palette } doc.body.toList
  -- premise: Tests.DeclaredColors.focusGateChecks — css=none and pdf-only pages draw no focus ring
  if doc.output.css == some "none" ||
      (!doc.output.formats.isEmpty && !doc.output.formats.contains "html") then
    { walk with focusPals := #[] } else walk

/-- The body walk's uses plus the running heads, feet and chrome footer. -/
private def docUses (doc : Doc) (walk : UseAcc) : UseAcc := Id.run do
  let base : UseCx := { base := doc.page.fontSize, size := doc.page.fontSize, scale := doc.page.scale
                        slides := stageOf doc }
  let mut acc := { walk with pal := doc.palette }
  for pal in walk.footPals do
    let look := (Design.ofPalette pal).footline
    let key : ColorRef := if (Design.declared? pal .muted).isSome then .role .muted else .role .ink
    let cx := { base with
      size := Ir.footlineSize doc.page.scale doc.page.fontSize
      ground := look.bar, groundName := look.bar.map (fun _ => "the footline")
      groundRole := look.bar.map fun _ => .footBand }
    acc := { acc with pal := pal }
    acc := { acc.use cx (some key) look.fg with runs := acc.runs + 1 }
  acc := { acc with pal := doc.palette }
  for run in [doc.head, doc.foot] do
    if let some content := run then
      acc := usesInlines base acc content.toList
  return acc

/-- The shipped ink/page pair: the resolved ink over the declared page, else the light surface. -/
public def effectivePair (doc : Doc) : ColorPair :=
  { fg := (Design.ofDoc doc).fg, bg := (Design.at doc.palette .light .page).getD Color.white }

/-- A design site as the document judge reads it, an undeclared page as the light surface. -/
public def judgedSite? (stage : Bool) (pal : Palette) (r : Role) : Option Site :=
  (Design.site? pal .print r).map fun st =>
    let st := { st with need := st.need.atStage stage }
    if st.on == .page then { st with ground := surfaceOf pal } else st

/-- What WCAG 2.2 asks of a need, as a message spells it. -/
private def needClause : Need → String
  | .text => "text (SC 1.4.3)"
  | .largeText => "large-scale text (SC 1.4.3)"
  | .nonText => "non-text information (SC 1.4.11)"
  | .state => "a state change (SC 1.4.11)"
  | .decorative => "nothing"

/-- A failing site's diagnostic: W0345 for a themed element, W0315 for page text, W0330 for
undeclared ink. -/
private def siteVerdict (site : ColorSite) (r : Role) (pal : Palette) (st : Site) : Diag :=
  let key := (ColorRef.role r).key
  let req := requiredIn st.scheme st.need
  let milli := contrastMilli st.ink st.ground
  let clause := needClause st.need
  let span := (site pal (some key) st.ink).map (·.2)
  if r.row.noun.isNone && (Design.declared? pal r).isNone then
    let onKey := (ColorRef.role st.on).key
    Diag.of .W0330
      (s!"the declared page keeps the defaulted ink, below the contrast WCAG 2.2 asks of " ++
        clause)
      (span := (site pal (some onKey) st.ground).map (·.2))
      (detail := some s!"{st.ink.hex} on {st.ground.hex}: {ratioString milli}, below {ratioString req}")
      (help := some ("a declared surface chooses its ink: declare " ++
        "\\palette{ " ++ key ++ " = ... }" ++ " beside " ++ onKey))
  else match r.row.noun with
    | some noun =>
      Diag.of .W0345
        (s!"{noun} pairs its ink and ground below the contrast WCAG 2.2 asks of " ++ clause)
        (span := span) (subject := some (inkKey key st.ink st.ground))
        (detail := some s!"{st.ink.hex} on {st.ground.hex}: {ratioString milli}, below {ratioString req}")
    | none =>
      Diag.of .W0315
        (s!"text coloured '{key}' reads on the page below the contrast WCAG 2.2 asks of " ++
          clause)
        (span := span) (subject := some (inkKey key st.ink st.ground))
        (detail := some s!"{st.ink.hex} on {st.ground.hex}: {ratioString milli}, below {ratioString req}")

/-- Judge one shipped design site; only a failing site no earlier epoch reported speaks. -/
private def judgeSite (site : ColorSite) (stage : Bool) (s : Array Diag × Array Site) :
    Role × Palette → Array Diag × Array Site
  | (r, pal) =>
    match judgedSite? stage pal r with
    | some st =>
      if pal.decorative.contains (.role r) || st.passes || s.2.contains st then s
      else (s.1.push (siteVerdict site r pal st), s.2.push st)
    | none => s

/-- A family of sites, judged in order. -/
private def judgeSites (site : ColorSite) (stage : Bool) (xs : Array (Role × Palette)) :
    Array Diag :=
  (xs.foldl (judgeSite site stage) (#[], #[])).1

/-- The registry sites the report reads at one shipped event, in registry order. -/
public def eventSites (ev : Judged) (pal : Palette) : Array (Role × Palette) :=
  ((Design.sites pal .print).filter (·.role.row.judged == ev)).toArray.map (·.role, pal)

/-- The epochs the page shows, those declared on a local ground standing on it instead. -/
private def pageEpochs (walk : UseAcc) : Array Palette :=
  walk.epochs.zipIdx.filterMap fun (p, i) => if walk.groundedEpochs.contains i then none else some p

/-- The page in every epoch it shows, the document's palette first. -/
private def pageEvents (doc : Doc) (walk : UseAcc) : Array (Judged × Palette) :=
  (#[doc.palette] ++ pageEpochs walk).map (.page, ·)

/-- The themed elements each epoch ships: block titles, frame titles, standout frames, title
pages and focus rings. -/
private def elementEvents (walk : UseAcc) : Array (Judged × Palette) :=
  walk.blockPals.map (fun (k, pal) => (.element (Element.ofTitled k), pal)) ++
    walk.titledPals.map (.element .frameTitle, ·) ++
    walk.standoutPals.map (.element .standout, ·) ++
    walk.titlePagePals.map (.element .titlePage, ·) ++
    walk.focusPals.map (.element .focusRing, ·)

private def pageSites (doc : Doc) (walk : UseAcc) : Array (Role × Palette) :=
  (pageEvents doc walk).flatMap fun (ev, pal) => eventSites ev pal

private def elementSites (walk : UseAcc) : Array (Role × Palette) :=
  (elementEvents walk).flatMap fun (ev, pal) => eventSites ev pal

/-- The events a document's report reads sites at, in judging order, each with its palette. -/
public def shippedEvents (doc : Doc) : Array (Judged × Palette) :=
  let walk := docWalk doc
  let elements := elementEvents walk
  pageEvents doc walk ++ elements

/-- The design sites a document ships, in judging order, each with its palette. -/
public def shippedSites (doc : Doc) : Array (Role × Palette) :=
  (shippedEvents doc).flatMap fun (ev, pal) => eventSites ev pal

/-- The shipped sites and coloured uses, from a walk that passes over listing tokens. -/
private def schemeWalk (doc : Doc) : Array (Role × Palette) × Array Use :=
  let walk := docWalk doc (sitesOnly := true)
  ((pageEvents doc walk ++ elementEvents walk).flatMap fun (ev, pal) => eventSites ev pal,
    (docUses doc walk).uses)

/-- The palettes a document's page carries: its own, then every epoch's, in
the order the body declares them. -/
public def docPalettes (doc : Doc) : List Palette :=
  doc.palette :: (Ir.foldBlocks (fun (acc : Array Palette) b => match b with
    | .setPalette p => acc.push p
    | _ => acc) (fun acc _ => acc) #[] doc.body).toList

/-- One colour a scheme cannot carry: its name, the role it is judged on,
what it reads there and what that scheme owes. -/
public structure SchemeLoss where
  name : ColorRef
  /-- The ground it is judged on: a role, or a box's literal colour. -/
  on : ColorRef
  ratio : Nat
  gate : Nat
  deriving Repr, BEq, Inhabited

/-- The schemes a web page ships, their palette views, and each dropped scheme's losses. -/
public structure SchemeJudgement where
  shipped : List Scheme := []
  frames : List SchemeFrame := []
  /-- Each palette of the page (`docPalettes`) beside its view in every
  shipped scheme, in `shipped`'s order. -/
  views : List (Palette × List Palette) := []
  dropped : List (Scheme × List SchemeLoss) := []
  deriving Inhabited

/-- One scheme's losses: colours a view could not carry and shipped sites short of its gate. -/
private def schemeLosses (s : Scheme) (f : SchemeFrame) (stage : Bool)
    (views : List (Palette × (Palette × Array Unrealized))) (sites : Array (Role × Palette))
    (uses : List (Palette × Array Use)) : List SchemeLoss := Id.run do
  let mut out : Array SchemeLoss := #[]
  let push (out : Array SchemeLoss) (l : SchemeLoss) : Array SchemeLoss :=
    if out.any fun o => o.name == l.name && o.on == l.on then out else out.push l
  for (p, (v, un)) in views do
    let used := (uses.lookup p).getD #[]
    for u in un do
      let site := match u.name with
        | .role r => sites.any (· == (r, p))
        | .color _ => false
      let painted := used.filter (·.name == some u.name)
      if painted.isEmpty && !site then continue
      let need := match u.name with
        | .role r => r.row.need
        | .color _ => .text
      let ink := match u.name with
        | .role r => Design.at v s r
        | .color n => v.lookup (.color n)
      if site then
        let (ratio, gate) := u.measured.getD ((match ink, Design.at v s u.on with
          | some a, some b => contrastMilli a b
          | _, _ => 0), requiredIn s (need.atStage stage))
        out := push out { name := u.name, on := .role u.on, ratio, gate }
      else
        -- A colour only text paints is judged on the grounds that text stands on.
        let fails := painted.filterMap fun w =>
          let marked := w.surfaceRole == some .alertMark && (Design.at v s .alertMark).isNone
          let (surface, role) := if marked then w.under.getD (w.surface, w.surfaceRole)
            else (w.surface, w.surfaceRole)
          let (g, on) := p.useGround v f surface role
          let gate := requiredIn s ((if w.large then Need.largeText else .text).atStage stage)
          let ratio := (ink.map (contrastMilli · g)).getD 0
          if ratio < gate then
            some ({ name := u.name, on := if w.onLiteral && !marked then .color surface.hex
                      else .role on, ratio, gate } : SchemeLoss)
          else none
        for l in fails do out := push out l
    for u in used do
      if u.name.isSome then continue
      let (surface, role) := if u.surfaceRole == some .alertMark && (Design.at v s .alertMark).isNone
        then u.under.getD (u.surface, u.surfaceRole) else (u.surface, u.surfaceRole)
      let (g, on) := p.useGround v f surface role
      -- A literal ink on a box's literal ground is carried on that ground, as the web page sets it.
      let c := if u.onLiteral then Design.literalOn f g u.color else Design.literalIn f u.color
      let on : ColorRef := if u.onLiteral then .color u.surface.hex else .role on
      let gate := requiredIn s (if u.large then .largeText else .text)
      if contrastMilli c g < gate then
        out := push out { name := .color u.color.hex, on, ratio := contrastMilli c g, gate }
  for (r, p) in sites do
    let v := ((views.find? (·.1 == p)).map (·.2.1)).getD p
    if let some st := Design.site? v s r then
      let st := { st with need := st.need.atStage stage }
      if !st.passes then
        out := push out { name := .role r, on := .role st.on, ratio := contrastMilli st.ink st.ground
                          gate := requiredIn s st.need }
  return out.toList

/-- A dropped scheme's diagnostic for one colour it could not carry (`scheme:name@ground`). -/
public def schemeLossDiag (s : Scheme) (l : SchemeLoss) : Diag :=
  let key := l.name.key
  let ground := l.on.key
  Diag.of .W0308
    s!"the {s.name} scheme cannot carry '{key}' legibly on '{ground}'; the page ships without it"
    (help := some "declare a colour that reaches the gate on its ground in that scheme, or name \
the schemes the page offers: \\output{ schemes = print, light }")
    (subject := some s!"{s.name}:{key}@{ground}")
    (detail := some s!"{ratioString l.ratio}, below {ratioString l.gate}")

/-- The colour schemes a web page ships, of those it asks: a scheme its colours were not
declared for ships only where every colour the page paints stays legible. -/
public def schemeJudge (doc : Doc) : SchemeJudgement :=
  let stage := stageOf doc
  let pals := docPalettes doc
  let carries := doc.requestedSchemes.any fun s => !(doc.palette.frame s stage).home
  let (sites, uses) := if carries then schemeWalk doc else (#[], #[])
  let usesOf : List (Palette × Array Use) := pals.map fun p =>
    (p, uses.filter fun u => !u.exempt && u.pal == p)
  let groundsOf (p : Palette) : List (ColorRef × List (Color × Bool × Option Role)) :=
    ((usesOf.lookup p).getD #[]).foldl (fun acc u => match u.name with
      | some k =>
        let gs := [(u.surface, u.large, u.surfaceRole)] ++
          (u.under.map fun (g, r) => [(g, u.large, r)]).getD []
        match acc.findIdx? (·.1 == k) with
        | some i => acc.modify i fun (k, gs') => (k, gs' ++ gs)
        | none => acc.push (k, gs)
      | none => acc) #[] |>.toList
  let judged := doc.requestedSchemes.map fun s =>
    let f := doc.palette.frame s stage
    let vs := pals.map fun p => (p, p.view f (groundsOf p))
    -- premise: dropChecks — a declared scheme's pairs are the document report's to name
    (s, f, vs, if f.home then [] else schemeLosses s f stage vs sites usesOf)
  let kept := judged.filter (·.2.2.2.isEmpty)
  { shipped := kept.map (·.1)
    frames := kept.map (·.2.1)
    views := pals.zipIdx.map fun (p, i) =>
      (p, kept.map fun k => ((k.2.2.1[i]?).map (·.2.1)).getD p)
    dropped := judged.filterMap fun (s, _, _, ls) => if ls.isEmpty then none else some (s, ls) }

/-- The diagnostics a scheme judgement owes: one per colour each dropped
scheme could not carry. -/
public def SchemeJudgement.diags (j : SchemeJudgement) : Array Diag :=
  (j.dropped.flatMap fun (s, ls) => ls.map (schemeLossDiag s)).toArray

public theorem scheme_drop_accounts (doc : Doc) :
    ∀ d ∈ (schemeJudge doc).dropped, d.2 ≠ [] ∧
      ∀ l ∈ d.2, schemeLossDiag d.1 l ∈ (schemeJudge doc).diags := by
  intro d hd
  refine ⟨?_, fun l hl => ?_⟩
  · simp only [schemeJudge, List.mem_filterMap] at hd
    obtain ⟨⟨s, f, vs, ls⟩, _, he⟩ := hd
    split at he
    · cases he
    · rename_i hne
      cases he
      intro h
      simp only at h hne
      exact hne (by simp [h])
  · simp only [SchemeJudgement.diags, List.mem_toArray, List.mem_flatMap, List.mem_map]
    exact ⟨d, hd, l, hl, rfl⟩

/-- A scheme loss's census key `scheme:name@ground`, its diagnostic's subject. -/
public def SchemeLoss.key (s : Scheme) (l : SchemeLoss) : String :=
  s!"{s.name}:{l.name.key}@{l.on.key}"

public theorem sites_named (doc : Doc) :
    ∀ d ∈ (schemeJudge doc).dropped, ∀ l ∈ d.2,
      ∃ g ∈ (schemeJudge doc).diags, g.subject = some (SchemeLoss.key d.1 l) :=
  fun d hd l hl => ⟨schemeLossDiag d.1 l, (scheme_drop_accounts doc d hd).2 l hl,
    by simp only [schemeLossDiag, SchemeLoss.key, Diag.of_record_exact]⟩

/-- Judge the covering per epoch that ships pending content: quieter than the active form,
and 3:1 from it (SC 1.4.11). -/
private def pendingCoverDiags (site : ColorSite) (doc : Doc) (pending : Array Palette)
    (covered : Array (Palette × ColorRef)) : Array Diag := Id.run do
  let mut out : Array Diag := #[]
  for pal in pending do
    if pal.decorative.contains (.role .covered) then continue
    let d := Design.ofDoc { doc with palette := pal }
    let cov := d.cover
    -- premise: Tests.PaletteCover.hiddenChecks — a hidden step ships none of its ink to judge
    if cov.hidden then continue
    let coverHelp := some ("a cover is a declaration too: lower " ++
      "'covered = <n>%', declare \\palette{ covered = ... } " ++
      "quieter than the ink it stands for, or declare the covered steps decorative: " ++
      "\\palette[decorative]{ covered = <n>% }")
    let judge (nm : String) (active covered : Color) : Array Diag :=
      let origin := (site pal (some "covered") covered).orElse fun _ =>
        site pal (some nm) active
      if coverHolds d.bg active covered then #[]
      else if contrastMilli covered d.bg ≥ contrastMilli active d.bg then
        #[Diag.of .W0345
          (s!"covering '{nm}' does not quiet it: the covered form " ++
            "reads as loud on the page as the active one")
          (span := origin.map (·.2))
          (subject := some s!"covered:{nm}")
          (help := coverHelp)]
      else
        let milli := contrastMilli active covered
        if milli < aaNonText then
          #[Diag.of .W0345
            (s!"covered '{nm}' reads against its active form below the contrast " ++
              "WCAG 2.2 asks of a state change (SC 1.4.11)")
            (span := origin.map (·.2))
            (subject := some s!"covered:{nm}")
            (detail := some (s!"{covered.hex} against {active.hex}: " ++
              s!"{ratioString milli}, below {ratioString aaNonText}"))
            (help := coverHelp)]
        else #[]
    out := out ++ judge "fg" d.fg (cov.of d.fg)
    -- A declared constant cover is judged under its own key; undeclared, it is the fg cover.
    if d.covered.isSome then
      out := out ++ judge "covered" d.fg d.inkCover
    for (role, r) in [("alert", Role.alert), ("example", Role.example)] do
      if let some c := Design.declared? pal r then
        if covered.contains (pal, .role r) then
          out := out ++ judge role c (cov.of c)
  return out

/-- One pairing: an ink and the ground it stood on. -/
private structure PairKey where
  color : Color
  ground : Color
  deriving BEq

private instance : Hashable PairKey where
  hash k := hash (k.color.r, k.color.g, k.color.b, k.color.cmyk,
    k.ground.r, k.ground.g, k.ground.b, k.ground.cmyk)

/-- What a use is judged under: its pairing and the name it carried there. -/
private structure UseKey where
  name : Option ColorRef
  pair : PairKey
  deriving BEq

private instance : Hashable UseKey where
  hash k := hash (k.name, k.pair)

private def Use.key (u : Use) : UseKey :=
  { name := u.name, pair := { color := u.color, ground := u.surface } }

/-- Whether each pairing stood as large-scale text everywhere it was used. -/
private def allLargeOf (uses : Array Use) : Std.HashMap UseKey Bool :=
  uses.foldl (fun m v => m.insert v.key (v.large && (m[v.key]?).getD true)) {}

private structure UseJudgeState where
  diags : Array Diag := #[]
  /-- The pairings already reported, seeded with the effective pair. -/
  done : Std.HashSet UseKey
  /-- The coloured run each pairing's warning last spoke for. -/
  sites : Std.HashMap UseKey Nat := {}

/-- A pairing warning at one coloured run: a warning at its first run, a note at later runs. -/
private def UseJudgeState.pairing (s : UseJudgeState) (dup : Bool) (key : UseKey)
    (run : Nat) (subject message detail : String) (span : Option Span) : UseJudgeState :=
  if dup && s.sites[key]? == some run then s
  else
    let d := Diag.of .W0315 message span (subject := some subject) (detail := some detail)
    { s with diags := s.diags.push (if dup then d.demote else d)
             sites := s.sites.insert key run }

private def useStep (site : ColorSite) (large : Std.HashMap UseKey Bool)
    (s : UseJudgeState) (u : Use) : UseJudgeState :=
  -- Exemption before dedup: an exempt use must not consume a later use's key.
  if u.exempt then s
  else
    let key := u.key
    let dup := s.done.contains key
    let done := s.done.insert key
    let allLarge := (large[key]?).getD true
    let threshold := if allLarge then aaLargeText else aaText
    let assessment := assessPair threshold u.color u.surface
    if assessment.passes then { s with done := done }
    else
      let origin := site u.pal (u.name.map (·.key)) u.color
      let spelled : Option String := match u.name with
        | some role => some role.key
        | none => origin.map Prod.fst
      let label := match u.styleName, spelled with
        | some st, _ => s!"by the '{st}' highlighting style"
        | none, some e => s!"'{e}'"
        | none, none => s!"'{u.color.hex}'"
      let s := s.pairing dup key u.site
        (inkKey (spelled.getD u.color.hex) u.color u.surface)
        (s!"text coloured {label} reads on {u.groundName.getD "the page"} below the contrast " ++
          s!"WCAG 2.2 asks of {if allLarge then "large-scale text" else "text"} (SC 1.4.3)")
        (s!"{u.color.hex} on {u.surface.hex}: {ratioString assessment.ratio}, " ++
          s!"below {ratioString threshold}")
        (origin.map (·.2))
      { s with done := done }

private def declaredUseJudged (site : ColorSite) (doc : Doc) (walk : UseAcc) : Array Diag :=
  let d := Design.ofDoc doc
  let uses := (docUses doc walk).uses
  (uses.foldl (useStep site (allLargeOf uses))
    { done := ({} : Std.HashSet UseKey).insert
        { name := some (.role .ink),
          pair := { color := d.fg, ground := (effectivePair doc).bg } } }).diags

/-- The document-level contrast report; `site` names each pairing's authored source and span. -/
public def docDiags (doc : Doc) (site : ColorSite := fun _ _ _ => none) : Array Diag :=
  let walk := docWalk doc
  let stage := stageOf doc
  let elements := judgeSites site stage (elementSites walk)
  -- A pairing a themed element's site names is reported by that site alone.
  let uses := (declaredUseJudged site doc walk).filter fun d =>
    !(elements.any fun e => e.subject.isSome && e.subject == d.subject)
  judgeSites site stage (pageSites doc walk) ++ uses ++ elements ++
    pendingCoverDiags site doc walk.pendingPals walk.coveredNames

public theorem judged_pair_is_shipped (doc : Doc) :
    (effectivePair doc).fg = (Design.ofDoc doc).fg ∧
    ((Design.ofDoc doc).bgDeclared = true →
      (effectivePair doc).bg = (Design.ofDoc doc).bg) := by
  refine ⟨rfl, fun h => ?_⟩
  have hdec : (Design.ofDoc doc).bgDeclared = (Design.declared? doc.palette .page).isSome := rfl
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (hdec ▸ h)
  have hbg : (Design.ofDoc doc).bg = (Design.at doc.palette .print .page).getD Color.white := rfl
  simp only [effectivePair, hbg, Design.at_declared doc.palette .light .page c hc,
    Design.at_declared doc.palette .print .page c hc]

private theorem titled_ground_agree (acc : UseAcc) (cx : UseCx) (kind : TitledKind)
    (nm : Option ColorRef) (c : Color) (stage : Bool) (st : Site)
    (h : judgedSite? stage acc.pal (Role.titleInk kind) = some st) :
    ((acc.use { cx with ground := (titledLook acc.pal kind).bar } nm c).uses.back?).map
        Use.surface = some st.ground := by
  have hg : (Role.titleInk kind).row.ground = some (Role.titleBar kind) := by cases kind <;> rfl
  have hn : (Role.titleInk kind).row.need.paired = true := by cases kind <;> rfl
  have hp : (Role.titleInk kind).row.presence = .always := by cases kind <;> rfl
  have hb : (Role.titleBar kind == Role.page) = false := by cases kind <;> rfl
  simp only [judgedSite?, Design.site?, hg, hn, hp, Presence.holds, Bool.and_self, ite_true,
    Option.bind_some, Option.map_map] at h
  obtain ⟨ink, -, rfl⟩ := Option.map_eq_some_iff.mp h
  simp only [UseAcc.use, titledLook, Array.back?_push, Option.map_some, Function.comp]
  cases Design.at acc.pal .print (Role.titleBar kind) <;> simp [hb]

private theorem effectivePair_bg (doc : Doc) : (effectivePair doc).bg = surfaceOf doc.palette :=
  rfl

private theorem judgedSite_ink (stage : Bool) (doc : Doc) :
    judgedSite? stage doc.palette .ink =
      some { role := .ink, ink := (effectivePair doc).fg, on := .page
             ground := (effectivePair doc).bg, need := Need.text.atStage stage
             scheme := .print } := by
  have hink : Design.at doc.palette .print .ink = some (effectivePair doc).fg := by
    have hfg : (effectivePair doc).fg = (Design.at doc.palette .print .ink).getD Color.black := rfl
    obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp (Design.at_ink_isSome doc.palette .print)
    rw [hfg, hc']
    rfl
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (Design.at_page_isSome doc.palette .print)
  simp [judgedSite?, Design.site?, Role.row, Row.keyed, Need.paired, Presence.holds, hink, hc,
    effectivePair_bg]

private theorem site?_role {pal : Palette} {s : Scheme} {r : Role} {st : Site}
    (h : Design.site? pal s r = some st) : st.role = r := by
  simp only [Design.site?, Option.bind_eq_some_iff] at h
  obtain ⟨g, _, h⟩ := h
  split at h
  · obtain ⟨ink, _, hst⟩ := Option.map_eq_some_iff.mp h
    split at hst <;> (subst hst; rfl)
  · cases h

private theorem filter_filterMap_role (f : Role → Option Site)
    (hf : ∀ r st, f r = some st → st.role = r) (q : Role → Bool) :
    ∀ l : List Role, (l.filterMap f).filter (fun st => q st.role) = (l.filter q).filterMap f
  | [] => rfl
  | r :: rs => by
    have ih := filter_filterMap_role f hf q rs
    cases h : f r with
    | none => by_cases hq : q r = true <;> simp [h, hq, ih]
    | some st =>
      have hr := hf r st h
      subst hr
      by_cases hq : q st.role = true <;> simp [h, hq, ih]

private theorem eventSites_page (pal : Palette) :
    eventSites .page pal = ((Design.site? pal .print .ink).toList.map (·.role, pal)).toArray := by
  have h := filter_filterMap_role (Design.site? pal .print) (fun _ _ h => site?_role h)
    (fun r => r.row.judged == .page) Role.all
  simp only [eventSites, Design.sites]
  rw [h, Role.judged_page]
  simp only [List.filterMap_cons, List.filterMap_nil]
  cases Design.site? pal .print .ink <;> simp

private theorem foldlList_invariant {α β : Type} (P : β → Prop) (f : β → α → β) :
    ∀ (xs : List α) (init : β), P init →
      (∀ b a, a ∈ xs → P b → P (f b a)) → P (xs.foldl f init)
  | [], _, hi, _ => hi
  | a :: as, init, hi, hs =>
    foldlList_invariant P f as (f init a) (hs init a (List.mem_cons_self ..) hi)
      (fun b x hx hb => hs b x (List.mem_cons_of_mem a hx) hb)

private theorem judgeSite_diags_mono (site : ColorSite) (stage : Bool)
    (s : Array Diag × Array Site) (x : Role × Palette) :
    s.1.size ≤ (judgeSite site stage s x).1.size := by
  obtain ⟨r, pal⟩ := x
  simp only [judgeSite]
  split
  · split
    · exact Nat.le_refl _
    · simp
  · exact Nat.le_refl _

public theorem defaulted_ink_cannot_escape (doc : Doc)
    (hdec : doc.palette.decorative.contains (.role .ink) = false)
    (hfail : contrastMilli (effectivePair doc).fg (effectivePair doc).bg <
      required (Need.text.atStage (stageOf doc))) :
    0 < (docDiags doc).size := by
  have hp : ({ role := .ink, ink := (effectivePair doc).fg, on := .page
               ground := (effectivePair doc).bg, need := Need.text.atStage (stageOf doc)
               scheme := .print } : Site).passes = false := by
    simp [Site.passes, requiredIn, Scheme.more, Nat.not_le.mpr hfail]
  have hdec' : ColorRef.role Role.ink ∉ doc.palette.decorative := by simpa using hdec
  have h1 : 0 < (judgeSite (fun _ _ _ => none) (stageOf doc) (#[], #[])
      (Role.ink, doc.palette)).1.size := by
    simp [judgeSite, judgedSite_ink (stageOf doc) doc, hdec', hp]
  obtain ⟨st0, h0⟩ : ∃ st0, Design.site? doc.palette .print .ink = some st0 := by
    have := judgedSite_ink (stageOf doc) doc
    simp only [judgedSite?, Option.map_eq_some_iff] at this
    obtain ⟨st0, h0, _⟩ := this
    exact ⟨st0, h0⟩
  have hr : st0.role = .ink := site?_role h0
  have he : (eventSites .page doc.palette).toList = [(Role.ink, doc.palette)] := by
    rw [eventSites_page, h0]
    simp [hr]
  have hps : ∃ rest, (pageSites doc (docWalk doc)).toList = (Role.ink, doc.palette) :: rest := by
    refine ⟨((pageEpochs (docWalk doc)).toList.map (Judged.page, ·)).flatMap
      (fun p => (eventSites p.1 p.2).toList), ?_⟩
    simp only [pageSites, pageEvents, Array.toList_flatMap, Array.toList_map, Array.toList_append,
      List.map_append, List.flatMap_append]
    simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil, he,
      List.cons_append, List.nil_append]
  have hE : 0 < (judgeSites (fun _ _ _ => none) (stageOf doc) (pageSites doc (docWalk doc))).size := by
    obtain ⟨rest, hrest⟩ := hps
    unfold judgeSites
    rw [← Array.foldl_toList, hrest, List.foldl_cons]
    exact foldlList_invariant (fun b => 0 < b.1.size) _ _ _ h1
      fun b x _ hb => Nat.lt_of_lt_of_le hb (judgeSite_diags_mono _ _ b x)
  simp only [docDiags, Array.size_append]
  omega

/-- Every pair the palette's design ships in print meets its need at the medium's size, `reported`
roles aside. -/
public def paletteContract (pal : Palette) (reported : List Role := []) (stage : Bool := false) :
    Bool :=
  (Design.sites pal .print).all fun st => st.passesAt stage || reported.contains st.role

/-- Every listing ink of every shipped style reads at the bundle's code floor on each listing ground. -/
public def listingContract (pal : Palette) : Bool :=
  let d := Design.ofPalette pal
  (none :: ListingStyle.all.map some).all fun style =>
    Listing.contract pal none style && Listing.contract pal (some d.standout.bg) style
      && (match d.titlepage with
          | some p => Listing.contract pal (some p.bg) style
          | none => true)

/-- Each text colour's cover is quieter than its active form and at least 3:1 from it
(SC 1.4.11); a role in `reported` is held to quieting alone. -/
public def coveredContract (pal : Palette) (reported : List Role := []) : Bool :=
  let d := Design.ofDoc { palette := pal }
  let cov := d.cover
  cov.hidden ||
  let visiblyCovered (r : Role) (c : Color) : Bool :=
    if reported.contains r then contrastMilli (cov.of c) d.bg < contrastMilli c d.bg
    else coverHolds d.bg c (cov.of c)
  visiblyCovered .ink d.fg
    && (match Design.declared? pal .alert with | some c => visiblyCovered .alert c | none => true)
    && (match Design.declared? pal .example with | some c => visiblyCovered .example c | none => true)
    && coverHolds d.bg d.fg d.inkCover

/-- Covering twice quiets further, for every text role the bundle ships. -/
public def coverMonotone (pal : Palette) : Bool :=
  let d := Design.ofDoc { palette := pal }
  let cov := d.cover
  cov.hidden ||
  let quieter (c : Color) : Bool :=
    contrastMilli (cov.of (cov.of c)) d.bg < contrastMilli (cov.of c) d.bg
  quieter d.fg
    && (match Design.declared? pal .alert with | some c => quieter c | none => true)
    && (match Design.declared? pal .example with | some c => quieter c | none => true)

/-- Each coloured use as the pair it stood in, furniture included. -/
public def usePairs (doc : Doc) : Array (Color × Color) :=
  (docUses doc (docWalk doc)).uses.map fun u => (u.color, u.surface)

/-- The (ink, ground) pairs the document judge enumerates: shipped sites and coloured uses, not
every placed pair (overlay dimming and picture labels lie outside it). -/
public def judgedPairs (doc : Doc) : Array (Color × Color) :=
  let uses := usePairs doc
  (shippedSites doc).filterMap (fun x =>
      (judgedSite? (stageOf doc) x.2 x.1).map fun st => (st.ink, st.ground))
    ++ uses

public theorem judged_covers (doc : Doc) :
    (∀ ev ∈ shippedEvents doc, ∀ st ∈ Design.sites ev.2 .print, st.role.row.judged = ev.1 →
      ∀ st', judgedSite? (stageOf doc) ev.2 st.role = some st' →
        (st'.ink, st'.ground) ∈ judgedPairs doc) ∧
    ∀ p ∈ usePairs doc, p ∈ judgedPairs doc := by
  refine ⟨fun ev hev st hst hj st' h' => ?_, fun p hp => Array.mem_append_right _ hp⟩
  have hsite : (st.role, ev.2) ∈ shippedSites doc := by
    unfold shippedSites
    refine Array.mem_flatMap.mpr ⟨ev, hev, ?_⟩
    obtain ⟨e, pal⟩ := ev
    simp only [eventSites, Array.mem_map, List.mem_toArray, List.mem_filter, beq_iff_eq]
    exact ⟨st, ⟨hst, by simpa using hj⟩, rfl⟩
  exact Array.mem_append_left _ (Array.mem_filterMap.mpr ⟨_, hsite, by rw [h']; rfl⟩)

private theorem judgeSite_id (site : ColorSite) (stage : Bool) (s : Array Diag × Array Site)
    (r : Role) (pal : Palette) (h : ∀ st, judgedSite? stage pal r = some st → st.passes = true) :
    judgeSite site stage s (r, pal) = s := by
  cases hst : judgedSite? stage pal r with
  | none => simp [judgeSite, hst]
  | some st => simp [judgeSite, hst, h st hst]

/-- The `palette:` phase line's facts: roles, sites, and the least margin above need (milli). -/
public structure PaletteSummary where
  roles : Nat
  schemes : Nat
  sites : Nat
  margin : Option Int
  seeded : Bool
  deriving Repr, BEq

/-- A palette's summary over the schemes it is judged in, each beside the
palette as that scheme carries it. -/
public def paletteSummaryIn (views : List (Scheme × Palette)) (seeded : Bool) : PaletteSummary :=
  let sites := views.flatMap fun (s, v) => Design.sites v s
  let margins := sites.map fun st => (contrastMilli st.ink st.ground : Int) - requiredIn st.scheme st.need
  { roles := (Role.all.filter fun r => views.any fun (s, v) => (Design.at v s r).isSome).length
    schemes := views.length
    sites := sites.length
    margin := margins.min?
    seeded := seeded }

public def paletteSummary (pal : Palette) (schemes : List Scheme) : PaletteSummary :=
  paletteSummaryIn (schemes.map (·, pal)) pal.seeded.isSome

/-- The palette summary for a web page, over the schemes it ships. -/
public def pageSummary (doc : Doc) : PaletteSummary :=
  let j := schemeJudge doc
  paletteSummaryIn (j.shipped.zip ((j.views.head?.map (·.2)).getD [])) doc.palette.seeded.isSome

/-- The phase line's words: roles, schemes, sites, the least margin — or,
where a site falls short of its need, by how much. -/
public def PaletteSummary.detail (p : PaletteSummary) : String :=
  let margin := match p.margin with
    | some m =>
      if m < 0 then s!"a site {ratioString (-m).toNat} short of its need"
      else s!"least margin {ratioString m.toNat}"
    | none => "no paired site"
  s!"{p.roles} roles, {p.schemes} scheme{if p.schemes == 1 then "" else "s"}, {p.sites} sites, " ++
    margin ++ (if p.seeded then ", generated from seeds" else "")

end LeanTex.Core.Contrast
