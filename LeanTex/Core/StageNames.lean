module

public import LeanTex.Core.Ir
import LeanTex.Core.NameClaim

namespace LeanTex.Core.Ir

/-! The in-page names a deck's stages answer to, which both artifacts set. -/

/-- A step's label: its frame's label and the step's number. -/
@[expose] public def stepLabel (label : String) (k : Nat) : String := s!"{label}.{k}"

/-- The route a section page answers to: its place among the deck's section pages. -/
@[expose] public def sectionRoute (n : Nat) : String := s!"section-{n}"

/-- The routes step `k` of a `steps`-step frame labelled `label` answers to: the label for a frame
of one step, else the step's label, the first step's also the bare label. -/
public def stepRoutes (label : String) (steps k : Nat) : Array String :=
  if steps ≤ 1 then #[label]
  else if k == 1 then #[label, stepLabel label 1]
  else #[stepLabel label k]

/-- The anchors a deck frame claims: its own, from its title's slug or `slide`, and past one step
each step's, from its own anchor and the step's number. -/
public structure FrameAnchors where
  frame : SectionAnchor
  steps : Array SectionAnchor
  deriving Repr, BEq

/-- The anchors a deck's top-level blocks claim at their body indices: each frame's and its steps',
and each level-one section's, from its title's slug or `section`. -/
public structure DeckAnchors where
  frames : Array (Option FrameAnchors)
  sections : Array (Option SectionAnchor)

/-- A deck's frames, their steps and its sections claim their anchors in one ledger in flow order. -/
public def deckAnchors (body : Array Block) : DeckAnchors := Id.run do
  let mut taken : NameClaim.Claims .dashed := {}
  let mut frames : Array (Option FrameAnchors) := #[]
  let mut sections : Array (Option SectionAnchor) := #[]
  for b in body do
    match b with
    | .frame title _ _ _ _ =>
      let text := firstPageText title
      let base := if (slug title).isEmpty then "slide" else slug title
      let (id, clash, next) := taken.claim base text
      taken := next
      let mut steps : Array SectionAnchor := #[]
      if frameSteps b > 1 then
        for k in [1:frameSteps b + 1] do
          let stepBase := s!"{id}-{k}"
          let (sid, sclash, next) := taken.claim stepBase text
          taken := next
          steps := steps.push { base := stepBase, id := sid, clash := sclash }
      frames := frames.push (some { frame := { base, id, clash }, steps })
      sections := sections.push none
    | .section 1 _ _ title =>
      let base := if (slug title).isEmpty then "section" else slug title
      let (id, clash, next) := taken.claim base (firstPageText title)
      taken := next
      frames := frames.push none
      sections := sections.push (some { base, id, clash })
    | _ =>
      frames := frames.push none
      sections := sections.push none
  return { frames, sections }

/-- Each top-level frame's anchors at its body index (`deckAnchors`). -/
public def frameAnchors (body : Array Block) : Array (Option FrameAnchors) :=
  (deckAnchors body).frames

/-- The names step `k` of the frame at body index `i` answers to: on its first step the frame's
anchor, past one step the step's anchor, and its routes. -/
public def frameStepNames (anchors : Array (Option FrameAnchors)) (labels : Array (Option String))
    (i steps k : Nat) : Array String :=
  let own := match anchors[i]?.join with
    | some fa =>
      (if k == 1 then #[fa.frame.id] else #[]) ++ ((fa.steps[k - 1]?).map (·.id)).toArray
    | none => #[]
  own ++ stepRoutes ((labels[i]?.join).getD "slide") steps k

/-- Each section page's route at its body index, the deck's section pages counted in flow order. -/
public def Doc.sectionRoutes (doc : Doc) : Array (Option String) := Id.run do
  let mut n := 0
  let mut out : Array (Option String) := #[]
  for b in doc.body do
    if b matches .section .. && doc.outside b == .stage then
      out := out.push (some (sectionRoute n))
      n := n + 1
    else out := out.push none
  return out

end LeanTex.Core.Ir
