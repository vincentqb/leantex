module

public import Tests.Support
public import LeanTex.Core.SeedPalette

public section

open LeanTex.Core

/-! A light palette's colours stand at their medium's floor on the paper and no darker: a seed
meeting it ships as itself, and each derived tone is its family's lightest that meets it. -/

namespace Tests.PaletteFloor

/-- How far above its floor a derived tone may stand on the paper: 0.15 of a ratio, two 8-bit
steps of a mid-lightness tone. -/
def floorSlack : Nat := 150

/-- Invented seeds on light papers, the last an orange meeting a deck's floor on white as given. -/
def seeds : List (String × SeedPalette.Seeds) := [
  ("a black ink and a yellow accent",
    { ink := Ir.Color.black, paper := Ir.Color.white, accent := Ir.Color.ofHtml 0xFA 0xCC 0x15 }),
  ("a violet ink and an orange accent",
    { ink := Ir.Color.ofHtml 0x2B 0x24 0x40, paper := Ir.Color.white,
      accent := Ir.Color.ofHtml 0xE8 0x5D 0x2A }),
  ("a warm ink on cream and a teal accent",
    { ink := Ir.Color.ofHtml 0x3B 0x2F 0x2A, paper := Ir.Color.ofHtml 0xFB 0xF6 0xEC,
      accent := Ir.Color.ofHtml 0x0D 0x94 0x88 }),
  ("a neutral ink and a magenta accent",
    { ink := Ir.Color.ofHtml 0x1A 0x1A 0x1A, paper := Ir.Color.white,
      accent := Ir.Color.ofHtml 0xC0 0x26 0xD3 }),
  ("an orange meeting a deck's floor",
    { ink := Ir.Color.ofHtml 0x1C 0x19 0x17, paper := Ir.Color.white,
      accent := Ir.Color.ofHtml 0xF0 0x6E 0x00 })]

/-- Every colour a light palette generates stands at its floor on the paper, at each depth: the
seed where it meets the floor, else within `floorSlack` of it, a container accent setting no text,
and every coloured role `CodeColor.roleGap` from the ink. -/
def floorChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  t "floor: each class names its depth, a poster a deck's grounds under a document's text floor"
    (Ir.DocClass.slides.record.groundDepth == .decks &&
      Ir.DocClass.article.record.groundDepth == .documents &&
      Ir.DocClass.poster.record.groundDepth == .posters &&
      Ir.GroundDepth.posters.body == Ir.GroundDepth.decks.body && Ir.GroundDepth.posters.text == 4500)
  let apart (x y : Ir.Color) : Bool :=
    decide (CodeColor.roleGap * CodeColor.roleGap ≤ ContrastSolve.deltaEOkSq x y)
  for (depth, d, text) in [("a deck", Ir.GroundDepth.decks, 3000),
      ("a document", Ir.GroundDepth.documents, 4500), ("a poster", Ir.GroundDepth.posters, 4500)] do
    for (label, s) in seeds do
      match SeedPalette.generate s (s.targets d) with
      | .error f => t s!"floor, {depth}, {label}: generates, not fail at {reprStr f.role}" false
      | .ok g =>
        let c := g.colors
        let at_ (floor : Nat) (seed : Option Ir.Color) (x : Ir.Color) : Bool :=
          let r := Contrast.contrastMilli x s.paper
          seed.any (· == x) && floor ≤ Contrast.contrastMilli x s.paper ||
            decide (floor ≤ r ∧ r < floor + floorSlack)
        let seedAt (floor : Nat) : Option Ir.Color :=
          if floor ≤ Contrast.contrastMilli s.accent s.paper then some s.accent else none
        if s.container (s.targets d) then
          t s!"floor, {depth}, {label}: the accent serves as a container, marking the alert"
            (c.alertMark == some s.accent && c.alert == s.ink && c.alertMark.all (apart · s.ink))
        else
          t s!"floor, {depth}, {label}: the accent's text tone stands apart from the ink"
            (apart c.accentText s.ink)
          t s!"floor, {depth}, {label}: the accent's text tone stands at the text floor on the paper"
            (at_ text (seedAt text) c.accentText && (seedAt text).all (· == c.accentText))
          t s!"floor, {depth}, {label}: the alert is the accent's text tone" (c.alert == c.accentText)
          t s!"floor, {depth}, {label}: the accent's edge stands at the marks' floor on the paper"
            (at_ 3000 (seedAt 3000) c.accentEdge && (seedAt 3000).all (· == c.accentEdge))
        t s!"floor, {depth}, {label}: the muted ink stands at the text floor on the paper"
          (at_ text none c.muted)
        t s!"floor, {depth}, {label}: the diagram's muted tone stands at the marks' floor"
          (at_ 3000 none c.diagramMuted)

/-- A run a light page's fill holds stands at its floor on that fill, its family's tone there,
where the paper's tones meet the floor on the paper alone (`SeedPalette.facing`). -/
def fillChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fonts ← serifFacesSet | failures ref "fill: the serif faces load"
  let (doc, ds) := elabStr (dvDeck
    "\\palette[seeds]{ ink = #1C1917, paper = #FFFFFF, accent = #F06E00 }\n"
    ("\\begin{frame}\n\\begin{block}{A block}\nAn \\alert{alerted} word, a " ++
      "\\textcolor{muted}{quiet} one and a \\textcolor{accent-text}{toned} one.\n\\end{block}\n" ++
      "A \\alert{paper} word.\n\\end{frame}"))
  t "fill: the report finds no pairing short" (ds.all (·.code != "W0315"))
  match doc.palette.seeded with
  | none => t "fill: the deck is seeded" false
  | some st =>
    let surface := st.colors.surface
    t "fill: the block's body stands on a fill darker than the paper"
      (decide (Contrast.contrastMilli Ir.Color.black surface < Contrast.contrastMilli Ir.Color.black st.seeds.paper))
    let lines := allLines (layoutOf fonts doc)
    for w in ["alerted", "quiet", "toned"] do
      t s!"fill: the {w} run stands at the deck's floor on the block's fill"
        ((wordRun lines w).any fun (c, _) => decide (st.targets.text ≤ Contrast.contrastMilli c surface))
    t "fill: on the paper the alert ships the accent itself, which meets the floor there"
      ((wordRun lines "paper").any (·.1 == st.seeds.accent))

/-- The tones a generated palette derives, its seeds aside. -/
private def derivedOf (c : SeedPalette.Colors) : List Ir.Color :=
  [c.surface, c.surfaceStrong, c.rule, c.accentWash, c.accentSoft, c.muted, c.diagramMuted,
    c.mutedOnInverse, c.accentText, c.accentEdge, c.accentOnInverse, c.alert, c.alertBand,
    c.exampleBand] ++ c.exampleText.toList

/-- Every tone a palette derives stands out of the disliked region on every page and ground, and
still generates: a dark page's olive, a light page's yellows carried to a dark one and a dark one's
gold to a light one, text on the ink, a run on a dark band, and a cleared hue's 8-bit rounding. -/
def regionChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let gen (label : String) (s : SeedPalette.Seeds) (tg : SeedPalette.Targets) : IO Unit := do
    match SeedPalette.generate s tg with
    | .error f => t s!"region, {label}: generates, not fail at {reprStr f.role}" false
    | .ok g =>
      t s!"region, {label}: no derived tone is disliked"
        ((derivedOf g.colors).all fun x => x == s.accent || x == s.ink || !dislikedBox x)
  let depths := [("a deck", Ir.GroundDepth.decks), ("a document", Ir.GroundDepth.documents)]
  let olive := Ir.Color.ofHtml 0x80 0x80 0x00
  for (pname, paper) in [("a navy paper", Ir.Color.ofHtml 0x1B 0x24 0x30),
      ("a blue-black paper", Ir.Color.ofHtml 0x00 0x2B 0x36)] do
    let s : SeedPalette.Seeds := { ink := Ir.Color.ofHtml 0xF4 0xF1 0xEA, paper, accent := olive }
    for (dn, d) in depths do
      gen s!"an olive accent on {pname}, {dn}" s (s.targets d)
  for (label, accent) in [("a yellow", Ir.Color.ofHtml 0xFA 0xCC 0x15),
      ("a lemon", Ir.Color.ofHtml 0xF0 0xE4 0x42), ("a mustard", Ir.Color.ofHtml 0xA6 0x8A 0x00)] do
    let s : SeedPalette.Seeds := { ink := Ir.Color.ofHtml 0x1C 0x19 0x17, paper := Ir.Color.white, accent }
    match s.carry true with
    | none => t s!"region, {label} carried to a dark page: carries" false
    | some c =>
      t s!"region, {label} carried to a dark page: its accent is not disliked" (!dislikedBox c.accent)
      for (dn, d) in depths do
        gen s!"{label} carried to a dark page, {dn}" c (c.targets d)
        gen s!"{label} carried to a dark page asking more, {dn}" c ((c.targets d).more)
  let gold : SeedPalette.Seeds :=
    { ink := Ir.Color.white, paper := Ir.Color.black, accent := Ir.Color.ofHtml 0xFF 0xD7 0x00 }
  gen "a gold on a black page, its text on the ink" gold (gold.targets .decks)
  match gold.carry false with
  | none => t "region, a gold carried to a light page: carries" false
  | some c =>
    t "region, a gold carried to a light page: its accent is not disliked" (!dislikedBox c.accent)
    gen "a gold carried to a light page" c (c.targets .decks)
  let dark := Ir.Color.ofHtml 0x7A 0x6A 0x00
  let mustard : SeedPalette.Seeds := { ink := Ir.Color.black, paper := Ir.Color.white, accent := dark }
  gen "a dark mustard on a light page, its text on the ink" mustard (mustard.targets .decks)
  let grey : SeedPalette.Seeds :=
    { ink := Ir.Color.black, paper := Ir.Color.ofHtml 0xEC 0xE8 0xE6, accent := Ir.Color.ofHtml 0x8A 0x7A 0x00 }
  gen "a dark yellow asking more on a warm grey paper" grey ((grey.targets .decks).more)
  let band := Ir.Color.ofHtml 0x2B 0x24 0x40
  match SeedPalette.generate mustard (mustard.targets .decks) with
  | .error _ => t "region, a dark mustard's palette generates" false
  | .ok g =>
    let st : SeedPalette.SeedState :=
      { seeds := mustard, targets := mustard.targets .decks, blocks := .tonal, colors := g.colors }
    t "region, a dark mustard's alert on a dark band takes a tone at its floor there, not disliked"
      ((st.toneOn .alert band).any fun (c, _) =>
        decide (st.targets.text ≤ Contrast.contrastMilli c band) && !dislikedBox c)

end Tests.PaletteFloor
