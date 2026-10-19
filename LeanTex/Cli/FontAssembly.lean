module

public import LeanTex.Core.Font
public import LeanTex.Core.FontDb
public import LeanTex.Core.Diag
public import LeanTex.Core.Ir
public import LeanTex.Cli.FontEnv
import LeanTex.Core.Math
import LeanTex.Cli.FontDiscovery
import LeanTex.Cli.DriverDiag
import LeanTex.Cli.SlotLoss
import LeanTex.Cli.FaceUse
import LeanTex.Core.Layout

/-! Font assembly shared by the driver and its artifact checks, resolving the document
against the caller's scan. -/

namespace LeanTex.Cli.FontAssembly

open LeanTex.Core

/-- The scan produced nothing usable at all. -/
private def noFontDiag : Diag := DriverDiag.noFont

/-- The host's face scan and its parses, taken once and shared by every assembly of a
run. -/
public structure FaceScan where
  faces : Array FontDb.Face
  docDirs : List String
  dirs : Array String
  diags : Array Diag
  /-- The roots only the engine was told about (`--font-dir`, `LEANTEX_FONT_PATH`), which
  no other program's font search reads. -/
  privateDirs : List String := []

/-- Which assembly a font set is: the document's settled one, or the provisional one a
picture's labels are measured against. -/
public inductive Purpose where
  /-- The environment the artifact is a function of. -/
  | settled
  /-- The face resolved from the preamble alone, with a math slot where the
  source's pictures set a formula. -/
  | provisional (math : Bool)
  deriving Repr, BEq, Inhabited

/-- The family a document's text is set in: a deck's sans, else its body, else the
engine's default family. -/
public def textFamilyIn (doc : Ir.Doc) (faces : Array FontDb.Face) : Option String :=
  let spec := doc.fonts
  let spec := if spec.body.isNone && spec.sans.isNone then
      { spec with body := FontDb.defaultFamily faces }
    else spec
  if doc.docClass == Ir.DocClass.slides then spec.sans.orElse fun _ => spec.body
  else spec.body.orElse fun _ => spec.sans

/-- The faces a document ships in its own directories, or the whole scan
where it ships none. -/
public def ownFaces (faces : Array FontDb.Face) (docDirs : List String) : Array FontDb.Face :=
  if docDirs.isEmpty then faces else faces.filter fun f =>
    docDirs.any fun dir => f.path.startsWith (if dir.endsWith "/" then dir else dir ++ "/")

/-- The typewriter default for an undeclared typewriter slot the document sets runs in
(`FontDb.monoPick`), answered from the document's own faces first; the second component
says whether the document ships it. -/
public def monoDefaultOf (doc : Ir.Doc) (faces : Array FontDb.Face) (docDirs : List String) :
    Option FontDb.MonoPick × Bool :=
  let textFamily := textFamilyIn doc faces
  -- premise: monoDefaultChecks — the default monospace follows the scan and the shipped faces
  let tex := doc.surface == .tex
  let declaredText := doc.fonts.body.isSome || doc.fonts.sans.isSome
  let own := ownFaces faces docDirs
  let wantsMono := doc.fonts.mono.isNone && (SlotLoss.slotsUsed doc).contains 2
  let ownPick := if wantsMono then FontDb.monoPick tex declaredText own textFamily else none
  let pick := ownPick.orElse fun _ =>
    if wantsMono then FontDb.monoPick tex declaredText faces textFamily else none
  (pick, !docDirs.isEmpty && ownPick.isSome)

/-- Every face a document can reach, the family slots crossed with the four variants,
loaded once and deduplicated by path, with per-glyph fallback precomputed over the
document's scalars. -/
public def buildFontSet (doc : Ir.Doc) (scan : FaceScan)
    (cache : FontEnv.Cache) (purpose : Purpose) (figureScalars : Array Char := #[])
    (sites : Array (String × Span) := #[]) :
    IO (Except Diag (Font.FontSet × Ir.Doc × Array Diag × Array String)) := do
  let spec := doc.fonts
  let bare := spec.body.isNone && spec.sans.isNone && spec.mono.isNone
    && spec.math.isNone
  if bare then
    if let some path ← IO.getEnv "LEANTEX_FONT" then
      match ← FontEnv.loadOverride path with
      | .error d => return .error d
      | .ok (f, path) =>
        let coverage := f.mathAlphabetCoverage spec.mathSources
        let (doc, alphaDiags) := Ir.resolveMathAlphas coverage f.family doc
        let set : Font.FontSet := { Font.FontSet.ofFace f with mathAlphabets := coverage }
        return .ok (set, doc, alphaDiags, #[path])
  let mut diags : Array Diag := scan.diags
  let docDirs := scan.docDirs
  let faces := scan.faces
  -- A declared text family no installed face or declared face file serves is named at its
  -- declaration, and its slot, faces included, reads as undeclared.
  let served (slot : Nat) (family : String) : Bool := FontDb.corners.all fun (w, i) =>
    (FontDb.resolveVariant faces family (spec.faceFor slot w i)
      { bold := w == 700, italic := i }).isSome
  let mut missing : Array String := #[]
  let mut kept := spec
  for (slot, declared) in [(0, spec.body), (1, spec.sans), (2, spec.mono)] do
    let some family := declared | continue
    if served slot family then continue
    unless missing.contains family do
      missing := missing.push family
      diags := diags.push (FontEnv.familyMissingIn faces family
        (FaceUse.familySite sites doc.fonts family))
    let unfaced := kept.faces.filter (·.1.1 != slot)
    kept := match slot with
      | 0 => { kept with body := none, faces := unfaced }
      | 1 => { kept with sans := none, faces := unfaced }
      | _ => { kept with mono := none, faces := unfaced }
  let spec := kept
  let resolving := { doc with fonts := spec }
  let spec := if spec.body.isNone && spec.sans.isNone then
      { spec with body := FontDb.defaultFamily faces }
    else spec
  let slides := doc.docClass == Ir.DocClass.slides
  let textFamily := textFamilyIn resolving faces
  let tex := doc.surface == .tex
  let own := ownFaces faces docDirs
  let (pick, monoOwn) := monoDefaultOf resolving faces docDirs
  let spec := match pick with
    | some p =>
      { spec with mono := some p.family
                  faces := spec.faces ++ (p.faces.map fun (c : (Nat × Bool) × String) =>
                    ((2, c.1.1, c.1.2), c.2)).toArray }
    | none => spec
  let mut italicCode : Option Bool := none
  let mut fonts : Array Font := #[]
  let mut paths : Array String := #[]
  let mut index : Array ((Nat × Nat × Bool) × Nat) := #[]
  -- A provisional assembly resolves only the text slot, the face a node label sets in.
  let slots : List (Nat × Option String) :=
    match purpose with
    | .provisional _ => [(0, spec.body)]
    | .settled => [(0, spec.body), (1, spec.sans), (2, spec.mono)] ++
      spec.families.toList.zipIdx.map fun ((_, fam), i) => (Ir.familySlotBase + i, some fam)
  -- beamer's default font theme is sans serif, so a deck's text slot is its sans family.
  let resolveName (slot : Nat) : Option String :=
    match slot with
    | 0 => textFamily
    | 1 => spec.sans.orElse fun _ => spec.body
    | 2 => spec.mono.orElse fun _ => spec.body
    | s => spec.slotFamily s
  -- A slot's declared faces live under the slot its family resolution reads.
  let effectiveOf (slot : Nat) : Nat := match slot with
    | 0 => if (slides || spec.body.isNone) && spec.sans.isSome then 1 else 0
    | 1 => if spec.sans.isSome then 1 else 0
    | 2 => if spec.mono.isSome then 2 else 0
    | s => s
  -- A sans or typewriter slot reading the body's family still takes the faces declared for it.
  let ownFirst (slot : Nat) : Bool := (slot == 1 || slot == 2) && effectiveOf slot != slot
  let declaredFace (slot : Nat) (weight : Nat) (italic : Bool) : Option String :=
    (if ownFirst slot then spec.faceFor slot weight italic else none).orElse fun _ =>
      spec.faceFor (effectiveOf slot) weight italic
  -- Off-corner keys: the styles' weights plus every declared face's, as fontspec loads them.
  let standard : List (Nat × Bool) := FontDb.corners
  let extraKeysFor (slot : Nat) : List (Nat × Bool) :=
    ((Layout.docWeightKeys doc).toList.filterMap fun (s, w, i) =>
      if s == slot then some (w, i) else none) ++
    (spec.faces.toList.filterMap fun ((s, w, i), _) =>
      if (s == effectiveOf slot || (ownFirst slot && s == slot)) && !(standard.contains (w, i))
      then some (w, i) else none)
  -- A weight off lualatex's corners sets in the nearest corner's file (W0366).
  let nearestFile (slot weight : Nat) (italic : Bool) : Option (Nat × String) :=
    if slot != 2 || weight == 400 || weight == 700 then none else
    match pick with
    | some p =>
      let corner := if weight < 550 then 400 else 700
      (p.faces.find? (·.1 == (corner, italic))).map fun c => (corner, c.2)
    | none => none
  for (slot, _) in slots do
    let some family := resolveName slot | continue
    for (weight, italic) in standard ++ (extraKeysFor slot).eraseDups do
      let pool := if slot == 2 && monoOwn then own else faces
      let answer ← match nearestFile slot weight italic with
        | some (corner, file) =>
          pure ((FontDb.resolveWeight pool family (some file) corner italic).map fun (f, s) =>
            (f, s.orElse fun _ => if f.weight == weight then none
              else some (.weight family weight f)))
        | none =>
          if slot == 2 && monoOwn then
            pure (FontDb.resolveWeight own family (declaredFace slot weight italic) weight italic)
          else cache.resolveWeight faces family (declaredFace slot weight italic) weight italic
      match answer with
      | none =>
        unless missing.contains family do
          missing := missing.push family
          diags := diags.push (FontEnv.familyMissingIn faces family
            (FaceUse.familySite sites doc.fonts family))
      | some (face, sub) =>
        -- premise: monoDefaultChecks — a declared typewriter family names each italic substitution
        let upright := slot == 2 && pick.isSome && italic && !face.italic
        if upright && !diags.any (·.kind == .N0031) then
          let asked := match italicCode with
            | some a => a
            | none => (Layout.docFaceKeys doc).any fun (s, _, i) => s == 2 && i
          italicCode := some asked
          if asked then
            diags := diags.push (DriverDiag.monoUpright family tex (own := monoOwn))
        if let some s := sub then
          unless upright && s matches .variant _ do
            let d := DriverDiag.substituted s
            -- Slots share families: a substitution is recorded once per message and detail.
            unless diags.any (fun e => e.message == d.message && e.detail == d.detail) do
              diags := diags.push d
        match paths.findIdx? (· == face.path) with
        | some i => index := index.push ((slot, weight, italic), i)
        | none =>
          match ← cache.parse face.path with
          | .error e =>
            diags := diags.push (DriverDiag.fontFileUnusable face.path e)
          | .ok f =>
            index := index.push ((slot, weight, italic), fonts.size)
            fonts := fonts.push f
            paths := paths.push face.path
  let wantsMath : Bool := match purpose with
    | .provisional math => math
    | .settled => !(Layout.docMathScalars doc).isEmpty
  let mathSource := (Ir.mathFaceRequest doc).bind (·.source)
  let math ← FontEnv.resolveMath faces spec.math spec.body
    wantsMath fonts paths missing (some cache) (source := mathSource)
    (declaredAt := spec.math.bind (FaceUse.familySite sites doc.fonts ·))
  fonts := math.fonts
  paths := math.paths
  missing := math.missing
  diags := diags ++ math.diags
  let mathIdx := math.index
  if fonts.isEmpty then
    -- No face loaded (an empty scan or unparsable files): the default family's, or a refusal.
    match FontDb.defaultFamily faces |>.bind (FontDb.resolve faces · {}) with
    | none => return .error ((diags.find? (·.severity == .error)).getD noFontDiag)
    | some (face, _) =>
      match ← cache.parse face.path with
      | .error _ => return .error ((diags.find? (·.severity == .error)).getD noFontDiag)
      | .ok f =>
        let coverage := f.mathAlphabetCoverage spec.mathSources
        let (doc, alphaDiags) := Ir.resolveMathAlphas coverage f.family doc
        let set : Font.FontSet := { Font.FontSet.ofFace f with mathAlphabets := coverage }
        return .ok (set, doc, diags ++ alphaDiags, #[face.path])
  -- Alphabets resolve before `docScalars`, so a missing one never reaches the fallback.
  let (doc, mathAlphabets, alphaDiags) :=
    match mathIdx.bind (fonts[·]?) with
    | some f =>
      let coverage := f.mathAlphabetCoverage spec.mathSources
      let (resolved, ds) := Ir.resolveMathAlphas coverage f.family doc
      (resolved, coverage, ds)
    | none =>
      let coverage : Math.MathAlphabetCoverage := { sources := spec.mathSources }
      let (resolved, ds) := Ir.resolveMathAlphas coverage "math face" doc
      (resolved, coverage, ds)
  diags := diags ++ alphaDiags
  let mut fallback : Array (Char × Nat) := #[]
  let mut uncovered : Array Char := #[]
  -- A drawn SVG's text sets in these faces too (`Layout.storeScalars`).
  let scalars := figureScalars.foldl (fun a c => if a.contains c then a else a.push c)
    (Layout.docScalars doc)
  for c in scalars do
    match fonts.findIdx? (fun f => (f.gid c).isSome) with
    | some i => fallback := fallback.push (c, i)
    | none => uncovered := uncovered.push c
  unless uncovered.isEmpty do
    -- A face the document ships answers first for every scalar it covers.
    let inDocDir (path : String) : Bool :=
      docDirs.any fun d => path.startsWith (d ++ "/") || path.startsWith d
    for (c, path) in ← FontDiscovery.fallbackPicksPreferring inDocDir faces uncovered do
      match paths.findIdx? (· == path) with
      | some i => fallback := fallback.push (c, i)
      | none =>
        match ← cache.parse path with
        | .error _ => pure ()  -- undecodable candidate; the scalar stays dropped
        | .ok f =>
          fallback := fallback.push (c, fonts.size)
          fonts := fonts.push f
          paths := paths.push path
  let set : Font.FontSet := {
    fonts := fonts
    index := index
    fallback := fallback
    math := mathIdx
    mathAlphabets := mathAlphabets
    missing := missing }
  return .ok (set, doc, diags, paths)

/-- The font roles a boundary standalone sets in: the document's declared roles and, for
an undeclared one, the family the engine resolved, when the scan found it in a root the
tool also searches. -/
-- premise: boundaryFaceChecks — only a family in a shared root travels
public def boundaryFonts (doc : Ir.Doc) (fs : Font.FontSet) (scan : FaceScan) :
    Ir.FontSpec :=
  let spec := doc.fonts
  let under (dirs : List String) (path : String) : Bool :=
    dirs.any fun d => path.startsWith (d ++ "/") || path == d
  let travels (fam : String) : Bool :=
    scan.faces.any fun f =>
      f.family == fam && !under scan.docDirs f.path && !under scan.privateDirs f.path
  let text := (fs.index.find? (·.1 == (0, 400, false))).bind fun (_, i) => fs.fonts[i]?
  let math := fs.math.bind (fs.fonts[·]?)
  let code := (monoDefaultOf doc scan.faces scan.docDirs).1.bind fun p =>
    if p.faces.isEmpty then some p.family else none
  { spec with
    body := if spec.body.isSome || spec.sans.isSome then spec.body
      else (text.map (·.family)).filter travels
    mono := spec.mono.orElse fun _ => code.filter travels
    math := spec.math.orElse fun _ => (math.map (·.family)).filter travels }

end LeanTex.Cli.FontAssembly
