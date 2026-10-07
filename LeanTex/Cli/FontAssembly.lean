import LeanTex.Cli.FontDiscovery
import LeanTex.Cli.FontEnv
import LeanTex.Core.Layout

/-! Font assembly shared by the driver and its artifact checks. Host discovery
stays with the caller; this module resolves the document against that scan. -/

namespace LeanTex.Cli.FontAssembly

open LeanTex.Core

/-- Every slot and variant mapped to one face: the shape of a single-font set. -/
private def singleFaceIndex : Array ((Nat × Nat × Bool) × Nat) :=
  ((List.range 3).flatMap fun slot =>
    [((slot, 400, false), 0), ((slot, 700, false), 0),
     ((slot, 400, true), 0), ((slot, 700, true), 0)]).toArray

/-- The scan produced nothing usable at all. -/
private def noFontDiag : Diag := DriverDiag.noFont

/-- The scan is the host's answer and the parses are the filesystem's, so
both are taken once and handed to every assembly that needs them. Two
assemblies do need them: the provisional font environment a picture's
labels are measured against, resolved from the preamble, and the final one
the document settles. -/
structure FaceScan where
  faces : Array FontDb.Face
  docDirs : List String
  dirs : Array String
  diags : Array Diag

/-- Which assembly a font set is: the one the document settles on, or the
provisional one a picture's labels are measured against before the body has
been read. A value rather than a flag — it says what the caller is doing,
and the assembly reads its own consequences off it. -/
inductive Purpose where
  /-- The environment the artifact is a function of. -/
  | settled
  /-- The face resolved from the preamble alone, with a math slot where the
  source's pictures set a formula. -/
  | provisional (math : Bool)
  deriving Repr, BEq, Inhabited

/-- Every face a document can reach: the three family slots crossed with the
four bold/italic variants, loaded once and deduplicated by path. Faces the
document never uses are still loaded but not embedded — `Pdf.keepFaces` decides
what reaches the file. A document with no `\fonts` is served by the same
mechanism: `FontDb.defaultFamily` picks a family from the scan and it fills
the body slot, so the default exists wherever any font does, by construction.
A `\fonts{ dir = ... }` is searched first, resolved against the document's own
directory like `\input`: a document that ships its fonts renders the same on
every host, whatever else is installed.

Per-glyph fallback is precomputed here, against the document's own scalars
(`Layout.docScalars`): a scalar some declared face covers maps to the first
covering face in declaration order, and one no declared face covers goes to
`FontDiscovery.fallbackPicks`, whose face is loaded at the end of the set. Layout
consults the map only on a missing glyph. The `LEANTEX_FONT` override is a
single face with no scan behind it, so it gets no fallback.

Whether a math face loads is the document's own answer — whether a formula
stands anywhere — except for the provisional assembly, which has no body to
ask and takes the answer from what its pictures set (`Elab.picWants`): a
node label setting `$x$` is the commonest reason a preamble-resolved face
would measure differently from the final one, and a math face is also the
most expensive parse a document makes, so it is resolved early exactly when
a picture would use it.

Neither `ui` nor `file` is an argument any more: the host's answer and the
document's own directories were the only reasons to hold them, and both are
now the scan's (`scanFaces`). Assembly is a function of the document, the
faces in hand, the parses already made, and which assembly this is. -/
def buildFontSet (doc : Ir.Doc) (scan : FaceScan)
    (cache : FontEnv.Cache) (purpose : Purpose) :
    IO (Except Diag (Font.FontSet × Ir.Doc × Array Diag × String)) := do
  let spec := doc.fonts
  let bare := spec.body.isNone && spec.sans.isNone && spec.mono.isNone
    && spec.math.isNone
  if bare then
    if let some path ← IO.getEnv "LEANTEX_FONT" then
      match ← FontEnv.loadOverride path with
      | .error d => return .error d
      | .ok (f, path) =>
        -- The override is one real face: read its own alphabet coverage so a
        -- math override face is not falsely told it lacks every alphabet, and
        -- carry the resolver's N0018 diagnostics out instead of dropping them.
        let coverage := f.mathAlphabetCoverage spec.mathSources
        let (doc, alphaDiags) := Ir.resolveMathAlphas coverage f.family doc
        let set : Font.FontSet := {
          fonts := #[f]
          index := singleFaceIndex
          mathAlphabets := coverage }
        return .ok (set, doc, alphaDiags, path)
  let mut diags : Array Diag := scan.diags
  let docDirs := scan.docDirs
  let faces := scan.faces
  -- Mono and math are independent roles; neither supplies the text default.
  let spec := if spec.body.isNone && spec.sans.isNone then
      { spec with body := FontDb.defaultFamily faces }
    else spec
  let mut fonts : Array Font.Font := #[]
  let mut paths : Array String := #[]
  let mut index : Array ((Nat × Nat × Bool) × Nat) := #[]
  let mut missing : Array String := #[]
  -- A provisional assembly resolves the *text* slot and nothing else: a
  -- node label sets in the document's text face, and the sans and mono
  -- slots cost a search of the whole scan per key for a face no label is
  -- going to ask for. A label that does ask — `\texttt` inside a node —
  -- measures against font 0 here, the settled face disagrees, and the
  -- driver elaborates again; the cost of being wrong is bounded and the
  -- cost of being thorough was not.
  let slots : List (Nat × Option String) :=
    match purpose with
    | .provisional _ => [(0, spec.body)]
    | .settled => [(0, spec.body), (1, spec.sans), (2, spec.mono)]
  -- A slot the document did not name falls back to the body family, and the
  -- body's declared per-variant faces come with it.
  -- beamer sets a presentation in its sans family: the class's default
  -- font theme is sans serif (beamer user guide §18, "the default font
  -- theme uses sans serif fonts"), so in the slides class the default
  -- text slot is the declared sans family, and its declared per-variant
  -- faces come with it. The engine's three slots carry no separate serif
  -- default for decks: \rmfamily follows the deck's face.
  let slides := doc.docClass == Ir.DocClass.slides
  let resolveName (slot : Nat) : Option String :=
    match slot with
    -- A document that names a sans family and no body family reads its
    -- text in that face. This was already the shipped behaviour — with no
    -- slot-0 entry every text lookup fell through to font 0, the sans
    -- regular — but as an accident of load order that no weight or
    -- variant could refine; naming it makes the sans's declared faces
    -- (its Medium upright, its Light) reach the text the card sets.
    | 0 => if slides then spec.sans.orElse fun _ => spec.body
      else spec.body.orElse fun _ => spec.sans
    | 1 => spec.sans.orElse fun _ => spec.body
    | _ => spec.mono.orElse fun _ => spec.body
  -- A slot's declared faces live under its *effective* slot: the one its
  -- family resolution reads (a deck's body — or a sans-only document's —
  -- follows the sans declaration).
  let effectiveOf (slot : Nat) : Nat := match slot with
    | 1 => if spec.sans.isSome then 1 else 0
    | 2 => if spec.mono.isSome then 2 else 0
    | _ => if (slides || spec.body.isNone) && spec.sans.isSome then 1 else 0
  let declaredFace (slot : Nat) (weight : Nat) (italic : Bool) : Option String :=
    spec.faceFor (effectiveOf slot) weight italic
  -- The off-corner keys this document can ask the index for: the weights
  -- its styles really use (`docWeightKeys`, exact so W0366 never fires
  -- for a weight nobody asked), plus every declared face's own key — a
  -- declaration is a request to load, as fontspec's is, so a declared
  -- Light ships in the HTML set even before a run selects it.
  let standard : List (Nat × Bool) :=
    [(400, false), (700, false), (400, true), (700, true)]
  let extraKeysFor (slot : Nat) : List (Nat × Bool) :=
    ((Layout.docWeightKeys doc).toList.filterMap fun (s, w, i) =>
      if s == slot then some (w, i) else none) ++
    (spec.faces.toList.filterMap fun ((s, w, i), _) =>
      if s == effectiveOf slot && !(standard.contains (w, i)) then some (w, i)
      else none)
  for (slot, _) in slots do
    let some family := resolveName slot | continue
    for (weight, italic) in standard ++ (extraKeysFor slot).eraseDups do
      match ← cache.resolveWeight faces family (declaredFace slot weight italic)
          weight italic with
      | none =>
        unless missing.contains family do
          missing := missing.push family
          -- A host with TeX Live installed has a thousand families; listing
          -- them all is not help. Name the ones that look like what was asked
          -- for, and how to see the rest.
          let all := FontDb.families faces
          diags := diags.push (DriverDiag.familyMissing family
            (FontDb.nearest all family).toList all.size)
      | some (face, sub) =>
        if let some s := sub then
          let d := DriverDiag.substituted s
          -- Slots share families, so the same substitution surfaces repeatedly.
          unless diags.any (·.message == d.message) do
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
  -- The math face: resolved like any named family, and installed only when
  -- it carries an OpenType MATH table (`FontEnv.resolveMath`, which is
  -- handed this scan rather than performing one).
  let wantsMath : Bool := match purpose with
    | .provisional math => math
    | .settled => !(Layout.docMathScalars doc).isEmpty
  let math ← FontEnv.resolveMath faces spec.math spec.body
    wantsMath fonts paths missing (some cache)
  fonts := math.fonts
  paths := math.paths
  missing := math.missing
  diags := diags ++ math.diags
  let mathIdx := math.index
  if fonts.isEmpty then
    -- Every named family failed and `diags` carries the errors; the caller
    -- stops on them, but nothing downstream may ever see an empty set.
    match FontDb.defaultFamily faces |>.bind (FontDb.resolve faces · {}) with
    | none => return .error ((diags.find? (·.severity == .error)).getD noFontDiag)
    | some (face, _) =>
      match ← cache.parse face.path with
      | .error _ => return .error ((diags.find? (·.severity == .error)).getD noFontDiag)
      | .ok f =>
        -- The single fallback face answers its own coverage, and its N0018
        -- diagnostics join the errors already collected rather than being
        -- dropped.
        let coverage := f.mathAlphabetCoverage spec.mathSources
        let (doc, alphaDiags) := Ir.resolveMathAlphas coverage f.family doc
        let set : Font.FontSet := {
          fonts := #[f]
          index := singleFaceIndex
          mathAlphabets := coverage }
        return .ok (set, doc, diags ++ alphaDiags, face.path)
  -- The math face answers its alphabet ranges once. Resolve the shared IR
  -- before `docScalars`, so a wholly unavailable alphabet never becomes a
  -- request the host fallback scan can answer by accident.
  let (doc, mathAlphabets, alphaDiags) :=
    match mathIdx.bind (fonts[·]?) with
    | some f =>
      let coverage := f.mathAlphabetCoverage spec.mathSources
      let (resolved, ds) := Ir.resolveMathAlphas coverage f.family doc
      (resolved, coverage, ds)
    | none =>
      -- No math face resolved: the coverage carries no range, so the resolver
      -- names every used alphabet as lost (N0018). Keep those diagnostics —
      -- they are appended once below, so the normal path is not doubled.
      let coverage : Math.MathAlphabetCoverage := { sources := spec.mathSources }
      let (resolved, ds) := Ir.resolveMathAlphas coverage "math face" doc
      (resolved, coverage, ds)
  diags := diags ++ alphaDiags
  -- Per-glyph fallback: map every scalar the resolved document uses to the first
  -- declared face covering it; scalars none covers go to the scan.
  let mut fallback : Array (Char × Nat) := #[]
  let mut uncovered : Array Char := #[]
  for c in Layout.docScalars doc do
    match fonts.findIdx? (fun f => (f.gid c).isSome) with
    | some i => fallback := fallback.push (c, i)
    | none => uncovered := uncovered.push c
  unless uncovered.isEmpty do
    -- The document's own directories outrank the host: a shipped face
    -- answers first for every scalar it covers.
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
    mathAlphabets := mathAlphabets }
  return .ok (set, doc, diags, String.intercalate ", " paths.toList)

end LeanTex.Cli.FontAssembly
