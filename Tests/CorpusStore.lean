module

public import Tests.Support
public import LeanTex.Cli.Driver
public import LeanTex.Core.FigureStore
public import LeanTex.Core.FigureAlt

public section

/-! The corpus's images, read as the driver reads them, for the suites that
judge what the corpus ships: the census, the artifact tier, the backends. -/

open LeanTex.Core LeanTex.Cli

/-- The corpus fixture's images, read from `testdata/corpus/` as the driver reads them; boundary
pictures stay unfulfilled. -/
def corpusStore (doc : Ir.Doc) (fs : Option Font.FontSet := none) : IO Image.Store := do
  let mut fetched : Array (Image.Request × Image.Fetch) := #[]
  let mut svgs : Array (Option Driver.SvgFetch) := #[]
  for req in Ir.imageRequests doc do
    let src := req.src
    let mut f : Image.Fetch := .missing src
    let mut svg : Option Driver.SvgFetch := none
    for cand in Image.sourceCandidates src do
      let p := System.FilePath.mk "testdata/corpus" / cand
      if ← p.pathExists then
        let bytes ← IO.FS.readBinFile p
        let href := if cand == src then "" else cand
        -- An SVG takes the native route with no converter, as a host with no tool ships it.
        if Image.isSvg cand then
          let r ← Driver.svgFetch src bytes req.page doc.info.locale.tag none
          f := .decoded href r.res (some bytes) none (some bytes) none
          svg := some r
        else
          let decoded := Image.decodeRequest .default bytes req
          f := .decoded href (decoded.map (·.1)) none (decoded.toOption.bind (·.2)) (some bytes) none
        break
    fetched := fetched.push (req, f)
    svgs := svgs.push svg
  let store := FigureStore.attach (Image.fulfilRequests fetched).1
    (svgs.map (·.map Driver.SvgFetch.drawn))
  -- A drawn figure's text sets in the page's faces, and a moving one gets its still face.
  match fs with
  | none => return store
  | some fs => return (FigureStore.settle fs store).1

/-- The document with each drawn figure's own `<title>` as the alternative it leaves undeclared, as
the driver gives it. -/
def corpusTitled (doc : Ir.Doc) (store : Image.Store) : Ir.Doc :=
  FigureAlt.titled (store.entries.filterMap fun en => (en.vector.bind (·.title)).map (en.src, ·)) doc
