import LeanTex.Core.Elab
import LeanTex.Core.MdDesugar
import LeanTex.Cli.Render
import Lean.Data.Json

open LeanTex.Core LeanTex.Cli

namespace Tests

private def imageOriginParse (file text : String) : Array Parse.Raw :=
  (Parse.parse file (Lex.lex file text).1).1

private def imageOriginTex (file text : String) : Ir.Doc × Array Diag × Elab.ReqSpans :=
  Elab.runRawsSpanned file (imageOriginParse file text)

/-- The delayed alternative judge names the object kind its IR preserves,
never guesses a frontend or macro spelling from an image request. Adding that
label must preserve the census, source span, acceptance and output scope. -/
def diagnosticImageOriginChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t (name : String) (ok : Bool) : IO Unit :=
    unless ok do ref.modify (name :: ·)
  let missing (ds : Array Diag) := ds.filter (·.kind == .W0376)
  let hasTrigger (ds : Array Diag) (trigger : String) :=
    ds.size == 1 && ds.all (·.trigger == some trigger)
  let (animated, animatedDs, spans) := imageOriginTex "animation.tex"
    "before\n\n\\animategraphics{12}{poster.pdf}{}{}"
  let ads := missing animatedDs
  t "image origin: a direct animation has a generic image label"
    (hasTrigger ads "image")
  t "image origin: animation keeps its source and one standard warning"
    (ads.size == 1 && ads.all fun d =>
      d.span == some ⟨"animation.tex", { line := 3, col := 1 }⟩ &&
      d.subject == some "poster.pdf" && d.kind.loss == .standard &&
      d.severity == .warning && d.sites == 1 && d.output.isNone)
  let mut macroWarnings : Array Diag := #[]
  for (label, body) in [
      ("plain", "\\animategraphics{12}{poster.pdf}{}{}"),
      ("conditional", "\\iftrue\\animategraphics{12}{poster.pdf}{}{}\\fi")] do
    let file := s!"{label}-macro-animation.tex"
    let (_, macroDs, _) := imageOriginTex file
      ("\\newcommand{\\movie}{" ++ body ++ "}\n\
        \\begin{document}\nbefore\n\\movie\n\\end{document}")
    let mds := missing macroDs
    t s!"image origin: a {label} animation macro keeps its invocation span"
      (mds.size == 1 && mds.all fun d =>
        d.span == some ⟨file, { line := 4, col := 1 }⟩ &&
        d.subject == some "poster.pdf" && d.kind.loss == .standard &&
        d.severity == .warning && d.sites == 1 && d.output.isNone)
    t s!"image origin: a {label} animation macro does not invent a source command"
      (hasTrigger mds "image")
    macroWarnings := macroWarnings ++ mds
  let (_, staticDs, _) := imageOriginTex "ordinary.tex" "\\includegraphics{poster.pdf}"
  t "image origin: a static image has a generic image label"
    (hasTrigger (missing staticDs) "image")
  -- The reader, not the filename suffix, decides this is Markdown.
  let (mdRaws, mdDs) := Md.read "included.data" "![](poster.pdf)"
  let (_, markdownDs, _) := Elab.runRawsSpanned "included.data" mdRaws mdDs
  t "image origin: lowered Markdown is never called includegraphics"
    (hasTrigger (missing markdownDs) "image")
  let child := imageOriginParse "child.tex" "\n\\animategraphics{12}{poster.pdf}{}{}"
  let (_, includedDs, _) := Elab.runRawsSpanned "root.tex"
    #[.env (Parse.inputEnv "child.tex") child {}]
  t "image origin: included animation keeps its file and generic image label"
    (hasTrigger (missing includedDs) "image" &&
      (missing includedDs).all fun d =>
        d.span == some ⟨"child.tex", { line := 2, col := 1 }⟩)
  for body in [
      "\\includegraphics{poster.pdf}\n\\animategraphics{12}{poster.pdf}{}{}",
      "\\animategraphics{12}{poster.pdf}{}{}\n\\includegraphics{poster.pdf}"] do
    let (_, ds, _) := imageOriginTex "mixed.tex" body
    t "image origin: mixed requests for one source do not claim one command"
      (hasTrigger (missing ds) "image")
  let (_, repeatedDs, _) := imageOriginTex "repeated.tex"
    "\\animategraphics{12}{poster.pdf}{}{}\n\\animategraphics{24}{poster.pdf}{}{}"
  t "image origin: repeated animation still accounts for one source"
    (hasTrigger (missing repeatedDs) "image" &&
      (missing repeatedDs).all (·.sites == 1))
  let pic (body : String) :=
    "\\begin{tikzpicture}\n" ++ body ++ "\n\\end{tikzpicture}"
  let (_, nativeDs, _) := imageOriginTex "native.tex"
    ("\\pictures{tool=none}\n" ++ pic "\\fill (0,0) rectangle (1,1);")
  t "image origin: a native picture has a picture label and stable key"
    (hasTrigger (missing nativeDs) "picture" &&
      (missing nativeDs).all (·.subject == some "picture#0"))
  let (boundary, boundaryDs, boundarySpans) := imageOriginTex "boundary.tex"
    (pic "\\draw (0,0) circle (1);")
  let spanOf := Elab.ReqSpans.spanOf boundarySpans.images
  let shipped := Ir.picAltDiags boundary spanOf (fun _ => true)
  t "image origin: a shipped boundary picture keeps its source and label"
    ((missing boundaryDs).isEmpty && hasTrigger shipped "picture" &&
      shipped.all fun d => d.span == some ⟨"boundary.tex", { line := 1, col := 1 }⟩)
  t "image origin: an unshipped boundary picture raises no alt warning"
    ((Ir.picAltDiags boundary spanOf (fun _ => false)).isEmpty)
  t "image origin: absent source evidence stays absent"
    ((Ir.altDiags animated).all (·.trigger.isNone) &&
      (Ir.picAltDiags boundary (fun _ => none) (fun _ => true)).all (·.trigger.isNone))
  for image in [
      "\\includegraphics[alt={A chart}]{poster.pdf}",
      "\\includegraphics[artifact]{poster.pdf}",
      "\\animategraphics[alt={A chart}]{12}{poster.pdf}{}{}"] do
    t "image origin: described and decorative images remain outside the census"
      ((missing (imageOriginTex "described.tex" image).2.1).isEmpty)
  let warnings := ads ++ macroWarnings ++ shipped
  for d in warnings do
    let (accepted, didAccept) := d.accept #["W0376"] false
    t "image origin: attribution does not change acceptance or common output scope"
      (didAccept && accepted.severity == .note &&
        accepted == d.demote &&
        Diag.forOutputs #[.pdf] #[d] == #[d] &&
        Diag.forOutputs #[.html] #[d] == #[d])
    let plain := { d with trigger := none }
    match Lean.Json.parse (Render.porcelainDiag d),
        Lean.Json.parse (Render.porcelainDiag plain) with
    | .ok (.obj after), .ok (.obj before) =>
      t "image origin: porcelain differs only by the optional trigger field"
        (Lean.Json.obj (after.erase "trigger") == Lean.Json.obj before &&
          ((Lean.Json.obj after).getObjValAs? String "trigger").toOption == d.trigger)
    | _, _ => t "image origin: porcelain remains valid JSON" false
  t "image origin: human animation header uses a generic image label"
    (ads.any fun d =>
      (Render.human false d).startsWith "⚠ [W0376] - animation.tex:3:1 - image\n")
  t "image origin: existing request span API remains sufficient"
    ((Ir.altDiags animated (Elab.ReqSpans.spanOf spans.images)).map (·.span) ==
      ads.map (·.span))

end Tests
