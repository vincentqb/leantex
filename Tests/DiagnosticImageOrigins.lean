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

/-- N0376 quotes the exact authored command at its recorded site, including a
macro invocation before expansion. Source spans alone justify no trigger in raw
IR. Attribution preserves the census, source span, acceptance and output scope. -/
def diagnosticImageOriginChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t (name : String) (ok : Bool) : IO Unit :=
    unless ok do ref.modify (name :: ·)
  let missing (ds : Array Diag) := ds.filter (·.kind == .N0376)
  let hasTrigger (ds : Array Diag) (trigger : String) :=
    ds.size == 1 && ds.all (·.trigger == some trigger)
  let hasHeader (ds : Array Diag) (location trigger : String) :=
    hasTrigger ds trigger && ds.all fun d =>
      (Render.human false d).startsWith s!"ℹ [N0376] - {location} - {trigger}\n"
  let noTrigger (ds : Array Diag) :=
    ds.size == 1 && ds.all (·.trigger.isNone)
  -- Backslash separates NFC slices: it survives decomposition, stops mark
  -- reordering, and cannot participate in a table-driven composition. The
  -- arithmetic Hangul rules are confined to non-ASCII Jamo/syllable ranges.
  let nfc := Nfc.tables.get
  let escape := '\\'
  let decompositions := nfc.decomp.toList
  t "image origin: NFC tables preserve the escape-boundary premise"
    (nfc.ccc.getD escape.val 0 == 0 && !nfc.decomp.contains escape.val &&
      decompositions.all (fun (_, parts) => !parts.contains escape) &&
      nfc.comp.toList.all fun (pair, result) =>
        pair.toNat / 0x100000000 != escape.toNat &&
        pair.toNat % 0x100000000 != escape.toNat && result != escape)
  let commandEvidence (tokens : Array Lex.Token) := tokens.filterMap fun tok =>
    match tok.tok with
    | .ctrl _ | .verb _ _ => some tok.pos.command
    | _ => none
  let prefixAgrees (leadText : String) :=
    let file := "nfc-prefix-evidence.tex"
    let source := leadText ++ " \\\u212A{} " ++ leadText ++ " \\includegraphics{poster.pdf}"
    let (tokens, ds) := Lex.lex file source
    let (normalized, normalizedDs) := Lex.lex file (Nfc.normalize source)
    -- Token equality ignores command evidence but includes normalized positions.
    ds.isEmpty && normalizedDs.isEmpty && tokens == normalized &&
      commandEvidence tokens == #[some "\\\u212A", some "\\includegraphics"]
  t "image origin: every decomposition scalar preserves normalized sites and raw triggers"
    (!decompositions.isEmpty && decompositions.all fun (scalar, _) =>
      prefixAgrees (String.ofList [Char.ofNat scalar.toNat]))
  t "image origin: every expanded decomposition preserves normalized sites and raw triggers"
    (!decompositions.isEmpty && decompositions.all fun (_, parts) =>
      prefixAgrees (String.ofList parts.toList))
  t "image origin: reordered marks and arithmetic Hangul preserve escape alignment"
    (["e\u0301\u0327", "\u1100\u1161\u11A8", "\uAC01"].all prefixAgrees)
  let skippedFile := "skipped-escapes.tex"
  let skippedSource := "e\u0301 % \\ignored\n\\verb|e\u0301\\ignored|\n" ++
    "\\\\" ++ "\\\u212A{} \\includegraphics{poster.pdf}"
  let (skippedTokens, skippedDs) := Lex.lex skippedFile skippedSource
  t "image origin: skipped and paired escapes preserve normalized tokens and positions"
    (skippedDs.isEmpty &&
      skippedTokens == (Lex.lex skippedFile (Nfc.normalize skippedSource)).1)
  t "image origin: comments, verb bodies and paired escapes do not shift raw triggers"
    (commandEvidence skippedTokens ==
      #[some "\\verb", some "\\\\", some "\\\u212A", some "\\includegraphics"])
  -- Several authored spellings share a normalized control token. Evidence
  -- keeps the full source slice, and ordinary following tokens inherit none.
  for (label, written, name) in [
      ("control-space", "\\ ", " "),
      ("control-LF", "\\\n", " "),
      ("control-CRLF", "\\\r\n", " "),
      ("Kelvin", "\\\u212A", "K")] do
    let file := s!"{label}-evidence.tex"
    let (tokens, lexDs) := Lex.lex file (written ++ "{tail} next\n\nlast")
    t s!"image origin: {label} evidence preserves normalized token semantics"
      (lexDs.isEmpty && tokens.map (·.tok) ==
        #[.ctrl name, .lbrace, .word "tail", .rbrace, .space,
          .word "next", .space, .par, .word "last"])
    let evidence := (tokens[0]?).bind (·.pos.command)
    t s!"image origin: {label} lexer evidence keeps the exact authored slice"
      (evidence == some written)
    let prepared := Elab.prepare file (Parse.parse file tokens).1
    t s!"image origin: {label} source index keeps the exact authored slice"
      (prepared.sourceTriggers[(file, 1, 1)]? == some written)
    let following := tokens.toList.drop 1
    t s!"image origin: {label} evidence is absent on following ordinary tokens"
      (!following.isEmpty && following.all fun tok =>
        tok.pos.command.isNone &&
          (prepared.sourceTriggers[(file, tok.pos.line, tok.pos.col)]?).isNone)
  let (animated, animatedDs, spans) := imageOriginTex "animation.tex"
    "before\n\n\\animategraphics{12}{poster.pdf}{}{}"
  let ads := missing animatedDs
  t "image origin: a direct animation quotes animategraphics"
    (hasHeader ads "animation.tex:3:1" "\\animategraphics")
  t "image origin: animation keeps its source and one informational diagnostic"
    (ads.size == 1 && ads.all fun d =>
      d.span == some ⟨"animation.tex", { line := 3, col := 1 }⟩ &&
      d.subject == some "poster.pdf" && d.kind.loss == .info &&
      d.severity == .note && d.sites == 1 && d.output.isNone)
  let mut macroWarnings : Array Diag := #[]
  for (label, body) in [
      ("plain", "\\animategraphics{12}{poster.pdf}{}{}"),
      ("conditional", "\\iftrue\\animategraphics{12}{poster.pdf}{}{}\\fi")] do
    for name in ["movie", "showclip", "\u212A"] do
      let file := s!"{label}-{name}-animation.tex"
      let invocation := "\\" ++ name
      let (_, macroDs, _) := imageOriginTex file
        ("\\newcommand{" ++ invocation ++ "}{" ++ body ++ "}\n" ++
          "\\begin{document}\nbefore\n" ++ invocation ++ "\n\\end{document}")
      let mds := missing macroDs
      t s!"image origin: a {label} {name} macro keeps its invocation span"
        (mds.size == 1 && mds.all fun d =>
          d.span == some ⟨file, { line := 4, col := 1 }⟩ &&
          d.subject == some "poster.pdf" && d.kind.loss == .info &&
          d.severity == .note && d.sites == 1 && d.output.isNone)
      t s!"image origin: a {label} {name} macro quotes its authored invocation"
        (hasHeader mds s!"{file}:4:1" invocation)
      macroWarnings := macroWarnings ++ mds
  let (_, staticDs, _) := imageOriginTex "ordinary.tex" "\\includegraphics{poster.pdf}"
  let staticWarnings := missing staticDs
  t "image origin: a static image quotes includegraphics"
    (hasHeader staticWarnings "ordinary.tex:1:1" "\\includegraphics")
  let prefixedFile := "decomposed-prefix.tex"
  let prefixedSource := "e\u0301 \\includegraphics{poster.pdf}"
  let (prefixedTokens, prefixedLexDs) := Lex.lex prefixedFile prefixedSource
  let imageTokens := prefixedTokens.filter (·.tok == .ctrl "includegraphics")
  t "image origin: preceding NFC contraction preserves exact ASCII command evidence"
    (prefixedLexDs.isEmpty && imageTokens.size == 1 &&
      prefixedTokens.any (·.tok == .word "\u00E9") &&
      prefixedTokens.all fun tok => tok.pos.command ==
        (if tok.tok == .ctrl "includegraphics" then some "\\includegraphics" else none))
  let (_, prefixedDs, _) := imageOriginTex prefixedFile prefixedSource
  let prefixedWarnings := missing prefixedDs
  -- Follow the lexer's position convention; preceding NFC contraction must
  -- neither shift the evidence onto another token nor break attribution.
  t "image origin: an ASCII image after decomposed text keeps its lexer site and header"
    (imageTokens.size == 1 && imageTokens.all fun tok =>
      hasHeader prefixedWarnings s!"{prefixedFile}:{tok.pos.line}:{tok.pos.col}"
        "\\includegraphics" && prefixedWarnings.all fun d =>
          d.span == some ⟨prefixedFile, tok.pos⟩ && d.subject == some "poster.pdf")
  -- The reader, not the filename suffix, decides this is Markdown.
  let (mdRaws, mdDs) := Md.read "included.data" "![](poster.pdf)"
  let (_, markdownDs, _) := Elab.runRawsSpanned "included.data" mdRaws mdDs
  let markdownWarnings := missing markdownDs
  t "image origin: lowered Markdown invents no TeX command or image label"
    (noTrigger markdownWarnings)
  let child := imageOriginParse "child.tex" "\n\\animategraphics{12}{poster.pdf}{}{}"
  let (_, includedDs, _) := Elab.runRawsSpanned "root.tex"
    #[.env (Parse.inputEnv "child.tex") child {}]
  let includedWarnings := missing includedDs
  t "image origin: included animation quotes its authored command in its own file"
    (hasHeader includedWarnings "child.tex:2:1" "\\animategraphics" &&
      includedWarnings.all fun d =>
        d.span == some ⟨"child.tex", { line := 2, col := 1 }⟩)
  let mut mixedWarnings : Array Diag := #[]
  for (first, body) in [
      ("\\includegraphics",
        "\\includegraphics{poster.pdf}\n\\animategraphics{12}{poster.pdf}{}{}"),
      ("\\animategraphics",
        "\\animategraphics{12}{poster.pdf}{}{}\n\\includegraphics{poster.pdf}")] do
    let (_, ds, _) := imageOriginTex "mixed.tex" body
    let mds := missing ds
    t s!"image origin: reused source quotes its first site's {first} command"
      (hasHeader mds "mixed.tex:1:1" first && mds.all fun d =>
        d.span == some ⟨"mixed.tex", { line := 1, col := 1 }⟩ &&
        d.subject == some "poster.pdf" && d.sites == 1)
    mixedWarnings := mixedWarnings ++ mds
  let (_, repeatedDs, _) := imageOriginTex "repeated.tex"
    "\\animategraphics{12}{poster.pdf}{}{}\n\\animategraphics{24}{poster.pdf}{}{}"
  let repeatedWarnings := missing repeatedDs
  t "image origin: repeated animation quotes its first site and accounts for one source"
    (hasHeader repeatedWarnings "repeated.tex:1:1" "\\animategraphics" &&
      repeatedWarnings.all (·.sites == 1))
  let pic (body : String) :=
    "\\begin{tikzpicture}\n" ++ body ++ "\n\\end{tikzpicture}"
  let (native, nativeDs, nativeSpans) := imageOriginTex "native.tex"
    ("\\pictures{tool=none}\n" ++ pic "\\fill (0,0) rectangle (1,1);")
  let nativeWarnings := missing nativeDs
  t "image origin: a native picture quotes its authored environment and keeps its key"
    (hasHeader nativeWarnings "native.tex:2:1" "\\begin" &&
      nativeWarnings.all (·.subject == some "picture#0"))
  let (_, spacedNativeDs, _) := imageOriginTex "spaced-native.tex"
    ("\\pictures{tool=none}\n\\begin   {tikzpicture}\n" ++
      "\\fill (0,0) rectangle (1,1);\n\\end{tikzpicture}")
  let spacedNativeWarnings := missing spacedNativeDs
  t "image origin: whitespace before the environment name still quotes only begin"
    (hasHeader spacedNativeWarnings "spaced-native.tex:2:1" "\\begin" &&
      spacedNativeWarnings.all (·.subject == some "picture#0"))
  let boundarySource := pic "\\draw (0,0) circle (1);"
  let (boundary, boundaryDs, boundarySpans) := imageOriginTex "boundary.tex" boundarySource
  let spanOf := Elab.ReqSpans.spanOf boundarySpans.images
  let shipped := Ir.picAltDiags boundary spanOf (fun _ => true)
  t "image origin: raw shipped boundary IR keeps its source without inventing a label"
    ((missing boundaryDs).isEmpty && noTrigger shipped &&
      shipped.all fun d =>
        d.span == some ⟨"boundary.tex", { line := 1, col := 1 }⟩ &&
        (Render.human false d).startsWith "ℹ [N0376] - boundary.tex:1:1\n")
  let boundaryPrepared := Elab.prepare "boundary.tex"
    (imageOriginParse "boundary.tex" boundarySource)
  let attributed := shipped.map boundaryPrepared.sourceTriggers.attribute
  t "image origin: shipped boundary attribution quotes its authored environment"
    (hasHeader attributed "boundary.tex:1:1" "\\begin")
  t "image origin: boundary attribution changes only the trigger"
    (attributed.map (fun d => { d with trigger := none }) == shipped)
  t "image origin: an unshipped boundary picture raises no alt diagnostic"
    ((Ir.picAltDiags boundary spanOf (fun _ => false)).isEmpty)
  t "image origin: absent source evidence stays absent"
    ((Ir.altDiags animated).all (·.trigger.isNone) &&
      (Ir.picAltDiags boundary (fun _ => none) (fun _ => true)).all (·.trigger.isNone))
  t "image origin: raw native IR does not fabricate a label from a span"
    (noTrigger (Ir.altDiags native (Elab.ReqSpans.spanOf nativeSpans.images)))
  for image in [
      "\\includegraphics[alt={A chart}]{poster.pdf}",
      "\\includegraphics[artifact]{poster.pdf}",
      "\\animategraphics[alt={A chart}]{12}{poster.pdf}{}{}"] do
    t "image origin: described and decorative images remain outside the census"
      ((missing (imageOriginTex "described.tex" image).2.1).isEmpty)
  let warnings := ads ++ macroWarnings ++ staticWarnings ++ prefixedWarnings ++
    markdownWarnings ++ includedWarnings ++ mixedWarnings ++ repeatedWarnings ++ nativeWarnings ++
    spacedNativeWarnings ++ shipped ++ attributed
  for d in warnings do
    let (accepted, didAccept) := d.accept #["N0376"] false
    t "image origin: informational attribution needs no acceptance and retains common output scope"
      (!didAccept && accepted.severity == .note &&
        accepted == d &&
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
  t "image origin: human animation header quotes the authored animategraphics token"
    (ads.any fun d =>
      (Render.human false d).startsWith "ℹ [N0376] - animation.tex:3:1 - \\animategraphics\n")
  let rawImages := Ir.altDiags animated (Elab.ReqSpans.spanOf spans.images)
  t "image origin: existing request span API remains sufficient"
    (rawImages.map (·.span) == ads.map (·.span))
  t "image origin: raw image IR does not fabricate a label from a span"
    (noTrigger rawImages)

end Tests
