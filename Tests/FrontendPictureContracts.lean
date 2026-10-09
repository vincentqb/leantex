import LeanTex.Core.Elab

open LeanTex.Core

/-- Configuration provenance crosses the production frontend, including
boundary withdrawal, source erasure, diagnostic attribution and tallying.
Artifact equality for the tool gate is checked by `pictureKeyGateChecks`. -/
def frontendPictureCompositionChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t (name : String) (ok : Bool) := unless ok do ref.modify (name :: ·)
  let settings :=
    "\\tikzset{box/.style={rectangle,draw,minimum width=9mm,minimum height=6mm}}\n" ++
    "\\tikzset{other/.style={box},overlay}\n\\tikzset{sloped,overlay}\n"
  let drawing := "\\begin{tikzpicture}\\node[other] at (0,0) {A};\\end{tikzpicture}"
  let src := settings ++ "\\begin{document}" ++ drawing ++
    "\\cite{missing}\\end{document}trailing"
  let final ← pure (Elab.run "picture-contract.tex" src)
  let named := final.2.filterMap fun d =>
    if d.kind == .W0334 then d.subject else none
  t "all setting lines are named after frontend finalization"
    (named == #["picture:set:'overlay'", "picture:set:'sloped'", "picture:set:'overlay'"])
  t "a style defined by an earlier setting line is read"
    (!named.contains "picture:set:'box'")
  t "picture accounting precedes later document diagnostics"
    ((final.2.findIdx? (·.kind == .W0334)).getD final.2.size <
      (final.2.findIdx? (·.kind == .W0351)).getD 0 &&
     (final.2.findIdx? (·.kind == .W0351)).getD final.2.size <
      (final.2.findIdx? (·.kind == .W0001)).getD 0)
  let quiet ← pure (Elab.run "picture-contract.tex"
    (settings ++ "\\begin{document}prose\\end{document}"))
  t "settings alone do not claim a rendered loss"
    (!(quiet.2.any (·.kind == .W0334)))
  let raws := (Parse.parse "picture-contract.tex"
    (Lex.lex "picture-contract.tex" src).1).1
  let prepared := Elab.prepare "picture-contract.tex" raws
  let full ← pure (Elab.runPrepared "picture-contract.tex" prepared)
  t "prepared and finalized frontends retain the same named keys"
    ((full.2.1.filterMap fun d =>
      if d.kind == .W0334 then d.subject else none) == named)
  -- The former claim quantified over every raw tree. Settling a closing
  -- half discards its payload before configuration is collected.
  let pos : Pos := {}
  let keys : Array Parse.Raw := #[.word "overlay" pos]
  let discarded : Parse.Raw := .env (Parse.splitClose "invented")
    #[.ctrl "tikzset" pos, .group keys pos] pos
  let live := (Parse.parse "picture-contract.tex"
    (Lex.lex "picture-contract.tex" ("\\begin{document}\\begin{tikzpicture}" ++
      "\\draw (0,0) -- (1,0);\\end{tikzpicture}\\end{document}")).1).1
  let unsettled := #[discarded] ++ live
  let settled ← pure (Elab.prepare "picture-contract.tex" unsettled)
  let result ← pure (Elab.runRaws "picture-contract.tex" unsettled)
  t "raw singleton setting census can be discarded by preparation"
    (Compat.tikzsetKeys "picture-contract.tex" unsettled ==
        #[(⟨"picture-contract.tex", pos⟩, keys)] && settled.picSets.isEmpty)
  t "raw-census naming claim is false even with an engine picture"
    (Elab.enginePictures result.1.body > 0 &&
      !(Picture.unreadKeys [] (Picture.ofRaws keys)).isEmpty &&
      !(result.2.any (·.kind == .W0334)))
  -- A setting line is named in the file that wrote it, at its own token:
  -- never at the root's line of the same number, whose token there the
  -- note would otherwise take as its trigger.
  let keyFile := "synthetic/picture-keys.tex"
  let keyRoot := (Parse.parse "picture-contract.tex" (Lex.lex "picture-contract.tex"
    ("\\pictures{tool=none}\n\\begin{document}\n" ++
      "\\begin{tikzpicture}\\draw (0,0) -- (1,0);\\end{tikzpicture}\n\\end{document}")).1).1
  let keyChild := (Parse.parse keyFile (Lex.lex keyFile "% keys\n\\tikzset{sloped}").1).1
  let keyed ← pure (Elab.runRaws "picture-contract.tex"
    (#[.env (Parse.inputEnv keyFile) keyChild {}] ++ keyRoot))
  let sloped := keyed.2.filter (·.subject == some "picture:set:'sloped'")
  t "a setting line an included file wrote is named in that file, at its own token"
    (!sloped.isEmpty && sloped.all fun d =>
      d.span.any (fun s => s.file == keyFile && s.pos.line == 2 && s.pos.col == 1) &&
        d.trigger == some "\\tikzset")
