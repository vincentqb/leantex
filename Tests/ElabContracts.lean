import LeanTex.Core.Elab

open LeanTex.Core

/-- Site accounting follows reporting calls, not repetitions of source text.
The preamble counterexample rules out the stronger, false duplication claim. -/
def elabWarningContractChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t (name : String) (ok : Bool) := unless ok do ref.modify (name :: ·)
  let ctx : Elab.Ctx := { file := "probe.tex" }
  let pos : Pos := { line := 1, col := 1 }
  let first := Elab.warnOnceState ctx "ctrl:zzone" .W0301 "first" pos
    (some "suggestion") false {}
  let second := Elab.warnOnceState ctx "ctrl:zzone" .W0301 "second" pos
    none true first
  let other := Elab.warnOnceState ctx "ctrl:zztwo" .W0301 "other" pos
    none false second
  let scopedState := Elab.warnOnceState ctx "ctrl:zzone" .W0301 "PDF" pos
    none false other (output := some .pdf)
  let counted := Diag.tallySites scopedState.diags
  t "warning contract: repeat calls remain separate diagnostic sites"
    (counted.size == 4)
  t "warning contract: code, subject and output determine each site count"
    (counted.map (·.sites) == #[2, 0, 1, 1])
  t "warning contract: demotion preserves the repeated site"
    (second.diags.size == 2 && (second.diags[1]?).any (·.demoted))
  t "warning contract: a new output scope has its own visible first site"
    ((scopedState.diags.back?).any fun d => d.output == some .pdf && !d.demoted)
  let source (body : String) :=
    "\\zzpreamble{zzkeyword}\n\\begin{document}\n" ++ body ++ "\n\\end{document}"
  let one := (Elab.run "probe.tex" (source "Plain body.")).2
  let two := (Elab.run "probe.tex" (source "Plain body. Plain body.")).2
  let keyed (ds : Array Diag) := ds.filter (·.subject == some "ctrl:zzpreamble")
  t "warning contract: duplicating a body does not duplicate preamble diagnostics"
    ((keyed one).size == 1 && (keyed two).size == 1)
