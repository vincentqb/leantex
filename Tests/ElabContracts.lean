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

/-- Alias equivalence belongs to the refused title body's declarative
read-out. A conditional operand still names the command the source wrote:
normalizing it globally would change which declarations execute. -/
def elabTitleBoundaryChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t (name : String) (ok : Bool) := unless ok do ref.modify (name :: ·)
  let style (out : Ir.Doc × Array Diag) : Option Ir.ElementStyle :=
    out.1.styles.find? "titlepage"
  let align (out : Ir.Doc × Array Diag) : Option String :=
    (style out).bind (·.align)
  let refusalSites (out : Ir.Doc × Array Diag) :
      Array (Option Span × Option String × Option String × Option String) :=
    (out.2.filter (·.kind == .W0361)).map
      (fun d => (d.span, d.subject, d.refused, d.trigger))
  let conditional (name : String) :=
    "\\newcommand{\\inserttitle}{}\n\\ifdefined\\" ++ name ++
      "\n\\style{titlepage}{align=left}\n\\else\n\\style{titlepage}{align=right}\n\\fi\n" ++
      "\\begin{document}Text.\\end{document}"
  let beamer ← pure (Elab.run "probe.tex" (conditional "inserttitle"))
  let internal ← pure (Elab.run "probe.tex" (conditional "@title"))
  t "title alias boundary: a conditional reads the actual source spelling"
    (align beamer == some "left" && align internal == some "right")
  let template (name : String) :=
    "\\documentclass{article}\n\\title{Title}\\author{Author}\\date{Date}\n" ++
      "\\renewcommand{\\maketitle}{\\centering\\bfseries\\large\\hrule\\@title\\" ++
      name ++ "\\hrule\\vskip 2pt}\n\\begin{document}\\maketitle\\end{document}"
  for (b, l) in Elab.beamerInsertAlias do
    let left ← pure (Elab.run "probe.tex" (template b))
    let right ← pure (Elab.run "probe.tex" (template l))
    t s!"title alias boundary: {b} keeps the whole elaborated style"
      (style left == style right && (style left).isSome)
    t s!"title alias boundary: {b} keeps the refusal site and provenance"
      (!(refusalSites left).isEmpty && refusalSites left == refusalSites right)

/-- Unknown-option erasure belongs to the actual recovery arm. Bindings,
definitions and palette roles are counterexamples to erasure for every
context; package internals are a different, code-consuming refusal. -/
def elabUnknownDispatchChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t (name : String) (ok : Bool) := unless ok do ref.modify (name :: ·)
  let ctx : Elab.Ctx := { file := "probe.tex" }
  let raws (name option : String) (withOption : Bool) : Array Parse.Raw :=
    #[.ctrl name {line := 1, col := 1}] ++
      (if withOption then
        #[.sym '[' {line := 1, col := 5}, .word option {line := 1, col := 6},
          .sym ']' {line := 1, col := 7}]
       else #[]) ++
      #[.group #[.word "kept" {line := 1, col := 9}] {line := 1, col := 8}]
  let run (c : Elab.Ctx) (name option : String) (withOption : Bool) :=
    (Elab.elabInlines c (raws name option withOption)).run {}
  let expected : Array Ir.Inline :=
    #[.located {file := ctx.file, pos := {line := 1, col := 9}} #[.text "kept"]]
  for name in #["zzz", "zzunregistered", "insertunknown"] do
    t s!"unknown dispatch: registry admits {name}" (Elab.recoversInlineName ctx name)
    for option in #["", "ignored", "kept"] do
      let withOption := run ctx name option true
      let withoutOption := run ctx name option false
      t s!"unknown dispatch: {name} drops option '{option}' and keeps positioned content"
        (withOption.1 == expected && withOption.1 == withoutOption.1)
      t s!"unknown dispatch: {name} names exactly its opening source site"
        (withOption.2.diags.size == 1 && withOption.2.diags.all fun d =>
          d.kind == .W0301 && d.subject == some ("ctrl:" ++ name) &&
          d.span == some {file := ctx.file, pos := {line := 1, col := 1}})
  for name in #["textbf", "inserttitle", "faIcon", "hfill"] do
    t s!"unknown dispatch: registry rejects the implemented name {name}"
      (!Elab.recoversInlineName ctx name)
  let cmd : Elab.UserCmd :=
    { name := "zzz", params := #[], body := #[.word "replacement" {}],
      span := {file := ctx.file, pos := {}} }
  let contexts : Array (String × Elab.Ctx) :=
    #[("argument", {ctx with args := #[("zzz", some #[.text "bound"])]}),
      ("definition", {ctx with user := #[cmd], limit := 1}),
      ("palette", {ctx with palette := {entries := #[("zzz", {r := 0, g := 0, b := 0})]}})]
  for (label, context) in contexts do
    t s!"unknown dispatch: a {label} binding is outside the recovery domain"
      (!Elab.recoversInlineName context "zzz")
    t s!"unknown dispatch: a {label} binding falsifies arbitrary-context erasure"
      (Ir.plainText (run context "zzz" "ignored" true).1 !=
        Ir.plainText (run context "zzz" "ignored" false).1)
  let packageCtx : Elab.Ctx := {ctx with file := "probe.sty"}
  t "unknown dispatch: package internals use code-consuming recovery"
    (!Elab.recoversInlineName packageCtx "zz@internal" &&
      Elab.recoversInlineName ctx "zz@internal" &&
      (run packageCtx "zz@internal" "ignored" true).1.isEmpty &&
      (run ctx "zz@internal" "ignored" true).1 == expected)
