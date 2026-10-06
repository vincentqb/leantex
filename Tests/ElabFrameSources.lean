import LeanTex.Core.Elab

open LeanTex.Core LeanTex.Core.Parse

private def frameAt (p : Pos) (body : Array Raw := #[]) : Raw :=
  .env "frame" body p

private def exactSpan (a b : Span) : Bool :=
  a == b && a.pos.origins == b.pos.origins && a.pos.command == b.pos.command

private def exactSites (actual expected : Array (Nat × Span)) : Bool :=
  actual.size == expected.size &&
    (actual.zip expected).all fun ((i, a), (j, b)) => i == j && exactSpan a b

/-- The metadata belongs to the block that actually survives elaboration.
Equal or empty frames cannot be identified by their content; splicing,
macro ownership, and title-frame flattening must follow the emitted shape.
These are elaboration tests, not claims about rendered page contents. -/
def elabFrameSourceChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t (name : String) (ok : Bool) := unless ok do ref.modify (name :: ·)
  let first : Pos := { line := 7, col := 3, command := some "\\begin" }
  let second : Pos := { line := 19, col := 5, command := some "\\begin" }
  let ctx : Elab.Ctx := { file := "frames.tex", slides := true }
  let check (name : String) (body : Array Raw) (expected : Array (Nat × Span)) := do
    let (blocks, st) ← pure ((Elab.elabBlocks ctx body).run {})
    t (name ++ ": exact opening sites") (exactSites st.spans.frames.sites expected)
    t (name ++ ": every recorded index is a surviving top-level frame")
      (st.spans.frames.sites.all fun (i, _) => blocks[i]?.any fun
        | .frame .. => true
        | _ => false)
    t (name ++ ": scope restores its caller's base") st.spans.frames.base.isNone
  check "frame source: identical empty frames"
    #[frameAt first, frameAt second]
    #[(0, ⟨ctx.file, first⟩), (1, ⟨ctx.file, second⟩)]
  check "frame source: group splice after a paragraph"
    #[frameAt first, .word "Body" {}, .par {}, .group #[frameAt second] {}]
    #[(0, ⟨ctx.file, first⟩), (2, ⟨ctx.file, second⟩)]
  check "frame source: included file owns its opening"
    #[frameAt first, .env (Parse.inputEnv "chapter.tex") #[frameAt second] {}]
    #[(0, ⟨ctx.file, first⟩), (1, ⟨"chapter.tex", second⟩)]
  check "frame source: unknown wrapper keeps its body"
    #[.env "zzwrapper" #[frameAt first] {}, frameAt second]
    #[(0, ⟨ctx.file, first⟩), (1, ⟨ctx.file, second⟩)]
  check "frame source: numbering scope splices its body"
    #[.env "appendices" #[frameAt first] {}, frameAt second]
    #[(0, ⟨ctx.file, first⟩), (1, ⟨ctx.file, second⟩)]
  check "frame source: retained wrapper cannot leave a stale top-level site"
    #[.env "quote" #[frameAt first] {}, frameAt second]
    #[(1, ⟨ctx.file, second⟩)]
  let owned := { first with origins := [{ id := 41, name := "framepair" }] }
  check "frame source: a closed macro role owns its frame"
    #[frameAt owned, frameAt second]
    #[(1, ⟨ctx.file, second⟩)]
  let call : Pos :=
    { line := 31, col := 2, origins := [{ id := 53, name := "outer" }],
      command := some "\\framecommand" }
  let (_, called) ← pure ((Elab.elabBlocks
    { ctx with callSite := some (⟨ctx.file, call⟩, "framecommand") }
    #[frameAt first]).run {})
  t "frame source: stored command bodies retain the exact outer call provenance"
    (exactSites called.spans.frames.sites #[(0, ⟨ctx.file, call⟩)])
  let titleCall : Pos := { line := 11, col := 1, command := some "\\titlepage" }
  let titleState : Elab.ESt := { title := some #[.text "A title"] }
  let (nested, nestedSt) ← pure ((Elab.elabBlocks ctx
    #[frameAt first #[.ctrl "titlepage" titleCall], frameAt second]).run titleState)
  t "frame source: flattened title frame keeps the outer opening"
    (exactSites nestedSt.spans.frames.sites
      #[(0, ⟨ctx.file, first⟩), (1, ⟨ctx.file, second⟩)])
  t "frame source: flattening keeps the title's vertical distribution"
    (nested[0]?.any fun
      | .frame _ _ .golden _ _ => true
      | _ => false)
  let (_, titleSt) ← pure ((Elab.elabBlocks ctx
    #[.ctrl "titlepage" titleCall]).run titleState)
  t "frame source: a standalone title frame names its written call"
    (exactSites titleSt.spans.frames.sites #[(0, ⟨ctx.file, titleCall⟩)])
  let raws := #[Raw.ctrl "documentclass" {}, .group #[.word "beamer" {}] {},
    .env "document"
      #[frameAt first, .env (Parse.inputEnv "chapter.tex") #[frameAt second] {}] {}]
  let prepared := Elab.prepare ctx.file raws
  let (doc, _, sites) ← pure (Elab.runPrepared ctx.file prepared)
  let (_, _, rerunSites) ← pure (Elab.runPrepared ctx.file prepared
    (picWithdrawn := #["unused-picture-request"]))
  t "frame source: the final prepared output exports matching block indices"
    (exactSites sites.frames #[(0, ⟨ctx.file, first⟩), (1, ⟨"chapter.tex", second⟩)] &&
      sites.frames.all fun (i, _) => doc.body[i]?.any fun
        | .frame .. => true
        | _ => false)
  t "frame source: a repeated prepared run rebuilds the same source output"
    (exactSites sites.frames rerunSites.frames)
