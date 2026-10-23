module

public import LeanTex.Core.TextAccount
public import LeanTex.Core.HtmlDocRead
public import LeanTex.Core.PdfCensus
public import LeanTex.Cli.Args

/-! The headline, nothing is lost silently, composed from the rows that state each stage. -/

namespace LeanTex.Cli

open LeanTex.Core
open LeanTex.Core.Text (ReadsAs)

/-- One run's results as the headline reads them: the texts each stage leaves, the diagnostics
the run reports, and what it writes. -/
public structure Run where
  /-- Every diagnostic the run reports. -/
  D : Array Diag
  /-- The diagnostics the front stages report, through `Bib.accountFront`. -/
  dFront : Array Diag
  emitted : List Diag.Output
  shipped : List Diag.Output
  /-- The executed source's text slots an artifact's target reads. -/
  srcText : Diag.Output → List (Char × Origin)
  /-- The located text of the last elaboration, `Elab.runPrepared`'s. -/
  elabText : Diag.Output → List (Char × Origin)
  /-- The located text of the document an artifact's backend reads. -/
  irText : Diag.Output → List (Char × Origin)
  /-- The text of the lines `Layout.runFitted` sets. -/
  setText : List (Char × Origin)
  /-- What a viewer extracts from an artifact. -/
  text : Diag.Output → List (Char × Origin)
  pdf : ByteArray
  hcfg : HtmlDoc.Config
  docH : Ir.Doc
  svgChecked : Array ByteArray
  html : String
  /-- The `--math-boundary` script the run read. -/
  boundaryText : Option String
  bytes : Diag.Output → ByteArray

/-- The losses that excuse text in an artifact. -/
@[expose] public def Run.lost (D : Array Diag) (A : Diag.Output) : Array Diag :=
  (Diag.forOutputs #[A] D).filter fun d => d.kind.loss matches .dropped | .pending

@[expose] public def Run.named (D : Array Diag) (A : Diag.Output) : List Span :=
  (Run.lost D A).toList.flatMap Diag.piece

/-- The rows the headline composes, each field the statement of the theorem it names over every
run `compile` presents. -/
public structure Rows {σ : Type} (compile : Config → σ → Run) : Prop where
  /-- DiagCode.error_iff_fatal, with the driver writing every artifact it emits. -/
  ships : ∀ cfg x, (∀ d ∈ (compile cfg x).D,
      ¬ d.kind.stopsWriter ∧ d.kind ∉ [.E0003, .E0005, .E0006, .E0606]) →
    (compile cfg x).shipped = (compile cfg x).emitted
  /-- Elab.runPrepared_text_accounts, from execution through both knots. -/
  knots : ∀ cfg x, ∀ A ∈ (compile cfg x).shipped,
    ReadsAs (Run.named (compile cfg x).dFront A) ((compile cfg x).srcText A)
      ((compile cfg x).elabText A)
  /-- Driver.passes_text_accounts, the driver's IR passes. -/
  passes : ∀ cfg x, ∀ A ∈ (compile cfg x).shipped,
    ReadsAs (Run.named (compile cfg x).dFront A) ((compile cfg x).elabText A)
      ((compile cfg x).irText A)
  /-- Layout.runFitted_text_accounts. -/
  layout : ∀ cfg x, .pdf ∈ (compile cfg x).shipped →
    ReadsAs (Run.named (compile cfg x).D .pdf) ((compile cfg x).irText .pdf)
      (compile cfg x).setText
  /-- PdfContent.pageText_accounts, the written page streams read back. -/
  layer : ∀ cfg x, .pdf ∈ (compile cfg x).shipped →
    ReadsAs (Run.named (compile cfg x).D .pdf) (compile cfg x).setText
      ((compile cfg x).text .pdf)
  /-- HtmlDoc.emit_text_accounts. -/
  page : ∀ cfg x, .html ∈ (compile cfg x).shipped →
    ReadsAs (Run.named (compile cfg x).D .html) ((compile cfg x).irText .html)
      ((compile cfg x).text .html)
  /-- MarkdownDoc.emit_text_accounts. -/
  twin : ∀ cfg x, .md ∈ (compile cfg x).shipped →
    ReadsAs (Run.named (compile cfg x).D .md) ((compile cfg x).irText .md)
      ((compile cfg x).text .md)
  /-- Driver.build_reports_contract, every front loss reaching D at its place. -/
  reports : ∀ cfg x, ∀ A ∈ (compile cfg x).shipped, ∀ s ∈ Run.named (compile cfg x).dFront A,
    ∃ s' ∈ Run.named (compile cfg x).D A, Span.samePlace s' s = true
  /-- Driver.build_reports_contract, no loss reported twice at one place. -/
  once : ∀ cfg x, ∀ A ∈ (compile cfg x).shipped,
    ((Run.lost (compile cfg x).D A).toList.map fun d => (d.kind, d.span.map Span.place)).Nodup
  /-- Pdf.writeChecked_census. -/
  census : ∀ cfg x, .pdf ∈ (compile cfg x).shipped → (PdfCensus.census (compile cfg x).pdf).isOk
  /-- Driver.build_page_exact, the page shipped being the closed emission. -/
  closed : ∀ cfg x, .html ∈ (compile cfg x).shipped →
    (∃ p, (HtmlDoc.emitClosed (compile cfg x).hcfg (compile cfg x).docH
      (compile cfg x).svgChecked).1 = .ok p) ∧
    (compile cfg x).html = (HtmlDoc.emit (compile cfg x).hcfg (compile cfg x).docH).1 ∧
    (compile cfg x).boundaryText = (compile cfg x).hcfg.mathRenderer
  /-- HtmlDoc.emitTree_docOk. -/
  docOk : ∀ cfg x, .html ∈ (compile cfg x).shipped →
    Html.DocOk ((compile cfg x).docH.info.language.getD "en")
      (HtmlDoc.emitTree (compile cfg x).hcfg (compile cfg x).docH).1
      (HtmlDoc.emitTree (compile cfg x).hcfg (compile cfg x).docH).2.1 = true
  /-- Driver.build_flag_free, the bytes reading only the flags
  artifact_flag_free projects and the font directories. -/
  flagFree : ∀ cfg cfg' x, (∀ fm, cfg.effectiveEmit fm = cfg'.effectiveEmit fm) →
    cfg.mathBoundary = cfg'.mathBoundary → cfg.fontDirs = cfg'.fontDirs →
    ∀ A ∈ (compile cfg x).shipped, A ∈ (compile cfg' x).shipped →
      (compile cfg' x).bytes A = (compile cfg x).bytes A

/-- Each shipped artifact's backend reads its document's text as its viewer extracts it. -/
private theorem Rows.backend {σ : Type} {compile : Config → σ → Run} (rows : Rows compile)
    (cfg : Config) (x : σ) :
    ∀ A ∈ (compile cfg x).shipped, ∃ base : List Span,
      (∀ s ∈ base, s ∈ Run.named (compile cfg x).D A) ∧
        ReadsAs base ((compile cfg x).irText A) ((compile cfg x).text A) := by
  intro A hA
  cases A with
  | pdf =>
    exact ⟨_, fun s hs => by simpa using hs,
      (rows.layout cfg x hA).trans (rows.layer cfg x hA)⟩
  | html => exact ⟨_, fun _ hs => hs, rows.page cfg x hA⟩
  | md => exact ⟨_, fun _ hs => hs, rows.twin cfg x hA⟩

/-- Nothing is lost silently: each shipped artifact's text is its source's less the places its
losses name, each once, its bytes well formed and read from no flag but the output, the boundary
and the fonts. -/
public theorem compile_text_accounts {σ : Type} (compile : Config → σ → Run)
    (rows : Rows compile) (cfg : Config) (x : σ) :
    let r := compile cfg x
    ((∀ d ∈ r.D, ¬ d.kind.stopsWriter ∧ d.kind ∉ [.E0003, .E0005, .E0006, .E0606]) →
      r.shipped = r.emitted) ∧
    (∀ A ∈ r.shipped,
      Text.view (Run.named r.D A) (r.text A) = Text.view (Run.named r.D A) (r.srcText A) ∧
      ((Run.lost r.D A).toList.map fun d => (d.kind, d.span.map Span.place)).Nodup) ∧
    (.pdf ∈ r.shipped → (PdfCensus.census r.pdf).isOk) ∧
    (.html ∈ r.shipped → ∀ x ∈ HtmlDoc.scripts r.html,
      x = .script (HtmlRead.trimWs HtmlDoc.deckScript.toList) ∨
        ∃ js, r.boundaryText = some js ∧ x = .script (HtmlRead.trimWs js.toList)) ∧
    ∀ cfg' : Config, cfg'.output = cfg.output → cfg'.mathBoundary = cfg.mathBoundary →
      cfg'.fontDirs = cfg.fontDirs → let r' := compile cfg' x
      ∀ A ∈ r.shipped, A ∈ r'.shipped → r'.bytes A = r.bytes A := by
  intro r
  refine ⟨rows.ships cfg x, fun A hA => ⟨?_, rows.once cfg x A hA⟩, rows.census cfg x, ?_, ?_⟩
  · obtain ⟨base, hbase, hb⟩ := rows.backend cfg x A hA
    have h := ((rows.knots cfg x A hA).trans (rows.passes cfg x A hA)).trans hb
    refine (h.at_places _ fun s hs => ?_).symm
    rcases List.mem_append.mp hs with hs | hs
    · rcases List.mem_append.mp hs with hs | hs
      · exact rows.reports cfg x A hA s hs
      · exact rows.reports cfg x A hA s hs
    · exact ⟨s, hbase s hs, Span.samePlace_self s⟩
  · intro hh
    obtain ⟨⟨p, hp⟩, hhtml, hbound⟩ := rows.closed cfg x hh
    have := (HtmlDoc.emitClosed_scripts_mem _ _ _ hp (rows.docOk cfg x hh)).2
    intro y hy
    rw [hhtml] at hy
    rw [hbound]
    exact this y hy
  · intro cfg' ho hm hf _ A hA hA'
    exact rows.flagFree cfg cfg' x
      (fun fm => congrArg Prod.fst (artifact_flag_free cfg cfg' ho.symm hm.symm fm))
      hm.symm hf.symm A hA hA'

end LeanTex.Cli
