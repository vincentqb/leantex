module

public import LeanTex.Core.TextAccount
public import LeanTex.Core.HtmlDocRead
public import LeanTex.Core.PdfCensus
public import LeanTex.Core.PdfTextRead
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
  /-- The codes the document's `\allow` accepts. -/
  allowed : Array String
  /-- Whether `--best-effort` accepts every loss. -/
  allowAll : Bool
  /-- The diagnostics the front stages report for an artifact's document, through
  `Bib.accountFront`. -/
  dFront : Diag.Output → Array Diag
  emitted : List Diag.Output
  shipped : List Diag.Output
  /-- The executed source's text slots an artifact's target reads. -/
  srcText : Diag.Output → List (Char × Origin)
  /-- The located text of the elaboration an artifact's document comes from. -/
  elabText : Diag.Output → List (Char × Origin)
  /-- The located text of the document an artifact's backend reads. -/
  irText : Diag.Output → List (Char × Origin)
  /-- The text of the lines `Layout.runFitted` sets. -/
  setText : List (Char × Origin)
  /-- What a viewer extracts from an artifact, each character with its origin. -/
  text : Diag.Output → List (Char × Origin)
  hcfg : HtmlDoc.Config
  docH : Ir.Doc
  svgChecked : Array ByteArray
  /-- The page whose bytes ship. -/
  html : String
  /-- The `--math-boundary` script the run read. -/
  boundaryText : Option String
  bytes : Diag.Output → ByteArray

/-- The losses that excuse text in an artifact. -/
@[expose] public def Run.lost (D : Array Diag) (A : Diag.Output) : Array Diag :=
  (Diag.forOutputs #[A] D).filter fun d => d.kind.loss matches .dropped | .pending

@[expose] public def Run.named (D : Array Diag) (A : Diag.Output) : List Span :=
  (Run.lost D A).toList.flatMap Diag.piece

/-- The refusals the driver prints without resolving them: the output name's, the PDF writer's and
publication's, and a missing font set. -/
@[expose] public def Run.refusals : List DiagCode := [.E0003, .E0005, .E0006, .E0606, .E0401]

theorem Run.refusals_stop : ∀ c ∈ Run.refusals, c.stopsWriter = true := by
  simp [Run.refusals, DiagCode.stopsWriter]

/-- The characters of a text, origins aside. -/
@[expose] public def Run.chars (t : List (Char × Origin)) : String := String.ofList (t.map (·.1))

/-- The rows the headline composes over every run `compile` presents, each field the statement of
the theorem it names or, for the readers, what an artifact's text is. -/
public structure Rows {σ : Type} (compile : Config → σ → Run) : Prop where
  /-- Driver.build_reports_contract: the driver writes every artifact it emits where resolving its
  diagnostics stops nothing and it prints no refusal. -/
  ships : ∀ cfg x, (∀ d ∈ (compile cfg x).D, d.kind ∉ Run.refusals) →
    (Diag.resolveAll (compile cfg x).allowed (compile cfg x).allowAll (compile cfg x).D).stops = 0 →
    (compile cfg x).shipped = (compile cfg x).emitted
  /-- Driver.build_written_exact: the page shipped is the closed emission over the boundary read. -/
  writesPage : ∀ cfg x, .html ∈ (compile cfg x).shipped →
    (∃ p, (HtmlDoc.emitClosed (compile cfg x).hcfg (compile cfg x).docH
      (compile cfg x).svgChecked).1 = .ok p) ∧
    (compile cfg x).html = (HtmlDoc.emit (compile cfg x).hcfg (compile cfg x).docH).1 ∧
    (compile cfg x).bytes .html = (compile cfg x).html.toUTF8 ∧
    (compile cfg x).boundaryText = (compile cfg x).hcfg.mathRenderer
  /-- The readers' text is each artifact's, its origins owed with the backend rows. -/
  extracted : ∀ cfg x,
    (.pdf ∈ (compile cfg x).shipped → PdfTextRead.structureText ((compile cfg x).bytes .pdf) =
      .ok (Run.chars ((compile cfg x).text .pdf))) ∧
    (.html ∈ (compile cfg x).shipped →
      HtmlRead.pageText (compile cfg x).html = some (Run.chars ((compile cfg x).text .html)))
  /-- Elab.runPrepared_text_accounts, from execution through both knots. -/
  knots : ∀ cfg x, ∀ A ∈ (compile cfg x).shipped,
    ReadsAs (Run.named ((compile cfg x).dFront A) A) ((compile cfg x).srcText A)
      ((compile cfg x).elabText A)
  /-- Driver.passes_text_accounts, the driver's IR passes. -/
  passes : ∀ cfg x, ∀ A ∈ (compile cfg x).shipped,
    ReadsAs (Run.named ((compile cfg x).dFront A) A) ((compile cfg x).elabText A)
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
  /-- MarkdownDoc.emit_text_accounts, over the markdown reader's text of the twin. -/
  twin : ∀ cfg x, .md ∈ (compile cfg x).shipped →
    ReadsAs (Run.named (compile cfg x).D .md) ((compile cfg x).irText .md)
      ((compile cfg x).text .md)
  /-- Driver.build_reports_contract, every front loss reaching D at its place. -/
  reports : ∀ cfg x, ∀ A ∈ (compile cfg x).shipped, ∀ s ∈ Run.named ((compile cfg x).dFront A) A,
    ∃ s' ∈ Run.named (compile cfg x).D A, Span.samePlace s' s = true
  /-- Driver.build_reports_contract, no loss reported twice at one place. -/
  once : ∀ cfg x, ∀ A ∈ (compile cfg x).shipped,
    ((Run.lost (compile cfg x).D A).toList.map fun d => (d.kind, d.span.map Span.place)).Nodup
  /-- Pdf.writeChecked_census, over the file the run ships. -/
  census : ∀ cfg x, .pdf ∈ (compile cfg x).shipped →
    (PdfCensus.census ((compile cfg x).bytes .pdf)).isOk
  /-- HtmlDoc.emitTree_docOk, over the page the run ships. -/
  docOk : ∀ cfg x, .html ∈ (compile cfg x).shipped →
    Html.DocOk ((compile cfg x).docH.info.language.getD "en")
      (HtmlDoc.emitTree (compile cfg x).hcfg (compile cfg x).docH).1
      (HtmlDoc.emitTree (compile cfg x).hcfg (compile cfg x).docH).2.1 = true
  /-- Driver.build_flag_free, the bytes reading no flag but the output, the boundary and the
  font directories. -/
  flagFree : ∀ cfg cfg' x, cfg'.output = cfg.output → cfg'.mathBoundary = cfg.mathBoundary →
    cfg'.fontDirs = cfg.fontDirs →
    ∀ A ∈ (compile cfg x).shipped, A ∈ (compile cfg' x).shipped →
      (compile cfg' x).bytes A = (compile cfg x).bytes A

/-- Each shipped artifact's backend reads its document's text as its viewer extracts it. -/
private theorem Rows.backend {σ : Type} {compile : Config → σ → Run} (rows : Rows compile)
    (cfg : Config) (x : σ) :
    ∀ A ∈ (compile cfg x).shipped,
      ReadsAs (Run.named (compile cfg x).D A) ((compile cfg x).irText A)
        ((compile cfg x).text A) := by
  intro A hA
  cases A with
  | pdf =>
    exact ((rows.layout cfg x hA).trans (rows.layer cfg x hA)).mono fun s hs => by
      simpa using hs
  | html => exact rows.page cfg x hA
  | md => exact rows.twin cfg x hA

/-- Nothing is lost silently: each shipped artifact's text is its executed source's less the places
its losses name, each once, the PDF passing the census, the page running only what it declares, and
the bytes read from no flag but the output, the boundary and the fonts. -/
public theorem compile_text_accounts {σ : Type} (compile : Config → σ → Run)
    (rows : Rows compile) (cfg : Config) (x : σ) :
    let r := compile cfg x
    ((∀ d ∈ r.D, ¬ d.kind.stopsWriter) → r.shipped = r.emitted) ∧
    (∀ A ∈ r.shipped,
      Text.view (Run.named r.D A) (r.text A) = Text.view (Run.named r.D A) (r.srcText A) ∧
      ((Run.lost r.D A).toList.map fun d => (d.kind, d.span.map Span.place)).Nodup) ∧
    (.pdf ∈ r.shipped → (PdfCensus.census (r.bytes .pdf)).isOk ∧
      PdfTextRead.structureText (r.bytes .pdf) = .ok (Run.chars (r.text .pdf))) ∧
    (.html ∈ r.shipped → r.bytes .html = r.html.toUTF8 ∧
      HtmlRead.pageText r.html = some (Run.chars (r.text .html)) ∧ ∀ x ∈ HtmlDoc.scripts r.html,
      x = .script (HtmlRead.trimWs HtmlDoc.deckScript.toList) ∨
        ∃ js, r.boundaryText = some js ∧ x = .script (HtmlRead.trimWs js.toList)) ∧
    ∀ cfg' : Config, cfg'.output = cfg.output → cfg'.mathBoundary = cfg.mathBoundary →
      cfg'.fontDirs = cfg.fontDirs → let r' := compile cfg' x
      ∀ A ∈ r.shipped, A ∈ r'.shipped → r'.bytes A = r.bytes A := by
  intro r
  refine ⟨fun hs => rows.ships cfg x (fun d hd hr => hs d hd (Run.refusals_stop _ hr))
    ((Diag.resolveAll_stops_exact _ _ _).mpr fun d hd hw => absurd hw (hs d hd)),
    fun A hA => ⟨?_, rows.once cfg x A hA⟩, fun hp => ?_, fun hh => ?_, ?_⟩
  · have front := ((rows.knots cfg x A hA).trans (rows.passes cfg x A hA)).mono
      (base' := Run.named (r.dFront A) A) fun s hs => by simpa using hs
    refine ((front.trans (rows.backend cfg x A hA)).at_places _ fun s hs => ?_).symm
    rcases List.mem_append.mp hs with hs | hs
    · exact rows.reports cfg x A hA s hs
    · exact ⟨s, hs, Span.samePlace_self s⟩
  · exact ⟨rows.census cfg x hp, (rows.extracted cfg x).1 hp⟩
  · obtain ⟨⟨p, hp⟩, hhtml, hbytes, hbound⟩ := rows.writesPage cfg x hh
    refine ⟨hbytes, (rows.extracted cfg x).2 hh, fun y hy => ?_⟩
    rw [hhtml] at hy
    rw [hbound]
    exact (HtmlDoc.emitClosed_scripts_mem _ _ _ hp (rows.docOk cfg x hh)).2 y hy
  · intro cfg' ho hm hf _ A hA hA'
    exact rows.flagFree cfg cfg' x ho hm hf A hA hA'

/-- Some compile shipping an artifact meets every row: one writing an empty twin. -/
example : Rows fun (_ : Config) (_ : Unit) =>
    ({ D := #[], allowed := #[], allowAll := false, dFront := fun _ => #[], emitted := [.md],
       shipped := [.md], srcText := fun _ => [],
       elabText := fun _ => [], irText := fun _ => [], setText := [], text := fun _ => [],
       hcfg := {}, docH := {}, svgChecked := #[], html := "", boundaryText := none,
       bytes := fun _ => .empty } : Run) := by
  have h0 : (Diag.forOutputs #[Diag.Output.md] (#[] : Array Diag)).toList = [] :=
    List.eq_nil_iff_forall_not_mem.mpr fun d hd => by simp [Diag.forOutputs_mem] at hd
  constructor <;> intros <;> simp_all [Text.ReadsAs, Run.named, Run.lost]

end LeanTex.Cli
