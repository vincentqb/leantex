import Tests.Diag
import Tests.Markdown
import Tests.FrameGeometry
import Tests.FrameFit
import Tests.Layout
import Tests.Themes
import Tests.FontMath
import Tests.Surface
import Tests.Kernel
import Tests.ListingProvider
import Tests.ListingStyleTable
import Tests.InlineCode
import Tests.PublicationPaths
import Tests.HtmlContained
import Tests.TableSide
import Tests.PdfBounds
import Tests.InputDecoding
import Tests.BibModel
import Tests.PdfNative
import Tests.SeedPalette
import Tests.Schemes
import Tests.SpotColor
import Tests.PageBoxes
import Tests.PrintX4
import Tests.SvgRoute
import scripts.Rung
import Tests.MonoDefault
import Tests.LeanStatements
import Tests.LeanViews
import Tests.LeanProse
import Tests.Blueprint
import Tests.Settings
import Tests.UnusedSettings
import Tests.BibEdges

/-! The diagnostics audit: each code's decided verdict, the construct rung it aims at, and the pin
that fails when the decision regresses; `scripts/diagaudit.lean` ratchets the codes no row binds. -/

open LeanTex.Core
open Tests (listingProviderChecks listingStyleTableChecks htmlContainedCliChecks
  publicationPathChecks)
open Tests.LayoutInkContracts (layoutInkChecks)

namespace DiagAudit

/-- Where an audit decided a code goes next. -/
inductive Ruling where
  /-- Implement the construct natively; the code leaves the page's census. -/
  | native
  /-- A decided divergence from LaTeX: the code stays and names it. -/
  | divergence
  /-- Refused by design: the construct stays out and the code says so. -/
  | refusal
  /-- The code is right as it stands, and its pin holds it there. -/
  | keep
  /-- One construct accounted twice: fold it into the other code's accounting. -/
  | merge
  /-- The right loss at the wrong span or key. -/
  | resite
  /-- The right loss in the wrong words: a count, an invented key, a help. -/
  | message
  deriving Repr, BEq, DecidableEq

def Ruling.word : Ruling → String
  | .native => "native"
  | .divergence => "divergence"
  | .refusal => "refusal"
  | .keep => "keep"
  | .merge => "merge"
  | .resite => "resite"
  | .message => "message"

def Ruling.all : List Ruling :=
  [.native, .divergence, .refusal, .keep, .merge, .resite, .message]

/-- What holds a verdict: a theorem pin carries its proof, a check pin elaborates the block it names
and binds while the suite runs it, a tier pin binds while the baseline holds its item. -/
inductive Pin where
  | thm (name : Lean.Name) (stmt : Prop) (proof : stmt)
  | check (name : Lean.Name) (seen : Unit)
  | tier (tier item : String)

/-- `thm% n`: a pin to the theorem `n`, checked to be a proof where it is
written. -/
syntax "thm%" ident : term
macro_rules
  | `(thm% $n) => `(DiagAudit.Pin.thm $(Lean.quote n.getId) _ @$n)

/-- `check% n`: a pin to the check block `n`, elaborated where it is
written. -/
syntax "check%" ident : term
macro_rules
  | `(check% $n) => `(DiagAudit.Pin.check $(Lean.quote n.getId) (let _ := @$n; ()))

def Pin.name : Pin → String
  | .thm n _ _ | .check n _ => n.toString
  | .tier t i => t ++ "/" ++ i

structure AuditRow where
  code : DiagCode
  verdict : Ruling
  target : Rung
  pin : Pin

/-- The decided codes; a code with no row is owed a verdict, which the tier counts. -/
def registry : List AuditRow :=
  [⟨.W0201, .keep, .native, check% measureChecks⟩,
   ⟨.W0202, .keep, .native, check% rhythmChecks⟩,
   ⟨.N0376, .keep, .native, check% a11yChecks⟩,
   ⟨.W0345, .native, .native, check% contrastChecks⟩,
   ⟨.W0009, .keep, .degraded, check% fallbackChecks⟩,
   ⟨.N0018, .keep, .rewritten, check% mathChecks⟩,
   ⟨.W0016, .keep, .degraded, check% isolatedHoleChecks⟩,
   ⟨.N0200, .keep, .rewritten, check% spacingChecks⟩,
   ⟨.W0110, .native, .native, check% themeTitleShipChecks⟩,
   ⟨.W0389, .native, .native, check% mathContainChecks⟩,
   ⟨.N0100, .merge, .rewritten, check% siteAccountingChecks⟩,
   ⟨.W0362, .merge, .native, check% siteAccountingChecks⟩,
   ⟨.W0419, .keep, .degraded, check% pictureRouteChecks⟩,
   ⟨.W0382, .keep, .degraded, check% pictureDefnReachChecks⟩,
   ⟨.W0386, .keep, .degraded, check% titleBreakChecks⟩,
   ⟨.W0435, .native, .native, check% kernelQedHereChecks⟩,
   ⟨.W0393, .keep, .degraded, check% listingProviderChecks⟩,
   ⟨.W0411, .keep, .native, check% Tests.inlineCodeChecks⟩,
   ⟨.W0412, .keep, .degraded, check% Tests.inlineCodeChecks⟩,
   ⟨.W0413, .divergence, .degraded, check% Tests.inlineCodeChecks⟩,
   ⟨.W0398, .native, .native, check% Tests.tableFaceOrderChecks⟩,
   ⟨.W0399, .native, .native, check% Tests.FrameGeometry.fillCarrierChecks⟩,
   ⟨.W0400, .keep, .degraded, check% Tests.FrameFit.overhangChecks⟩,
   ⟨.W0384, .divergence, .degraded, check% Tests.FrameFit.overhangChecks⟩,
   ⟨.W0306, .keep, .degraded, check% Tests.SeedPalette.failureChecks⟩,
   ⟨.W0308, .keep, .degraded, check% Tests.Schemes.dropChecks⟩,
   ⟨.W0414, .keep, .degraded, check% Tests.LeanStatements.leanStatementChecks⟩,
   ⟨.W0433, .keep, .degraded, check% Tests.LeanStatements.leanStatementChecks⟩,
   ⟨.N0032, .keep, .rewritten, check% Tests.LeanStatements.leanStatementChecks⟩,
   ⟨.W0431, .keep, .degraded, check% Tests.LeanViews.leanViewChecks⟩,
   ⟨.W0432, .keep, .degraded, check% Tests.LeanViews.leanViewChecks⟩,
   ⟨.W0440, .keep, .degraded, check% Tests.SpotColor.checks⟩,
   ⟨.W0441, .keep, .degraded, check% Tests.SpotColor.checks⟩,
   ⟨.W0415, .keep, .degraded, check% Tests.LeanProse.leanProseChecks⟩,
   ⟨.W0416, .keep, .degraded, check% Tests.LeanProse.leanProseChecks⟩,
   ⟨.W0442, .keep, .degraded, check% Tests.PageBoxes.checks⟩,
   ⟨.W0443, .keep, .degraded, check% Tests.PageBoxes.checks⟩,
   ⟨.W0434, .keep, .degraded, check% Tests.Blueprint.blueprintChecks⟩,
   ⟨.W0109, .keep, .degraded, check% compatChecks⟩,
   ⟨.W0436, .keep, .degraded, check% Tests.Blueprint.blueprintChecks⟩,
   ⟨.W0444, .keep, .degraded, check% Tests.PrintX4.checks⟩,
   ⟨.W0445, .keep, .degraded, check% Tests.PrintX4.checks⟩,
   ⟨.W0446, .keep, .degraded, check% Tests.PrintX4.checks⟩,
   ⟨.W0447, .keep, .degraded, check% Tests.PrintX4.checks⟩,
   ⟨.N0448, .keep, .native, check% Tests.PrintX4.checks⟩,
   ⟨.W0394, .keep, .degraded, check% layoutInkChecks⟩,
   ⟨.E0395, .keep, .fails, check% layoutInkChecks⟩,
   ⟨.W0396, .keep, .degraded, check% layoutInkChecks⟩,
   ⟨.E0390, .refusal, .fails, check% mdSurfaceChecks⟩,
   ⟨.W0609, .native, .native, check% figureRouteChecks⟩,
   ⟨.N0024, .native, .native, check% Tests.svgRouteChecks⟩,
   ⟨.N0026, .keep, .rewritten, check% Tests.svgFontMatchChecks⟩,
   ⟨.N0027, .native, .native, check% Tests.svgLinkNoteChecks⟩,
   ⟨.E0606, .refusal, .fails, check% htmlContainedCliChecks⟩,
   ⟨.E0607, .refusal, .fails, check% pdfBoundsChecks⟩,
   ⟨.E0003, .refusal, .fails, check% publicationPathChecks⟩,
   ⟨.E0004, .keep, .fails, check% Tests.publicationWriteChecks⟩,
   ⟨.E0005, .refusal, .fails, check% Tests.publicationInputChecks⟩,
   ⟨.E0006, .refusal, .fails, check% Tests.outputNameChecks⟩,
   ⟨.W0002, .keep, .degraded, check% inputDecodingChecks⟩,
   ⟨.W0004, .keep, .degraded, check% inputDecodingChecks⟩,
   ⟨.N0025, .divergence, .native, check% inputDecodingChecks⟩,
   ⟨.N0029, .keep, .rewritten, check% bibNamedChecks⟩,
   ⟨.W0420, .keep, .degraded, check% bibNamedChecks⟩,
   ⟨.W0421, .keep, .degraded, check% bibLanguageChecks⟩,
   ⟨.W0422, .keep, .degraded, check% bibSetChecks⟩,
   ⟨.W0423, .keep, .degraded, check% bibRelatedChecks⟩,
   ⟨.W0424, .keep, .degraded, check% bibSourcesChecks⟩,
   ⟨.W0503, .keep, .degraded, check% Tests.BibEdges.missingChecks⟩,
   ⟨.W0450, .keep, .native, check% Tests.BibEdges.duplicateChecks⟩,
   ⟨.W0425, .keep, .degraded, check% biblatexXdataChecks⟩,
   ⟨.W0426, .keep, .degraded, check% bibStringStoreChecks⟩,
   ⟨.W0427, .keep, .degraded, check% biblatexLocaleSortChecks⟩,
   ⟨.N0030, .divergence, .rewritten, check% bibReservedChecks⟩,
   ⟨.N0031, .divergence, .rewritten, check% Tests.MonoDefault.monoDefaultChecks⟩,
   ⟨.W0428, .keep, .degraded, check% biblatexSuperciteChecks⟩,
   ⟨.W0429, .keep, .degraded, check% bibFieldBackstopChecks⟩,
   ⟨.W0107, .keep, .degraded, check% unreadableLengthChecks⟩,
   ⟨.W0449, .keep, .native, check% Tests.UnusedSettings.firesChecks⟩]

/-- An engine source's tier item: `LeanTex/Core/Elab.lean` is `Core.Elab`,
`Main.lean` is `Main`. -/
def moduleItem (path : String) : String :=
  let p := if path.startsWith "LeanTex/" then (path.drop "LeanTex/".length).toString else path
  let p := if p.endsWith ".lean" then (p.dropEnd ".lean".length).toString else p
  p.replace "/" "."

/-- The registries: each names the blocks it pins by writing them, so a
mention there is never the suite running one. -/
def registryFiles : List String := ["Tests/DiagAudit.lean", "Tests/Reports.lean", "Tests/Premises.lean"]

/-- The suite's own code, which a check pin must be run from: the driver and every suite module but
the registries. -/
def suiteText : IO String := do
  let mut text := stripNonCode (← IO.FS.readFile "Tests.lean")
  for f in ← System.FilePath.walkDir "Tests" do
    if f.toString.endsWith ".lean" && !registryFiles.contains f.toString then
      text := text ++ stripNonCode (← IO.FS.readFile f)
  return text

/-- Whether the pin holds anything: a theorem pin always, a check pin while code outside the
registries references its declaration, a tier pin while the baseline has its item. -/
def Pin.resolves (suite : String) : Pin → IO Bool
  | .thm .. => pure true
  | .check n _ => pure (wordCountWhere suite n.toString (fun before =>
      let previous := (before.trimAsciiEnd.takeEndWhile fun c : Char =>
        c.isAlphanum || c == '_').toString
      !["def", "abbrev", "opaque", "theorem", "lemma", "axiom", "constant",
        "namespace", "end", "import", "open", "export"].contains previous) > 0)
  | .tier t item => do
    let path : System.FilePath := s!"testdata/scoreboard/{t}.tsv"
    if !(← path.pathExists) then return false
    return ((← IO.FS.readFile path).splitOn "\n").any (·.startsWith (item ++ "\t"))

/-- The codes a registry binds, or what makes it malformed: a code with two rows, or a pin that
holds nothing. -/
def auditBound (suite : String) (rows : List AuditRow) : IO (Except String (List DiagCode)) := do
  let mut bound : List DiagCode := []
  for r in rows do
    if bound.contains r.code then
      return .error s!"{r.code.code} has two audit rows"
    unless ← r.pin.resolves suite do
      return .error s!"{r.code.code}: its pin {r.pin.name} holds nothing"
    bound := r.code :: bound
  return .ok bound

/-- Per engine module, the codes it applies that no row binds. -/
def unboundByModule (sources : Array (String × List String)) (bound : List DiagCode) :
    Array (String × List String) :=
  sources.filterMap fun (path, applied) =>
    if applied.isEmpty then none
    else some (moduleItem path, applied.filter fun c => !bound.any (·.code == c))

end DiagAudit

open DiagAudit in
/-- Every audit row is held by a checker, and every code can be charged to a module. -/
def diagAuditChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let suite ← suiteText
  match ← auditBound suite registry with
  | .error e => t s!"diag audit: {e}" false
  | .ok bound => t s!"diag audit: {bound.length} rows, each pin resolving" true
  let sources ← codeSources
  let charged := DiagCode.all.filter fun c => !sources.any (·.2.contains c.code)
  t s!"diag audit: every code is applied by some engine module ({charged.map (·.code)})"
    charged.isEmpty
  t "diag audit: a check the suite runs resolves"
    (← (check% a11yChecks).resolves suite)
  t "diag audit: a check nothing runs does not"
    !(← (Pin.check `zzNoSuchChecks ()).resolves suite)
  -- The suite spells `StreamChecks` only as the tail of a longer name, so it holds nothing.
  t "diag audit: a name inside a longer name does not resolve"
    (hasStr suite "StreamChecks" && wordCount suite "pdfStreamChecks" ≥ 2 &&
      !(← (Pin.check `StreamChecks ()).resolves suite))
  for (source, expected) in [
      ("namespace Sample\ndef checks := ()\nend Sample\nSample.checks ref", true),
      ("def Sample.checks := ()\nSample.checks ref", true),
      ("public def\n Sample.checks := ()", false),
      ("namespace Sample.checks\nend Sample.checks", false),
      ("public import Sample.checks\nopen Sample.checks", false),
      ("def Sample.checksMore := ()\nSample.checksMore ref", false)] do
    t "diag audit: qualification preserves calls and excludes declarations"
      ((← (Pin.check `Sample.checks ()).resolves source) == expected)
  t "diag audit: a committed tier item resolves"
    (← (Pin.tier "compat" "cancel.impl").resolves suite)
  t "diag audit: an item no baseline holds does not"
    !(← (Pin.tier "compat" "zz-no-such.impl").resolves suite)
