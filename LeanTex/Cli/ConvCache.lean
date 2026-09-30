import LeanTex.Cli.PicCache
import LeanTex.Core.Flate

/-! The host-conversion cache's vocabulary, as values. The SVG browser
faces are drawn by host tools — `xmllint` guards the support boundary,
`rsvg-convert` and `pdftocairo` render the bytes — and each is external, so
each invocation carries a wall-clock budget and each *completed* answer is
worth remembering. This module holds the policy the way `PicCache` holds
the TeX boundary's: what one conversion's attempt ended as, whether that
ending is the tool's own verdict, and what the next run does about it — all
IO-free, so the one-attempt-per-request invariant is checkable with no tool
installed. `Main.lean` (through `ImageAssets`) supplies the process results
and reads and writes the files named here; the semantics are all here,
where they can be stated.

The process vocabulary — how a run ended (`PicCache.Ran`), what it left in
its log (`PicCache.Log`), and the answer it amounts to (`PicCache.Outcome`,
with `remembers`/`step`) — is reused from `PicCache` verbatim rather than
re-invented, so the boundary and the converter share one meaning of
"verdict". Only the *reading* differs: a picture the TeX boundary exited
cleanly on but drew no PDF for is that tool's own refusal, but a converter
that exits cleanly and yet leaves no usable output has produced truncated or
unreadable output — a fact about the machine, not the request — so it is
retried, never remembered as a refusal. -/

namespace LeanTex.Cli.ConvCache

open LeanTex.Core

/-! ## The invocation contract

The support boundary and the argument builders live here, as one source of
truth: the real invocations in `ImageAssets` read exactly these, and the
cache key hashes their recipe, so a change to how a tool is called moves
both the command and its slot together — a stale answer is never served
across a recipe change (`browserFaceContract` re-exports the recipes for
the browser oracle to record). -/

/-- A deliberately narrow support boundary, evaluated over libxml's parsed
XML, never the source spelling. Only fragment references are supported.
CSS is plain declarations/rules without functions, escapes or at-rules;
presentation attributes admit exactly `url(#ASCII-id)`, without paint-server
fallback syntax such as `url(#id) red`. Transforms and SMIL timing have their
own non-resource function syntax. Animated resource/style assignments,
scripts and foreign objects are refused.

Text and font features are refused too — `text`/`tspan`/`textPath`/`tref`,
the SVG-font elements, and the `font`/`font-family` presentation attributes
(`@font-face` is already caught by the at-rule CSS refusal). This is what
makes the conversion's output a function of its inputs alone: with no glyph
to shape, `rsvg-convert` and `pdftocairo` never consult the host's installed
fonts or fontconfig, so the cache key — source content, recipe, tool version
and engine version — captures everything that can change the bytes, and no
font/environment fingerprint is owed. This is a refusal boundary, not a
second XML or CSS parser. -/
def supportedSvg : String :=
  let localUrl := "(starts-with(normalize-space(.),'url(#') and " ++
    "substring(normalize-space(.),string-length(normalize-space(.)),1)=')' and " ++
    "string-length(normalize-space(.))>6 and " ++
    "translate(substring(normalize-space(.),6,string-length(normalize-space(.))-6)," ++
    "'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789_.:-','')='')"
  let cssSyntax := "(contains(.,'(') or contains(.,'\\') or contains(.,'@'))"
  let textOrFont :=
    "//*[local-name()='text' or local-name()='tspan' or local-name()='textPath' or " ++
      "local-name()='tref' or local-name()='altGlyph' or local-name()='altGlyphDef' or " ++
      "local-name()='altGlyphItem' or local-name()='glyphRef' or local-name()='font' or " ++
      "local-name()='font-face'] | " ++
    "//@*[local-name()='font-family' or local-name()='font']"
  let unsupported :=
    textOrFont ++ " | " ++
    "//processing-instruction() | " ++
    "//*[local-name()='script' or local-name()='foreignObject'] | " ++
    "//@*[local-name()='base' or starts-with(local-name(),'on')] | " ++
    "//@*[local-name()='href' or local-name()='src'][not(starts-with(normalize-space(.),'#'))] | " ++
    "//*[local-name()='style'][" ++ cssSyntax ++ "] | " ++
    "//@*[not(local-name()='transform' or local-name()='gradientTransform' or " ++
      "local-name()='patternTransform' or local-name()='begin' or local-name()='end')]" ++
      "[" ++ cssSyntax ++ " and not(" ++ localUrl ++ ")] | " ++
    "//@*[local-name()='attributeName'][" ++
      "normalize-space(.)='href' or substring-after(normalize-space(.),':')='href' or " ++
      "normalize-space(.)='src' or substring-after(normalize-space(.),':')='src' or " ++
      "normalize-space(.)='base' or substring-after(normalize-space(.),':')='base' or " ++
      "normalize-space(.)='style' or normalize-space(.)='attributeName' or " ++
      "normalize-space(.)='from' or normalize-space(.)='to' or normalize-space(.)='by' or " ++
      "normalize-space(.)='values' or starts-with(normalize-space(.),'on')]"
  "boolean(/*[local-name()='svg' and namespace-uri()='http://www.w3.org/2000/svg']) and " ++
    "not(" ++ unsupported ++ ")"

/-- `xmllint --sax`: report a DTD as an event before any tree query can
hide it. No entity substitution, external-DTD loading, XInclude or
recovery. -/
def saxArgs (input : System.FilePath) : Array String :=
  #["--nonet", "--nocatalogs", "--sax", input.toString]

/-- `xmllint --xpath`: the support boundary over the parsed tree. -/
def xpathArgs (input : System.FilePath) : Array String :=
  #["--nonet", "--nocatalogs", "--xpath", supportedSvg, input.toString]

/-- `rsvg-convert --format=…`: librsvg's static reading of a self-contained
SVG, to PDF (validation) or SVG (poster). -/
def rsvgArgs (format : String) (input output : System.FilePath) : Array String :=
  #["--format=" ++ format, "--output", output.toString, input.toString]

/-- `pdftocairo -svg`: Poppler's vector reading of one selected physical
page. -/
def pdfSvgArgs (page : String) (input output : System.FilePath) : Array String :=
  #["-svg", "-f", page, "-l", page, input.toString, output.toString]

/-- `pdftocairo -svg` of a boundary picture's own single-page PDF: the
first page, no range. -/
def picFaceArgs (input output : System.FilePath) : Array String :=
  #["-svg", input.toString, output.toString]

/-- One tool invocation as its normalized command line, with placeholder
paths so the recipe is a function of the arguments alone. -/
def commandText (tool : String) (args : Array String) : String :=
  tool ++ " " ++ String.intercalate " " args.toList

private def ph (name : String) : System.FilePath := System.FilePath.mk name

/-- One host conversion the browser faces need. Each names its tool and the
exact commands it runs; `pdfPage` carries the selected page, so two pages
of one PDF are two operations with two slots. -/
inductive Op where
  /-- `xmllint` SAX pass then support-boundary XPath over a captured SVG. -/
  | validate
  /-- `rsvg-convert` SVG→PDF, the static validity conversion. -/
  | svgPdf
  /-- `rsvg-convert` SVG→SVG, the static print/reduced-motion poster. -/
  | svgPoster
  /-- `pdftocairo` PDF→SVG of one selected physical page. -/
  | pdfPage (page : Nat)
  /-- `pdftocairo` PDF→SVG of a boundary picture's own first page. -/
  | picFace
  deriving BEq, Repr, DecidableEq

/-- For a byte-producing op, the single spec the runtime both keys and runs:
its tool, input and output extensions, and argument builder. `none` for the
two-pass validation op, which `byteConv` never runs. `Op.tool`, `Op.recipe`
and `byteConv` all read this, so the op keyed and the command run can never
diverge — the runtime cannot key one op and run another. -/
def Op.byteSpec : Op →
    Option (String × String × String × (System.FilePath → System.FilePath → Array String))
  | .validate => none
  | .svgPdf => some ("rsvg-convert", "svg", "pdf", rsvgArgs "pdf")
  | .svgPoster => some ("rsvg-convert", "svg", "svg", rsvgArgs "svg")
  | .pdfPage p => some ("pdftocairo", "pdf", "svg", pdfSvgArgs (toString p))
  | .picFace => some ("pdftocairo", "pdf", "svg", picFaceArgs)

/-- The tool binary whose identity keys this operation's slots — the byte
op's own tool from `byteSpec`, and `xmllint` for the two-pass validation. -/
def Op.tool (op : Op) : String :=
  match op.byteSpec with
  | some (tool, _, _, _) => tool
  | none => "xmllint"

/-- One byte op's normalized recipe, built from its `byteSpec` so the string
the key hashes is the command the runtime runs. -/
private def byteRecipe (op : Op) : String :=
  match op.byteSpec with
  | some (tool, _, _, args) => commandText tool (args (ph "<input>") (ph "<output>"))
  | none => ""

/-- The normalized recipe: every command this operation runs, with
placeholder paths, derived from the one `byteSpec` (validation is the
two-pass exception). The cache key hashes this, so the same edit that moves
an argument builder moves every slot the operation ever filled. -/
def Op.recipe : Op → String
  | .validate =>
    commandText "xmllint" (saxArgs (ph "<input>")) ++ "\n" ++
    commandText "xmllint" (xpathArgs (ph "<input>"))
  | .svgPdf => byteRecipe .svgPdf
  | .svgPoster => byteRecipe .svgPoster
  | .pdfPage p => byteRecipe (.pdfPage p)
  | .picFace => byteRecipe .picFace

/-- Every operation's recipe, in a stable order: the value the browser
oracle records and `ImageAssets.browserFaceContract` re-exports. A recipe
change here is a change there, so the committed report moves with the
invocation. -/
def contract : String :=
  String.intercalate "\n"
    [Op.recipe .validate, Op.recipe .svgPdf, Op.recipe .svgPoster,
      Op.recipe (.pdfPage 0), Op.recipe .picFace]

/-! ## The key

A conversion's slot is named by everything that could change its bytes: the
source's content (an edited figure re-converts, an unchanged one never
does), the operation's recipe (a moved argument re-converts — req: recipe
moves ⇒ key moves), the tool's own version string (an upgraded tool
re-converts every slot), and the engine version (a changed converter policy
re-converts). No document text or output path enters the key, so the same
figure in two documents shares one warmed slot. -/

/-- The operation-and-tool-and-engine half of the key: the recipe, the
tool's version, and the engine version, hashed to a content key. The
source's own content key is prefixed by the caller — the slot is that
source under this variant. -/
def variant (op : Op) (toolVersion engineVersion : String) : String :=
  Flate.contentKey (String.intercalate "\u0000"
    [op.recipe, toolVersion, engineVersion]).toUTF8

/-- The slot stem for one source under one variant: the source's content
key and the variant, so an edit to either names a different slot. -/
def stem (srcKey variant : String) : String := srcKey ++ "-" ++ variant

/-- The converted bytes' name in the slot. -/
def outName (srcKey variant : String) : String := stem srcKey variant ++ ".out"

/-- The remembered refusal's name in the slot, beside the output: one slot
per request, whichever way the tool answered. -/
def failName (srcKey variant : String) : String := stem srcKey variant ++ ".fail"

/-- The temporary name one writer builds under before the atomic rename.
Every writer gets its own name — the slot stem, that writer's fresh nonce,
and `.part` — so the output writer, the refusal writer and any concurrent
process filling the same slot never share a temp, and a killed writer's
half-written `.part` is named after nobody else and never renamed into
place. The `.part` suffix also keeps it out of the served/replayed names
(`.out`, `.fail`), so a half-written temp is never mistaken for a slot. -/
def partName (srcKey variant nonce : String) : String :=
  stem srcKey variant ++ "-" ++ nonce ++ ".part"

/-! ## The reading

One conversion process read as a `PicCache.Outcome`. `readable` is the
platform-independent evidence the tool produced its result: a non-empty
output file that was read back for a byte conversion, or the boundary's
`true` verdict for validation. A clean exit with no usable result is not the
tool's refusal — it is truncated or unreadable output, a fact about the
machine — so, unlike `PicCache.outcome`, it is inconclusive and retried. A
tool's own no is a nonzero exit that left a log (or the boundary's explicit
refusal, fed in as such). Everything else — a budget kill, a failed spawn,
a nonzero exit with no log at all — says nothing about the request. -/
def convOutcome (ran : PicCache.Ran) (readable : Bool) (log : PicCache.Log) :
    PicCache.Outcome :=
  let said (fallback : String) : String :=
    if log.tail.isEmpty then fallback else log.tail
  match ran with
  | .exited 0 => if readable then .drawn else .inconclusive (said "no usable output was produced")
  | .exited c =>
    match log with
    | .absent => .inconclusive s!"exit code {c}"
    | .says _ => .refused (said s!"exit code {c}")
  | .overran s => .inconclusive (said s!"no result within {s} s; killed")
  | .unstarted e => .inconclusive (said e)

/-- The boundary's own refusal — `xmllint` exits cleanly but the support
XPath answered `false`, or a DTD was seen — carrying the boundary's words.
This is a completed verdict of the tool, so it is remembered like any
refusal; it is spelled here rather than routed through `convOutcome`
because the "no" lives in the tool's stdout, not its exit code. -/
def boundaryRefusal (says : String) : PicCache.Outcome := .refused says

/-- A two-stage operation (validate, then convert) as one answer: the first
stage's `.drawn` means "continue", so the composite is the second stage;
any refusal or inconclusive short-circuits and is the composite. The IO
layer never runs the second stage unless the first drew, so this is only
ever evaluated with a `.drawn` first stage, but the short-circuit equations
are stated for completeness. -/
def seq (first second : PicCache.Outcome) : PicCache.Outcome :=
  match first with
  | .drawn => second
  | other => other

/-! ## The invariants

The three that close the loop, mirroring `PicCache`, plus the one that is
this cache's own: a converter that exits cleanly and produces nothing usable
is retried, never remembered. -/

/-- **A conversion succeeds exactly when the tool exited cleanly and left a
usable result.** No other ending is a success, so no truncated output is ever
served as the converted bytes. -/
theorem convOutcome_converted_exact (ran : PicCache.Ran) (readable : Bool)
    (log : PicCache.Log) :
    convOutcome ran readable log = .drawn ↔ (ran = .exited 0 ∧ readable = true) := by
  cases ran with
  | exited c =>
    cases c with
    | zero => cases readable <;> simp [convOutcome]
    | succ n => cases log <;> simp [convOutcome]
  | overran _ => simp [convOutcome]
  | unstarted _ => simp [convOutcome]

/-- **A clean exit that produced nothing usable is retried, not remembered.**
This cache's own invariant, and the one that separates it from the TeX
boundary: `rsvg-convert` or `pdftocairo` can exit 0 and yet write an empty
or unreadable file when the machine is under load or out of space, and that
is truncated output, not a verdict that the figure cannot be drawn. So the
slot stays empty and the next build runs the tool again — the honest
outcome, where remembering it would condemn a convertible figure forever. -/
theorem unreadable_retried_exact (log : PicCache.Log) :
    PicCache.remembers (convOutcome (.exited 0) false log) = none := by
  cases log <;> simp [convOutcome, PicCache.remembers]

/-- **The tool's own no is a nonzero exit that left a log, kept in the
tool's words.** -/
theorem convOutcome_refused_exact (c : Nat) (hc : c ≠ 0) (readable : Bool)
    (tail : String) (ht : tail ≠ "") :
    convOutcome (.exited c) readable (.says tail) = .refused tail := by
  cases c with
  | zero => exact absurd rfl hc
  | succ n => simp [convOutcome, PicCache.Log.tail, ht]

/-- **A budget kill is not remembered, so the next build retries.** -/
theorem overrun_retried_exact (s : Nat) (readable : Bool) (log : PicCache.Log) :
    PicCache.remembers (convOutcome (.overran s) readable log) = none := by
  cases log <;> simp [convOutcome, PicCache.remembers]

/-- **A failed spawn is not remembered, so the next build retries.** -/
theorem unstarted_retried_exact (e : String) (readable : Bool) (log : PicCache.Log) :
    PicCache.remembers (convOutcome (.unstarted e) readable log) = none := by
  cases log <;> simp [convOutcome, PicCache.remembers]

/-- **A nonzero exit that left no log at all is not remembered.** The
machine-fact half a host with no tool installed lands on: a spawn that
reached `exec` and failed there comes back as an exit code like any other,
so the absent log is what separates it from a verdict. -/
theorem unlogged_retried_exact (c : Nat) (hc : c ≠ 0) (readable : Bool) :
    PicCache.remembers (convOutcome (.exited c) readable .absent) = none := by
  cases c with
  | zero => exact absurd rfl hc
  | succ n => simp [convOutcome, PicCache.remembers]

/-- **Only the tool's own refusal is remembered.** Reuses the boundary's
`remembers`, whose meaning is unchanged: a verdict is written exactly when
the outcome is a refusal. -/
theorem remembers_verdict_exact (o : PicCache.Outcome) (says : String) :
    PicCache.remembers o = some says ↔ o = .refused says :=
  PicCache.remembers_verdict_exact o says

/-- **A held answer is never re-attempted.** Reuses the boundary's cold
rule: the tool runs exactly when the slot holds neither converted output
nor a remembered refusal. -/
theorem step_cold_exact (drawn : Bool) (refusal : Option String) :
    PicCache.step drawn refusal = .run ↔ (drawn = false ∧ refusal = none) :=
  PicCache.step_cold_exact drawn refusal

/-- **A composite short-circuits on its first non-success.** A validation
refusal or an inconclusive first stage is the whole answer; the converter
never runs. -/
theorem seq_short_exact (first second : PicCache.Outcome) (h : first ≠ .drawn) :
    seq first second = first := by
  cases first with
  | drawn => exact absurd rfl h
  | refused _ => rfl
  | inconclusive _ => rfl

/-- **A composite whose first stage drew is its second stage.** -/
theorem seq_drawn_exact (second : PicCache.Outcome) :
    seq .drawn second = second := rfl

end LeanTex.Cli.ConvCache
