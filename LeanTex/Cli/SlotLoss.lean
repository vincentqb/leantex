module

public import LeanTex.Core.Font
public import LeanTex.Core.Ir
public import LeanTex.Cli.Args
import LeanTex.Cli.DriverDiag

/-! **A family slot set in a face that is not of its kind, named.**

The engine resolves three family slots — body, sans, mono. A sans slot the
document declares no family for is filled by the body family
(`resolveName` in the driver's assembly); an undeclared mono slot takes an
installed fixed-pitch face first (`FontDb.pickMono`) and falls to the body
family only on a scan that holds none — so a `\texttt`, `\url` or verbatim
run sets in body prose exactly there. This module is the decision; the
diagnostic is `DriverDiag.slotCollapsed` (W0390).

The decision reads the face, never the slot index. An index says which
face; it does not say what that face is, and the two part company in a
common setup: the slides class sets its text in the sans family and hands
an undeclared mono slot to the body family, so the typewriter face is not
the text face — the index reads "own face" — and it is a proportional
serif all the same. What the loss is depends on the slot (`SlotKind`): a
typewriter run wants fixed pitch, which every face declares; a sans run
wants contrast with the running text, which no face field records, so the
one fact the engine has is whether the face is the text's own.

Beyond the face, the decision needs two facts, each a condition here
rather than an assumption:

* what the document *set* — a slot no run reaches is no loss (`slotsUsed`);
* which artifacts carry a face at all — a page that declares `css =` ships
  none, and "set in the body face" then describes a file nobody receives
  (`carries`). Where a PDF carries the face and a page beside it does not,
  the report says which artifact lost (`Carry.only`).

It sits under `LeanTex/Cli/` for two reasons. The emission needs the
document's `\fonts` declaration *and* the resolved index, and the driver's
assembly is the one place holding both. And a decision that is a module
returning its diagnostics is reachable as a unit — the property that lets a
probe run the real path rather than rebuild it, which a decision inlined in
the entry path is not.

Effects as data: nothing here opens a file or asks the host anything. The
font environment arrives as a resolved `FontSet` and a declared `FontSpec`,
both values; the answer leaves as `Diag` values. The policy is therefore
checkable with no font installed at all, which is the `Cli/PicCache.lean`
and `Cli/FontFix.lean` shape. -/

namespace LeanTex.Cli.SlotLoss

open LeanTex.Core

/-- What a slot's runs ask of the face that sets them, which is what
"lost" means for that slot. -/
public inductive SlotKind where
  /-- Fixed pitch: the typewriter family's defining property, and one
  every face declares (`post.isFixedPitch`). -/
  | fixedPitch
  /-- Contrast with the running text. No face field says "is a sans
  design" — many faces declare no OS/2 family class — so the fact the
  engine holds is whether the face is the text's own. -/
  | contrast
  deriving Repr, BEq, DecidableEq

/-- Is the face serving `slot` not of this kind? Read off the face through
the same `lookup` the setter uses: its own pitch flag, or its identity
with the face the text is set in. -/
public def SlotKind.lost (k : SlotKind) (fs : Font.FontSet) (slot : Nat) : Bool :=
  match k with
  | .fixedPitch => !fs.slotIsFixedPitch slot
  | .contrast => fs.slotCollapsed slot

/-- A family slot, with the words a diagnostic about it needs: the `\fonts`
key that would declare it, the runs the loss is about, what is honestly
known about the substitute, and what the slot's runs ask of a face. Data
rather than a case split at the message site, so the two slots cannot drift
into saying the loss differently.

`runs` names the slot, not the constructs: which spelling reached a slot is
not a fact this census keeps (`\url` and `\texttt` are one `.styled .mono`
inline by the time the IR exists), and a message listing constructs the
document never wrote is a message that misreports. -/
public structure SlotWord where
  slot : Nat
  key : String
  runs : String
  note : String
  kind : SlotKind
  deriving Repr, BEq

/-- Slot 1: NFSS's sans family. The note claims no more than the engine
knows: a sans run set in the text's own face does not contrast with the
text around it, whatever that face is. -/
public def sansWord : SlotWord :=
  { slot := 1, key := "sans", runs := "sans runs"
    note := "so they do not contrast with the text around them"
    kind := .contrast }

/-- Slot 2: NFSS's typewriter family. The note is what the kind's test
established, so the message cannot say it of a fixed-pitch face. -/
public def monoWord : SlotWord :=
  { slot := 2, key := "mono", runs := "typewriter runs"
    note := "which is not fixed-pitch"
    kind := .fixedPitch }

/-- The slots a loss can be reported for. Slot 0 is absent by
construction: it is the text face the others are compared *against*, so a
report about it would be a vacuous truth rather than a loss (`words_mem`,
`Font.FontSet.slotCollapsed_body`). -/
public def words : Array SlotWord := #[sansWord, monoWord]

/-- **Every reportable slot is drawn from the two past the body.** Keeps a
reader from being told the body face fell to itself. -/
public theorem words_mem : ∀ w ∈ words, w.slot = 1 ∨ w.slot = 2 := by
  simp [words, sansWord, monoWord]

/-- The family a document declared for a slot, if it declared one. The
driver's own fallback order (`resolveName`) is what makes `none` the
condition worth reporting: an undeclared slot does not fail to resolve, it
resolves somewhere else. -/
public def declared (spec : Ir.FontSpec) : Nat → Option String
  | 1 => spec.sans
  | 2 => spec.mono
  | _ => spec.body

/-- What served a lost slot, in words a reader can check against the
artifact: the face the running text is set in, or — in a class whose text
face is another family's, a deck's sans — the body family, which the
driver's fallback order hands every undeclared slot. -/
public inductive Served where
  | bodyFace
  | bodyFamily
  deriving Repr, BEq, DecidableEq

def Served.words : Served → String
  | .bodyFace => "the body face"
  | .bodyFamily => "the body family"

/-- Which of the two served the slot: the text's own face exactly when the
slot resolves where the text does. -/
public def served (fs : Font.FontSet) (slot : Nat) : Served :=
  if fs.slotCollapsed slot then .bodyFace else .bodyFamily

/-- What this run's artifacts do with the resolved faces. `faced`: the
emitted artifacts that set runs in the resolved set — the PDF always, an
HTML page only where `Doc.fontPolicy` is `embedded`. `unfaced`: the emitted
artifacts that set runs from a stylesheet of their own instead — an HTML
page under a declared `css =`, which styles code from its own monospace
stack. A markdown twin sets runs in no face at all and is in neither. -/
public structure Carry where
  faced : Array Emit
  unfaced : Array Emit
  deriving Repr, BEq

/-- **Which artifacts carry a face.** A loss about the face a run set in is
a loss only where a reader receives that face. -/
public def carries (emit : Array Emit) (policy : Ir.FontPolicy) : Carry :=
  { faced := emit.filter fun e => e == .pdf || (e == .html && policy == .embedded)
    unfaced := emit.filter fun e => e == .html && policy != .embedded }

/-- **An HTML-only page under a declared stylesheet carries nothing.**
The gate's own condition, stated where the driver reads it: the
configuration the site port builds in is the one that must stay silent. -/
public theorem carries_exact (policy : Ir.FontPolicy) :
    (carries #[.html, .md] policy).faced.isEmpty = (policy != .embedded) := by
  cases policy <;> rfl

/-- **A PDF beside a page under its own stylesheet is the one artifact that
lost.** The page styles its runs from its own stack, so the loss the report
names is the PDF's alone. -/
public theorem carries_mixed_exact :
    carries #[.pdf, .html] .none = { faced := #[.pdf], unfaced := #[.html] } := by
  rfl

/-- How a report names an artifact. -/
def artifactWord : Emit → String
  | .pdf => "the PDF"
  | .html => "the HTML page"
  | .md => "the markdown twin"

/-- The artifacts a report names, when not every artifact the run emits
sets its runs in the resolved faces; `none` when every one does, and the
report then holds of the whole build. -/
def Carry.only (c : Carry) : Option String :=
  if c.unfaced.isEmpty then none
  else some (" and ".intercalate (c.faced.toList.map artifactWord))

/-- **Which family slots does this document's own content ask for?**
`foldBlocks`/`foldInlines` leaves, so the descent — a `\texttt` inside a
footnote, a running head, a style's font template — is the fold's and is
not re-decided here. A document that never sets mono is never told about
its mono slot.

Slot 2 is reached two ways and both are leaves: `Ir.Style.mono` on a
`.styled` inline (`\texttt`, `\ttfamily`, `\url`, inline verbatim), and an
`Ir.Block.verbatim`, which the layout sets by wrapping its content in
`.styled .mono`. -/
public def slotsUsed (doc : Ir.Doc) : Array Nat :=
  let push (acc : Array Nat) (n : Nat) : Array Nat :=
    if acc.contains n then acc else acc.push n
  let fi (acc : Array Nat) : Ir.Inline → Array Nat
    | .styled .mono _ => push acc 2
    | .styled .sans _ => push acc 1
    | _ => acc
  let fb (acc : Array Nat) : Ir.Block → Array Nat
    | .verbatim _ _ _ => push acc 2
    | _ => acc
  (Ir.furnitureInlines doc).foldl (fun acc r => Ir.foldInlines fi acc r)
    (Ir.foldBlocks fb fi #[] doc.body)

/-- **The slots this document lost.** Four conditions, all necessary: some
artifact carries a face, the document asks for the slot, it declared no
family for it, and the face serving the slot is not of the slot's kind.
Drop any one and the diagnostic becomes noise: a build shipping no face has
no face to lose, a document that never sets mono does not care, a document
that declared `mono` got what it asked for whatever that family is, and a
fixed-pitch face sets typewriter runs in fixed pitch whichever slot index
it came through. -/
public def losses (spec : Ir.FontSpec) (fs : Font.FontSet) (used : Array Nat)
    (c : Carry) : Array SlotWord :=
  if c.faced.isEmpty then #[] else
  words.filter fun w =>
    used.contains w.slot && (declared spec w.slot).isNone && w.kind.lost fs w.slot

/-- **The report is exactly its conditions.** A diagnostic resting on
`losses` names the condition it says it names, rather than a proxy that
could drift — the shape `slotCollapsed_exact` has one layer down. -/
public theorem losses_exact (spec : Ir.FontSpec) (fs : Font.FontSet) (used : Array Nat)
    (c : Carry) (w : SlotWord) :
    w ∈ losses spec fs used c ↔
      (c.faced.isEmpty = false ∧ w ∈ words ∧ used.contains w.slot = true
        ∧ (declared spec w.slot).isNone = true ∧ w.kind.lost fs w.slot = true) := by
  by_cases h : c.faced.isEmpty
  · simp [losses, h]
  · simp [losses, h, Array.mem_filter, and_assoc]

/-- **The mono decision reads the face, never the index.** A typewriter
slot is reported exactly when the artifact carries a face, the document
sets the slot, declared no mono family, and the face serving slot 2 is not
fixed-pitch: `lookup`'s answer enters only through that face's own flag, so
no index arithmetic — which face the text is in, whether slot 2 shares it —
can make the answer differ. -/
public theorem losses_mono_exact (spec : Ir.FontSpec) (fs : Font.FontSet) (used : Array Nat)
    (c : Carry) :
    monoWord ∈ losses spec fs used c ↔
      (c.faced.isEmpty = false ∧ used.contains 2 = true ∧ spec.mono.isNone = true
        ∧ fs.slotIsFixedPitch 2 = false) := by
  rw [losses_exact]
  simp [monoWord, words, declared, SlotKind.lost]

/-- A reported slot is drawn from the slots the document set: the loss is
what a reader sees, and a reader sees nothing where the document set
nothing. -/
public theorem losses_mem (spec : Ir.FontSpec) (fs : Font.FontSet) (used : Array Nat)
    (c : Carry) (w : SlotWord) (h : w ∈ losses spec fs used c) :
    used.contains w.slot := by
  exact ((losses_exact spec fs used c w).mp h).2.2.1

/-- The diagnostics for one resolved environment: one per lost slot the
document uses, each carrying `slot:<key>` as its subject so the site census
counts it, saying what served the slot and — in a build where not every
artifact carries the face — which artifact lost. Never one per `\texttt`
run: the loss is the slot's, and it is the same loss wherever the slot is
set. -/
public def diags (spec : Ir.FontSpec) (fs : Font.FontSet) (doc : Ir.Doc)
    (c : Carry) : Array Diag :=
  (losses spec fs (slotsUsed doc) c).map fun w =>
    DriverDiag.slotCollapsed w.key w.runs (served fs w.slot).words w.note c.only

end LeanTex.Cli.SlotLoss
