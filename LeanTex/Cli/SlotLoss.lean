import LeanTex.Core.Font
import LeanTex.Core.Ir
import LeanTex.Cli.DriverDiag

/-! **A family slot that fell to the body face, named.**

The engine resolves three family slots — body, sans, mono. A slot the
document declares no family for is filled by the body family
(`resolveName` in the driver's assembly), so a `\texttt`, `\url` or
verbatim run in a document with no `\fonts{ mono = ... }` sets in body
prose. `Font.FontSet.slotCollapsed` is that fact, stated where `FontSet`
can see it; this module is the decision built on it, and the diagnostic is
`DriverDiag.slotCollapsed`.

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

/-- A family slot, with the words a diagnostic about it needs: the `\fonts`
key that would declare it, and the constructs that ask for it. Data rather
than a case split at the message site, so the two slots cannot drift into
saying the loss differently. -/
structure SlotWord where
  slot : Nat
  key : String
  asks : String
  deriving Repr, BEq

/-- Slot 1: NFSS's sans family. -/
def sansWord : SlotWord :=
  { slot := 1, key := "sans", asks := "'\\textsf' and '\\sffamily'" }

/-- Slot 2: NFSS's typewriter family. `\url` joins the two NFSS spellings
because url.sty sets a URL in the typewriter family by default, which is
where the engine sets it. -/
def monoWord : SlotWord :=
  { slot := 2, key := "mono", asks := "'\\texttt', '\\url' and verbatim" }

/-- The slots a collapse can be reported for. Slot 0 is absent by
construction: it is the face the others are compared *against*, so a report
about it would be a vacuous truth rather than a loss (`words_nonzero`,
`Font.FontSet.slotCollapsed_body`). -/
def words : Array SlotWord := #[sansWord, monoWord]

/-- **The reference slot is never a subject.** Keeps a reader from being
told the body face fell to itself. -/
theorem words_nonzero : ∀ w ∈ words, w.slot ≠ 0 := by
  simp [words, sansWord, monoWord]

/-- The family a document declared for a slot, if it declared one. The
driver's own fallback order (`resolveName`) is what makes `none` the
condition worth reporting: an undeclared slot does not fail to resolve, it
resolves somewhere else. -/
def declared (spec : Ir.FontSpec) : Nat → Option String
  | 1 => spec.sans
  | 2 => spec.mono
  | _ => spec.body

/-- **Which family slots does this document's own content ask for?**
`foldBlocks`/`foldInlines` leaves, so the descent — a `\texttt` inside a
footnote, a running head, a style's font template — is the fold's and is
not re-decided here. A document that never sets mono is never told about
its mono slot.

Slot 2 is reached two ways and both are leaves: `Ir.Style.mono` on a
`.styled` inline (`\texttt`, `\ttfamily`, `\url`, inline verbatim), and an
`Ir.Block.verbatim`, which the layout sets by wrapping its content in
`.styled .mono`. -/
def slotsUsed (doc : Ir.Doc) : Array Nat :=
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

/-- **The slots this document lost.** Three conditions, all necessary: the
document asks for the slot, it declared no family for it, and the resolved
index puts it on the body face. Drop any one and the diagnostic becomes
noise — a document that never sets mono does not care, a document that
declared `mono` got what it asked for even if that family *is* the body
family, and a slot resolving to its own face lost nothing. -/
def losses (spec : Ir.FontSpec) (fs : Font.FontSet) (used : Array Nat) :
    Array SlotWord :=
  words.filter fun w =>
    used.contains w.slot && (declared spec w.slot).isNone && fs.slotCollapsed w.slot

/-- **The report is exactly its three conditions.** A diagnostic resting on
`losses` names the condition it says it names, rather than a proxy that
could drift — the shape `slotCollapsed_exact` has one layer down. -/
theorem losses_exact (spec : Ir.FontSpec) (fs : Font.FontSet) (used : Array Nat)
    (w : SlotWord) :
    w ∈ losses spec fs used ↔
      (w ∈ words ∧ used.contains w.slot = true ∧ (declared spec w.slot).isNone = true
        ∧ fs.slotCollapsed w.slot = true) := by
  simp [losses, Array.mem_filter, and_assoc]

/-- A declared slot is never reported: the document got the family it named,
whichever face that family resolves to. -/
theorem losses_declared (spec : Ir.FontSpec) (fs : Font.FontSet) (used : Array Nat)
    (w : SlotWord) (h : (declared spec w.slot).isSome) :
    w ∉ losses spec fs used := by
  intro hw
  have := (losses_exact spec fs used w).mp hw
  simp [Option.isNone_iff_eq_none] at this
  simp_all

/-- An unused slot is never reported: the loss is what a reader sees, and a
reader sees nothing where the document set nothing. -/
theorem losses_used (spec : Ir.FontSpec) (fs : Font.FontSet) (used : Array Nat)
    (w : SlotWord) (h : w ∈ losses spec fs used) : used.contains w.slot := by
  exact ((losses_exact spec fs used w).mp h).2.1

/-- The diagnostics for one resolved environment: one per collapsed slot the
document uses, each carrying `slot:<key>` as its subject so the site census
counts it. Never one per `\texttt` run — the loss is the slot's, and it is
the same loss wherever the slot is set. -/
def diags (spec : Ir.FontSpec) (fs : Font.FontSet) (doc : Ir.Doc) : Array Diag :=
  (losses spec fs (slotsUsed doc)).map fun w =>
    DriverDiag.slotCollapsed w.key w.asks

/-- **Which `\urlstyle` values the resolved environment satisfies.**
url.sty's selector names the face a `\url` sets in, and the engine sets one
in the mono slot and does not switch it — so whether the selector was
*honoured* is a question about where that slot resolved, and the answer is
not the same in every document. That is why the elaboration cannot decide
it: `\urlstyle` is read in a pass that runs before a font exists, and the
arm that reads it was asserting a font fact it had no way to check.

With a distinct mono face declared, `tt` is what the page does. With none,
the slot is the body face (`Font.FontSet.slotCollapsed`), so a URL sets in
the running roman face: `same` and `rm` are satisfied there and `tt` is not.
`sf` asks for the sans family, which neither configuration gives a URL.

This gates nothing yet, and says so rather than implying otherwise. The
refusal it exists to condition is `Compat.lean`'s `urlstyle` arm, which
fires `W0104` for every value but `tt` with no font in scope to check
against — so `\urlstyle{same}` is refused in the one configuration that
satisfies it. That arm is another owner's; when it reads this predicate the
`-- premise: slotLossChecks` line moves there with it, and
`slotLossChecks`'s last two rows — which assert today's wrong answer —
break in both directions the moment it lands.

The claims above are not prose: every row is asserted against both resolved
sets it speaks of (`slotLossChecks`), so a wrong one is falsified by an
environment rather than by a reader. -/
def urlStyleSatisfied (fs : Font.FontSet) (value : String) : Bool :=
  match value with
  | "tt" => !fs.slotCollapsed 2
  | "same" => fs.slotCollapsed 2
  | "rm" => fs.slotCollapsed 2
  | _ => false

/-- **No value is satisfied in both configurations.** The selector is a
choice between faces, so an environment answering yes to `tt` and to `same`
would be one where the mono slot both was and was not the body face. -/
theorem urlStyleSatisfied_exact (fs : Font.FontSet) :
    urlStyleSatisfied fs "tt" = !urlStyleSatisfied fs "same" := by
  simp [urlStyleSatisfied]

end LeanTex.Cli.SlotLoss
