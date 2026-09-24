import Tests.Support

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-! # The styling API's own closure: a declared token is a read token

`tokenVars` emits every design token as a CSS custom property, and the
backend's docstring states why: "a reader's stylesheet can override them".
That contract has a silent failure mode no other tier sees. A token the
engine declares in `:root` and then reads from no rule is a knob wired to
nothing — a reader overrides it, the page does not move, and every check in
the suite stays green, because elaboration was correct, the census is
correct, and the bytes are exactly what the backend meant to write. The
defect is the *absence* of a reference, which only the emitted stylesheet
can witness.

So this is a check, not a theorem: the property is decidable by reading
what the backend emitted, and AGENTS.md's rule is that an inspectable
artifact fact wants a test rather than a proof.

Two distinctions make the claim true rather than merely loud.

*Whose token.* A document's `\tokens{ rhythm = 2ex }` names a length for
its own use; the engine resolves it at elaboration and emits the property
so a host page can read it. The engine owes no rule for a name it does not
define, so the claim ranges over the names the engine itself declares —
the union over `Theme.builtin`, the shipped bundles' own tables.

*Where read.* A token is read if any fixture's HTML references it, not
every fixture's: `separator` is a palette key the title page's rule reads
only where a title page draws one, and a fixture that declares the key
without drawing a rule is correct. The union over the corpus is what
separates "no rule can read this" from "this document did not use it".

The union is also why the measurement must match `var(--name,` as well as
`var(--name)`. Two of the three tokens this check first cleared are read
with fallbacks — `var(--frametitlefg, var(--bg, #fff))` — and a scan for
the bare closing paren alone reports them unread, which is how the bar's
foreground came to be called a defect when the rule for it was already
there.

*Why not the `_agree` theorem.* The deeper fact wants to be one: both
backends read the same `Design`, so "the PDF and the HTML honour the same
token set" is `_agree`-shaped. It is not statable today, and the reason is
structural rather than a proof wall. `backend_gaps_agree` can be stated
because `Ir.rhythmGapQuanta` is a declared table and each backend's gap is
a *function of a row* — the theorem quantifies over the table and compares
two projections. A token's reads are not a value either backend projects:
the PDF's are `tokens.find?` call sites scattered through `Layout`, this
backend's are string literals inside emitted rules. There is nothing to
quantify over, so the honest version needs a carrier neither backend
has — a declared per-token read set, `rhythmGapQuanta`'s shape for
tokens — and until one exists the claim is checkable only by reading the
artifact, which is what this block does. -/

/-- Every token name a shipped bundle declares: the set the engine is
answerable for, as against a document's own `\tokens` names. -/
def engineTokenNames : List String :=
  (Theme.builtin.flatMap fun th =>
    th.tokens.entries.toList.map (·.1)).eraseDups

/-- A custom property's declaration site, as `tokenVars` spells it. The
colon anchors the name, so `--sep:` never matches `--separator:`. -/
def declaresToken (html name : String) : Bool := hasStr html s!"--{name}:"

/-- A reference to the property from a rule or an inline style, in either
form the backend writes: bare, or with a fallback. The delimiter anchors
the name for the same reason. -/
def readsToken (html name : String) : Bool :=
  hasStr html s!"var(--{name})" || hasStr html s!"var(--{name},"

/-- The engine tokens no rule reads anywhere in the corpus, each with the
reason it is still owed. A ratchet in both directions: a row whose token
starts being read fails until the row goes, and a token that falls out of
every rule fails until it is wired or recorded here.

Five of the five are one finding. The title page's gaps and its separator's
thickness are resolved in the elaborator, which pushes `Ir.Block.spaced`
with the resolved `SymGlue` and the rule with a bare thickness. Neither
constructor carries the name of the token the value came from, so the
backend has nothing to reference: it writes the length it was handed.
Wiring them is an IR change — a name beside the glue, as `Ir.Block.rule`
already carries one for its colour, which is exactly why `separator` is
read and `separatorheight` is not — and that is a carrier neither backend
has today, not a rule this backend is missing. -/
def htmlUnreadTokenOffences : List (String × String) := [
  ("separatorheight",
    "the title separator's thickness reaches the backend as a bare glue on \
Ir.Block.rule, which names its colour but not its thickness"),
  ("separatorgap",
    "the gap above and below the separator is resolved into Ir.Block.spaced, \
which carries no token name"),
  ("subtitlegap", "the same, above the subtitle"),
  ("authorgap", "the same, below the author"),
  ("institutegap", "the same, below the institute")]

/-- A design token the engine emits is a token some rule reads. -/
def htmlTokenClosureChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  for (n, _) in htmlUnreadTokenOffences do
    t s!"unread token row {n}: names an engine token"
      (engineTokenNames.contains n)
  let mut pages : List String := []
  for n in goldenNames do
    let src ← IO.FS.readFile s!"tests/corpus/{n}.tex"
    let (doc, _) ← elabFixture n src
    pages := (HtmlDoc.emit {} doc).1 :: pages
  for tok in engineTokenNames do
    let declared := pages.any fun h => declaresToken h tok
    let read := pages.any fun h => readsToken h tok
    if htmlUnreadTokenOffences.any fun (f, _) => f == tok then
      t s!"token closure {tok}: the recorded offence no longer fires — a rule \
now reads it; delete its row" (declared && !read)
    else
      t s!"token closure {tok}: declared as a custom property by some fixture, \
so some rule must reference it" (!declared || read)
