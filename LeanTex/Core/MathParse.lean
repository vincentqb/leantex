import LeanTex.Core.Parse
import LeanTex.Core.Decl
import LeanTex.Core.Math
import LeanTex.Core.MathSymData
import LeanTex.Core.Ir
import LeanTex.Core.Loop

/-! The math surface: `$...$` bodies and alignment environments elaborated
into `Math.MList` atoms. Pure and total; the caller (the elaborator) owns
diagnostics. A construct outside this slice — `\cfrac`, `\text` with
markup inside — returns `.error name`, and the formula stays
`.math` source text with a warning naming the construct: out of scope is a
named warning, never a silent drop (PLAN M6). A ragged alignment row is
returned as a note beside the parse, rendered padded and diagnosed. -/

namespace LeanTex.Core.MathParse

open LeanTex.Core LeanTex.Core.Math

/-- A variable sets in mathematical italic (ISO 80000-2 §7 / TeXbook ch. 18:
letters denote variables and set italic; digits, operators, and named
functions are upright). The Mathematical Alphanumeric Symbols block carries
the italic letters, with Unicode's one hole: italic h is U+210E PLANCK
CONSTANT. -/
def italicVar (c : Char) : Char :=
  if c == 'h' then '\u210E'
  else if 'a' ≤ c && c ≤ 'z' then Char.ofNat (0x1D44E + (c.toNat - 'a'.toNat))
  else if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (0x1D434 + (c.toNat - 'A'.toNat))
  else c

/-- Literal Greek in math is unicode-math's second spelling of the control
words in `ctrlAtom` (`math-style=TeX`, unicode-math's default): the lowercase
block α..ω maps onto the Mathematical Italic block in order (ο and ς
included), the six symbol-slot forms ϵ ϑ ϰ ϕ ϱ ϖ onto their own italic
slots, and the capitals stay upright. The literal and the control word
denote one scalar — `greek_literal_agree` is the statement. -/
def greekLiteral (c : Char) : Option Char :=
  let n := c.toNat
  if 0x3B1 ≤ n && n ≤ 0x3C9 then some (Char.ofNat (0x1D6FC + (n - 0x3B1)))
  else if 0x391 ≤ n && n ≤ 0x3A9 && n != 0x3A2 then some c
  else match c with
    | 'ϵ' => some '𝜖'
    | 'ϑ' => some '𝜗'
    | 'ϰ' => some '𝜘'
    | 'ϕ' => some '𝜙'
    | 'ϱ' => some '𝜚'
    | 'ϖ' => some '𝜛'
    | 'ϴ' => some 'ϴ'
    | _ => none

/-- Characters that classify directly (TeX's mathcodes, plain format): the
class and the scalar actually set — `-` is MINUS SIGN, `*` is ASTERISK
OPERATOR. Digits and Latin letters classify after the table; a literal
Greek letter is the second spelling of its `ctrlAtom` row (`greekLiteral`). -/
def charAtom (c : Char) : Option (MathClass × Char) :=
  match c with
  | '+' => some (.bin, '+')
  | '-' => some (.bin, '\u2212')
  | '*' => some (.bin, '\u2217')
  | '/' => some (.ord, '/')
  | '=' => some (.rel, '=')
  | '<' => some (.rel, '<')
  | '>' => some (.rel, '>')
  | ':' => some (.rel, ':')
  | ',' => some (.punct, ',')
  | ';' => some (.punct, ';')
  | '.' => some (.ord, '.')
  | '!' => some (.closing, '!')
  | '?' => some (.closing, '?')
  | '(' => some (.opening, '(')
  | ')' => some (.closing, ')')
  | '[' => some (.opening, '[')
  | ']' => some (.closing, ']')
  | '|' => some (.ord, '|')
  | '@' => some (.ord, '@')
  | '×' => some (.bin, '×')
  | '·' => some (.bin, '\u22C5')
  | '±' => some (.bin, '±')
  | '−' => some (.bin, '\u2212')
  | '≤' => some (.rel, '≤')
  | '≥' => some (.rel, '≥')
  | '≠' => some (.rel, '≠')
  | '→' => some (.rel, '→')
  | '∈' => some (.rel, '∈')
  | '∞' => some (.ord, '∞')
  | _ =>
    if c.isDigit then some (.ord, c)
    else if c.isAlpha && c.toNat < 128 then some (.ord, italicVar c)
    else (greekLiteral c).map ((.ord, ·))

/-- The literal spellings of `ctrlAtom`'s Greek rows: unicode-math's one
table keyed by scalar, read as (literal, name) pairs. -/
def greekSpellings : List (Char × String) :=
  [('α', "alpha"), ('β', "beta"), ('γ', "gamma"), ('δ', "delta"),
   ('ϵ', "epsilon"), ('ε', "varepsilon"), ('ζ', "zeta"), ('η', "eta"),
   ('θ', "theta"), ('ϑ', "vartheta"), ('ι', "iota"), ('κ', "kappa"),
   ('λ', "lambda"), ('μ', "mu"), ('ν', "nu"), ('ξ', "xi"),
   ('π', "pi"), ('ϖ', "varpi"), ('ρ', "rho"), ('ϱ', "varrho"),
   ('σ', "sigma"), ('ς', "varsigma"), ('τ', "tau"), ('υ', "upsilon"),
   ('ϕ', "phi"), ('φ', "varphi"), ('χ', "chi"), ('ψ', "psi"), ('ω', "omega"),
   ('Γ', "Gamma"), ('Δ', "Delta"), ('Θ', "Theta"), ('Λ', "Lambda"),
   ('Ξ', "Xi"), ('Π', "Pi"), ('Σ', "Sigma"), ('Υ', "Upsilon"),
   ('Φ', "Phi"), ('Ψ', "Psi"), ('Ω', "Omega")]

/-- Control words that are one symbol atom: `(class, scalar)`. The rows
here are the engine's own decisions; every other symbol is a row of
`MathSymData.rows`, generated from the file that declares it (the kernel's
fontmath.ltx, amsfonts, amssymb) and unicode-math's table, and appended
below, so a row here is the one `lookup` finds for its name. Greek
lowercase is italic (the Mathematical Italic block, with TeX's `\epsilon` ↦
lunate and `\phi` ↦ straight forms); Greek capitals upright, TeX's
convention — kept whole here because `greek_literal_agree` reads it. -/
def ctrlAtom : List (String × MathClass × Char) :=
  [-- Greek, lowercase italic
   ("alpha", .ord, '𝛼'), ("beta", .ord, '𝛽'),
   ("gamma", .ord, '𝛾'), ("delta", .ord, '𝛿'),
   ("epsilon", .ord, '𝜖'), ("varepsilon", .ord, '𝜀'),
   ("zeta", .ord, '𝜁'), ("eta", .ord, '𝜂'),
   ("theta", .ord, '𝜃'), ("vartheta", .ord, '𝜗'),
   ("iota", .ord, '𝜄'), ("kappa", .ord, '𝜅'),
   ("lambda", .ord, '𝜆'), ("mu", .ord, '𝜇'),
   ("nu", .ord, '𝜈'), ("xi", .ord, '𝜉'),
   ("pi", .ord, '𝜋'), ("varpi", .ord, '𝜛'),
   ("rho", .ord, '𝜌'), ("varrho", .ord, '𝜚'),
   ("sigma", .ord, '𝜎'), ("varsigma", .ord, '𝜍'),
   ("tau", .ord, '𝜏'), ("upsilon", .ord, '𝜐'),
   ("phi", .ord, '𝜙'), ("varphi", .ord, '𝜑'),
   ("chi", .ord, '𝜒'), ("psi", .ord, '𝜓'),
   ("omega", .ord, '𝜔'),
   -- Greek, capitals upright
   ("Gamma", .ord, 'Γ'), ("Delta", .ord, 'Δ'), ("Theta", .ord, 'Θ'),
   ("Lambda", .ord, 'Λ'), ("Xi", .ord, 'Ξ'), ("Pi", .ord, 'Π'),
   ("Sigma", .ord, 'Σ'), ("Upsilon", .ord, 'Υ'), ("Phi", .ord, 'Φ'),
   ("Psi", .ord, 'Ψ'), ("Omega", .ord, 'Ω'),
   -- the operator scalar, where unicode-math sets U+2022
   ("bullet", .bin, '\u2219'),
   ("iff", .rel, '\u27FA'),
   -- inner: the dotses, TeX's \mathinner forms
   ("ldots", .inner, '…'), ("dots", .inner, '…'), ("cdots", .inner, '\u22EF'),
   -- amsmath's semantic dots are these two (amsmath.sty: `\let\dotsb\cdots`,
   -- `\let\dotsm\cdots`; `\dotsc` and `\dotso` set `\@ldots`)
   ("dotsc", .inner, '…'), ("dotso", .inner, '…'),
   ("dotsb", .inner, '\u22EF'), ("dotsm", .inner, '\u22EF'),
   ("iint", .op, '\u222C'),
   ("|", .ord, '\u2016'), ("colon", .punct, ':'),
   -- escapes: the reserved characters as content
   ("{", .opening, '{'), ("}", .closing, '}'), ("$", .ord, '$'),
   ("%", .ord, '%'), ("&", .ord, '&'), ("#", .ord, '#'), ("_", .ord, '_')]
    ++ MathSymData.rows

/-- Two spellings, one atom: every literal Greek letter classifies to exactly
the atom its control word does. The invariant whose absence let `$λ$`
degrade to source text while `$\lambda$` set the italic scalar. -/
theorem greek_literal_agree :
    ∀ p ∈ greekSpellings, charAtom p.1 = ctrlAtom.lookup p.2 := by
  decide

/-- Every letter of the lowercase and capital Greek blocks classifies —
including ο, ς, and the capitals TeX has no control word for (Α, Β, …),
which unicode-math sets from their literal spelling alone. -/
theorem greek_literal_covers :
    (∀ k < 25, (charAtom (Char.ofNat (0x3B1 + k))).isSome) ∧
    (∀ k < 25, k ≠ 17 → (charAtom (Char.ofNat (0x391 + k))).isSome) := by
  decide

/-- The big operators whose scripts become above/below limits in display
style — TeX's `\displaylimits` default for every `\mathop` except the
integrals, which plain TeX declares `\nolimits` (TeXbook p. 144). -/
def limitOps : List String :=
  ["sum", "prod", "coprod", "bigcup", "bigcap", "bigvee", "bigwedge",
   "bigoplus", "bigotimes", "bigodot", "bigsqcup", "biguplus"]

/-- The named functions TeX sets upright (TeXbook p. 162): Op atoms whose
nucleus is a word. -/
def ctrlWord : List (String × String) :=
  [("arccos", "arccos"), ("arcsin", "arcsin"), ("arctan", "arctan"),
   ("arg", "arg"), ("cos", "cos"), ("cosh", "cosh"), ("cot", "cot"),
   ("coth", "coth"), ("csc", "csc"), ("deg", "deg"), ("det", "det"),
   ("dim", "dim"), ("exp", "exp"), ("gcd", "gcd"), ("hom", "hom"),
   ("inf", "inf"), ("ker", "ker"), ("lg", "lg"), ("lim", "lim"),
   ("liminf", "lim inf"), ("limsup", "lim sup"), ("ln", "ln"),
   ("log", "log"), ("max", "max"), ("min", "min"), ("Pr", "Pr"),
   ("sec", "sec"), ("sin", "sin"), ("sinh", "sinh"), ("sup", "sup"),
   ("tan", "tan"), ("tanh", "tanh")]

/-- The function names whose scripts set as limits (TeXbook p. 162 marks
them: "the following … have limits that are placed above and below"). -/
def limitWords : List String :=
  ["det", "gcd", "inf", "lim", "liminf", "limsup", "max", "min", "Pr", "sup"]

/-- Explicit spacing commands, in mu (18ths of an em): TeX's values
(TeXbook p. 167); `\ ` and `~` take an interword third of an em. -/
def ctrlSpace : List (String × Int) :=
  [(",", 3), (":", 4), (";", 5), ("!", -3), ("quad", 18), ("qquad", 36),
   (" ", 6), ("~", 6)]

/-- The math alphabet commands, each one argument whose letters remap
(`Math.MathAlphabet.apply`): LaTeX's `\math…` family, `\bm`/`\boldsymbol`
(bold with variables kept italic), and the plain-TeX `\cal`/`\frak`, whose
dominant use `{\cal L}` reads here as `\cal` taking the single letter. -/
def alphaCtrl : List (String × Math.MathAlphabet × Math.AlphaSource) :=
  [("mathbb", .bb, .doc), ("mathcal", .cal, .doc), ("cal", .cal, .doc),
   ("mathfrak", .frak, .doc), ("frak", .frak, .doc),
   -- amsfonts.sty's obsolete spellings of `\mathbb` and `\mathbf`
   ("Bbb", .bb, .doc), ("bold", .bf, .doc),
   ("mathbf", .bf, .doc), ("bm", .bm, .doc), ("boldsymbol", .bm, .doc),
   ("mathit", .it, .doc), ("mathsf", .sf, .doc), ("mathtt", .tt, .doc), ("mathrm", .rm, .doc),
   -- unicode-math's `\sym…` family selects the math (`sym`) version of each
   -- alphabet explicitly, forcing the symbol source regardless of the
   -- document's `MathAlphabetSources`. `\symup`/`\symrm` are the upright
   -- roman; `\symbf` the default TeX bold (italic lowercase Greek),
   -- `\symbfup` upright bold, and `\symbfit` bold italic; the rest name
   -- their shape.
   ("symup", .rm, .sym), ("symrm", .rm, .sym), ("symit", .it, .sym),
   ("symbf", .bfDefault, .sym), ("symbfup", .bf, .sym), ("symbfit", .bfit, .sym),
   ("symsf", .sf, .sym), ("symtt", .tt, .sym), ("symbb", .bb, .sym),
   ("symcal", .cal, .sym), ("symfrak", .frak, .sym),
   -- LaTeX's text-style commands used inside math: `\textbf{x}` sets an
   -- upright bold roman x, which is exactly what `\mathbf` does, so they
   -- resolve to the same alphabets (document-sourced) rather than leaving
   -- the formula unrenderable. `\textrm` keeps the word arm above, which
   -- sets its letters as one upright word instead of letter by letter.
   ("textbf", .bf, .doc), ("textit", .it, .doc), ("textsf", .sf, .doc), ("texttt", .tt, .doc),
   ("textnormal", .rm, .doc), ("emph", .it, .doc)]

/-- A loss the parser can name without failing the formula: the
mathematics renders, something about its presentation does not. Typed
rather than a bare string so the elaborator dispatches each kind to its own
diagnostic — a ragged alignment row and a dropped colour are different
losses and may not share a code. -/
inductive Note where
  | ragged (msg : String)
  /-- A colour or font change inside math whose content renders in the
  surrounding style: `what` names the change for the message. -/
  | styleDropped (what : String)
  /-- A construct outside this slice that cost only itself: its name and its
  naming arguments are gone and its one content operand stands in its place,
  parsed as mathematics along with the rest of the formula. `what` names the
  construct. -/
  | constructFloored (what : String)
  /-- A colour expression the formula inks in, as the palette resolved it:
  the elaborator records its span, as the text path does, so the contrast
  judge can name where a colour came from. -/
  | inkUsed (expr : String) (color : Ir.Color) (entry : Bool)
  /-- A colour expression the palette cannot resolve: its content sets in
  the colour in force, named as the text path names it (W0304). -/
  | inkMissed (expr : String)
  deriving Repr, BEq

/-- What a formula reads from the document beyond its own tokens: a colour
expression resolved as the text path resolves one (`Palette.resolve`), with
whether it names a declared entry (`Palette.find?`, the HTML custom
property's name), and the cancel package's options and `\CancelColor`. The
defaults resolve nothing and load no option, which is how a formula parses
where no document stands behind it. -/
structure Env where
  ink : String → Option (Ir.Color × Bool) := fun _ => none
  cancel : CancelSpec := {}
  /-- The expression `\CancelColor` names when the palette cannot resolve
  it: a formula that draws a mark names it (W0304), the marks set in the
  colour in force. -/
  cancelMiss : Option String := none

/-- Text-style commands whose styling cannot be carried inside `\text`:
there the body is one upright word, so the command contributes its letters
and the styling is named as lost. At the formula's own level these resolve
through `alphaCtrl` instead, with no loss. -/
def textStyleCtrl : List String :=
  ["textbf", "textit", "textsf", "texttt", "textsc", "emph",
   "bf", "it", "sf", "tt"]

/-- Wrappers that ask for upright roman, which is already what `\text`'s
body sets: inside it they lose nothing, so they contribute their letters
and say nothing. Keeping them out of `textStyleCtrl` is what stops a
`degraded` code from firing over a no-op and failing a `--werror` run for
it — one code, one meaning, and the meaning is a loss. -/
def textNeutralCtrl : List String :=
  ["text", "mbox", "textrm", "textup", "textnormal", "rm"]

/-- The math accent commands: the combining mark set over the base
(unicode-math's accent table — `\hat` is U+0302), and whether it
stretches to the base's width through the face's horizontal variants.
`\overline` maps to U+0305, the mark layout draws as a rule from the
overbar constants (TeXbook Appendix G rule 9), so its stretch is exact. -/
def accentCtrl : List (String × Char × Bool) :=
  [("hat", '\u0302', false), ("widehat", '\u0302', true),
   ("tilde", '\u0303', false), ("widetilde", '\u0303', true),
   ("bar", '\u0304', false),
   ("dot", '\u0307', false), ("ddot", '\u0308', false),
   ("vec", '\u20D7', false), ("overline", '\u0305', true)]

/-- Delimiters `\left`/`\right` accept: the char actually set, or `none`
for the empty `.`. Names looked up in `ctrlAtom` too, so `\left\langle`
works. -/
def delimChar : Char → Option (Option Char)
  | '.' => some none
  | '(' => some (some '(')
  | ')' => some (some ')')
  | '[' => some (some '[')
  | ']' => some (some ']')
  | '|' => some (some '|')
  | '<' => some (some '\u27E8')
  | '>' => some (some '\u27E9')
  | _ => none

/-- The control words `parseToks` reads structurally, rather than through one
of the symbol tables: every name that reaches a `.ctrl` arm of the parse loop
by itself. Together with the tables, this is the whole of what this slice
models, and `knownCtrl` is the question the containment pass asks.

Listed rather than derived because the parse loop's arms are a `match` and
not a table; `containKnownChecks` probes each name here through
`parseMath`, so a name that stops being structural fails the suite rather
than quietly starting to be contained. -/
def structuralCtrl : List String :=
  ["over", "genfrac", "sqrt", "ensuremath", "left", "right",
   "limits", "nolimits", "text", "mbox", "textrm", "operatorname", "textcolor",
   "color", "cancelto",
   "bmod", "mod", "pod", "pmod", "dotsi"]

/-- cancel.sty's one-argument marks (v2.2): the command and the mark it
draws. `\cancelto` takes two arguments and is structural. -/
def cancelCtrl : List (String × CancelMark) :=
  [("cancel", .up), ("bcancel", .down), ("xcancel", .cross)]

/-- The fraction commands, each the `\genfrac` row its definition is
(amsmath.sty, TeX Live 2026: `\dfrac` is `\genfrac{}{}{}0`, `\tfrac`
`\genfrac{}{}{}1`, `\binom` `\genfrac()\z@{}`, `\dbinom` `\genfrac(){0pt}0`,
`\tbinom` `\genfrac(){0pt}1`; `\frac` sets the face's rule in the current
style, as `\genfrac{}{}{}{}` does). -/
def fracCmds : List (String × FracSpec) :=
  let binom : FracSpec := { left := some '(', right := some ')', rule := some 0 }
  [("frac", {}), ("dfrac", { style := some (.display false) }),
   ("tfrac", { style := some (.text false) }),
   ("binom", binom), ("dbinom", { binom with style := some (.display false) }),
   ("tbinom", { binom with style := some (.text false) })]

/-- amsmath's environments that build a grid inside a formula, each as the
grid it expands to and the delimiters `\left`/`\right` grow around it
(amsmath.sty, TeX Live 2026: `\env@matrix` is `\array{*\c@MaxMatrixCols c}`
with `MaxMatrixCols` 10, the five delimited matrices wrap it in
`\left…\right`; `\env@cases` is `\left\lbrace\array{@{}l@{\quad}l@{}}`
closed by `\right.`, under `\def\arraystretch{1.2}`; `aligned`,
`gathered` and `split` are the display alignments' own column models).
`\substack` is `subarray{c}`, one centred column. -/
def gridEnvs : List (String × GridKind × Option Char × Option Char) :=
  let matrix : GridKind := .array (Array.replicate 10 .center) 1000
  [("matrix", matrix, none, none), ("pmatrix", matrix, some '(', some ')'),
   ("bmatrix", matrix, some '[', some ']'), ("Bmatrix", matrix, some '{', some '}'),
   ("vmatrix", matrix, some '|', some '|'),
   ("Vmatrix", matrix, some '\u2016', some '\u2016'),
   ("cases", .array #[.left, .left] 1200, some '{', none),
   ("aligned", .align, none, none), ("gathered", .gather, none, none),
   ("split", .align, none, none), ("substack", .array #[.center] 1000, none, none)]

/-- Does this slice model the control word at all? -/
def knownCtrl (n : String) : Bool :=
  structuralCtrl.contains n
    || (cancelCtrl.lookup n).isSome
    || (fracCmds.lookup n).isSome
    || (alphaCtrl.lookup n).isSome
    || (accentCtrl.lookup n).isSome
    || (ctrlSpace.lookup n).isSome
    || (ctrlAtom.lookup n).isSome
    || (ctrlWord.lookup n).isSome

/-- The flat token stream a formula parses from: group edges, alignment
edges, and array boundaries become explicit markers, so the parser is one
pass over one array with a frame stack — totality immediate (the shape
`Parse.parse` set). -/
private inductive MTok where
  | ch (c : Char)
  | ws
  | sup
  | sub
  | openGrp
  | closeGrp
  | amp
  | rowEnd
  | arrOpen
  | arrClose
  /-- A `gridEnvs` environment opens: the grid its row names, closed by
  `arrClose` as an `array` is. -/
  | gridOpen (env : String)
  | ctrl (name : String)
  deriving Repr, BEq, Inhabited

private def flattenErr : Parse.Raw → Option String
  | .math _ _ _ => some "nested math"
  | .env n _ _ => some s!"\\begin\{{n}}"
  | .verb _ _ _ => some "verbatim"
  | .par _ => some "a blank line"
  | .sym c _ =>
    if c == '^' || c == '_' || c == '[' || c == ']' || c == '&' then none
    else some s!"'{String.ofList [c]}'"
  | _ => none

mutual

private def flattenList (out : Array MTok) : List Parse.Raw →
    Except String (Array MTok)
  | [] => .ok out
  | .ctrl "substack" _ :: .group body _ :: rest => do
    let o ← flattenList (out.push (.gridOpen "substack")) body.toList
    flattenList (o.push .arrClose) rest
  | r :: rest => do flattenList (← flattenOne out r) rest

private def flattenOne (out : Array MTok) : Parse.Raw →
    Except String (Array MTok)
  | .word s _ => .ok (s.foldl (fun a c => a.push (.ch c)) out)
  | .space => .ok (out.push .ws)
  | .ctrl "\\" _ => .ok (out.push .rowEnd)
  | .ctrl n _ => .ok (out.push (.ctrl n))
  | .sym '^' _ => .ok (out.push .sup)
  | .sym '_' _ => .ok (out.push .sub)
  | .sym '[' _ => .ok (out.push (.ch '['))
  | .sym ']' _ => .ok (out.push (.ch ']'))
  | .sym '&' _ => .ok (out.push .amp)
  | .sym '~' _ => .ok (out.push (.ctrl "~"))
  | .group body _ => do
    let o ← flattenList (out.push .openGrp) body.toList
    .ok (o.push .closeGrp)
  | .env "array" body _ => do
    -- `\begin{array}[pos]{spec} rows`: everything flattens; the parser
    -- reads the position and spec back out of the tokens after `arrOpen`.
    let o ← flattenList (out.push .arrOpen) body.toList
    .ok (o.push .arrClose)
  | .env n body p =>
    if (gridEnvs.lookup n).isSome then do
      let o ← flattenList (out.push (.gridOpen n)) body.toList
      .ok (o.push .arrClose)
    else match flattenErr (.env n body p) with
      | some what => .error what
      | none => .error "this construct"
  | r => match flattenErr r with
    | some what => .error what
    | none => .error "this construct"

end

/-- Past the spaces at `i`. -/
private def skipTokWs (toks : Array MTok) (i : Nat) : Nat := Id.run do
  let mut j := i
  for _ in [0:toks.size + 1] do
    if j ≥ toks.size then break
    if toks[j]? != some .ws then break
    j := j + 1
  return j

/-- Past a `[...]` option run beginning at `i`, else `i` itself. A command's
option run is markup with its name, whether or not this slice knows the
command — the rule `Ir.floorMask` already applies to a math source, here at
token scope. -/
private def skipTokOption (toks : Array MTok) (i : Nat) : Nat := Id.run do
  if toks[i]? != some (.ch '[') then return i
  let mut j := i + 1
  for _ in [0:toks.size + 1] do
    if j ≥ toks.size then break
    let t := toks[j]?
    j := j + 1
    if t == some (.ch ']') then break
  return j

/-- Past a balanced `{...}` beginning at `i`, or `i` itself when no group
opens there. An index loop, so the bound is the array and no measure is
owed — the shape `Ir.skipBalanced` has over characters. -/
private def skipTokGroup (toks : Array MTok) (i : Nat) : Nat := Id.run do
  if toks[i]? != some .openGrp then return i
  let mut j := i
  let mut depth := 0
  for _ in [0:toks.size + 1] do
    if j ≥ toks.size then break
    match toks[j]? with
    | some .openGrp =>
      depth := depth + 1
      j := j + 1
    | some .closeGrp =>
      j := j + 1
      if depth ≤ 1 then break else depth := depth - 1
    | _ => j := j + 1
  return j

/-- How many braced groups stand contiguously at `i`, spaces between them
ignored as LaTeX ignores them when it collects a command's arguments. The
containment decision reads this and nothing else about the operands. -/
private def countTokGroups (toks : Array MTok) (i : Nat) : Nat := Id.run do
  let mut j := skipTokWs toks i
  let mut n := 0
  for _ in [0:toks.size + 1] do
    let stop := skipTokGroup toks j
    if stop == j then break
    n := n + 1
    j := skipTokWs toks stop
  return n

/-- Which tokens of a formula survive containment, and the constructs
contained: one flag per token, the shape `Ir.floorMask` has over a source's
characters and for the same reason — the salvage is then a filter, so no
token can be invented (`keptToks_mem`).

Containment is confined to the commands `Ir.floorNamedArgs` names, and that
confinement is the whole of the judgement here. For those the floor has
*already* ruled on every operand — which ones name and which one carries —
so reducing the construct to its content operand applies a decision already
made rather than making a new one. The name, the option run and the naming
arguments are markup exactly as they are to `Ir.floorMask`; what remains
parses as mathematics with the rest of the formula.

Two refusals, both of them the same rule:

* more than one group left after the naming arguments — the operands would
  have to be juxtaposed, and `formulaFloor_separates` is the statement that
  juxtaposing two content operands states a claim the source does not
  (`\overset{a}{b}` as `ab` reads as a product);
* a command with no entry at all, whose operands nothing has ruled on. A
  glyph can be load-bearing between its neighbours rather than around its
  argument: `$a \xleftarrow{f} b$` reduced to its one operand is `𝑎𝑓𝑏`,
  which is the same falsity one construct further out. Whether a command is
  a wrapper or an operator is a per-command judgement and belongs beside the
  tables that already make it, not to a token walk that cannot see it.

A refused construct degrades the formula whole and is named as it was
before, so a lossy floor stays the contract and a false one stays
unreachable. -/
private def containPlan (toks : Array MTok) :
    Except String (Array Bool × Array String) := do
  let mut keep : Array Bool := Array.replicate toks.size true
  let mut names : Array String := #[]
  let mut i := 0
  for _ in [0:toks.size + 1] do
    if i ≥ toks.size then break
    match toks[i]? with
    | some (.ctrl n) =>
      if knownCtrl n then
        i := i + 1
      else
        let some naming := Ir.floorNamedArgs.lookup n | throw s!"\\{n}"
        let mut j := i + 1
        let o0 := skipTokWs toks j
        let o1 := skipTokOption toks o0
        if o1 != o0 then j := o1
        for _ in [0:naming] do
          let opened := skipTokWs toks (skipTokOption toks (skipTokWs toks j))
          if toks[opened]? != some .openGrp then
            j := opened
            break
          j := skipTokGroup toks opened
        if countTokGroups toks j > 1 then throw s!"\\{n}"
        for m in [i:j] do
          keep := keep.setIfInBounds m false
        names := names.push s!"\\{n}"
        i := j
    | some _ => i := i + 1
    | none => break
  return (keep, names)

/-- The one boundary that permits reducing a construct to its operand. -/
private def ContainedName (w : String) : Prop :=
  ∃ n, w = "\\" ++ n ∧ knownCtrl n = false ∧
    (Ir.floorNamedArgs.lookup n).isSome

/-- The existing fallible scan names only unknown, declared wrappers.
Both inner loops leave this invariant alone; the sole push has the
unknown-control and successful-lookup premises in scope. -/
private theorem containPlan_accounts (toks : Array MTok) :
    Loop.OnSuccess (fun plan => ∀ w ∈ plan.2, ContainedName w) (containPlan toks) := by
  unfold containPlan
  refine Loop.except_bind_of_inv
    (fun (st : Array Bool × Array String × Nat) => ∀ w ∈ st.2.1, ContainedName w)
    _ _ _ (Loop.except_forIn_range_inv _ _ _ _ _ (by simp) ?_) ?_
  · intro _ _ _ st hst
    dsimp only
    split
    · exact hst
    · split
      · rename_i n _
        split
        · exact hst
        · rename_i hknown
          split
          · rename_i naming hlookup
            have hname : ContainedName ("\\" ++ n) :=
              ⟨n, rfl, by simpa using hknown, by simp [hlookup]⟩
            have hpush : ∀ w ∈ st.2.1.push ("\\" ++ n), ContainedName w := by
              intro w hw
              rcases Array.mem_push.mp hw with hw | hw
              · exact hst w hw
              · simpa [hw] using hname
            split <;>
              refine Loop.except_bind_of_inv (fun _ => True) _ _ _
                (Loop.onSuccess_true _) ?_
            all_goals
              intro j _
              split
              · trivial
              · exact Loop.except_bind_of_inv (fun _ => True) _ _ _
                  (Loop.onSuccess_true _) (fun _ _ => hpush)
          · trivial
      · exact hst
      · exact hst
  · intro st hst
    exact hst

/-- The tokens a plan keeps, in order. Factored out of `containUnknown` so
that the salvage is a filter over the input with nothing else in the way,
which is what makes `keptToks_mem` readable off it. -/
private def keptToks (toks : Array MTok) (keep : Array Bool) : Array MTok :=
  (toks.toList.zipIdx.filterMap fun (t, i) =>
    if (keep[i]?.getD true) then some t else none).toArray

/-- **Nothing invented: every token kept is a token of the input.** The
upper bound on containment, and the reason it is stated as a filter — the
same argument `Ir.floorChars_mem` makes for the filtered salvage, at the
scope where what survives is parsed as mathematics rather than set as text.

What it deliberately does not say, exactly as at the other floor: this
permits a plan that dropped everything. The clause that bounds *when* the
plan may drop anything at all is `mathContain_accounts`, and the page-level
witness is `mathContainChecks`. -/
private theorem keptToks_mem (toks : Array MTok) (keep : Array Bool) :
    ∀ t ∈ keptToks toks keep, t ∈ toks := by
  intro t ht
  simp only [keptToks, List.mem_toArray, List.mem_filterMap] at ht
  obtain ⟨p, hp, hq⟩ := ht
  have hfst : p.1 ∈ toks.toList := by
    have hm := List.mem_map_of_mem (f := Prod.fst) hp
    rwa [List.zipIdx_map_fst] at hm
  split at hq
  · cases hq
    simpa using hfst
  · simp at hq

/-- The token stream a formula parses from once every construct outside this
slice has been reduced to its content operand, and the names of the
constructs so reduced. -/
private def containUnknown (toks : Array MTok) :
    Except String (Array MTok × Array String) :=
  match containPlan toks with
  | .error e => .error e
  | .ok (keep, names) => .ok (keptToks toks keep, names)

/-- `keptToks_mem` where the parser reads it: whatever plan `containPlan`
made, the stream `parseToks` consumes is drawn from the author's own
tokens. -/
private theorem containUnknown_mem (toks out : Array MTok) (names : Array String)
    (h : containUnknown toks = .ok (out, names)) : ∀ t ∈ out, t ∈ toks := by
  simp only [containUnknown] at h
  cases hp : containPlan toks with
  | error e => rw [hp] at h; simp at h
  | ok pn =>
    rw [hp] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    exact keptToks_mem toks pn.1

/-- Attach a script to the last atom of `acc`, or to a fresh empty atom when
none is there to take it (`$^2$`, TeX's empty-nucleus behaviour). A second
script on the same side is TeX's "double superscript" error. -/
private def attach (acc : Array MItem) (isSup : Bool) (script : MList) :
    Except String (Array MItem) := do
  let put (x : MItem) : Except String MItem :=
    match x, isSup with
    | .atom cls nuc .nil sub lim, true => .ok (.atom cls nuc script sub lim)
    | .atom cls nuc sup .nil lim, false => .ok (.atom cls nuc sup script lim)
    | .space _, _ => .error "a script on a space"
    | _, true => .error "a double superscript"
    | _, false => .error "a double subscript"
  match acc.back? with
  | some (.space _) | some (.ink _ _) | none =>
    let fresh ← put (.atom .ord (.list .nil) .nil .nil false)
    .ok (acc.push fresh)
  | some x =>
    .ok (acc.pop.push (← put x))

/-- A prime after an atom: `x'` is `x^\prime`, and primes accumulate
(`x''`). A prime after a written superscript is TeX's double-superscript
error, spelled by name. -/
private def attachPrime (acc : Array MItem) : Except String (Array MItem) := do
  let primeAtom : MItem := .atom .ord (.sym '\u2032') .nil .nil false
  let rec allPrimes : MList → Bool
    | .nil => true
    | .cons (.atom _ (.sym '\u2032') .nil .nil _) rest => allPrimes rest
    | .cons _ _ => false
  let rec appendPrime : MList → MList
    | .nil => .cons primeAtom .nil
    | .cons x rest => .cons x (appendPrime rest)
  match acc.back? with
  | some (.atom cls nuc .nil sub lim) =>
    .ok (acc.pop.push (.atom cls nuc (.cons primeAtom .nil) sub lim))
  | some (.atom cls nuc sup sub lim) =>
    if allPrimes sup then
      .ok (acc.pop.push (.atom cls nuc (appendPrime sup) sub lim))
    else
      .error "a prime after a superscript"
  | some (.space _) | some (.ink _ _) | none =>
    .ok (acc.push (.atom .ord (.list .nil) (.cons primeAtom .nil) .nil false))

/-- One atom for a token met as a script argument or in the run of a list. -/
private def tokAtom : MTok → Option MItem
  | .ch c => (charAtom c).map fun (cls, c') => .atom cls (.sym c') .nil .nil false
  | .ctrl n =>
    match ctrlAtom.lookup n with
    | some (cls, c) => some (.atom cls (.sym c) .nil .nil (limitOps.contains n))
    | none => (ctrlWord.lookup n).map fun s =>
        .atom .op (.word s) .nil .nil (limitWords.contains n)
  | _ => none

private def tokName : MTok → String
  | .ch c => s!"'{String.ofList [c]}'"
  | .ctrl n => s!"\\{n}"
  | .ws => "a space"
  | .sup => "'^'"
  | .sub => "'_'"
  | .openGrp => "'{'"
  | .closeGrp => "'}'"
  | .amp => "'&'"
  | .rowEnd => "'\\\\'"
  | .arrOpen => "'\\begin{array}'"
  | .arrClose => "'\\end{array}'"
  | .gridOpen n => s!"'\\begin\{{n}}'"

/-- The delimiter after `\left`/`\right` (the twins read one shape): the
char actually set (`none` for the empty `.`) and the index past it,
skipping one leading space. `cmd` names the caller in the error. -/
private def readDelim (toks : Array MTok) (i : Nat) (cmd : String) :
    Except String (Option Char × Nat) := do
  let j := if toks[i]? == some .ws then i + 1 else i
  match toks[j]? with
  | some (.ch c) =>
    match delimChar c with
    | some d => return (d, j + 1)
    | none => throw s!"'\\{cmd} {String.ofList [c]}'"
  | some (.ctrl n) =>
    match ctrlAtom.lookup n with
    | some (_, c) => return (some c, j + 1)
    | none => throw s!"'\\{cmd} \\{n}'"
  | _ => throw s!"'\\{cmd}' without a delimiter"

/-- What an argument of `\genfrac`'s spec spells, skipping one leading space:
a braced group's tokens, or the one token that stands unbraced (amsmath's
own `\binom` is `\genfrac()\z@{}`), and the index past it. -/
private def readSpecArg (toks : Array MTok) (i : Nat) :
    Except String (Array MTok × Nat) := do
  let j := if toks[i]? == some .ws then i + 1 else i
  match toks[j]? with
  | some .openGrp =>
    let stop := skipTokGroup toks j
    unless stop ≥ j + 2 && toks[stop - 1]? == some .closeGrp do
      throw "an unbalanced group"
    return (toks.extract (j + 1) (stop - 1), stop)
  | some .closeGrp | none => throw "'\\genfrac' without its arguments"
  | some t => return (#[t], j + 1)

/-- `\genfrac{left}{right}{thickness}{style}`, read into the spec its two
operands set under: a delimiter as `\left` reads one (empty or `.` for
none), a thickness in an absolute unit (empty for the face's rule, zero for
a stack), and amsmath's `\@mathstyle` digit (empty for the current style;
0 display, 1 text, 2 script, any other scriptscript, as its `\ifcase`
reads). The index is past the fourth argument. -/
private def readGenfracSpec (toks : Array MTok) (i : Nat) :
    Except String (FracSpec × Nat) := do
  let delim (arg : Array MTok) : Except String (Option Char) :=
    match arg.toList.filter (· != .ws) with
    | [] => .ok none
    | [.ch c] => match delimChar c with
      | some d => .ok d
      | none => .error s!"'\\genfrac' with the delimiter '{String.ofList [c]}'"
    | [.ctrl n] => match ctrlAtom.lookup n with
      | some (_, c) => .ok (some c)
      | none => .error s!"'\\genfrac' with the delimiter '\\{n}'"
    | _ => .error "'\\genfrac' with a delimiter it cannot read"
  let (a1, j1) ← readSpecArg toks i
  let (a2, j2) ← readSpecArg toks j1
  let (a3, j3) ← readSpecArg toks j2
  let (a4, j4) ← readSpecArg toks j3
  let left ← delim a1
  let right ← delim a2
  let spelled (arg : Array MTok) : Option String :=
    arg.foldl (fun s t => match s, t with
      | some s, .ch c => some (s.push c)
      | some s, .ws => some s
      | _, _ => none) (some "")
  let rule ← match spelled a3 with
    | some "" => pure none
    | some s => match Decl.parseLength s with
      | some l =>
        if l.em == 0 && l.ex == 0 then pure (some l.sp)
        else throw s!"'\\genfrac' with the font-relative thickness '{s}'"
      | none => throw s!"'\\genfrac' with the thickness '{s}'"
    | none => throw "'\\genfrac' with a thickness it cannot read"
  let style ← match spelled a4 with
    | some "" => pure none
    | some "0" => pure (some (.display false))
    | some "1" => pure (some (.text false))
    | some "2" => pure (some (.script false))
    | some s =>
      if s.length == 1 && s.all Char.isDigit then pure (some (.scriptscript false))
      else throw s!"'\\genfrac' with the style '{s}'"
    | none => throw "'\\genfrac' with a style it cannot read"
  return ({ left, right, rule, style }, j4)

/-- What a `{`-opened level will become when it closes, or what an argument
just parsed is for. -/
private inductive Dest where
  | grp
  | script (isSup : Bool)
  | fracNum (spec : FracSpec)
  | fracDen (spec : FracSpec) (num : MList)
  | sqrtBody (deg : MList)
  /-- A math alphabet's argument: its letters remap
  (`Math.MathAlphabet.apply`) when the argument closes. `source` records
  whether it came from `\sym…` (forced symbol) or a legacy command. -/
  | alpha (a : Math.MathAlphabet) (source : Math.AlphaSource)
  /-- A math accent's base: the mark sets over it when it closes. -/
  | accentBody (mark : Char) (stretch : Bool)
  | leftRight (l : Option Char)
  /-- amsmath's `\pod`/`\pmod` argument: it closes into `(…)`, after the
  word "mod" and a 6 mu kern when `withMod` (`\pmod` is `\pod{mod\mkern6mu #1}`). -/
  | pod (withMod : Bool)
  /-- `\textcolor`'s content: it closes into `{\color{c} …}`, the braced
  Ord atom whose list opens with the colour switch (xcolor's
  `\textcolor` is `{\color{c}#2}`). -/
  | inked (color : Ir.Color) (name : Option String)
  /-- `\cancelto`'s first argument, the value: it becomes the request for
  the second. -/
  | cancelValue (spec : CancelSpec)
  /-- A cancel mark's struck subformula: it closes into the mark's Ord
  atom (cancel.sty sets the mark as a box). -/
  | cancelBody (mark : CancelMark) (spec : CancelSpec) (value : MList)
  /-- A grid awaiting its rows. `wrap` is `none` for the formula's own
  alignment (`top`), which only the end of the formula closes; a nested
  grid carries the delimiters it closes between, `(none, none)` for an
  `array` or an undelimited `gridEnvs` row. -/
  | grid (kind : GridKind) (wrap : Option (Option Char × Option Char))
      (rows : Array (Array MList)) (cells : Array MList)

private structure PFrame where
  acc : Array MItem
  /-- The items before a `\over` on this level, once one is seen: TeX's
  whole-level fraction (TeXbook ch. 17). -/
  overNum : Option (Array MItem)
  /-- What this level answers when it closes, innermost awaiting
  construction first: `x^\mathbb{…}` opens with
  `[.alpha .bb .doc, .script true]`. -/
  dests : List Dest

/-- Close a level's items into the list it denotes: everything before a
`\over` over everything after it, else just the items. -/
private def closeLevel (overNum : Option (Array MItem)) (acc : Array MItem) : MList :=
  match overNum with
  | some num =>
    .cons (.atom .inner (.frac {} (MList.ofList num.toList) (MList.ofList acc.toList))
      .nil .nil false) .nil
  | none => MList.ofList acc.toList

/-- The upright word amsmath's modulo commands set (`{\operator@font mod}`),
an Ord: `\bmod`'s Bin spacing is realized by its own kerns (below). -/
private def modWord : MItem := .atom .ord (.word "mod") .nil .nil false

/-- The one place every parsed argument lands: an argument answers the
innermost awaiting destination, whose result may in turn answer the next —
`x^\frac{a}{b}` feeds the braced numerator to the fraction and the built
fraction to the script. Each iteration pops one destination (or turns a
numerator into its awaiting denominator and returns), so the loop is
bounded by the chain's length. Returns the new accumulator and what is
still awaited. -/
private def resolveChain (acc0 : Array MItem) (chain : List Dest) (arg0 : MList) :
    Except String (Array MItem × List Dest) := do
  let mut acc := acc0
  let mut arg := arg0
  let mut rest := chain
  for _ in [0:chain.length + 1] do
    match rest with
    | [] =>
      -- Every wrap step below leaves one constructed atom; land it.
      match arg with
      | .cons x .nil => return (acc.push x, [])
      | _ => throw "an unbalanced group"
    | .script isSup :: more =>
      return (← attach acc isSup arg, more)
    | .grp :: more =>
      arg := .cons (.atom .ord (.list arg) .nil .nil false) .nil
      rest := more
    | .fracNum spec :: more =>
      return (acc, .fracDen spec arg :: more)
    | .fracDen spec num :: more =>
      -- Every LaTeX fraction command braces its fraction (latex.ltx's and
      -- amsmath.sty's `\frac` is `{…\over…}`, `\genfrac` `{{…}}`), so it
      -- spaces as the Ord atom a braced subformula is (TeXbook ch. 17).
      arg := .cons (.atom .ord (.frac spec num arg) .nil .nil false) .nil
      rest := more
    | .sqrtBody deg :: more =>
      arg := .cons (.atom .ord (.rad deg arg) .nil .nil false) .nil
      rest := more
    | .alpha a src :: more =>
      arg := .cons (.atom .ord (.alpha a src arg) .nil .nil false) .nil
      rest := more
    | .accentBody mark stretch :: more =>
      arg := .cons (.atom .ord (.accent mark stretch arg) .nil .nil false) .nil
      rest := more
    | .pod withMod :: more =>
      let inner : List MItem :=
        [.atom .opening (.sym '(') .nil .nil false] ++
        (if withMod then [modWord, .space 6] else []) ++
        [.atom .ord (.list arg) .nil .nil false, .atom .closing (.sym ')') .nil .nil false]
      arg := .cons (.atom .ord (.list (MList.ofList inner)) .nil .nil false) .nil
      rest := more
    | .inked c n :: more =>
      arg := .cons (.atom .ord (.list (.cons (.ink c n) arg)) .nil .nil false) .nil
      rest := more
    | .cancelValue spec :: more =>
      return (acc, .cancelBody .to spec arg :: more)
    | .cancelBody mark spec value :: more =>
      arg := .cons (.atom .ord (.cancel mark spec value arg) .nil .nil false) .nil
      rest := more
    | .leftRight _ :: _ => throw "'\\left' without its '\\right'"
    | .grid _ _ _ _ :: _ => throw "an unbalanced group"
  throw "an unbalanced group"

/-- A command's naming argument: the `{...}` whose content is a name rather
than content, read as a string and stepped over. `\textcolor{alert}{x}`'s
first group is the one case today. Returns the name and the index past the
group's closer. -/
private def skipNamedArg (toks : Array MTok) (i : Nat) (cmd : String) :
    Except String (String × Nat) := do
  let mut j := if toks[i]? == some .ws then i + 1 else i
  let some .openGrp := toks[j]? | throw s!"'\\{cmd}' without its group"
  j := j + 1
  let mut name := ""
  for _ in [j:toks.size + 1] do
    match toks[j]? with
    | some (.ch c) =>
      name := name.push c
      j := j + 1
    | some .ws =>
      name := name.push ' '
      j := j + 1
    | some .closeGrp => break
    | some t => throw s!"{tokName t} inside '\\{cmd}'"
    | none => throw "an unbalanced group"
  let some .closeGrp := toks[j]? | throw "an unbalanced group"
  return (name, j + 1)

/-- One atom joins the list: on its own when nothing is pending, otherwise
through the pending chain's resolution. Every site that emits an atom goes
through here, so a new one cannot land an atom past a pending script,
accent or alphabet. -/
private def joinAtom (acc : Array MItem) (pending : List Dest) (atom : MItem) :
    Except String (Array MItem × List Dest) :=
  if pending.isEmpty then return (acc.push atom, pending)
  else resolveChain acc pending (.cons atom .nil)

/-- amsmath's even alignment columns open with an empty Ord (`{}#` in
`\align@preamble`, amsmath.dtx), so a cell beginning with a relation keeps
its thick space and a leading `+` stays binary. -/
private def emptyOrd : MItem := .atom .ord (.list .nil) .nil .nil false

/-- Close the running cell into its grid frame. -/
private def closeCell (kind : GridKind) (cells : Array MList)
    (overNum : Option (Array MItem)) (acc : Array MItem) : Array MList :=
  let body := closeLevel overNum acc
  let body := match kind with
    | .align =>
      if cells.size % 2 == 1 then .cons emptyOrd body else body
    | _ => body
  cells.push body

/-- Rows into a rectangular grid nucleus: a ragged row is named in a note
and padded with empty cells (`MRows.pad`, whose rectangularity and
conservation are theorems); a row overrunning an `array`'s column spec is
named too, its extra columns centring. -/
private def buildGrid (kind : GridKind) (rows : Array (Array MList)) :
    MNucleus × Array Note := Id.run do
  let mut notes : Array Note := #[]
  let widths := rows.map (·.size)
  let maxCols := widths.foldl Nat.max 0
  for k in [0:rows.size] do
    if widths[k]! != maxCols then
      notes := notes.push (.ragged
        s!"row {k + 1} has {widths[k]!} cell(s) where {maxCols} align; \
padded with empty cells")
  if let GridKind.array cols _ := kind then
    if maxCols > cols.size then
      notes := notes.push (.ragged
        s!"a row has {maxCols} cells where the column spec declares \
{cols.size}; extra columns centre")
  let rs := MRows.ofList (rows.toList.map fun r => MRow.ofList r.toList)
  return (.grid kind (rs.pad rs.maxCols), notes)

/-- Parse flattened tokens into a math list, or name the construct that
puts the formula outside this slice. One forward pass with an explicit
frame stack; every iteration consumes at least one token, so the loop
bound is never the reason it stops. `top` opens an alignment grid at the
bottom of the stack (`align`/`gather` bodies); notes name ragged rows.
`pending` is the chain of constructions awaiting their next argument,
innermost first — `x^\frac{a}{b}` stacks the fraction's request on the
script's — and `resolveChain` is where every argument lands. `display` is
amsmath's `\if@display`, which picks the modulo commands' leading kerns. -/
private def parseToks (toks : Array MTok) (top : Option GridKind) (display : Bool)
    (env : Env) :
    Except String (MList × Array Note) := do
  let mut stack : Array PFrame := #[]
  let mut acc : Array MItem := #[]
  let mut overNum : Option (Array MItem) := none
  let mut pending : List Dest := []
  let mut notes : Array Note := #[]
  if let some kind := top then
    stack := stack.push { acc := #[], overNum := none, dests := [.grid kind none #[] #[]] }
  let mut i := 0
  for _ in [0:toks.size] do
    let some tok := toks[i]? | break
    match tok with
    | .ws =>
      i := i + 1
    | .sup =>
      unless pending.isEmpty do throw (tokName tok)
      pending := [.script true]
      i := i + 1
    | .sub =>
      unless pending.isEmpty do throw (tokName tok)
      pending := [.script false]
      i := i + 1
    | .openGrp =>
      let dests := if pending.isEmpty then [.grp] else pending
      stack := stack.push { acc, overNum, dests }
      pending := []
      acc := #[]
      overNum := none
      i := i + 1
    | .closeGrp =>
      unless pending.isEmpty do throw (tokName tok)
      let some frame := stack.back? | throw "an unbalanced group"
      match frame.dests with
      | .grid _ _ _ _ :: _ => throw "an unbalanced group"
      | .leftRight _ :: _ => throw "'\\left' without its '\\right'"
      | [] => throw "an unbalanced group"
      | dests =>
        stack := stack.pop
        let body := closeLevel overNum acc
        overNum := frame.overNum
        let (acc', pending') ← resolveChain frame.acc dests body
        acc := acc'
        pending := pending'
        i := i + 1
    | .amp =>
      unless pending.isEmpty do throw (tokName tok)
      let some frame := stack.back? | throw "'&'"
      let [.grid kind wrap rows cells] := frame.dests | throw "'&'"
      if kind matches .gather then throw "'&'"
      let cells := closeCell kind cells overNum acc
      acc := #[]
      overNum := none
      stack := stack.pop.push { frame with dests := [.grid kind wrap rows cells] }
      i := i + 1
    | .rowEnd =>
      unless pending.isEmpty do throw (tokName tok)
      let some frame := stack.back? | throw "'\\\\'"
      let [.grid kind wrap rows cells] := frame.dests | throw "'\\\\'"
      if let some (.ch '[') := toks[i+1]? then
        throw "'\\\\[...]' extra row space"
      let cells := closeCell kind cells overNum acc
      acc := #[]
      overNum := none
      stack := stack.pop.push { frame with dests := [.grid kind wrap (rows.push cells) #[]] }
      i := i + 1
    | .arrOpen =>
      -- `[pos]{spec}`: the position is burned (the grid centres on the
      -- axis either way in this slice); the spec gives the column
      -- alignments. Anything else a spec can say (`|` rules, `@{}`,
      -- `p{}`) is outside this slice, named.
      unless pending.isEmpty do throw (tokName tok)
      let mut j := i + 1
      if let some .ws := toks[j]? then j := j + 1
      if let some (.ch '[') := toks[j]? then
        j := j + 1
        for _ in [j:toks.size] do
          match toks[j]? with
          | some (.ch ']') => break
          | some _ => j := j + 1
          | none => break
        let some (.ch ']') := toks[j]? | throw "an unclosed array position option"
        j := j + 1
      if let some .ws := toks[j]? then j := j + 1
      let some .openGrp := toks[j]? | throw "an array without its column spec"
      j := j + 1
      let mut cols : Array ColAlign := #[]
      for _ in [j:toks.size] do
        match toks[j]? with
        | some .closeGrp => break
        | some (.ch 'l') => cols := cols.push .left; j := j + 1
        | some (.ch 'c') => cols := cols.push .center; j := j + 1
        | some (.ch 'r') => cols := cols.push .right; j := j + 1
        | some .ws => j := j + 1
        | some t => throw s!"the array column spec {tokName t}"
        | none => break
      let some .closeGrp := toks[j]? | throw "an array without its column spec"
      stack := stack.push
        { acc, overNum, dests := [.grid (.array cols 1000) (some (none, none)) #[] #[]] }
      acc := #[]
      overNum := none
      i := j + 1
    | .gridOpen n =>
      unless pending.isEmpty do throw (tokName tok)
      let some (kind, l, r) := gridEnvs.lookup n | throw (tokName tok)
      -- `aligned` and `gathered` read amsmath's `[t]`/`[b]`/`[c]` position
      -- (`\aligned@a[1][c]`; `t` is a `\vtop`, `b` a `\vbox`); this grid
      -- centres on the axis, which is `[c]`, so the other two are named.
      -- Every other row's `[` is its first cell's content.
      let mut j := i + 1
      if n == "aligned" || n == "gathered" then
        let k := if toks[j]? == some .ws then j + 1 else j
        if toks[k]? == some (.ch '[') then
          unless toks[k+1]? == some (.ch 'c') && toks[k+2]? == some (.ch ']') do
            throw s!"'\\begin\{{n}}[...]' top or bottom alignment"
          j := k + 3
      stack := stack.push { acc, overNum, dests := [.grid kind (some (l, r)) #[] #[]] }
      acc := #[]
      overNum := none
      i := j
    | .arrClose =>
      unless pending.isEmpty do throw (tokName tok)
      let some frame := stack.back? | throw "'\\end{array}'"
      let [.grid kind (some (l, r)) rows cells] := frame.dests | throw "'\\end{array}'"
      stack := stack.pop
      let rows :=
        if cells.isEmpty && acc.isEmpty && overNum.isNone then rows
        else rows.push (closeCell kind cells overNum acc)
      if rows.isEmpty then throw "an empty array"
      let (grid, gnotes) := buildGrid kind rows
      notes := notes ++ gnotes
      let atom : MItem := .atom .ord grid .nil .nil false
      acc := frame.acc.push <| if l.isNone && r.isNone then atom
        else .atom .inner (.delim l r (.cons atom .nil)) .nil .nil false
      overNum := frame.overNum
      i := i + 1
    | .ctrl "over" =>
      unless pending.isEmpty do throw (tokName tok)
      if overNum.isSome then throw "a double \\over"
      overNum := some acc
      acc := #[]
      i := i + 1
    | .ctrl "genfrac" =>
      let (spec, j) ← readGenfracSpec toks (i + 1)
      pending := .fracNum spec :: pending
      i := j
    | .ctrl "sqrt" =>
      let mut j := i + 1
      let mut deg : Array MItem := #[]
      if let some (.ch '[') := toks[j]? then
        j := j + 1
        for _ in [j:toks.size] do
          match toks[j]? with
          | some (.ch ']') => break
          | some (.ws) => j := j + 1
          | some t =>
            let some a := tokAtom t | throw (tokName t)
            deg := deg.push a
            j := j + 1
          | none => throw "an unclosed root index"
        let some (.ch ']') := toks[j]? | throw "an unclosed root index"
        j := j + 1
      pending := .sqrtBody (MList.ofList deg.toList) :: pending
      i := j
    | .ctrl "ensuremath" =>
      -- Transparent inside math (amsldoc: `\ensuremath`'s argument sets in
      -- math mode, which this already is): the group after it is an
      -- ordinary braced group.
      i := i + 1
    -- amsmath's modulo commands (amsmath.sty). `\bmod` is a Bin "mod" whose
    -- medium spaces are cancelled and replaced by 5 mu a side in every
    -- style; `\mod` kerns 18 mu in a display, else 12, then sets "mod" and
    -- `\,\,` before its argument; `\pod` kerns 18 mu, else 8, and
    -- parenthesises its argument; `\pmod` is `\pod{mod\mkern6mu #1}`.
    | .ctrl "bmod" =>
      unless pending.isEmpty do throw (tokName tok)
      acc := acc ++ #[.space 5, modWord, .space 5]
      i := i + 1
    | .ctrl "mod" =>
      unless pending.isEmpty do throw (tokName tok)
      acc := acc ++ #[.space (if display then 18 else 12), modWord, .space 3, .space 3]
      i := i + 1
    | .ctrl "pod" | .ctrl "pmod" =>
      unless pending.isEmpty do throw (tokName tok)
      acc := acc.push (.space (if display then 18 else 8))
      pending := [.pod (tok == .ctrl "pmod")]
      i := i + 1
    | .ctrl "dotsi" =>
      -- amsmath.sty: `\newcommand{\dotsi}{\!\@cdots}`, the dots between
      -- integrals pulled a thin space back.
      unless pending.isEmpty do throw (tokName tok)
      acc := acc ++ #[.space (-3), .atom .inner (.sym '\u22EF') .nil .nil false]
      i := i + 1
    | .ctrl "left" =>
      unless pending.isEmpty do throw (tokName tok)
      let (l, j) ← readDelim toks (i + 1) "left"
      stack := stack.push { acc, overNum, dests := [.leftRight l] }
      acc := #[]
      overNum := none
      i := j
    | .ctrl "right" =>
      unless pending.isEmpty do throw (tokName tok)
      let (r, j) ← readDelim toks (i + 1) "right"
      let some frame := stack.back? | throw "'\\right' without its '\\left'"
      let [.leftRight l] := frame.dests | throw "'\\right' without its '\\left'"
      stack := stack.pop
      let body := closeLevel overNum acc
      overNum := frame.overNum
      acc := frame.acc.push (.atom .inner (.delim l r body) .nil .nil false)
      i := j
    | .ctrl "limits" =>
      unless pending.isEmpty do throw (tokName tok)
      match acc.back? with
      | some (.atom cls nuc sup sub _) =>
        acc := acc.pop.push (.atom cls nuc sup sub true)
      | _ => throw "\\limits without an operator"
      i := i + 1
    | .ctrl "nolimits" =>
      unless pending.isEmpty do throw (tokName tok)
      match acc.back? with
      | some (.atom cls nuc sup sub _) =>
        acc := acc.pop.push (.atom cls nuc sup sub false)
      | _ => throw "\\nolimits without an operator"
      i := i + 1
    | .ctrl "text" | .ctrl "mbox" | .ctrl "textrm" | .ctrl "operatorname" =>
      -- \text sets its letters upright as an Ord atom; \operatorname is
      -- the same word as an Op atom, binding with a thin space like the
      -- built-in function names (TeXbook p. 162's class).
      --
      -- The body is one upright word, so a group inside it is grouping and
      -- nothing more, a known symbol contributes its scalar, and a style or
      -- colour command contributes its letters with the change named as
      -- lost — the mathematics is what a reader needs, and a formula that
      -- degraded whole over an inner `\textbf` gave them neither.
      let mut j := i + 1
      if let some .ws := toks[j]? then j := j + 1
      let some .openGrp := toks[j]? | throw s!"{tokName tok} without its group"
      j := j + 1
      let mut s := ""
      let mut depth := 0
      for _ in [j:toks.size + 1] do
        match toks[j]? with
        | some (.ch c) =>
          s := s.push c
          j := j + 1
        | some .ws =>
          s := s.push ' '
          j := j + 1
        | some .openGrp =>
          depth := depth + 1
          j := j + 1
        | some .closeGrp =>
          if depth == 0 then break
          depth := depth - 1
          j := j + 1
        | some (.ctrl n) =>
          -- A space after a control word is the word's, as in LaTeX: the
          -- token stream keeps it, so each arm below steps over it.
          let afterCmd (k : Nat) : Nat := if toks[k]? == some .ws then k + 1 else k
          if n == "textcolor" then
            let (name, j') ← skipNamedArg toks (j + 1) n
            notes := notes.push (.styleDropped s!"the colour '{name}'")
            j := j'
          else if textStyleCtrl.contains n then
            notes := notes.push (.styleDropped s!"'\\{n}'")
            j := afterCmd (j + 1)
          else if textNeutralCtrl.contains n then
            j := afterCmd (j + 1)
          else
            match ctrlAtom.lookup n with
            | some (_, c) =>
              s := s.push c
              j := afterCmd (j + 1)
            | none =>
              match ctrlWord.lookup n with
              | some w =>
                s := s ++ w
                j := afterCmd (j + 1)
              | none => throw s!"\\{n} inside {tokName tok}"
        | some t => throw s!"{tokName t} inside {tokName tok}"
        | none => throw "an unbalanced group"
      let some .closeGrp := toks[j]? | throw "an unbalanced group"
      let cls : MathClass := if tok == .ctrl "operatorname" then .op else .ord
      let atom : MItem := .atom cls (.word s) .nil .nil false
      let (acc', pending') ← joinAtom acc pending atom
      acc := acc'
      pending := pending'
      i := j + 1
    | .ctrl n =>
      if n == "textcolor" then
        -- `\textcolor{c}{body}`: the colour is a name, not content, so its
        -- group is consumed here; the body is the next argument, which
        -- closes into `{\color{c} body}`. An expression the palette cannot
        -- resolve leaves the body in the colour in force, named (W0304),
        -- as the text path leaves it.
        let (name, j) ← skipNamedArg toks (i + 1) n
        match env.ink name with
        | some (c, entry) =>
          notes := notes.push (.inkUsed name c entry)
          pending := .inked c (if entry then some name else none) :: pending
        | none => notes := notes.push (.inkMissed name)
        i := j
      else if n == "color" then
        -- `\color{c}`: a declaration, TeX's colour whatsit — the rest of
        -- this list inks in `c`, and no atom or class enters the list.
        -- xcolor's model form (`\color[rgb]{…}`) names its colour by
        -- components the palette cannot resolve by name: its group is
        -- consumed and the change named (W0385), the content kept.
        unless pending.isEmpty do throw (tokName tok)
        let k := if toks[i + 1]? == some .ws then i + 2 else i + 1
        if toks[k]? == some (.ch '[') then
          let o := skipTokOption toks k
          let model := String.ofList ((toks.extract (k + 1) (o - 1)).toList.filterMap
            fun t => match t with
              | .ch c => some c
              | _ => none)
          notes := notes.push (.styleDropped s!"the colour in model '{model}'")
          i := skipTokGroup toks (skipTokWs toks o)
        else
          let (name, j) ← skipNamedArg toks (i + 1) n
          match env.ink name with
          | some (c, entry) =>
            notes := notes.push (.inkUsed name c entry)
            acc := acc.push (.ink c (if entry then some name else none))
          | none => notes := notes.push (.inkMissed name)
          i := j
      else if n == "cancelto" then
        if let some k := env.cancelMiss then notes := notes.push (.inkMissed k)
        pending := .cancelValue env.cancel :: pending
        i := i + 1
      else
      match cancelCtrl.lookup n with
      | some mark =>
        if let some k := env.cancelMiss then notes := notes.push (.inkMissed k)
        pending := .cancelBody mark env.cancel .nil :: pending
        i := i + 1
      | none =>
      match fracCmds.lookup n with
      | some spec =>
        pending := .fracNum spec :: pending
        i := i + 1
      | none =>
      match alphaCtrl.lookup n with
      | some (a, src) =>
        pending := .alpha a src :: pending
        i := i + 1
      | none =>
      match accentCtrl.lookup n with
      | some (mark, stretch) =>
        pending := .accentBody mark stretch :: pending
        i := i + 1
      | none =>
      match ctrlSpace.lookup n with
      | some mu =>
        unless pending.isEmpty do throw (tokName tok)
        acc := acc.push (.space mu)
        i := i + 1
      | none =>
        match tokAtom tok with
        | some atom =>
          let (acc', pending') ← joinAtom acc pending atom
          acc := acc'
          pending := pending'
          i := i + 1
        | none => throw (tokName tok)
    | .ch '\'' =>
      unless pending.isEmpty do throw (tokName tok)
      acc := ← attachPrime acc
      i := i + 1
    | .ch _ =>
      match tokAtom tok with
      | some atom =>
        let (acc', pending') ← joinAtom acc pending atom
        acc := acc'
        pending := pending'
        i := i + 1
      | none => throw (tokName tok)
  unless pending.isEmpty do throw "a trailing script mark"
  let unbalanced (f : Option PFrame) : String :=
    match f with
    | some { dests := .leftRight _ :: _, .. } => "'\\left' without its '\\right'"
    | _ => "an unbalanced group"
  match top with
  | none =>
    unless stack.isEmpty do
      throw (unbalanced stack.back?)
    return (closeLevel overNum acc, notes)
  | some kind =>
    unless stack.size == 1 do
      throw (unbalanced stack.back?)
    let some frame := stack.back? | throw "an unbalanced group"
    let [.grid _ _ rows cells] := frame.dests | throw "an unbalanced group"
    let rows :=
      if cells.isEmpty && acc.isEmpty && overNum.isNone then rows
      else rows.push (closeCell kind cells overNum acc)
    if rows.isEmpty then throw "an empty alignment"
    let (grid, gnotes) := buildGrid kind rows
    return (.cons (.atom .ord grid .nil .nil false) .nil, notes ++ gnotes)

/-- Parse a formula's raw body into a math list, or name the construct that
puts it outside this slice. Notes name ragged alignment rows (an `array`
inside the formula) and each construct contained rather than modelled.

Containment runs first, so an unmodelled construct costs itself and not the
mathematics around it: its name and naming arguments go, its content operand
stays, and the formula parses. Where containment leaves the formula inking
nothing at all the whole-formula floor is the better recovery — it has a
declared placeholder (`Ir.floorInk_accounts`) where this path would ship a
blank — so the construct is named through the same channel it always was. -/
def parseMath (display : Bool) (raws : Array Parse.Raw) (env : Env := {}) :
    Except String (MList × Array Note) := do
  let (toks, names) ← containUnknown (← flattenList #[] raws.toList)
  let (l, notes) ← parseToks toks none display env
  if let some n := names[0]? then
    if (MList.scalarsList #[] l).isEmpty then throw n
  return (l, names.map Note.constructFloored ++ notes)

/-- Parse an alignment environment's body (`align`/`gather` rows split at
`&` and `\\`) into one grid formula. Containment applies as it does to a
formula (`parseMath`): one unmodelled addend of one row costs that addend. -/
def parseMathRows (kind : GridKind) (raws : Array Parse.Raw) (env : Env := {}) :
    Except String (MList × Array Note) := do
  let (toks, names) ← containUnknown (← flattenList #[] raws.toList)
  let (l, notes) ← parseToks toks (some kind) true env
  if let some n := names[0]? then
    if (MList.scalarsList #[] l).isEmpty then throw n
  return (l, names.map Note.constructFloored ++ notes)

end LeanTex.Core.MathParse
