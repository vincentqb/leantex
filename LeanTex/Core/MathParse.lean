import LeanTex.Core.Parse
import LeanTex.Core.Math

/-! The math surface: `$...$` bodies and alignment environments elaborated
into `Math.MList` atoms. Pure and total; the caller (the elaborator) owns
diagnostics. A construct outside this slice — accents, `\binom`,
`\text` with markup inside — returns `.error name`, and the formula stays
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

/-- Characters that classify directly (TeX's mathcodes, plain format): the
class and the scalar actually set — `-` is MINUS SIGN, `*` is ASTERISK
OPERATOR. Letters and digits are handled before this table. -/
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
    else none

/-- Control words that are one symbol atom: `(class, scalar)`. Greek
lowercase is italic (the Mathematical Italic block, with TeX's `\epsilon` ↦
lunate and `\phi` ↦ straight forms); Greek capitals upright, TeX's
convention. -/
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
   -- binary operations
   ("times", .bin, '×'), ("cdot", .bin, '\u22C5'), ("pm", .bin, '±'),
   ("mp", .bin, '\u2213'), ("div", .bin, '÷'), ("ast", .bin, '\u2217'),
   ("star", .bin, '\u22C6'), ("circ", .bin, '\u2218'),
   ("bullet", .bin, '\u2219'), ("cup", .bin, '\u222A'),
   ("cap", .bin, '\u2229'), ("setminus", .bin, '\u2216'),
   ("wedge", .bin, '\u2227'), ("land", .bin, '\u2227'),
   ("vee", .bin, '\u2228'), ("lor", .bin, '\u2228'),
   ("oplus", .bin, '\u2295'), ("ominus", .bin, '\u2296'),
   ("otimes", .bin, '\u2297'), ("odot", .bin, '\u2299'),
   -- relations
   ("le", .rel, '≤'), ("leq", .rel, '≤'), ("ge", .rel, '≥'),
   ("geq", .rel, '≥'), ("ne", .rel, '≠'), ("neq", .rel, '≠'),
   ("equiv", .rel, '\u2261'), ("sim", .rel, '\u223C'),
   ("simeq", .rel, '\u2243'), ("approx", .rel, '\u2248'),
   ("cong", .rel, '\u2245'), ("propto", .rel, '\u221D'),
   ("subset", .rel, '\u2282'), ("supset", .rel, '\u2283'),
   ("subseteq", .rel, '\u2286'), ("supseteq", .rel, '\u2287'),
   ("in", .rel, '\u2208'), ("notin", .rel, '\u2209'), ("ni", .rel, '\u220B'),
   ("ll", .rel, '\u226A'), ("gg", .rel, '\u226B'),
   ("prec", .rel, '\u227A'), ("succ", .rel, '\u227B'),
   ("mid", .rel, '\u2223'), ("parallel", .rel, '\u2225'),
   ("perp", .rel, '\u27C2'),
   ("to", .rel, '→'), ("rightarrow", .rel, '→'),
   ("leftarrow", .rel, '←'), ("gets", .rel, '←'),
   ("mapsto", .rel, '\u21A6'), ("leftrightarrow", .rel, '\u2194'),
   ("Rightarrow", .rel, '\u21D2'), ("Leftarrow", .rel, '\u21D0'),
   ("Leftrightarrow", .rel, '\u21D4'), ("iff", .rel, '\u27FA'),
   -- ordinary symbols
   ("infty", .ord, '∞'), ("partial", .ord, '𝜕'),
   ("nabla", .ord, '\u2207'), ("forall", .ord, '\u2200'),
   ("exists", .ord, '\u2203'), ("nexists", .ord, '\u2204'),
   ("neg", .ord, '¬'), ("lnot", .ord, '¬'),
   ("emptyset", .ord, '\u2205'), ("varnothing", .ord, '\u2205'),
   ("hbar", .ord, '\u210F'), ("ell", .ord, '\u2113'),
   ("Re", .ord, '\u211C'), ("Im", .ord, '\u2111'),
   ("aleph", .ord, '\u2135'), ("wp", .ord, '\u2118'),
   ("angle", .ord, '\u2220'), ("top", .ord, '\u22A4'),
   ("bot", .ord, '\u22A5'), ("prime", .ord, '\u2032'),
   ("backslash", .ord, '\\'),
   -- inner: the dotses, TeX's \mathinner forms
   ("ldots", .inner, '…'), ("dots", .inner, '…'),
   ("cdots", .inner, '\u22EF'), ("vdots", .inner, '\u22EE'),
   ("ddots", .inner, '\u22F1'),
   -- big operators: Op atoms; display-size variants and above/below limits
   -- are the layout's, per atom `limits` (see `limitOps`)
   ("sum", .op, '\u2211'), ("prod", .op, '\u220F'),
   ("coprod", .op, '\u2210'), ("int", .op, '\u222B'),
   ("oint", .op, '\u222E'), ("iint", .op, '\u222C'),
   ("bigcup", .op, '\u22C3'), ("bigcap", .op, '\u22C2'),
   ("bigvee", .op, '\u22C1'), ("bigwedge", .op, '\u22C0'),
   ("bigoplus", .op, '\u2A01'), ("bigotimes", .op, '\u2A02'),
   -- delimiters as ordinary (non-growing) atoms; `\left` grows them
   ("langle", .opening, '\u27E8'), ("rangle", .closing, '\u27E9'),
   ("lfloor", .opening, '\u230A'), ("rfloor", .closing, '\u230B'),
   ("lceil", .opening, '\u2308'), ("rceil", .closing, '\u2309'),
   ("vert", .ord, '|'), ("Vert", .ord, '\u2016'), ("|", .ord, '\u2016'),
   ("colon", .punct, ':'),
   -- escapes: the reserved characters as content
   ("{", .opening, '{'), ("}", .closing, '}'), ("$", .ord, '$'),
   ("%", .ord, '%'), ("&", .ord, '&'), ("#", .ord, '#'), ("_", .ord, '_')]

/-- The big operators whose scripts become above/below limits in display
style — TeX's `\displaylimits` default for every `\mathop` except the
integrals, which plain TeX declares `\nolimits` (TeXbook p. 144). -/
def limitOps : List String :=
  ["sum", "prod", "coprod", "bigcup", "bigcap", "bigvee", "bigwedge",
   "bigoplus", "bigotimes"]

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
  | ctrl (name : String)
  deriving Repr, BEq, Inhabited

private def flattenErr : Parse.Raw → Option String
  | .math _ _ _ => some "nested math"
  | .env n _ _ => some s!"\\begin\{{n}}"
  | .verb _ _ => some "verbatim"
  | .par _ => some "a blank line"
  | .sym c _ =>
    if c == '^' || c == '_' || c == '[' || c == ']' || c == '&' then none
    else some s!"'{String.ofList [c]}'"
  | _ => none

mutual

private def flattenList (out : Array MTok) : List Parse.Raw →
    Except String (Array MTok)
  | [] => .ok out
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
  | r => match flattenErr r with
    | some what => .error what
    | none => .error "this construct"

end

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
  | some (.space _) | none =>
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
  | some (.space _) | none =>
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

/-- What a `{`-opened level will become when it closes, or what an argument
just parsed is for. -/
private inductive Dest where
  | grp
  | script (isSup : Bool)
  | fracNum
  | fracDen (num : MList)
  | sqrtBody (deg : MList)
  | leftRight (l : Option Char)
  | grid (kind : GridKind) (rows : Array (Array MList)) (cells : Array MList)

private structure PFrame where
  acc : Array MItem
  /-- The items before a `\over` on this level, once one is seen: TeX's
  whole-level fraction (TeXbook ch. 17). -/
  overNum : Option (Array MItem)
  dest : Dest

/-- Close a level's items into the list it denotes: everything before a
`\over` over everything after it, else just the items. -/
private def closeLevel (overNum : Option (Array MItem)) (acc : Array MItem) : MList :=
  match overNum with
  | some num =>
    .cons (.atom .inner (.frac (MList.ofList num.toList) (MList.ofList acc.toList))
      .nil .nil false) .nil
  | none => MList.ofList acc.toList

/-- The one place every parsed argument lands: an argument answers the
`Await` that asked for it — a script attaches, a numerator asks for its
denominator, a completed construction becomes an atom. Returns the new
accumulator and the next pending state. -/
private def resolveArg (acc : Array MItem) (await : Dest) (arg : MList) :
    Except String (Array MItem × Option Dest) := do
  match await with
  | .script isSup => return (← attach acc isSup arg, none)
  | .fracNum => return (acc, some (.fracDen arg))
  | .fracDen num =>
    return (acc.push (.atom .inner (.frac num arg) .nil .nil false), none)
  | .sqrtBody deg =>
    return (acc.push (.atom .ord (.rad deg arg) .nil .nil false), none)
  | .grp => return (acc.push (.atom .ord (.list arg) .nil .nil false), none)
  | .leftRight _ => throw "'\\left' without its '\\right'"
  | .grid _ _ _ => throw "an unbalanced group"

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
    MNucleus × Array String := Id.run do
  let mut notes : Array String := #[]
  let widths := rows.map (·.size)
  let maxCols := widths.foldl Nat.max 0
  for k in [0:rows.size] do
    if widths[k]! != maxCols then
      notes := notes.push
        s!"row {k + 1} has {widths[k]!} cell(s) where {maxCols} align; \
padded with empty cells"
  if let GridKind.array cols := kind then
    if maxCols > cols.size then
      notes := notes.push
        s!"a row has {maxCols} cells where the column spec declares \
{cols.size}; extra columns centre"
  let rs := MRows.ofList (rows.toList.map fun r => MRow.ofList r.toList)
  return (.grid kind (rs.pad rs.maxCols), notes)

/-- Parse flattened tokens into a math list, or name the construct that
puts the formula outside this slice. One forward pass with an explicit
frame stack; every iteration consumes at least one token, so the loop
bound is never the reason it stops. `top` opens an alignment grid at the
bottom of the stack (`align`/`gather` bodies); notes name ragged rows. -/
private def parseToks (toks : Array MTok) (top : Option GridKind) :
    Except String (MList × Array String) := do
  let mut stack : Array PFrame := #[]
  let mut acc : Array MItem := #[]
  let mut overNum : Option (Array MItem) := none
  let mut pending : Option Dest := none
  let mut notes : Array String := #[]
  if let some kind := top then
    stack := stack.push { acc := #[], overNum := none, dest := .grid kind #[] #[] }
  let mut i := 0
  for _ in [0:toks.size] do
    let some tok := toks[i]? | break
    -- One argument, when a construct is waiting for it: a braced group
    -- opens a frame; a single atom token answers at once.
    match pending, tok with
    | some _, .ws =>
      i := i + 1
    | some await, .openGrp =>
      pending := none
      stack := stack.push { acc, overNum, dest := await }
      acc := #[]
      overNum := none
      i := i + 1
    | some await, t =>
      match tokAtom t with
      | some a =>
        pending := none
        let (acc', pending') ← resolveArg acc await (.cons a .nil)
        acc := acc'
        pending := pending'
        i := i + 1
      | none => throw (tokName t)
    | none, _ =>
    match tok with
    | .ws =>
      i := i + 1
    | .sup =>
      pending := some (.script true)
      i := i + 1
    | .sub =>
      pending := some (.script false)
      i := i + 1
    | .openGrp =>
      stack := stack.push { acc, overNum, dest := .grp }
      acc := #[]
      overNum := none
      i := i + 1
    | .closeGrp =>
      let some frame := stack.back? | throw "an unbalanced group"
      match frame.dest with
      | .grid _ _ _ => throw "an unbalanced group"
      | .leftRight _ => throw "'\\left' without its '\\right'"
      | dest =>
        stack := stack.pop
        let body := closeLevel overNum acc
        overNum := frame.overNum
        let (acc', pending') ← resolveArg frame.acc dest body
        acc := acc'
        pending := pending'
        i := i + 1
    | .amp =>
      let some frame := stack.back? | throw "'&'"
      let .grid kind rows cells := frame.dest | throw "'&'"
      if kind matches .gather then throw "'&'"
      let cells := closeCell kind cells overNum acc
      acc := #[]
      overNum := none
      stack := stack.pop.push { frame with dest := .grid kind rows cells }
      i := i + 1
    | .rowEnd =>
      let some frame := stack.back? | throw "'\\\\'"
      let .grid kind rows cells := frame.dest | throw "'\\\\'"
      if let some (.ch '[') := toks[i+1]? then
        throw "'\\\\[...]' extra row space"
      let cells := closeCell kind cells overNum acc
      acc := #[]
      overNum := none
      stack := stack.pop.push { frame with dest := .grid kind (rows.push cells) #[] }
      i := i + 1
    | .arrOpen =>
      -- `[pos]{spec}`: the position is burned (the grid centres on the
      -- axis either way in this slice); the spec gives the column
      -- alignments. Anything else a spec can say (`|` rules, `@{}`,
      -- `p{}`) is outside this slice, named.
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
      stack := stack.push { acc, overNum, dest := .grid (.array cols) #[] #[] }
      acc := #[]
      overNum := none
      i := j + 1
    | .arrClose =>
      let some frame := stack.back? | throw "'\\end{array}'"
      let .grid kind rows cells := frame.dest | throw "'\\end{array}'"
      let .array _ := kind | throw "'\\end{array}'"
      stack := stack.pop
      let rows :=
        if cells.isEmpty && acc.isEmpty && overNum.isNone then rows
        else rows.push (closeCell kind cells overNum acc)
      if rows.isEmpty then throw "an empty array"
      let (grid, gnotes) := buildGrid kind rows
      notes := notes ++ gnotes
      acc := frame.acc.push (.atom .ord grid .nil .nil false)
      overNum := frame.overNum
      i := i + 1
    | .ctrl "over" =>
      if overNum.isSome then throw "a double \\over"
      overNum := some acc
      acc := #[]
      i := i + 1
    | .ctrl "frac" | .ctrl "dfrac" | .ctrl "tfrac" =>
      -- \dfrac/\tfrac force display/text style in LaTeX; this slice sets
      -- them as \frac, the style the formula is already in.
      pending := some .fracNum
      i := i + 1
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
      pending := some (.sqrtBody (MList.ofList deg.toList))
      i := j
    | .ctrl "left" =>
      let mut j := i + 1
      if let some .ws := toks[j]? then j := j + 1
      let l ← match toks[j]? with
        | some (.ch c) =>
          match delimChar c with
          | some l => pure l
          | none => throw s!"'\\left {String.ofList [c]}'"
        | some (.ctrl n) =>
          match ctrlAtom.lookup n with
          | some (_, c) => pure (some c)
          | none => throw s!"'\\left \\{n}'"
        | _ => throw "'\\left' without a delimiter"
      stack := stack.push { acc, overNum, dest := .leftRight l }
      acc := #[]
      overNum := none
      i := j + 1
    | .ctrl "right" =>
      let mut j := i + 1
      if let some .ws := toks[j]? then j := j + 1
      let r ← match toks[j]? with
        | some (.ch c) =>
          match delimChar c with
          | some r => pure r
          | none => throw s!"'\\right {String.ofList [c]}'"
        | some (.ctrl n) =>
          match ctrlAtom.lookup n with
          | some (_, c) => pure (some c)
          | none => throw s!"'\\right \\{n}'"
        | _ => throw "'\\right' without a delimiter"
      let some frame := stack.back? | throw "'\\right' without its '\\left'"
      let .leftRight l := frame.dest | throw "'\\right' without its '\\left'"
      stack := stack.pop
      let body := closeLevel overNum acc
      overNum := frame.overNum
      acc := frame.acc.push (.atom .inner (.delim l r body) .nil .nil false)
      i := j + 1
    | .ctrl "limits" =>
      match acc.back? with
      | some (.atom cls nuc sup sub _) =>
        acc := acc.pop.push (.atom cls nuc sup sub true)
      | _ => throw "\\limits without an operator"
      i := i + 1
    | .ctrl "nolimits" =>
      match acc.back? with
      | some (.atom cls nuc sup sub _) =>
        acc := acc.pop.push (.atom cls nuc sup sub false)
      | _ => throw "\\nolimits without an operator"
      i := i + 1
    | .ctrl "text" | .ctrl "mbox" | .ctrl "textrm" =>
      let mut j := i + 1
      if let some .ws := toks[j]? then j := j + 1
      let some .openGrp := toks[j]? | throw s!"{tokName tok} without its group"
      j := j + 1
      let mut s := ""
      for _ in [j:toks.size] do
        match toks[j]? with
        | some (.ch c) =>
          s := s.push c
          j := j + 1
        | some .ws =>
          s := s.push ' '
          j := j + 1
        | some .closeGrp => break
        | some t => throw s!"{tokName t} inside {tokName tok}"
        | none => throw "an unbalanced group"
      let some .closeGrp := toks[j]? | throw "an unbalanced group"
      acc := acc.push (.atom .ord (.word s) .nil .nil false)
      i := j + 1
    | .ctrl n =>
      match ctrlSpace.lookup n with
      | some mu =>
        acc := acc.push (.space mu)
        i := i + 1
      | none =>
        match tokAtom tok with
        | some atom =>
          acc := acc.push atom
          i := i + 1
        | none => throw (tokName tok)
    | .ch '\'' =>
      acc := ← attachPrime acc
      i := i + 1
    | .ch _ =>
      match tokAtom tok with
      | some atom =>
        acc := acc.push atom
        i := i + 1
      | none => throw (tokName tok)
  if pending.isSome then throw "a trailing script mark"
  let unbalanced (f : Option PFrame) : String :=
    match f with
    | some { dest := .leftRight _, .. } => "'\\left' without its '\\right'"
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
    let .grid _ rows cells := frame.dest | throw "an unbalanced group"
    let rows :=
      if cells.isEmpty && acc.isEmpty && overNum.isNone then rows
      else rows.push (closeCell kind cells overNum acc)
    if rows.isEmpty then throw "an empty alignment"
    let (grid, gnotes) := buildGrid kind rows
    return (.cons (.atom .ord grid .nil .nil false) .nil, notes ++ gnotes)

/-- Parse a formula's raw body into a math list, or name the construct that
puts it outside this slice. Notes name ragged alignment rows (an `array`
inside the formula). -/
def parseMath (raws : Array Parse.Raw) : Except String (MList × Array String) := do
  parseToks (← flattenList #[] raws.toList) none

/-- Parse an alignment environment's body (`align`/`gather` rows split at
`&` and `\\`) into one grid formula. -/
def parseMathRows (kind : GridKind) (raws : Array Parse.Raw) :
    Except String (MList × Array String) := do
  parseToks (← flattenList #[] raws.toList) (some kind)

end LeanTex.Core.MathParse
