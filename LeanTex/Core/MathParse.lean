import LeanTex.Core.Parse
import LeanTex.Core.Math

/-! The math surface: `$...$` bodies elaborated into `Math.MList` atoms.
Pure and total; the caller (the elaborator) owns diagnostics. A construct
outside this slice — fractions, radicals, `\left`, accents, `\text{}`,
alignment — returns `.error name`, and the formula stays `.math` source
text with a warning naming the construct: out of scope is a named warning,
never a silent drop (PLAN M6). -/

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
   -- big operators, set as ordinary Op glyphs in this slice: display-size
   -- variants and above/below limits are what M6 still owes
   ("sum", .op, '\u2211'), ("prod", .op, '\u220F'),
   ("coprod", .op, '\u2210'), ("int", .op, '\u222B'),
   ("oint", .op, '\u222E'), ("iint", .op, '\u222C'),
   ("bigcup", .op, '\u22C3'), ("bigcap", .op, '\u22C2'),
   ("bigvee", .op, '\u22C1'), ("bigwedge", .op, '\u22C0'),
   ("bigoplus", .op, '\u2A01'), ("bigotimes", .op, '\u2A02'),
   -- delimiters as ordinary (non-growing) atoms
   ("langle", .opening, '\u27E8'), ("rangle", .closing, '\u27E9'),
   ("lfloor", .opening, '\u230A'), ("rfloor", .closing, '\u230B'),
   ("lceil", .opening, '\u2308'), ("rceil", .closing, '\u2309'),
   ("vert", .ord, '|'), ("Vert", .ord, '\u2016'), ("|", .ord, '\u2016'),
   ("colon", .punct, ':'),
   -- escapes: the reserved characters as content
   ("{", .opening, '{'), ("}", .closing, '}'), ("$", .ord, '$'),
   ("%", .ord, '%'), ("&", .ord, '&'), ("#", .ord, '#'), ("_", .ord, '_')]

/-- The named functions TeX sets upright (TeXbook p. 162): Op atoms whose
nucleus is a word. Limits placement (`\lim` below in display) is owed with
the big operators; scripts set as ordinary scripts. -/
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

/-- Explicit spacing commands, in mu (18ths of an em): TeX's values
(TeXbook p. 167); `\ ` and `~` take an interword third of an em. -/
def ctrlSpace : List (String × Int) :=
  [(",", 3), (":", 4), (";", 5), ("!", -3), ("quad", 18), ("qquad", 36),
   (" ", 6), ("~", 6)]

/-- The flat token stream a formula parses from: group edges become
explicit markers so the parser is one pass over one array with a frame
stack, totality immediate (the shape `Parse.parse` set). -/
private inductive MTok where
  | ch (c : Char)
  | sup
  | sub
  | openGrp
  | closeGrp
  | ctrl (name : String)
  deriving Repr, BEq, Inhabited

private def flattenErr : Parse.Raw → Option String
  | .math _ _ _ => some "nested math"
  | .env n _ _ => some s!"\\begin\{{n}}"
  | .verb _ _ => some "verbatim"
  | .par _ => some "a blank line"
  | .sym c _ =>
    if c == '^' || c == '_' || c == '[' || c == ']' then none
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
  | .space => .ok out
  | .ctrl n _ => .ok (out.push (.ctrl n))
  | .sym '^' _ => .ok (out.push .sup)
  | .sym '_' _ => .ok (out.push .sub)
  | .sym '[' _ => .ok (out.push (.ch '['))
  | .sym ']' _ => .ok (out.push (.ch ']'))
  | .sym '~' _ => .ok (out.push (.ctrl "~"))
  | .group body _ => do
    let o ← flattenList (out.push .openGrp) body.toList
    .ok (o.push .closeGrp)
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
    | .atom cls nuc .nil sub, true => .ok (.atom cls nuc script sub)
    | .atom cls nuc sup .nil, false => .ok (.atom cls nuc sup script)
    | .space _, _ => .error "a script on a space"
    | _, true => .error "a double superscript"
    | _, false => .error "a double subscript"
  match acc.back? with
  | some (.space _) | none =>
    let fresh ← put (.atom .ord (.list .nil) .nil .nil)
    .ok (acc.push fresh)
  | some x =>
    .ok (acc.pop.push (← put x))

/-- One atom for a token met as a script argument or in the run of a list. -/
private def tokAtom : MTok → Option MItem
  | .ch c => (charAtom c).map fun (cls, c') => .atom cls (.sym c') .nil .nil
  | .ctrl n =>
    match ctrlAtom.lookup n with
    | some (cls, c) => some (.atom cls (.sym c) .nil .nil)
    | none => (ctrlWord.lookup n).map fun s => .atom .op (.word s) .nil .nil
  | _ => none

private def tokName : MTok → String
  | .ch c => s!"'{String.ofList [c]}'"
  | .ctrl n => s!"\\{n}"
  | .sup => "'^'"
  | .sub => "'_'"
  | .openGrp => "'{'"
  | .closeGrp => "'}'"

/-- Why a level was opened: a braced group atom, or the argument of a
script on the parent's last atom. -/
private inductive Dest where
  | grp
  | script (isSup : Bool)

private structure PFrame where
  acc : Array MItem
  dest : Dest

/-- Parse a formula's raw body into a math list, or name the construct that
puts it outside this slice. One forward pass over the flattened tokens with
an explicit frame stack; every step consumes a token, so the loop bound is
never the reason it stops. -/
def parseMath (raws : Array Parse.Raw) : Except String MList := do
  let toks ← flattenList #[] raws.toList
  let mut stack : Array PFrame := #[]
  let mut acc : Array MItem := #[]
  let mut pending : Option Bool := none
  for tok in toks do
    match tok with
    | .sup =>
      if pending.isSome then throw "a double script mark"
      pending := some true
    | .sub =>
      if pending.isSome then throw "a double script mark"
      pending := some false
    | .openGrp =>
      let dest := match pending with
        | some isSup => Dest.script isSup
        | none => Dest.grp
      pending := none
      stack := stack.push { acc, dest }
      acc := #[]
    | .closeGrp =>
      let some frame := stack.back? | throw "an unbalanced group"
      stack := stack.pop
      let body := MList.ofList acc.toList
      match frame.dest with
      | .grp => acc := frame.acc.push (.atom .ord (.list body) .nil .nil)
      | .script isSup => acc := ← attach frame.acc isSup body
    | .ctrl n =>
      match ctrlSpace.lookup n with
      | some mu =>
        if pending.isSome then throw s!"\\{n} as a script"
        acc := acc.push (.space mu)
      | none =>
        match tokAtom tok with
        | some atom =>
          match pending with
          | some isSup =>
            pending := none
            acc := ← attach acc isSup (.cons atom .nil)
          | none => acc := acc.push atom
        | none => throw (tokName tok)
    | .ch _ =>
      match tokAtom tok with
      | some atom =>
        match pending with
        | some isSup =>
          pending := none
          acc := ← attach acc isSup (.cons atom .nil)
        | none => acc := acc.push atom
      | none => throw (tokName tok)
  if pending.isSome then throw "a trailing script mark"
  unless stack.isEmpty do throw "an unbalanced group"
  return MList.ofList acc.toList

end LeanTex.Core.MathParse
