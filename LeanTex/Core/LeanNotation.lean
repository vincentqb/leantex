module

import LeanTex.Core.DeriveBEq
/-! # The notation table

The one table a Lean statement's constants show through: arithmetic, relations, logic, existence,
the number sets and numerals; every other constant shows as its own name. -/

namespace LeanTex.Core.LeanNotation

/-- The controls a statement's mathematics writes. -/
public inductive MathCtrl where
  | forAll | exist | mem | to | mapsto | cdot | bmod | mid | neq | leq | geq | land | lor
  | lnot | iff | times | mathbb | mathit | mathrm | mathtt | operatorname | text | space | underscore
  | textunderscore | textbraceleft | textbraceright | textdollar | tilde | caret | backslash
  | hash | percent | amp
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A control as the surface spells it. -/
@[expose] public def MathCtrl.name : MathCtrl → String
  | .forAll => "forall"
  | .exist => "exists"
  | .mem => "in"
  | .to => "to"
  | .mapsto => "mapsto"
  | .cdot => "cdot"
  | .bmod => "bmod"
  | .mid => "mid"
  | .neq => "neq"
  | .leq => "leq"
  | .geq => "geq"
  | .land => "land"
  | .lor => "lor"
  | .lnot => "lnot"
  | .iff => "leftrightarrow"
  | .times => "times"
  | .mathbb => "mathbb"
  | .mathit => "mathit"
  | .mathrm => "mathrm"
  | .mathtt => "mathtt"
  | .operatorname => "operatorname"
  | .text => "text"
  | .space => " "
  | .underscore => "_"
  | .textunderscore => "textunderscore"
  | .textbraceleft => "textbraceleft"
  | .textbraceright => "textbraceright"
  | .textdollar => "textdollar"
  | .tilde => "textasciitilde"
  | .caret => "textasciicircum"
  | .backslash => "textbackslash"
  | .hash => "#"
  | .percent => "%"
  | .amp => "&"

/-- Every control, as the vocabulary admits them. -/
@[expose] public def MathCtrl.all : List MathCtrl :=
  [.forAll, .exist, .mem, .to, .mapsto, .cdot, .bmod, .mid, .neq, .leq, .geq, .land, .lor,
   .lnot, .iff, .times, .mathbb, .mathit, .mathrm, .mathtt, .operatorname, .text, .space,
   .underscore, .textunderscore, .textbraceleft,
   .textbraceright, .textdollar, .tilde, .caret, .backslash, .hash, .percent, .amp]

public theorem MathCtrl.mem_all (c : MathCtrl) : c ∈ MathCtrl.all := by
  cases c <;> simp [MathCtrl.all]

/-- A statement's mathematics: words, controls, braced arguments and raised or lowered parts. -/
public inductive Math where
  | word (s : String)
  | ctrl (c : MathCtrl)
  | arg (body : List Math)
  | sup (body : List Math)
  | sub (body : List Math)
  deriving Repr, Inhabited

deriving_structural_beq Math

/-- How a notation spells its symbol: a control, a word, a blackboard letter, or the numeral its
argument is. -/
public inductive Glyph where
  | ctrl (c : MathCtrl)
  | word (text : String)
  | bb (letter : String)
  | numeral
  deriving Repr, BEq, DecidableEq, Inhabited

public inductive Assoc where
  | left
  | right
  | none
  deriving Repr, BEq, DecidableEq, Inhabited

/-- How a notation sets its explicit arguments around its glyph. -/
public inductive Shape where
  /-- `a ⋆ b` at a precedence. -/
  | infix (prec : Nat) (assoc : Assoc)
  /-- `b ⋆ a` from `a`, `b`: membership, whose collection Lean passes first. -/
  | swapped (prec : Nat)
  /-- `⋆a`, its argument at a precedence. -/
  | prefix (prec : Nat)
  /-- `a` raised to `b`. -/
  | power
  /-- The glyph alone. -/
  | constant
  /-- The literal its one argument is. -/
  | numeral
  /-- `⋆ x ∈ T, P` from an argument `fun x : T => P`. -/
  | binder
  deriving Repr, BEq, DecidableEq, Inhabited

/-- One constant's notation. -/
public structure Notation where
  const : String
  glyph : Glyph
  shape : Shape
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The table, at Lean's own precedences where Lean declares the notation. -/
@[expose] public def notations : List Notation :=
  [⟨"HAdd.hAdd", .word "+", .infix 65 .left⟩,
   ⟨"HSub.hSub", .word "-", .infix 65 .left⟩,
   ⟨"HMul.hMul", .ctrl .cdot, .infix 70 .left⟩,
   ⟨"HDiv.hDiv", .word "/", .infix 70 .left⟩,
   ⟨"HMod.hMod", .ctrl .bmod, .infix 70 .left⟩,
   ⟨"HPow.hPow", .word "^", .power⟩,
   ⟨"Neg.neg", .word "-", .prefix 75⟩,
   ⟨"Dvd.dvd", .ctrl .mid, .infix 50 .none⟩,
   ⟨"Eq", .word "=", .infix 50 .none⟩,
   ⟨"Ne", .ctrl .neq, .infix 50 .none⟩,
   ⟨"LE.le", .ctrl .leq, .infix 50 .none⟩,
   ⟨"LT.lt", .word "<", .infix 50 .none⟩,
   ⟨"GE.ge", .ctrl .geq, .infix 50 .none⟩,
   ⟨"GT.gt", .word ">", .infix 50 .none⟩,
   ⟨"Membership.mem", .ctrl .mem, .swapped 50⟩,
   ⟨"Iff", .ctrl .iff, .infix 20 .none⟩,
   ⟨"And", .ctrl .land, .infix 35 .right⟩,
   ⟨"Or", .ctrl .lor, .infix 30 .right⟩,
   ⟨"Not", .ctrl .lnot, .prefix 40⟩,
   ⟨"Exists", .ctrl .exist, .binder⟩,
   ⟨"Prod", .ctrl .times, .infix 35 .right⟩,
   ⟨"List.cons", .word "::", .infix 67 .right⟩,
   ⟨"Nat", .bb "N", .constant⟩,
   ⟨"Int", .bb "Z", .constant⟩,
   ⟨"Rat", .bb "Q", .constant⟩,
   ⟨"Real", .bb "R", .constant⟩,
   ⟨"Complex", .bb "C", .constant⟩,
   ⟨"OfNat.ofNat", .numeral, .numeral⟩]

/-- What a constant's occurrence shows: its notation's glyph and shape, or its own name. -/
public inductive Shown where
  | notation (glyph : Glyph) (shape : Shape)
  | name (const : String)
  deriving Repr, BEq, DecidableEq, Inhabited

@[expose] public def shownOf (c : String) : Shown :=
  match notations.find? (·.const == c) with
  | some n => .notation n.glyph n.shape
  | none => .name c

end LeanTex.Core.LeanNotation
