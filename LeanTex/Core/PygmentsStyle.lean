module

public import LeanTex.Core.Color
public import LeanTex.Core.ListingHighlight
import LeanTex.Core.PygmentsStyleData
public import Std.Data.HashMap

/-!
Pygments' style model for listing tokens, over the declarations
`PygmentsStyleData` carries. Two readings of one table:

* `Resolved` is Pygments' inheritance (pygments/style.py, `StyleMeta`): a
  type starts from its parent's resolved style and applies its own
  declaration's words in order. It is `style_for_token`'s answer, which the
  suite compares row by row with Pygments' own.
* `Look` is what a lualatex build with minted ships: the LaTeX formatter
  (pygments/formatters/latex.py) writes a token as `\PYG{k+kt}{…}`, and
  `\PYG@toks` applies each type's command from the top level down. A later
  colour or box replaces an earlier one; bold, italic and underline, once
  set, stay set, so a `nobold` below a bold type is lost exactly as it is in
  the lualatex build. The colour remembers the type whose declaration set
  it, which is where a document's own listing colour enters (`Listing`).
-/
namespace LeanTex.Core.PygmentsStyle

open Ir ListingHighlight

/-- One style declaration's words: what each field sets, `none` where the
type keeps its parent's value. `bgcolor` and `border` may be set to nothing
(`bg:`), as Pygments allows. -/
public structure Decl where
  color : Option Color := none
  bold : Option Bool := none
  italic : Option Bool := none
  underline : Option Bool := none
  bgcolor : Option (Option Color) := none
  border : Option (Option Color) := none
  deriving Repr, BEq, Inhabited

/-- `style_for_token`'s fields the carried declarations reach. `color`
carries the type whose declaration set it. -/
public structure Resolved where
  color : Option (Color × Kind) := none
  bold : Bool := false
  italic : Bool := false
  underline : Bool := false
  bgcolor : Option Color := none
  border : Option Color := none
  deriving Repr, BEq, Inhabited

/-- The box the LaTeX formatter draws around a token: `\fcolorbox` with the
border and a fill (white where the style names none), or `\colorbox`. -/
public inductive Box where
  | frame (border fill : Color)
  | fill (color : Color)
  deriving Repr, BEq, Inhabited

/-- What minted ships for a token of one type. -/
public structure Look where
  color : Option (Color × Kind) := none
  bold : Bool := false
  italic : Bool := false
  underline : Bool := false
  box : Option Box := none
  deriving Repr, BEq, Inhabited

/-- `#rgb` or `#rrggbb`, the spellings the generator admits. -/
public def hexColor? (s : String) : Option Color :=
  let digits := s.toList.drop 1
  let value (cs : List Char) : Option Nat := cs.foldlM (init := 0) fun n c =>
    if c.isDigit then some (n * 16 + (c.toNat - '0'.toNat))
    else if 'a' ≤ c.toLower && c.toLower ≤ 'f' then some (n * 16 + (c.toLower.toNat - 'a'.toNat + 10))
    else none
  let full := match digits with
    | [r, g, b] => some [r, r, g, g, b, b]
    | ds => if ds.length == 6 then some ds else none
  if s.toList.head? != some '#' then none else do
    let ds ← full
    let v ← value ds
    some { r := (v / 65536).toUInt8, g := (v / 256 % 256).toUInt8, b := (v % 256).toUInt8 }

private def optColor? (s : String) : Option (Option Color) :=
  if s.isEmpty then some none else (hexColor? s).map some

/-- A declaration's words, in order; `none` for a word the painter does not
carry, which the generator refuses before it reaches the data. -/
public def parseDecl? (text : String) : Option Decl :=
  (text.split Char.isWhitespace).toList.foldlM (init := ({} : Decl)) fun d slice =>
    let word := slice.toString
    match word with
    | "" => some d
    | "bold" => some { d with bold := some true }
    | "nobold" => some { d with bold := some false }
    | "italic" => some { d with italic := some true }
    | "noitalic" => some { d with italic := some false }
    | "underline" => some { d with underline := some true }
    | "nounderline" => some { d with underline := some false }
    | _ =>
      if word.startsWith "bg:" then
        (optColor? (word.drop 3).toString).map fun c => { d with bgcolor := some c }
      else if word.startsWith "border:" then
        (optColor? (word.drop 7).toString).map fun c => { d with border := some c }
      else (hexColor? word).map fun c => { d with color := some c }

/-- One inheritance step: `k`'s resolved style from its parent's. -/
public def Resolved.step (parent : Resolved) (k : Kind) (d : Decl) : Resolved :=
  { color := (d.color.map (·, k)).or parent.color
    bold := d.bold.getD parent.bold
    italic := d.italic.getD parent.italic
    underline := d.underline.getD parent.underline
    bgcolor := d.bgcolor.getD parent.bgcolor
    border := d.border.getD parent.border }

/-- The fill `\fcolorbox` takes when a style names a border and no
background: the formatter's `rgbcolor('')`, `1,1,1`. -/
private def unfilled : Color := { r := 255, g := 255, b := 255 }

/-- One `\PYG@tok`: the next type's command over what the types above it set. -/
public def Look.step (acc : Look) (r : Resolved) : Look :=
  { color := r.color.or acc.color
    bold := acc.bold || r.bold
    italic := acc.italic || r.italic
    underline := acc.underline || r.underline
    box := match r.border, r.bgcolor with
      | some border, fill => some (.frame border (fill.getD unfilled))
      | none, some fill => some (.fill fill)
      | none, none => acc.box }

/-- A style resolved: every declared type and its ancestors, the root
included. A type the table does not hold declares nothing, so it reads as
its nearest ancestor does (`resolvedOf`, `lookOf`). -/
public structure Table where
  resolved : Std.HashMap Kind Resolved
  looks : Std.HashMap Kind Look

private def root : Kind := ⟨""⟩

/-- Resolve declarations, each type after its parent: a chain lists its
ancestors first, so walking the declared types' chains in order meets every
parent before its children. -/
public def Table.build (decls : List (String × String)) : Table := Id.run do
  let parsed := decls.filterMap fun (t, d) => (parseDecl? d).map (Kind.ofPygments t, ·)
  let declOf (k : Kind) : Decl := ((parsed.find? (·.1 == k)).map (·.2)).getD {}
  let top := Resolved.step {} root (declOf root)
  let mut resolved : Std.HashMap Kind Resolved := Std.HashMap.emptyWithCapacity |>.insert root top
  let mut looks : Std.HashMap Kind Look := Std.HashMap.emptyWithCapacity |>.insert root {}
  for (k, _) in parsed do
    let mut parent := root
    for t in k.chain do
      unless resolved.contains t do
        let r := (resolved.getD parent top).step t (declOf t)
        resolved := resolved.insert t r
        looks := looks.insert t ((looks.getD parent {}).step r)
      parent := t
  return { resolved, looks }

/-- The nearest ancestor-or-self of `k` the table holds; the root otherwise. -/
private def Table.nearest (t : Table) (k : Kind) : Kind :=
  (k.chain.reverse.find? t.resolved.contains).getD root

/-- `style_for_token` for any type. -/
public def Table.resolvedOf (t : Table) (k : Kind) : Resolved :=
  t.resolved.getD (t.nearest k) {}

/-- What minted ships for any type. The root itself carries no style. -/
public def Table.lookOf (t : Table) (k : Kind) : Look :=
  if k.path.isEmpty then {} else t.looks.getD (t.nearest k) {}

/-- Every type the table holds: the domain a contract over its colours
ranges over, since every other type reads as one of these. -/
public def Table.kinds (t : Table) : List Kind := t.resolved.keys

public def defaultTable : Table := Table.build PygmentsStyleData.defaultStyle

public def friendlyTable : Table := Table.build PygmentsStyleData.friendlyStyle

/-- Every shipped declaration parses: what the generator admitted, this
module carries. -/
public def declarationsParse : Bool :=
  (PygmentsStyleData.defaultStyle ++ PygmentsStyleData.friendlyStyle).all fun (_, d) =>
    (parseDecl? d).isSome

end LeanTex.Core.PygmentsStyle
