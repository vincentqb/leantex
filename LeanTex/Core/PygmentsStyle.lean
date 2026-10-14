module

public import LeanTex.Core.Color
import LeanTex.Core.CssColor
public import LeanTex.Core.ListingHighlight
import LeanTex.Core.PygmentsStyleData
public import Std.Data.HashMap

/-! Pygments' style model over `PygmentsStyleData`: `Resolved`, Pygments' inheritance
(`style_for_token`), and `Look`, what minted's LaTeX formatter ships under lualatex. -/
namespace LeanTex.Core.PygmentsStyle

open Ir ListingHighlight

/-- One style declaration's words; `none` where the type keeps its parent's value. -/
public structure Decl where
  color : Option Color := none
  bold : Option Bool := none
  italic : Option Bool := none
  underline : Option Bool := none
  bgcolor : Option (Option Color) := none
  border : Option (Option Color) := none
  deriving Repr, BEq, Inhabited

/-- The `style_for_token` fields the declarations reach; `color` carries the type that set it. -/
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

private def optColor? (s : String) : Option (Option Color) :=
  if s.isEmpty then some none else (CssColor.hex? s).map (some ·.color)

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
      else (CssColor.hex? word).map fun v => { d with color := some v.color }

/-- One inheritance step: `k`'s resolved style from its parent's. -/
public def Resolved.step (parent : Resolved) (k : Kind) (d : Decl) : Resolved :=
  { color := (d.color.map (·, k)).or parent.color
    bold := d.bold.getD parent.bold
    italic := d.italic.getD parent.italic
    underline := d.underline.getD parent.underline
    bgcolor := d.bgcolor.getD parent.bgcolor
    border := d.border.getD parent.border }

/-- The fill `\fcolorbox` takes for a border with no background: the formatter's `1,1,1`. -/
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

/-- A style resolved: every declared type and its ancestors, the root included. -/
public structure Table where
  resolved : Std.HashMap Kind Resolved
  looks : Std.HashMap Kind Look

private def root : Kind := ⟨""⟩

/-- Resolve declarations, each type after its parent. -/
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

/-- What minted ships for any type; the root carries no style. -/
public def Table.lookOf (t : Table) (k : Kind) : Look :=
  if k.path.isEmpty then {} else t.looks.getD (t.nearest k) {}

/-- Every type the table holds, the domain a contract over its colours ranges over. -/
public def Table.kinds (t : Table) : List Kind := t.resolved.keys

/-- Every standard type with its formatter macro name, in token order (`STANDARD_TYPES`). -/
public def standardTypes : List (Kind × String) :=
  PygmentsStyleData.standardTypes.map fun (path, n) => (Kind.ofPygments path, n)

public def defaultTable : Table := Table.build PygmentsStyleData.defaultStyle

public def friendlyTable : Table := Table.build PygmentsStyleData.friendlyStyle

/-- Every shipped declaration parses. -/
public def declarationsParse : Bool :=
  (PygmentsStyleData.defaultStyle ++ PygmentsStyleData.friendlyStyle).all fun (_, d) =>
    (parseDecl? d).isSome

end LeanTex.Core.PygmentsStyle
