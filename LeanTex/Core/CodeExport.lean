module

public import LeanTex.Core.Listing

/-!
A palette's code colours as the Pygments LaTeX formatter's own macros, for a
TeX build of the same document: each code role's colour from the one
resolving site (`CodeColor.resolve`, as both of the engine's artifacts paint
it, through `Listing.roleBrushes`), and its weights (`Role.weights`), written
as one `\PYG@tok@<type>` redefinition per standard token type inside a
command minted's `formatcom` runs after it defines the style's macros. The
engine never reads the export: it paints the same roles from the palette
itself, so the TeX build is the one that needs it.
-/

namespace LeanTex.Core.CodeExport

open Ir ListingHighlight

/-- A role's colour name in an export: the stem, `Code`, and the role. -/
public def colorName (stem : String) : ListingHighlight.Role → String
  | .ink => stem ++ "CodeInk"
  | .keyword => stem ++ "CodeKeyword"
  | .name => stem ++ "CodeName"
  | .literal => stem ++ "CodeLiteral"
  | .comment => stem ++ "CodeComment"
  | .error => stem ++ "CodeError"

private def hexOf (c : Color) : String :=
  Color.hexByte c.r ++ Color.hexByte c.g ++ Color.hexByte c.b

/-- One type's macro as the formatter writes one, inside a command's body
(each `#` doubled once for the command and once for the macro). Every
setting is stated, so neither the base style's macro for the type nor an
ancestor's shows through: the role's weights, and its colour, or none for a
role that sets in the listing's own ink. -/
private def macroText (stem : String) (brushes : RoleTable Listing.Brush) (k : Kind) : String :=
  let r := k.role
  let b := brushes.get r
  (if b.look.bold then "\\let\\PYG@bf=\\textbf" else "\\let\\PYG@bf=\\relax") ++
  (if b.look.italic then "\\let\\PYG@it=\\textit" else "\\let\\PYG@it=\\relax") ++
  "\\let\\PYG@ul=\\relax\\let\\PYG@bc=\\relax" ++
  match b.ink with
  | some _ => "\\def\\PYG@tc####1{\\textcolor{" ++ colorName stem r ++ "}{####1}}"
  | none => "\\let\\PYG@tc=\\relax"

/-- The colour each role ships on the palette's page, as `Listing.roleBrushes`
paints it in both artifacts, and its weights. -/
public def pageBrushes (pal : Palette) (style : Ir.ListingStyle) : RoleTable Listing.Brush :=
  Listing.roleBrushes pal none none style

/-- **The export**: an xcolor colour per role that has one, and one command,
`\<stem>Pygments`, redefining every standard type's `\PYG@tok@<name>` macro
from its role. Apply it with `\setminted{formatcom=\<stem>Pygments}`. -/
public def texDeclarations (stem : String) (pal : Palette) (style : Ir.ListingStyle) : String :=
  Id.run do
    let brushes := pageBrushes pal style
    let mut defs := ""
    for r in ListingHighlight.Role.all do
      if let some c := (brushes.get r).ink then
        defs := defs ++ "\\definecolor{" ++ colorName stem r ++ "}{HTML}{" ++ hexOf c ++ "}\n"
    let mut body := ""
    for (k, name) in PygmentsStyle.standardTypes do
      unless name.isEmpty do
        body := body ++ "  \\@namedef{PYG@tok@" ++ name ++ "}{" ++ macroText stem brushes k ++ "}%\n"
    return "% Code colours from this palette's code roles, as leantex paints them on the page.\n" ++
      "% Load after minted; apply with \\setminted{formatcom=\\" ++ stem ++ "Pygments}.\n" ++
      defs ++ "\\makeatletter\n\\newcommand\\" ++ stem ++ "Pygments{%\n" ++ body ++
      "}\n\\makeatother\n"

end LeanTex.Core.CodeExport
