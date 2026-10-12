module

public import LeanTex.Core.Highlight
import LeanTex.Core.PygmentsLexData

/-!
The lexer names a listing's language may spell: a native lexer's
(`Highlight.Lexer.ofName?`), or an alias Pygments' registry holds for the
release the mirror tracks (`PygmentsLexData.registryAliases`). A name
outside both selects no lexer anywhere, so the document is told where it
stands, with the known name nearest its spelling, rather than the boundary
asked a question no provider of that release answers.
-/
namespace LeanTex.Core.LexerName

open Highlight

/-- The registry's aliases. A function of `Unit`, so no process pays for the
split before a listing asks. -/
private def registry (_ : Unit) : Array String :=
  (PygmentsLexData.registryAliases.splitOn " ").toArray

/-- A language a listing may name, case-insensitively, as the registry's own
lookup is. -/
public def known (name : String) : Bool :=
  let n := name.trimAscii.toString.toLower
  (Lexer.ofName? n).isSome || (registry ()).contains n

/-- The optimal-string-alignment distance: insertions, deletions,
substitutions and adjacent transpositions, each one edit. Each row is built
from the two before it, the index's default never read inside the bounds. -/
private def editDistance (a b : Array Char) : Nat := Id.run do
  let n := b.size
  let mut before : Array Nat := #[]
  let mut prev : Array Nat := Array.range (n + 1)
  for i in [1:a.size + 1] do
    let mut cur : Array Nat := #[i]
    for j in [1:n + 1] do
      let ai := a.getD (i - 1) ' '
      let bj := b.getD (j - 1) ' '
      let cost := if ai == bj then 0 else 1
      let mut d := min (prev.getD j 0 + 1) (min (cur.getD (j - 1) 0 + 1) (prev.getD (j - 1) 0 + cost))
      if i > 1 && j > 1 && ai == b.getD (j - 2) ' ' && a.getD (i - 2) ' ' == bj then
        d := min d (before.getD (j - 2) 0 + 1)
      cur := cur.push d
    before := prev
    prev := cur
  return prev.getD n 0

/-- The known name a misspelt one most likely meant: fewest edits away,
within two edits and a third of the name's length (one at least), a native
lexer's spelling first among equals, then the registry's order. `none` when
nothing stands that near. -/
public def nearest? (name : String) : Option String :=
  let cs := name.trimAscii.toString.toLower.toList.toArray
  let bound := max 1 (min 2 (cs.size / 3))
  let natives := Lexer.all.toArray.flatMap (·.aliases)
  let pool := natives ++ (registry ()).filter (!natives.contains ·)
  (pool.foldl (fun (best : Option (String × Nat)) alias =>
    let d := editDistance cs alias.toList.toArray
    if d == 0 || d > bound then best else
    match best with
    | some (_, b) => if d < b then some (alias, d) else best
    | none => some (alias, d)) none).map (·.1)

end LeanTex.Core.LexerName
