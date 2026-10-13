module

public import LeanTex.Core.Highlight
import LeanTex.Core.PygmentsLexData

/-! The language names a listing may spell, and the known
name nearest a misspelt one. -/
namespace LeanTex.Core.LexerName

open Highlight

/-- The registry's aliases, split on first use. -/
private def registry (_ : Unit) : Array String :=
  (PygmentsLexData.registryAliases.splitOn " ").toArray

/-- Whether a listing may name the language, compared case-insensitively. -/
public def known (name : String) : Bool :=
  let n := name.trimAscii.toString.toLower
  (Lexer.ofName? n).isSome || (registry ()).contains n

/-- The optimal-string-alignment distance: insertions, deletions, substitutions
and adjacent transpositions, each one edit. -/
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

/-- The known name a misspelt one most likely meant: same first letter, at most
one edit for five letters or fewer and two otherwise, native names first; `none`
for three letters or fewer. -/
public def nearest? (name : String) : Option String :=
  let cs := name.trimAscii.toString.toLower.toList.toArray
  let bound := if cs.size ≤ 5 then 1 else 2
  let natives := Lexer.all.toArray.flatMap (·.aliases)
  let pool := natives ++ (registry ()).filter (!natives.contains ·)
  if cs.size ≤ 3 then none else
  (pool.foldl (fun (best : Option (String × Nat)) alias =>
    let a := alias.toList.toArray
    if a[0]? != cs[0]? then best else
    let d := editDistance cs a
    if d == 0 || d > bound then best else
    match best with
    | some (_, b) => if d < b then some (alias, d) else best
    | none => some (alias, d)) none).map (·.1)

end LeanTex.Core.LexerName
