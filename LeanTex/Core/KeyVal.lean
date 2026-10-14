module

/-! Lists cut at separators that stand outside groups, and LaTeX's comma and key=value lists over
them. -/

namespace LeanTex.Core.KeyVal

private def splitGo {α : Type} (opens closes : α → Bool) (sepLen : List α → Nat) :
    List α → Nat → Array α → Array (Array α) → Array (Array α)
  | [], _, cur, out => out.push cur
  | l@(x :: rest), depth, cur, out =>
    if opens x then splitGo opens closes sepLen rest (depth + 1) (cur.push x) out
    else if closes x then splitGo opens closes sepLen rest (depth - 1) (cur.push x) out
    else if depth == 0 && sepLen l > 0 then
      splitGo opens closes sepLen (rest.drop (sepLen l - 1)) depth #[] (out.push cur)
    else splitGo opens closes sepLen rest depth (cur.push x) out
termination_by l _ _ _ => l.length
decreasing_by all_goals simp only [List.length_cons, List.length_drop]; omega

/-- `xs` cut at each separator standing outside every group `opens` and `closes` delimit, where
`sepLen` is the length of the separator a suffix starts with, 0 for none; an unmatched close
counts as none. -/
public def splitTopWith {α : Type} (opens closes : α → Bool) (sepLen : List α → Nat)
    (xs : List α) : Array (Array α) :=
  splitGo opens closes sepLen xs 0 #[] #[]

/-- `xs` cut at each element `isSep` holds of outside every group `opens` and `closes` delimit. -/
public def splitTopAt {α : Type} (opens closes isSep : α → Bool) (xs : List α) :
    Array (Array α) :=
  splitTopWith opens closes (fun | x :: _ => if isSep x then 1 else 0 | [] => 0) xs

/-- `s` cut at each character `isSep` holds of outside braces. -/
public def splitBraced (isSep : Char → Bool) (s : String) : Array String :=
  (splitTopAt (· == '{') (· == '}') isSep s.toList).map (String.ofList ·.toList)

/-- A comma list as TeX's `\@for` reads it: cut at the commas outside braces, every item kept. -/
public def split (s : String) : Array String := splitBraced (· == ',') s

/-- A comma list as keyval reads it: its items trimmed, the empty ones dropped. -/
public def items (s : String) : Array String :=
  ((split s).map (·.trimAscii.toString)).filter (!·.isEmpty)

/-- A keyval item's key and value, cut at its first `=` outside braces and both trimmed; a bare key
has no value. -/
public def entry (item : String) : String × Option String :=
  match (splitBraced (· == '=') item).toList with
  | [] => ("", none)
  | [k] => (k.trimAscii.toString, none)
  | k :: rest => (k.trimAscii.toString, some ("=".intercalate rest).trimAscii.toString)

end LeanTex.Core.KeyVal
