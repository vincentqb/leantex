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

/-- LaTeX source as atoms: a control symbol, its backslash and character, one atom; every other
character alone. -/
private def texAtoms : List Char → Array (List Char) → Array (List Char)
  | [], acc => acc
  | '\\' :: c :: rest, acc => texAtoms rest (acc.push ['\\', c])
  | c :: rest, acc => texAtoms rest (acc.push [c])

/-- LaTeX source cut at each `sep` outside braces; an escaped character neither separates nor
groups. -/
private def splitTeX (sep : Char) (s : String) : Array String :=
  (splitTopAt (· == ['{']) (· == ['}']) (· == [sep]) (texAtoms s.toList #[]).toList).map
    fun item => String.ofList (item.toList.flatMap id)

/-- Whether atoms after an opening brace close its group at the last one and nowhere before. -/
private def closesAtEnd : List (List Char) → Nat → Bool
  | [], _ => false
  | [a], depth => a == ['}'] && depth == 1
  | a :: rest, depth =>
    if a == ['{'] then closesAtEnd rest (depth + 1)
    else if a == ['}'] then depth > 1 && closesAtEnd rest (depth - 1)
    else closesAtEnd rest depth

/-- A key or value as keyval hands it on: trimmed, and the braces around the whole removed. -/
public def unbrace (s : String) : String :=
  let t := s.trimAscii.toString
  match (texAtoms t.toList #[]).toList with
  | ['{'] :: rest => if closesAtEnd rest 1 then ((t.drop 1).dropEnd 1).toString else t
  | _ => t

/-- A comma list as LaTeX's `\@for` reads it: cut at the commas outside braces, every item kept. -/
public def split (s : String) : Array String := splitTeX ',' s

/-- A key=value list's items: trimmed, the empty ones dropped. -/
public def items (s : String) : Array String :=
  ((split s).map (·.trimAscii.toString)).filter (!·.isEmpty)

/-- A keyval item cut at its first `=` outside braces: its key and its value as written, both
trimmed; a bare key has no value. -/
public def rawEntry (item : String) : String × Option String :=
  match (splitTeX '=' item).toList with
  | [] => ("", none)
  | [k] => (k.trimAscii.toString, none)
  | k :: rest => (k.trimAscii.toString, some ("=".intercalate rest).trimAscii.toString)

/-- A keyval item's key and the value its key receives: `rawEntry`'s, each `unbrace`d. -/
public def entry (item : String) : String × Option String :=
  let (k, v) := rawEntry item
  (unbrace k, v.map unbrace)

/-- A keyval item's key and value where both are nonempty, as `entry` reads them. -/
public def pair? (item : String) : Option (String × String) :=
  match entry item with
  | (k, some v) => if k.isEmpty || v.isEmpty then none else some (k, v)
  | (_, none) => none

end LeanTex.Core.KeyVal
