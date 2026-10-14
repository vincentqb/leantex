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

/-- Text trimmed, with the braces around the whole of it removed: a value as kvsetkeys and l3keys
hand it on, and a key as kvsetkeys does. -/
public def unbrace (s : String) : String :=
  let t := s.trimAscii.toString
  match (texAtoms t.toList #[]).toList with
  | ['{'] :: rest => if closesAtEnd rest 1 then ((t.drop 1).dropEnd 1).toString else t
  | _ => t

/-- A comma list cut at the commas outside braces, every item kept as written. -/
public def split (s : String) : Array String := splitTeX ',' s

/-- A key=value list's items: trimmed, the empty ones dropped. -/
public def items (s : String) : Array String :=
  ((split s).map (·.trimAscii.toString)).filter (!·.isEmpty)

/-- A keyval item, its braces removed where they hold the whole of it, cut at its first `=` outside
braces: its key and its value as written, both trimmed; a bare key has no value. -/
public def rawEntry (item : String) : String × Option String :=
  match (splitTeX '=' (unbrace item)).toList with
  | [] => ("", none)
  | [k] => (k.trimAscii.toString, none)
  | k :: rest => (k.trimAscii.toString, some ("=".intercalate rest).trimAscii.toString)

/-- A keyval item's key and the value its key receives: `rawEntry`'s, each `unbrace`d. -/
public def entry (item : String) : String × Option String :=
  let (k, v) := rawEntry item
  (unbrace k, v.map unbrace)

/-- An item's key and value where both are written nonempty, each `unbrace`d: `k={}` reads as an
empty value, `k=` as none. -/
public def pair? (item : String) : Option (String × String) :=
  match rawEntry item with
  | (k, some v) => if k.isEmpty || v.isEmpty then none else some (unbrace k, unbrace v)
  | (_, none) => none

/-- Whether an item's parentheses, brackets or double quotes outside braces fail to balance, as a
piece of a value cut at a comma inside them does. -/
public def unbalanced (item : String) : Bool := Id.run do
  let mut depth := 0
  let mut paren : Int := 0
  let mut bracket : Int := 0
  let mut quotes := 0
  for a in (texAtoms item.toList #[]).toList do
    if a == ['{'] then depth := depth + 1
    else if a == ['}'] then depth := depth - 1
    else if depth == 0 then
      if a == ['('] then paren := paren + 1
      else if a == [')'] then paren := paren - 1
      else if a == ['['] then bracket := bracket + 1
      else if a == [']'] then bracket := bracket - 1
      else if a == ['"'] then quotes := quotes + 1
  return paren != 0 || bracket != 0 || quotes % 2 == 1

private theorem intercalate_snoc_last {α : Type} (sep : List α) (c : List α) (x : α) :
    ∀ L : List (List α), sep.intercalate (L ++ [c ++ [x]]) = sep.intercalate (L ++ [c]) ++ [x]
  | [] => by simp [List.intercalate_singleton]
  | l :: L => by
    rw [List.cons_append, List.cons_append,
      List.intercalate_cons_of_ne_nil (by simp), List.intercalate_cons_of_ne_nil (by simp),
      intercalate_snoc_last sep c x L]
    simp only [List.append_assoc]

private theorem intercalate_snoc_empty {α : Type} (sep : List α) (c : List α) :
    ∀ L : List (List α), sep.intercalate (L ++ [c] ++ [[]]) = sep.intercalate (L ++ [c]) ++ sep
  | [] => by simp [List.intercalate_cons_cons, List.intercalate_singleton]
  | l :: L => by
    rw [List.cons_append, List.cons_append,
      List.intercalate_cons_of_ne_nil (by simp), List.intercalate_cons_of_ne_nil (by simp),
      intercalate_snoc_empty sep c L]
    simp only [List.append_assoc]

private theorem splitGo_join {α : Type} [BEq α] [LawfulBEq α] (opens closes : α → Bool) (s : α)
    (l : List α) (depth : Nat) (cur : Array α) (out : Array (Array α)) :
    [s].intercalate ((splitGo opens closes (fun | x :: _ => if x == s then 1 else 0 | [] => 0)
        l depth cur out).toList.map Array.toList) =
      [s].intercalate ((out.push cur).toList.map Array.toList) ++ l := by
  fun_induction splitGo opens closes (fun | x :: _ => if x == s then 1 else 0 | [] => 0)
    l depth cur out with
  | case1 => simp
  | case2 x rest depth cur out _ ih =>
    rw [ih]
    simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil]
    rw [intercalate_snoc_last]
    simp
  | case3 x rest depth cur out _ _ ih =>
    rw [ih]
    simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil]
    rw [intercalate_snoc_last]
    simp
  | case4 x rest depth cur out _ _ hsep ih =>
    have hx : x = s := by
      cases hxs : x == s with
      | true => exact eq_of_beq hxs
      | false => simp [hxs] at hsep
    subst hx
    rw [ih]
    simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil, beq_self_eq_true,
      ↓reduceIte, Nat.sub_self, List.drop_zero]
    rw [intercalate_snoc_empty]
    simp
  | case5 x rest depth cur out _ _ _ ih =>
    rw [ih]
    simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil]
    rw [intercalate_snoc_last]
    simp

/-- Joined at the separator element, the pieces `splitTopAt` cuts are the list it cut. -/
public theorem splitTopAt_join_id {α : Type} [BEq α] [LawfulBEq α] (opens closes : α → Bool)
    (s : α) (xs : List α) :
    [s].intercalate ((splitTopAt opens closes (· == s) xs).toList.map Array.toList) = xs := by
  unfold splitTopAt splitTopWith
  rw [splitGo_join]
  simp

private theorem texAtoms_flatten (cs : List Char) (acc : Array (List Char)) :
    (texAtoms cs acc).toList.flatten = acc.toList.flatten ++ cs := by
  fun_induction texAtoms cs acc with
  | case1 acc => simp
  | case2 c rest acc ih => rw [ih]; simp
  | case3 c rest acc _ ih => rw [ih]; simp

private theorem flatten_intercalate (a : List Char) :
    ∀ segs : List (List (List Char)),
      ([a].intercalate segs).flatten = a.intercalate (segs.map List.flatten)
  | [] => by simp
  | [x] => by simp [List.intercalate_singleton]
  | x :: y :: rest => by
    rw [List.intercalate_cons_cons, List.map_cons, List.map_cons, List.intercalate_cons_cons,
      ← List.map_cons, ← flatten_intercalate a (y :: rest)]
    simp

/-- Joined at their commas, the items `split` cuts are the text it cut. -/
public theorem split_join_id (s : String) :
    [','].intercalate ((split s).toList.map String.toList) = s.toList := by
  have h := splitTopAt_join_id (· == ['{']) (· == ['}']) [','] (texAtoms s.toList #[]).toList
  have hf := congrArg List.flatten h
  rw [flatten_intercalate, texAtoms_flatten] at hf
  simp only [split, splitTeX, Array.toList_map, List.map_map, Function.comp_def,
    String.toList_ofList, List.flatMap_id]
  simpa [List.map_map, Function.comp_def] using hf

end LeanTex.Core.KeyVal
