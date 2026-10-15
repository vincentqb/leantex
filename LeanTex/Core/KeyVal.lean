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

/-- One element's step through a scan for a separator outside groups: the depth after it, `none`
once a separator stands at depth 0. -/
private def cutStep {α : Type} (opens closes isSep : α → Bool) : Option Nat → α → Option Nat
  | none, _ => none
  | some d, x =>
    if opens x then some (d + 1) else if closes x then some (d - 1)
    else if d == 0 && isSep x then none else some d

private theorem foldl_cutStep_none {α : Type} (opens closes isSep : α → Bool) :
    ∀ l : List α, l.foldl (cutStep opens closes isSep) none = none
  | [] => rfl
  | _ :: rest => by
    simp only [List.foldl, cutStep]
    exact foldl_cutStep_none opens closes isSep rest

private theorem splitGo_uncut {α : Type} (opens closes isSep : α → Bool) (l : List α)
    (depth : Nat) (cur : Array α) (out : Array (Array α))
    (h : (l.foldl (cutStep opens closes isSep) (some depth)).isSome) :
    splitGo opens closes (fun | x :: _ => if isSep x then 1 else 0 | [] => 0) l depth cur out =
      out.push (cur ++ l.toArray) := by
  fun_induction splitGo opens closes (fun | x :: _ => if isSep x then 1 else 0 | [] => 0)
    l depth cur out with
  | case1 depth cur out => simp
  | case2 x rest depth cur out hx ih =>
    rw [ih (by simpa [List.foldl, cutStep, hx] using h)]
    simp
  | case3 x rest depth cur out hx hc ih =>
    rw [ih (by simpa [List.foldl, cutStep, hx, hc] using h)]
    simp
  | case4 x rest depth cur out hx hc hsep _ =>
    exfalso
    simp only [Bool.and_eq_true, beq_iff_eq, gt_iff_lt] at hsep
    obtain ⟨hd, hs⟩ := hsep
    have hsx : isSep x = true := by
      cases hxs : isSep x
      · simp [hxs] at hs
      · rfl
    simp [List.foldl, cutStep, hx, hc, hd, hsx, foldl_cutStep_none] at h
  | case5 x rest depth cur out hx hc hsep ih =>
    have hstep : cutStep opens closes isSep (some depth) x = some depth := by
      have : ¬(depth == 0 && isSep x) = true := by
        intro h'
        apply hsep
        simp only [Bool.and_eq_true, beq_iff_eq] at h' ⊢
        exact ⟨h'.1, by simp [h'.2]⟩
      simp [cutStep, hx, hc, this]
    rw [ih (by simpa [List.foldl, hstep] using h)]
    simp

private theorem splitGo_pieces_uncut {α : Type} (opens closes isSep : α → Bool) (l : List α)
    (depth : Nat) (cur : Array α) (out : Array (Array α))
    (hout : ∀ p ∈ out.toList, (p.toList.foldl (cutStep opens closes isSep) (some 0)).isSome)
    (hcur : cur.toList.foldl (cutStep opens closes isSep) (some 0) = some depth) :
    ∀ p ∈ (splitGo opens closes (fun | x :: _ => if isSep x then 1 else 0 | [] => 0)
        l depth cur out).toList,
      (p.toList.foldl (cutStep opens closes isSep) (some 0)).isSome := by
  fun_induction splitGo opens closes (fun | x :: _ => if isSep x then 1 else 0 | [] => 0)
    l depth cur out with
  | case1 depth cur out =>
    intro p hp
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact hout p hp
    · simp [hcur]
  | case2 x _ depth cur out hx ih =>
    exact ih hout (by simp [List.foldl_append, hcur, cutStep, hx])
  | case3 x _ depth cur out hx hc ih =>
    exact ih hout (by simp [List.foldl_append, hcur, cutStep, hx, hc])
  | case4 x rest depth cur out _ _ hsep ih =>
    have hd : depth = 0 := by
      simp only [Bool.and_eq_true, beq_iff_eq] at hsep
      exact hsep.1
    apply ih
    · intro p hp
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · exact hout p hp
      · simp [hcur]
    · simp [hd]
  | case5 x rest depth cur out hx hc hsep ih =>
    apply ih hout
    have : ¬(depth == 0 && isSep x) = true := by
      intro h'
      apply hsep
      simp only [Bool.and_eq_true, beq_iff_eq] at h' ⊢
      exact ⟨h'.1, by simp [h'.2]⟩
    simp only [Array.toList_push, List.foldl_append, hcur, List.foldl_cons, List.foldl_nil,
      cutStep, hx, hc, Bool.false_eq_true, ↓reduceIte, this]

/-- A piece `splitTopAt` cuts holds no separator outside its groups: cut again, it is itself. -/
public theorem splitTopAt_fixed_point {α : Type} (opens closes isSep : α → Bool) (xs : List α) :
    ∀ p ∈ (splitTopAt opens closes isSep xs).toList,
      splitTopAt opens closes isSep p.toList = #[p] := by
  intro p hp
  unfold splitTopAt splitTopWith at hp ⊢
  have h := splitGo_pieces_uncut opens closes isSep xs 0 #[] #[] (by simp) (by simp) p hp
  rw [splitGo_uncut opens closes isSep p.toList 0 #[] #[] h]
  simp

/-- Whether an atom is one `texAtoms` makes before the last: a control symbol, or a character other
than a backslash. -/
private def innerAtom : List Char → Bool
  | [c, _] => c == '\\'
  | [c] => c != '\\'
  | _ => false

/-- Whether atoms are as `texAtoms` makes them: inner atoms, the last possibly a lone backslash. -/
private def atomsAsMade : List (List Char) → Bool
  | [] => true
  | [a] => innerAtom a || a == ['\\']
  | a :: b :: rest => innerAtom a && atomsAsMade (b :: rest)

private theorem atomsAsMade_append (l2 : List (List Char)) (h2 : atomsAsMade l2 = true) :
    ∀ l1 : List (List Char), (∀ a ∈ l1, innerAtom a = true) → atomsAsMade (l1 ++ l2) = true
  | [], _ => h2
  | a :: l1, h1 => by
    have ih := atomsAsMade_append l2 h2 l1 (fun b hb => h1 b (List.mem_cons_of_mem _ hb))
    have ha := h1 a (by simp)
    rw [List.cons_append]
    cases hl : (l1 ++ l2) with
    | nil => simp [atomsAsMade, ha]
    | cons b r => rw [hl] at ih; simp [atomsAsMade, ha, ih]

private theorem atomsAsMade_prefix :
    ∀ l1 l2 : List (List Char), atomsAsMade (l1 ++ l2) = true → atomsAsMade l1 = true
  | [], _, _ => rfl
  | [a], l2, h => by
    cases l2 with
    | nil => simpa using h
    | cons b r =>
      simp only [List.cons_append, List.nil_append, atomsAsMade, Bool.and_eq_true] at h
      simp [atomsAsMade, h.1]
  | a :: b :: l1, l2, h => by
    simp only [List.cons_append, atomsAsMade, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, atomsAsMade_prefix (b :: l1) l2 h.2⟩

private theorem atomsAsMade_suffix :
    ∀ l1 l2 : List (List Char), atomsAsMade (l1 ++ l2) = true → atomsAsMade l2 = true
  | [], _, h => h
  | a :: l1, l2, h => by
    apply atomsAsMade_suffix l1 l2
    rw [List.cons_append] at h
    cases hl : (l1 ++ l2) with
    | nil => rfl
    | cons b r =>
      rw [hl] at h
      simp only [atomsAsMade, Bool.and_eq_true] at h
      exact h.2

private theorem atomsAsMade_intercalate (sep : List (List Char)) :
    ∀ L : List (List (List Char)), atomsAsMade (sep.intercalate L) = true →
      ∀ p ∈ L, atomsAsMade p = true
  | [], _ => by simp
  | [p], h => by simpa [List.intercalate_singleton] using h
  | p :: q :: rest, h => by
    rw [List.intercalate_cons_cons, List.append_assoc] at h
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact atomsAsMade_prefix _ _ h
    · have h' := atomsAsMade_suffix _ _ (atomsAsMade_suffix _ _ h)
      exact atomsAsMade_intercalate sep (q :: rest) h' x (by simpa using hx)

private theorem texAtoms_asMade (cs : List Char) (acc : Array (List Char))
    (h : ∀ a ∈ acc.toList, innerAtom a = true) : atomsAsMade (texAtoms cs acc).toList = true := by
  fun_induction texAtoms cs acc with
  | case1 acc => simpa using atomsAsMade_append [] rfl acc.toList h
  | case2 c _ acc ih =>
    apply ih
    intro a ha
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact h a ha
    · simp [innerAtom]
  | case3 c rest acc hne ih =>
    by_cases hc : c = '\\'
    · subst hc
      cases rest with
      | cons d r => exact absurd (hne d r rfl rfl) id
      | nil =>
        simp only [texAtoms, Array.toList_push]
        exact atomsAsMade_append [['\\']] (by simp [atomsAsMade, innerAtom]) acc.toList h
    · apply ih
      intro a ha
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | rfl
      · exact h a ha
      · simp [innerAtom, hc]

private theorem texAtoms_made (acc : Array (List Char)) :
    ∀ as : List (List Char), atomsAsMade as = true → texAtoms as.flatten acc = acc ++ as.toArray
  | [], _ => by simp [texAtoms]
  | [a], h => by
    match a, h with
    | [c, d], h =>
      simp only [atomsAsMade, innerAtom, Bool.or_eq_true, beq_iff_eq] at h
      rcases h with rfl | h
      · simp [texAtoms]
      · simp at h
    | [c], _ => simp [texAtoms]
    | [], h => simp [atomsAsMade, innerAtom] at h
    | _ :: _ :: _ :: _, h => simp [atomsAsMade, innerAtom] at h
  | a :: b :: rest, h => by
    simp only [atomsAsMade, Bool.and_eq_true] at h
    obtain ⟨ha, hrest⟩ := h
    match a, ha with
    | [c, d], ha =>
      simp only [innerAtom, beq_iff_eq] at ha
      subst ha
      have ih := texAtoms_made (acc.push ['\\', d]) (b :: rest) hrest
      rw [List.flatten_cons] at ih
      simp only [List.flatten_cons, List.cons_append, List.nil_append]
      rw [texAtoms.eq_2, ih]
      simp
    | [c], ha =>
      simp only [innerAtom, bne_iff_ne, ne_eq] at ha
      have ih := texAtoms_made (acc.push [c]) (b :: rest) hrest
      rw [List.flatten_cons] at ih
      simp only [List.flatten_cons, List.cons_append, List.nil_append]
      rw [texAtoms.eq_3 _ _ _ (fun _ _ hc _ => ha hc), ih]
      simp
    | [], ha => simp [innerAtom] at ha
    | _ :: _ :: _ :: _, ha => simp [innerAtom] at ha

/-- An item `split` cuts holds no comma outside braces: split again, it is itself. -/
public theorem split_fixed_point (s : String) : ∀ p ∈ (split s).toList, split p = #[p] := by
  intro p hp
  simp only [split, splitTeX, Array.toList_map, List.mem_map] at hp
  obtain ⟨piece, hpiece, rfl⟩ := hp
  have hjoin := splitTopAt_join_id (· == ['{']) (· == ['}']) [','] (texAtoms s.toList #[]).toList
  have hmade : atomsAsMade piece.toList = true := by
    refine atomsAsMade_intercalate [[',']] _ ?_ piece.toList (List.mem_map_of_mem hpiece)
    rw [hjoin]
    exact texAtoms_asMade s.toList #[] (by simp)
  have hre : texAtoms (piece.toList.flatMap id) #[] = piece := by
    rw [List.flatMap_id, texAtoms_made #[] piece.toList hmade]
    simp
  simp only [split, splitTeX, String.toList_ofList, hre]
  rw [splitTopAt_fixed_point _ _ _ _ piece hpiece]
  simp

end LeanTex.Core.KeyVal
