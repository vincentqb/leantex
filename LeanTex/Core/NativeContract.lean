module

public import LeanTex.Core.Native
public import LeanTex.Core.Decl
import all LeanTex.Core.NativeKey
import all LeanTex.Core.Native
import all LeanTex.Core.Decl
import all LeanTex.Core.KeyVal

/-! Kernel checks of the native settings' carrier: the block a surface writes, the elaborator's entry
reader reads back as exactly its entries. -/

namespace LeanTex.Core.Native

open LeanTex.Core.Decl LeanTex.Core.KeyVal LeanTex.Core.Parse

private theorem dropWhile_self (cs : List Char) (h : cs.head?.any Char.isWhitespace = false) :
    cs.dropWhile Char.isWhitespace = cs := by
  cases cs with
  | nil => rfl
  | cons c rest => simp_all

private theorem trim_self (cs : List Char) (hh : cs.head?.any Char.isWhitespace = false)
    (hl : cs.getLast?.any Char.isWhitespace = false) : trimChars cs = cs := by
  have hr : cs.reverse.head?.any Char.isWhitespace = false := by simpa [List.head?_reverse] using hl
  simp only [trimChars, dropWhile_self cs hh, dropWhile_self _ hr, List.reverse_reverse]

private theorem trim_space (cs : List Char) : trimChars (' ' :: cs) = trimChars cs := by
  simp [trimChars, Char.isWhitespace]

private theorem trim_snoc_space (k : List Char) (hh : k.head?.any Char.isWhitespace = false)
    (hl : k.getLast?.any Char.isWhitespace = false) (hk : k ≠ []) : trimChars (k ++ [' ']) = k := by
  have h1 : (k ++ [' ']).head?.any Char.isWhitespace = false := by
    cases k with
    | nil => exact absurd rfl hk
    | cons c rest => simpa using hh
  have hr : k.reverse.head?.any Char.isWhitespace = false := by simpa [List.head?_reverse] using hl
  simp only [trimChars, dropWhile_self _ h1, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.singleton_append, List.dropWhile_cons, Char.isWhitespace]
  simp [dropWhile_self _ hr]

private theorem quoteAtoms_cons (c : Char) (rest : List Char) (acc : Array (List Char))
    (hc : c ≠ '"') : quoteAtoms (c :: rest) acc = quoteAtoms rest (acc.push [c]) := by
  rw [quoteAtoms]
  exact hc

private theorem quoteAtoms_acc :
    ∀ (cs : List Char) (acc : Array (List Char)), quoteAtoms cs acc = acc ++ quoteAtoms cs #[]
  | [], acc => by simp [quoteAtoms]
  | c :: rest, acc => by
    by_cases hc : c = '"'
    · subst hc
      rw [quoteAtoms, quoteAtoms, quoteAtoms_acc _ (acc.push _), quoteAtoms_acc _ (#[].push _)]
      simp
    · rw [quoteAtoms_cons _ _ _ hc, quoteAtoms_cons _ _ _ hc, quoteAtoms_acc rest (acc.push _),
        quoteAtoms_acc rest (#[].push _)]
      simp
termination_by cs => cs.length
decreasing_by all_goals simp only [List.length_cons, List.length_drop]; omega

private theorem quote_closed (rest : List Char)
    (h : (rest.takeWhile (· != '"')).length < rest.length) :
    rest = rest.takeWhile (· != '"') ++ '"' :: rest.drop ((rest.takeWhile (· != '"')).length + 1) := by
  have hs := List.takeWhile_append_dropWhile (p := (· != '"')) (l := rest)
  have hne : rest.dropWhile (· != '"') ≠ [] := by
    intro he
    have hl := congrArg List.length hs
    rw [he, List.append_nil] at hl
    omega
  have hhead := List.head_dropWhile_not (· != '"') hne
  obtain ⟨x, d', hxd⟩ := List.exists_cons_of_ne_nil hne
  have hx : x = '"' := by simpa [hxd] using hhead
  rw [hxd, hx] at hs
  generalize rest.takeWhile (· != '"') = t at hs ⊢
  subst hs
  simp

private theorem quote_open (rest : List Char)
    (h : ¬ (rest.takeWhile (· != '"')).length < rest.length) :
    rest.takeWhile (· != '"') = rest := by
  have hs := List.takeWhile_append_dropWhile (p := (· != '"')) (l := rest)
  have hl := congrArg List.length hs
  rw [List.length_append] at hl
  have hd : rest.dropWhile (· != '"') = [] := List.eq_nil_of_length_eq_zero (by omega)
  rw [hd, List.append_nil] at hs
  exact hs

private theorem quoteAtoms_flatten :
    ∀ (cs : List Char) (acc : Array (List Char)),
      (quoteAtoms cs acc).toList.flatten = acc.toList.flatten ++ cs
  | [], acc => by simp [quoteAtoms]
  | c :: rest, acc => by
    by_cases hc : c = '"'
    · subst hc
      rw [quoteAtoms, quoteAtoms_flatten]
      simp only [Array.toList_push, List.flatten_append, List.flatten_cons, List.flatten_nil,
        List.append_nil, List.append_assoc, List.cons_append]
      congr 2
      split
      · next hlt =>
        rw [List.singleton_append]
        exact (quote_closed rest hlt).symm
      · next hge =>
        rw [List.nil_append, quote_open rest hge, List.drop_eq_nil_of_le (by omega), List.append_nil]
    · rw [quoteAtoms_cons _ _ _ hc, quoteAtoms_flatten]
      simp
termination_by cs => cs.length
decreasing_by all_goals simp only [List.length_cons, List.length_drop]; omega

private theorem closedAtom_quote (rest : List Char)
    (h : closedAtom ('"' :: rest.takeWhile (· != '"') ++
      (if (rest.takeWhile (· != '"')).length < rest.length then ['"'] else [])) = true) :
    (rest.takeWhile (· != '"')).length < rest.length := by
  refine Classical.byContradiction fun hge => ?_
  rw [ite_eq_right hge, List.append_nil] at h
  have hall := List.all_takeWhile (p := (· != '"')) (l := rest)
  generalize rest.takeWhile (· != '"') = t at h hall
  cases t with
  | nil => simp [closedAtom] at h
  | cons y ys =>
    simp only [closedAtom, List.head?_cons, bne_self_eq_false, List.length_cons,
      Bool.false_or, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨_, hl⟩ := h
    rw [List.getLast?_cons_cons] at hl
    have hmem := List.mem_of_getLast? hl
    simp only [List.all_eq_true] at hall
    simpa using hall _ hmem

private theorem quoteAtoms_append :
    ∀ (a b : List Char) (acc : Array (List Char)), (quoteAtoms a #[]).toList.all closedAtom = true →
      quoteAtoms (a ++ b) acc = quoteAtoms b (quoteAtoms a acc)
  | [], b, acc, _ => by simp [quoteAtoms]
  | c :: rest, b, acc, h => by
    by_cases hc : c = '"'
    · subst hc
      rw [quoteAtoms, quoteAtoms_acc] at h
      simp only [Array.toList_append, Array.toList_push, List.all_append, List.all_cons,
        List.all_nil, Bool.and_true, Bool.and_eq_true, true_and] at h
      obtain ⟨hatom, htail⟩ := h
      have hlt := closedAtom_quote rest hatom
      have ht : (rest ++ b).takeWhile (· != '"') = rest.takeWhile (· != '"') := by
        rw [List.takeWhile_append, ite_eq_right (by omega)]
      rw [List.cons_append, quoteAtoms, quoteAtoms, ht, ite_eq_left hlt,
        ite_eq_left (by rw [List.length_append]; omega), List.drop_append_of_le_length (by omega)]
      exact quoteAtoms_append _ b _ htail
    · rw [quoteAtoms_cons _ _ _ hc, quoteAtoms_acc] at h
      simp only [Array.toList_append, Array.toList_push, List.all_append, List.all_cons,
        List.all_nil, Bool.and_true, Bool.and_eq_true, true_and] at h
      rw [List.cons_append, quoteAtoms_cons _ _ _ hc, quoteAtoms_cons _ _ _ hc]
      exact quoteAtoms_append rest b _ h.2
termination_by a => a.length
decreasing_by all_goals simp only [List.length_cons, List.length_drop]; omega

/-- The splitter's separator length for a single-element separator. -/
private abbrev sepOne {α : Type} (isSep : α → Bool) : List α → Nat :=
  fun | x :: _ => if isSep x then 1 else 0 | [] => 0

private theorem splitGo_append {α : Type} (opens closes isSep : α → Bool) :
    ∀ (l rest : List α) (d d' : Nat) (cur : Array α) (out : Array (Array α)),
      l.foldl (cutStep opens closes isSep) (some d) = some d' →
      splitGo opens closes (sepOne isSep) (l ++ rest) d cur out =
        splitGo opens closes (sepOne isSep) rest d' (cur ++ l.toArray) out
  | [], rest, d, d', cur, out, h => by
    simp only [List.foldl_nil, Option.some.injEq] at h
    subst h
    simp
  | x :: l, rest, d, d', cur, out, h => by
    rw [List.cons_append, splitGo]
    by_cases ho : opens x = true
    · rw [ite_eq_left ho, splitGo_append opens closes isSep l rest (d + 1) d' (cur.push x) out
        (by simpa [List.foldl, cutStep, ho] using h)]
      simp
    · by_cases hc : closes x = true
      · rw [ite_eq_right ho, ite_eq_left hc, splitGo_append opens closes isSep l rest (d - 1) d'
          (cur.push x) out (by simpa [List.foldl, cutStep, ho, hc] using h)]
        simp
      · have hs : ¬ (d == 0 && sepOne isSep (x :: (l ++ rest)) > 0) = true := by
          intro hh
          simp only [sepOne, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hh
          obtain ⟨hd, hx⟩ := hh
          have hsx : isSep x = true := by
            cases hxs : isSep x
            · simp [hxs] at hx
            · rfl
          simp [List.foldl, cutStep, ho, hc, hd, hsx, foldl_cutStep_none] at h
        have hstep : cutStep opens closes isSep (some d) x = some d := by
          have : ¬(d == 0 && isSep x) = true := by
            intro h'
            apply hs
            simp only [Bool.and_eq_true, beq_iff_eq] at h' ⊢
            exact ⟨h'.1, by simp [sepOne, h'.2]⟩
          simp [cutStep, ho, hc, this]
        rw [ite_eq_right ho, ite_eq_right hc, ite_eq_right hs, splitGo_append opens closes isSep l rest d
          d' (cur.push x) out (by simpa [List.foldl, hstep] using h)]
        simp

private theorem splitTopAt_sepOne {α : Type} (opens closes isSep : α → Bool) (xs : List α) :
    splitTopAt opens closes isSep xs = splitGo opens closes (sepOne isSep) xs 0 #[] #[] := rfl

private theorem splitGo_sep {α : Type} (opens closes isSep : α → Bool) (x : α) (rest : List α)
    (cur : Array α) (out : Array (Array α)) (hs : isSep x = true) (ho : opens x = false)
    (hc : closes x = false) :
    splitGo opens closes (sepOne isSep) (x :: rest) 0 cur out =
      splitGo opens closes (sepOne isSep) rest 0 #[] (out.push cur) := by
  rw [splitGo]
  simp [ho, hc, hs, sepOne]

private theorem quoteAtoms_plain (p rest : List Char) :
    ∀ (acc : Array (List Char)), (∀ c ∈ p, c ≠ '"') →
      quoteAtoms (p ++ rest) acc = quoteAtoms rest (acc ++ (p.map fun c => [c]).toArray) := by
  induction p with
  | nil => intro acc _; simp
  | cons c p ih =>
    intro acc h
    rw [List.cons_append, quoteAtoms_cons _ _ _ (h c List.mem_cons_self),
      ih _ (fun d hd => h d (List.mem_cons_of_mem _ hd))]
    simp

private theorem fold_plain (p : List Char) (d : Nat)
    (h : ∀ c ∈ p, c ≠ '{' ∧ c ≠ '[' ∧ c ≠ '(' ∧ c ≠ '}' ∧ c ≠ ']' ∧ c ≠ ')' ∧ c ≠ ',') :
    (p.map fun c => [c]).foldl (cutStep entryOpens entryCloses (· == [','])) (some d) = some d := by
  induction p with
  | nil => rfl
  | cons c p ih =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h c List.mem_cons_self
    simp only [List.map_cons, List.foldl_cons]
    have hstep : cutStep entryOpens entryCloses (· == [',']) (some d) [c] = some d := by
      simp [cutStep, entryOpens, entryCloses, h1, h2, h3, h4, h5, h6, h7]
    rw [hstep]
    exact ih (fun e he => h e (List.mem_cons_of_mem _ he))

/-- An entry the splitter keeps whole: its atoms all closed and its depth back at zero. -/
private def Good (e : List Char) : Prop :=
  (quoteAtoms e #[]).toList.all closedAtom = true ∧
    (quoteAtoms e #[]).toList.foldl (cutStep entryOpens entryCloses (· == [','])) (some 0) = some 0

private theorem splitGo_entries :
    ∀ (es : List String) (cur : Array (List Char)) (out : Array (Array (List Char))),
      es ≠ [] → (∀ e ∈ es, Good e.toList) →
      splitGo entryOpens entryCloses (sepOne (· == [',']))
          (quoteAtoms (", ".intercalate es).toList #[]).toList 0 cur out =
        (out.push (cur ++ quoteAtoms (es.headD "").toList #[])) ++
          (es.tail.map fun e => #[[' ']] ++ quoteAtoms e.toList #[]).toArray
  | [], _, _, h, _ => absurd rfl h
  | [e], cur, out, _, hg => by
    obtain ⟨_, hfold⟩ := hg e List.mem_cons_self
    rw [String.intercalate_singleton]
    have := splitGo_append entryOpens entryCloses (· == [',']) (quoteAtoms e.toList #[]).toList [] 0 0
      cur out hfold
    rw [List.append_nil] at this
    rw [this, splitGo]
    simp
  | e :: e' :: rest, cur, out, _, hg => by
    obtain ⟨hclosed, hfold⟩ := hg e List.mem_cons_self
    have hsep : (", ").toList = [',', ' '] := rfl
    rw [String.intercalate_cons_cons, String.toList_append, String.toList_append, List.append_assoc,
      quoteAtoms_append _ _ _ hclosed, quoteAtoms_acc _ (quoteAtoms _ #[]), hsep, List.cons_append,
      List.cons_append, List.nil_append, quoteAtoms_cons _ _ _ (by decide),
      quoteAtoms_cons _ _ _ (by decide), quoteAtoms_acc _ ((#[].push _).push _)]
    simp only [Array.toList_append, Array.toList_push, List.nil_append, List.cons_append]
    rw [splitGo_append _ _ _ _ _ 0 0 cur out hfold, splitGo_sep _ _ _ _ _ _ _ rfl rfl rfl]
    rw [show ([' '] :: (quoteAtoms (", ".intercalate (e' :: rest)).toList #[]).toList) =
        [[' ']] ++ (quoteAtoms (", ".intercalate (e' :: rest)).toList #[]).toList from rfl,
      splitGo_append _ _ _ _ _ 0 0 _ _ rfl,
      splitGo_entries (e' :: rest) _ _ (List.cons_ne_nil _ _)
        (fun x hx => hg x (List.mem_cons_of_mem _ hx))]
    simp
termination_by es => es.length

/-- An entry's piece read back: its atoms flattened and trimmed, the entry itself. -/
private def Trimmed (e : String) : Prop := trimChars e.toList = e.toList ∧ e.toList ≠ []

private theorem pieces_read (rest : List String) (h : ∀ e ∈ rest, Trimmed e) :
    (rest.map fun e => #[[' ']] ++ quoteAtoms e.toList #[]).filterMap (fun piece =>
        let t := trimChars (piece.toList.flatMap id)
        if t.isEmpty then none else some (String.ofList t)) = rest := by
  induction rest with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨htrim, hne⟩ := h e List.mem_cons_self
    have hflat : (#[[' ']] ++ quoteAtoms e.toList #[]).toList.flatMap id = ' ' :: e.toList := by
      have := quoteAtoms_flatten e.toList #[]
      simp only [List.flatten_nil, List.nil_append] at this
      simp [List.flatMap_id, this]
    have hne' : e.toList.isEmpty = false := List.isEmpty_eq_false_iff.mpr hne
    simp only [List.map_cons, List.filterMap_cons, hflat, trim_space, htrim, hne',
      Bool.false_eq_true, ↓reduceIte, String.ofList_toList,
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

private theorem splitEntries_join (es : List String) (hg : ∀ e ∈ es, Good e.toList)
    (ht : ∀ e ∈ es, Trimmed e) : splitEntries (", ".intercalate es) = es := by
  cases es with
  | nil =>
    unfold splitEntries
    rw [String.intercalate_nil, splitTopAt_sepOne]
    simp [quoteAtoms, splitGo, trimChars]
  | cons e rest =>
    obtain ⟨htrim, hne⟩ := ht e List.mem_cons_self
    unfold splitEntries
    rw [splitTopAt_sepOne, splitGo_entries (e :: rest) #[] #[] (List.cons_ne_nil _ _) hg]
    have hpieces : ((#[] : Array (Array (List Char))).push (#[] ++ quoteAtoms e.toList #[]) ++
        (rest.map fun x => #[[' ']] ++ quoteAtoms x.toList #[]).toArray).toList =
        (quoteAtoms e.toList #[]) :: rest.map fun x => #[[' ']] ++ quoteAtoms x.toList #[] := by
      simp
    have hflat : (quoteAtoms e.toList #[]).toList.flatMap id = e.toList := by
      have := quoteAtoms_flatten e.toList #[]
      simp only [List.flatten_nil, List.nil_append] at this
      simp [List.flatMap_id, this]
    have hne' : e.toList.isEmpty = false := List.isEmpty_eq_false_iff.mpr hne
    simp only [List.headD_cons, List.tail_cons]
    rw [hpieces, List.filterMap_cons, pieces_read rest (fun x hx => ht x (List.mem_cons_of_mem _ hx))]
    simp only [hflat, htrim, hne', Bool.false_eq_true, ↓reduceIte, String.ofList_toList]

private theorem plainChar_facts (c : Char) (h : plainChar c = true) :
    c.isWhitespace = false ∧ c ≠ '=' ∧ c ≠ '"' ∧ (c ≠ '{' ∧ c ≠ '[' ∧ c ≠ '(' ∧ c ≠ '}' ∧ c ≠ ']' ∧
      c ≠ ')' ∧ c ≠ ',') := by
  simp only [plainChar, Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hw, he⟩, hcomma⟩, hq⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨hw, he, hq, h1, h3, h5, h2, h4, h6, hcomma⟩

private theorem entry_facts (k v : String) (hk : plainKey k = true) (hv : wholeValue v = true) :
    Good (k ++ " = " ++ v).toList ∧ Trimmed (k ++ " = " ++ v) ∧ entryOf (k ++ " = " ++ v) = (k, v) := by
  simp only [plainKey, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true] at hk
  obtain ⟨hkne, hkc⟩ := hk
  simp only [wholeValue, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    beq_iff_eq] at hv
  obtain ⟨⟨⟨⟨hvne, hvh⟩, hvl⟩, hvc⟩, hvf⟩ := hv
  have heq : (" = ").toList = [' ', '=', ' '] := rfl
  have htext : (k ++ " = " ++ v).toList = (k.toList ++ [' ', '=', ' ']) ++ v.toList := by
    rw [String.toList_append, String.toList_append, heq]
  have hp : ∀ c ∈ k.toList ++ [' ', '=', ' '], c ≠ '"' ∧ (c ≠ '{' ∧ c ≠ '[' ∧ c ≠ '(' ∧ c ≠ '}' ∧
      c ≠ ']' ∧ c ≠ ')' ∧ c ≠ ',') := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · have := plainChar_facts c (hkc c hc)
      exact ⟨this.2.2.1, this.2.2.2⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> decide
  have hatoms : quoteAtoms ((k.toList ++ [' ', '=', ' ']) ++ v.toList) #[] =
      ((k.toList ++ [' ', '=', ' ']).map fun c => [c]).toArray ++ quoteAtoms v.toList #[] := by
    rw [quoteAtoms_plain _ _ _ (fun c hc => (hp c hc).1), quoteAtoms_acc]
    simp
  have hkh : k.toList.head?.any Char.isWhitespace = false := by
    obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil hkne
    have := plainChar_facts c (hkc c (by rw [hcs]; exact List.mem_cons_self))
    simp [hcs, this.1]
  have hkl : k.toList.getLast?.any Char.isWhitespace = false := by
    have hmem := List.getLast_mem hkne
    have := plainChar_facts _ (hkc _ hmem)
    simp [List.getLast?_eq_some_getLast hkne, this.1]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [htext, hatoms]
    simp only [Array.toList_append, List.all_append, Bool.and_eq_true]
    refine ⟨?_, hvc⟩
    simp only [List.all_map, List.all_eq_true, Function.comp_apply]
    intro c hc
    simp [closedAtom, (hp c hc).1]
  · rw [htext, hatoms]
    simp only [Array.toList_append, List.foldl_append]
    rw [fold_plain _ 0 (fun c hc => (hp c hc).2)]
    exact hvf
  · rw [htext]
    apply trim_self
    · obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil hkne
      have := plainChar_facts c (hkc c (by rw [hcs]; exact List.mem_cons_self))
      simp [hcs, this.1]
    · obtain ⟨c, hcl⟩ : ∃ c, v.toList.getLast? = some c := by
        cases h : v.toList.getLast? with
        | none => simp_all
        | some c => exact ⟨c, rfl⟩
      rw [List.getLast?_append, hcl]
      simpa [hcl] using hvl
  · rw [htext]
    simp [hkne]
  · have hcut : KeyVal.cutAt '=' (k ++ " = " ++ v).toList = (k.toList ++ [' '], some (' ' :: v.toList)) := by
      rw [htext, List.append_assoc, KeyVal.cutAt_append '=' _ _ (fun hm => (plainChar_facts _ (hkc _ hm)).2.1 rfl)]
      simp [KeyVal.cutAt]
    simp only [entryOf, hcut, Option.getD_some, trim_snoc_space _ hkh hkl hkne, trim_space,
      trim_self _ (by simpa using hvh) (by simpa using hvl), String.ofList_toList]

private theorem kept_carried (s : Setting) : ∀ kv ∈ s.kept.pairs, Setting.carried kv = true := by
  cases s with
  | page es =>
    intro kv hkv
    simp only [Setting.kept, Setting.pairs, List.mem_map, Array.mem_toList_iff, Array.mem_filter] at hkv
    obtain ⟨⟨k, v⟩, ⟨_, hc⟩, rfl⟩ := hkv
    exact hc
  | tokens es =>
    intro kv hkv
    simp only [Setting.kept, Setting.pairs, Array.mem_toList_iff, Array.mem_filter] at hkv
    exact hkv.2

/-- A setting's block reads back, entry by entry, as exactly its kept entries. -/
public theorem body_read_exact (s : Setting) :
    (splitEntries s.kept.body).map entryOf = s.kept.pairs := by
  have hc := kept_carried s
  have hfacts : ∀ kv ∈ s.kept.pairs, Good (kv.1 ++ " = " ++ kv.2).toList ∧
      Trimmed (kv.1 ++ " = " ++ kv.2) ∧ entryOf (kv.1 ++ " = " ++ kv.2) = kv := by
    intro kv hkv
    have := hc kv hkv
    simp only [Setting.carried, Bool.and_eq_true] at this
    exact entry_facts kv.1 kv.2 this.1 this.2
  unfold Setting.body
  rw [splitEntries_join]
  · rw [List.map_map, List.map_congr_left (g := id) (fun ⟨k, v⟩ hkv => (hfacts (k, v) hkv).2.2),
      List.map_id]
  · intro e he
    obtain ⟨⟨k, v⟩, hkv, rfl⟩ := List.mem_map.mp he
    exact (hfacts (k, v) hkv).1
  · intro e he
    obtain ⟨⟨k, v⟩, hkv, rfl⟩ := List.mem_map.mp he
    exact (hfacts (k, v) hkv).2.1

private theorem kept_head (s : Setting) : s.kept.head = s.head := by
  cases s <;> rfl

/-- A setting's carrier is its control and a group whose block, the one its translation note names,
the declaration reader reads back entry by entry as exactly the setting's kept entries. -/
public theorem render_parse_exact (s : Setting) (pos : Pos) :
    ∃ body, s.raws pos = #[.ctrl s.head pos, .group body pos] ∧
      s.kept.render = "\\" ++ s.head ++ "{ " ++ declSrc body ++ " }" ∧
      (splitEntries (declSrc body)).map entryOf = s.kept.pairs :=
  ⟨if s.kept.body.isEmpty then #[] else #[.word s.kept.body pos], rfl, by
    have hsrc : declSrc (if s.kept.body.isEmpty then #[] else #[.word s.kept.body pos]) =
        s.kept.body := by
      split
      · next h => simp [declSrc, String.isEmpty_iff.mp h]
      · rfl
    exact ⟨by rw [hsrc]; simp [Setting.render, kept_head], by rw [hsrc]; exact body_read_exact s⟩⟩

/-- Every page key reads back from its name. -/
public theorem PageKey.ofName_name (k : PageKey) : PageKey.ofName? k.name = some k := by
  cases k <;> decide +kernel

/-- Every metadata key reads back from its name. -/
public theorem MetaKey.ofName_name (k : MetaKey) : MetaKey.ofName? k.name = some k := by
  cases k <;> decide +kernel

end LeanTex.Core.Native
