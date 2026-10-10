module

public import LeanTex.Core.DesignRole
import all LeanTex.Core.DesignRole

/-!
The registry's kernel-checked facts over its shipped table, kept in a leaf so
their evaluations run beside the build rather than in series with every
module the registry's importers compile: every role once (`Role.all_nodup`),
one role per key (`Role.key_inj`, `Role.ofKey?_key_exact`), and CSS names
that never collide (`CssName.ident_inj`, `CssName.ident_internal`).
-/

namespace LeanTex.Core.Ir

/-- **Every role once**: with `Role.all_complete`, a miscount of the registry
is a build failure in both directions. -/
public theorem Role.all_nodup : Role.all.Nodup := by decide +kernel

private theorem inj_of_nodup_map {α β : Type} (f : α → β) :
    ∀ (l : List α), (l.map f).Nodup → ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b
  | [], _, a, ha, _, _, _ => absurd ha List.not_mem_nil
  | x :: xs, hn, a, ha, b, hb, he => by
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · rfl
      · exact absurd (he ▸ List.mem_map_of_mem hb') hn.1
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact absurd (he.symm ▸ List.mem_map_of_mem ha') hn.1
      · exact inj_of_nodup_map f xs hn.2 a ha' b hb' he

private theorem Role.keyed_nodup :
    ((Role.all.filter (·.row.key.isSome)).map (·.row.key)).Nodup := by decide +kernel

public theorem Role.key_inj {a b : Role} {k : String} (ha : a.row.key = some k)
    (hb : b.row.key = some k) : a = b := by
  have mem : ∀ r : Role, r.row.key = some k → r ∈ Role.all.filter (·.row.key.isSome) := by
    intro r hr
    exact List.mem_filter.mpr ⟨List.contains_iff_mem.mp (Role.all_complete r), by simp [hr]⟩
  exact inj_of_nodup_map (·.row.key) _ Role.keyed_nodup a (mem a ha) b (mem b hb)
    (ha.trans hb.symm)

/-- A key reads back the role that declared it. -/
public theorem Role.ofKey?_key_exact (r : Role) (k : String) (h : r.row.key = some k) :
    Role.ofKey? k = some r := by
  unfold Role.ofKey?
  have hmem : r ∈ Role.all := List.contains_iff_mem.mp (Role.all_complete r)
  cases hf : Role.all.find? (·.row.key == some k) with
  | none =>
    have := List.find?_eq_none.mp hf r hmem
    simp [h] at this
  | some r' =>
    have hk := List.find?_some hf
    simp only [beq_iff_eq] at hk
    rw [Role.key_inj hk h]

private def hexValue (c : Char) : Option Nat :=
  ("0123456789abcdef".toList.idxOf? c)

private theorem hexValue_digit : ∀ d < 16, hexValue (hexDigit d) = some d := by
  decide

private def unesc : List Char → Option (List Char)
  | [] => some []
  | c :: rest =>
    if c == '_' then
      match rest with
      | a :: b :: c' :: d :: e :: f :: rest' => do
        let n := (← hexValue a) * 1048576 + (← hexValue b) * 65536 + (← hexValue c') * 4096 +
          (← hexValue d) * 256 + (← hexValue e) * 16 + (← hexValue f)
        (Char.ofNat n :: ·) <$> unesc rest'
      | _ => none
    else if c.isAlphanum then (c :: ·) <$> unesc rest else none

private theorem hex6_value (n : Nat) (h : n < 16777216) :
    (n / 1048576 % 16) * 1048576 + (n / 65536 % 16) * 65536 + (n / 4096 % 16) * 4096 +
      (n / 256 % 16) * 256 + (n / 16 % 16) * 16 + n % 16 = n := by
  omega

private theorem unesc_escChar (c : Char) (rest : List Char) :
    unesc (escChar c ++ rest) = (c :: ·) <$> unesc rest := by
  unfold escChar
  by_cases hc : c.isAlphanum = true
  · have hne : (c == '_') = false := by
      cases h : c == '_'
      · rfl
      · rw [beq_iff_eq] at h
        subst h
        exact absurd hc (by decide)
    simp only [hc, ite_true, List.cons_append, List.nil_append]
    rw [unesc.eq_def]
    simp [hne, hc]
  · have hlt : c.toNat < 16777216 := by
      have hv := c.valid
      simp only [UInt32.isValidChar, Nat.isValidChar] at hv
      show c.val.toNat < 16777216
      omega
    simp only [hc, Bool.false_eq_true, ite_false, hex6, List.cons_append, List.nil_append]
    simp only [unesc, beq_self_eq_true, ite_true,
      hexValue_digit _ (Nat.mod_lt _ (by decide)), Option.bind_eq_bind, Option.bind_some,
      hex6_value c.toNat hlt, Char.ofNat_toNat]

private theorem unesc_escape (l : List Char) : unesc (l.flatMap escChar) = some l := by
  induction l with
  | nil => rfl
  | cons c rest ih =>
    rw [List.flatMap_cons, unesc_escChar, ih]
    rfl

public theorem cssEscape_inj {a b : String} (h : cssEscape a = cssEscape b) : a = b := by
  unfold cssEscape at h
  have h1 := String.ofList_inj.mp h
  have ha := unesc_escape a.toList
  have hb := unesc_escape b.toList
  rw [h1] at ha
  rw [ha] at hb
  exact String.toList_inj.mp (Option.some.inj hb)

private theorem Role.css_distinct :
    (Role.all.map (·.row.css)).Nodup := by decide +kernel

/-- Every role identifier stays clear of the other kinds' prefixes: an
author colour's `c-`, the engine's `box-` and `cap`. -/
private theorem Role.css_clear :
    (Role.all.all fun r =>
      !("c-".toList.isPrefixOf r.row.css.toList) &&
        !("box-".toList.isPrefixOf r.row.css.toList) &&
        !("cap".toList.isPrefixOf r.row.css.toList)) = true := by
  decide +kernel

private theorem Role.css_inj {a b : Role} (h : a.row.css = b.row.css) : a = b :=
  inj_of_nodup_map (·.row.css) _ Role.css_distinct a
    (List.contains_iff_mem.mp (Role.all_complete a)) b
    (List.contains_iff_mem.mp (Role.all_complete b)) h

private theorem Role.css_clear_of (r : Role) :
    ¬ ("c-".toList <+: r.row.css.toList) ∧ ¬ ("box-".toList <+: r.row.css.toList) ∧
      ¬ ("cap".toList <+: r.row.css.toList) := by
  have h := List.all_eq_true.mp Role.css_clear r
    (List.contains_iff_mem.mp (Role.all_complete r))
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  refine ⟨fun hp => ?_, fun hp => ?_, fun hp => ?_⟩
  · have := List.isPrefixOf_iff_prefix.mpr hp; simp_all
  · have := List.isPrefixOf_iff_prefix.mpr hp; simp_all
  · have := List.isPrefixOf_iff_prefix.mpr hp; simp_all

private theorem ident_toList_role (r : Role) :
    (CssName.role r).ident.toList = "ltx-".toList ++ r.row.css.toList := by
  simp [CssName.ident, String.toList_append]

private theorem ident_toList_color (n : String) :
    (CssName.color n).ident.toList = "ltx-".toList ++ ("c-".toList ++ (cssEscape n).toList) := by
  simp [CssName.ident, String.toList_append]

private theorem string_ext {x y : String} (h : x.toList = y.toList) : x = y :=
  String.toList_inj.mp h

/-- **Role, author colour and token names never collide**, the escape
included: a document's `\definecolor{bg}` is `--ltx-c-bg`, never the page's
`--ltx-bg`, and no colour can spell a length token's name. -/
public theorem CssName.ident_inj {a b : CssName} (ha : a.wellFormed) (hb : b.wellFormed)
    (h : a.ident = b.ident) : a = b := by
  have hl := congrArg String.toList h
  have hrole : ∀ (r : Role) (n : String),
      (CssName.role r).ident.toList ≠ (CssName.color n).ident.toList := by
    intro r n e
    rw [ident_toList_role, ident_toList_color, List.append_cancel_left_eq] at e
    exact (Role.css_clear_of r).1 ⟨_, e.symm⟩
  have htok : ∀ (n : String) (c : CssName), '-' ∉ n.toList →
      (∃ t, c.ident.toList = "ltx-".toList ++ t) → n.toList ≠ c.ident.toList := by
    intro n c hn ⟨t, ht⟩ e
    apply hn
    rw [e, ht]
    simp
  have rolePre : ∀ r : Role, ∃ t, (CssName.role r).ident.toList = "ltx-".toList ++ t :=
    fun r => ⟨_, ident_toList_role r⟩
  have colorPre : ∀ n : String, ∃ t, (CssName.color n).ident.toList = "ltx-".toList ++ t :=
    fun n => ⟨_, ident_toList_color n⟩
  cases a with
  | role r =>
    cases b with
    | role r' =>
      rw [ident_toList_role, ident_toList_role, List.append_cancel_left_eq] at hl
      exact congrArg CssName.role (Role.css_inj (string_ext hl))
    | color n => exact absurd hl (hrole r n)
    | token n => exact absurd hl.symm (htok n _ hb (rolePre r))
  | color n =>
    cases b with
    | role r => exact absurd hl.symm (hrole r n)
    | color m =>
      rw [ident_toList_color, ident_toList_color, List.append_cancel_left_eq,
        List.append_cancel_left_eq] at hl
      exact congrArg CssName.color (cssEscape_inj (string_ext hl))
    | token m => exact absurd hl.symm (htok m _ hb (colorPre n))
  | token n =>
    cases b with
    | role r => exact absurd hl (htok n _ ha (rolePre r))
    | color m => exact absurd hl (htok n _ ha (colorPre m))
    | token m => exact congrArg CssName.token h

/-- **No colour name is one of the engine's own layout properties**: those
are `--ltx-box-*` and `--ltx-cap*`. -/
public theorem CssName.ident_internal (a : CssName) (ha : a.wellFormed) :
    ¬ ("ltx-box-".toList <+: a.ident.toList) ∧ ¬ ("ltx-cap".toList <+: a.ident.toList) := by
  have box : "ltx-box-".toList = "ltx-".toList ++ "box-".toList := by decide
  have cap : "ltx-cap".toList = "ltx-".toList ++ "cap".toList := by decide
  cases a with
  | role r =>
    rw [ident_toList_role, box, cap, List.prefix_append_right_inj,
      List.prefix_append_right_inj]
    exact ⟨(Role.css_clear_of r).2.1, (Role.css_clear_of r).2.2⟩
  | color n =>
    rw [ident_toList_color, box, cap, List.prefix_append_right_inj,
      List.prefix_append_right_inj]
    constructor
    · intro hp
      have := (List.prefix_iff_eq_take.mp hp)
      simp at this
    · intro hp
      have := (List.prefix_iff_eq_take.mp hp)
      simp at this
  | token n =>
    simp only [CssName.wellFormed] at ha
    simp only [CssName.ident]
    constructor
    · rintro ⟨t, ht⟩
      apply ha
      rw [← ht]
      simp
    · rintro ⟨t, ht⟩
      apply ha
      rw [← ht]
      simp

/-- A role's key reads back as that role. -/
public theorem ColorRef.ofKey_role (r : Role) (k : String) (h : r.row.key = some k) :
    ColorRef.ofKey k = .role r := by
  simp [ColorRef.ofKey, Role.ofKey?_key_exact r k h]

end LeanTex.Core.Ir
