module

/-! Hexadecimal digits: the one reader and the one speller of every hex field the engine reads or
writes. -/

namespace LeanTex.Core.Hex

/-- A hexadecimal digit's value from its code point, either case. -/
@[expose] public def val? (c : Nat) : Option Nat :=
  if 48 ≤ c && c ≤ 57 then some (c - 48)
  else if 65 ≤ c && c ≤ 70 then some (c - 55)
  else if 97 ≤ c && c ≤ 102 then some (c - 87)
  else none

/-- A hexadecimal digit's value, either case. -/
@[expose] public def digit? (c : Char) : Option Nat := val? c.toNat

/-- Hexadecimal digits as a number, most significant first. -/
public def value? (cs : List Char) : Option Nat :=
  cs.foldl (fun acc c => acc.bind fun n => (digit? c).map (n * 16 + ·)) (some 0)

/-- The hexadecimal digit of `n`'s low four bits. -/
@[expose] public def spell (upper : Bool) (n : Nat) : Char :=
  let d := n % 16
  if d < 10 then Char.ofNat (48 + d) else Char.ofNat ((if upper then 55 else 87) + d)

/-- `n`'s last `width` hexadecimal digits, most significant first. -/
@[expose] public def digitList (upper : Bool) : Nat → Nat → List Char
  | 0, _ => []
  | w + 1, n => digitList upper w (n / 16) ++ [spell upper n]

/-- `n`'s last `width` hexadecimal digits, most significant first. -/
@[expose] public def digits (upper : Bool) (width n : Nat) : String :=
  String.ofList (digitList upper width n)

/-- A byte as two hexadecimal digits. -/
@[expose] public def byte (upper : Bool) (b : UInt8) : String := digits upper 2 b.toNat

/-- A code point as Unicode spells it after `U+`: four upper-case digits, more where it needs
them. -/
public def scalar (n : Nat) : String :=
  digits true (if n < 0x10000 then 4 else if n < 0x100000 then 5 else 6) n

private theorem val?_spell_digit : ∀ u : Bool, ∀ d < 16, val? (spell u d).toNat = some d := by
  decide

public theorem val?_spell (u : Bool) (n : Nat) : val? (spell u n).toNat = some (n % 16) := by
  have h : spell u n = spell u (n % 16) := by simp only [spell, Nat.mod_mod]
  rw [h]
  exact val?_spell_digit u (n % 16) (Nat.mod_lt _ (by decide))

private theorem spell_inj_digit :
    ∀ u : Bool, ∀ i < 16, ∀ j < 16, spell u i = spell u j → i = j := by
  decide

public theorem spell_mod (u : Bool) (n : Nat) : spell u n = spell u (n % 16) := by
  simp only [spell, Nat.mod_mod]

public theorem spell_eq_mod {u : Bool} {a b : Nat} (h : spell u a = spell u b) :
    a % 16 = b % 16 := by
  rw [spell_mod u a, spell_mod u b] at h
  exact spell_inj_digit u _ (Nat.mod_lt _ (by decide)) _ (Nat.mod_lt _ (by decide)) h

private theorem spell_ascii_digit : ∀ u : Bool, ∀ d < 16, (spell u d).toNat < 128 := by
  decide

public theorem spell_ascii (u : Bool) (n : Nat) : (spell u n).toNat < 128 := by
  rw [spell_mod]
  exact spell_ascii_digit u _ (Nat.mod_lt _ (by decide))

public theorem mem_digitList {u : Bool} :
    ∀ {w n : Nat} {c : Char}, c ∈ digitList u w n → ∃ k, c = spell u k
  | 0, _, _, h => by simp [digitList] at h
  | w + 1, n, c, h => by
    simp only [digitList, List.mem_append, List.mem_singleton] at h
    rcases h with h | rfl
    · exact mem_digitList h
    · exact ⟨n, rfl⟩

public theorem byte_inj (u : Bool) (a b : UInt8) (h : byte u a = byte u b) : a = b := by
  have hl := congrArg String.toList h
  simp only [byte, digits, digitList, String.toList_ofList, List.nil_append,
    List.singleton_append, List.cons.injEq, and_true] at hl
  have ha : a.toNat < 256 := a.toNat_lt
  have hb : b.toNat < 256 := b.toNat_lt
  have e1 := spell_eq_mod hl.1
  have e2 := spell_eq_mod hl.2
  exact UInt8.toNat_inj.mp (by omega)

end LeanTex.Core.Hex
