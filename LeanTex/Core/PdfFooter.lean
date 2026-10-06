import LeanTex.Core.PdfReadProof

namespace LeanTex.Core.PdfRead

open PdfLex

/-! Recovery of the actual writer's `startxref` footer. The scan is the
reader's backwards, bounded range loop. Its invariant tracks the first
hit in scan order; the decimal parser reads the footer's own bytes. -/

private def scanStep (b : ByteArray) (f : Nat → Nat) (k : Nat)
    (s : Option Nat) : Id (ForInStep (Option Nat)) :=
  if (keywordAt b (f k) "startxref").isSome then pure (.done (some (f k)))
  else pure (.yield s)

private theorem scan_hit (b : ByteArray) (f : Nat → Nat) (count start target : Nat)
    (ht : start ≤ target) (hb : target < start+count)
    (hit : (keywordAt b (f target) "startxref").isSome = true)
    (miss : ∀ k, start ≤ k → k < target →
      keywordAt b (f k) "startxref" = none) :
    (forIn (List.range' start count) none (scanStep b f) : Id (Option Nat)).run =
      some (f target) := by
  induction count generalizing start with
  | zero => omega
  | succ n ih =>
    simp only [List.range'_succ, List.forIn_cons]
    by_cases hs : start = target
    · subst start
      simp [scanStep, hit]
    · have hmiss := miss start (Nat.le_refl _) (by omega)
      simp only [scanStep, hmiss, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        pure, bind, Id.run]
      exact ih (start+1) (by omega) (by omega) (fun k hk hkt => miss k (by omega) hkt)

private def findStartxref (b : ByteArray) : Option Nat := Id.run do
  let lo := b.size - min b.size 2048
  let mut sx : Option Nat := none
  for k in [lo:b.size] do
    let i := lo + (b.size - 1 - k)
    if (keywordAt b i "startxref").isSome then
      sx := some i
      break
  return sx

private theorem findStartxref_last_exact (b : ByteArray) (pos : Nat)
    (hl : b.size-min b.size 2048 ≤ pos) (hp : pos < b.size)
    (hit : (keywordAt b pos "startxref").isSome = true)
    (miss : ∀ i, pos < i → i < b.size → keywordAt b i "startxref" = none) :
    findStartxref b = some pos := by
  let lo := b.size - min b.size 2048
  let target := lo+(b.size-1-pos)
  let f := fun k => lo+(b.size-1-k)
  have hlo : lo ≤ pos := hl
  have ht : lo ≤ target := by dsimp only [target]; omega
  have hb : target < b.size := by dsimp only [target]; omega
  have hft : f target = pos := by dsimp only [f, target]; omega
  have hhit : (keywordAt b (f target) "startxref").isSome = true := by simpa [hft] using hit
  have hmiss : ∀ k, lo ≤ k → k < target → keywordAt b (f k) "startxref" = none := by
    intro k hk hkt
    apply miss
    · dsimp only [f, target] at *; omega
    · dsimp only [f, target] at *; omega
  have law := scan_hit b f (b.size-lo) lo target ht (by omega) hhit hmiss
  rw [hft] at law
  unfold findStartxref
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.add_sub_cancel, Nat.div_one]
  change (forIn (List.range' lo (b.size-lo)) none (scanStep b f) : Id (Option Nat)).run = _
  exact law

private theorem nat_size (n : Nat) (hn : n < 256^4) :
    (toString n).toUTF8.size ≤ 10 := by
  rw [numeric_size _ (nat_numeric n), Nat.toString_eq_ofList_toDigits,
    String.toList_ofList]
  exact (Nat.length_toDigits_le_iff (by decide : 1 < 10) (by decide : 0 < 10)).2
    (by omega)

private theorem findStartxref_footer_exact (pre : ByteArray) (n : Nat) (hn : n < 256^4) :
    findStartxref (pre ++ (s!"startxref\n{n}\n%%EOF\n").toUTF8) = some pre.size := by
  have hf : (s!"startxref\n{n}\n%%EOF\n").toUTF8 =
      "startxref\n".toUTF8 ++ (toString n).toUTF8 ++ "\n%%EOF\n".toUTF8 := rfl
  let digits := octets (toString n).toUTF8
  have ndigits : ∀ c ∈ digits, c ≠ 115 := by
    intro c hc
    dsimp only [digits] at hc
    rw [numeric_octets _ (nat_numeric n)] at hc
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
    have hdigit := Char.isDigit_iff_toNat.mp (Number.nat_chars n d hd)
    change 48 ≤ d.toNat ∧ d.toNat ≤ 57 at hdigit
    omega
  have no_s : ∀ c ∈ ([116,97,114,116,120,114,101,102,10] ++ digits ++ [10,37,37,69,79,70,10]),
      c ≠ 115 := by
    intro c hc
    simp only [List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      omega
    · exact ndigits c hc
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      omega
  have hs := PdfLex.Span.of_bytes pre (s!"startxref\n{n}\n%%EOF\n").toUTF8 ByteArray.empty
  change PdfLex.Span (pre ++ (s!"startxref\n{n}\n%%EOF\n").toUTF8 ++ ByteArray.empty)
    pre.size (octets (s!"startxref\n{n}\n%%EOF\n").toUTF8) at hs
  simp only [ByteArray.append_empty, hf, octets_append] at hs
  have hfull : PdfLex.Span (pre ++ (s!"startxref\n{n}\n%%EOF\n").toUTF8) pre.size
      (115 :: ([116,97,114,116,120,114,101,102,10] ++ digits ++ [10,37,37,69,79,70,10])) := by
    rw [hf]
    simpa only [digits, show octets "startxref\n".toUTF8 =
      [115,116,97,114,116,120,114,101,102,10] from rfl,
      show octets "\n%%EOF\n".toUTF8 = [10,37,37,69,79,70,10] from rfl,
      List.cons_append, List.nil_append] using hs
  have size : (pre ++ (s!"startxref\n{n}\n%%EOF\n").toUTF8).size =
      pre.size + 17 + digits.length := by
    simp only [hf, ByteArray.size_append, digits, octets_length]
    change pre.size+(10+(toString n).toUTF8.size+7) = _
    omega
  have hlen : digits.length ≤ 10 := by simpa [digits] using nat_size n hn
  apply findStartxref_last_exact
  · rw [size]
    omega
  · rw [size]
    omega
  · have hk : PdfLex.Span (pre ++ (s!"startxref\n{n}\n%%EOF\n").toUTF8) pre.size
        (octets "startxref".toUTF8) := by
      have hs' : PdfLex.Span (pre ++ (s!"startxref\n{n}\n%%EOF\n").toUTF8) pre.size
          ([115,116,97,114,116,120,114,101,102] ++
            10 :: (digits ++ [10,37,37,69,79,70,10])) := by
        simpa only [List.append_assoc, List.cons_append, List.nil_append] using hfull
      exact hs'.append_left
    have he : at? (pre ++ (s!"startxref\n{n}\n%%EOF\n").toUTF8) (pre.size+9) = 10 := by
      exact hfull.byte 9 (by simp)
    rw [keywordAt_exact hk (Or.inr (Or.inl (by
      change isWs (at? _ (pre.size+9)) = true
      rw [he]; rfl)))]
    rfl
  · intro i hi hib
    apply keywordAt_ne (by decide)
    change at? _ i ≠ 115
    have hj : i-(pre.size+1) <
        ([116,97,114,116,120,114,101,102,10] ++ digits ++ [10,37,37,69,79,70,10]).length := by
      rw [size] at hib
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have he := hfull.tail.byte (i-(pre.size+1)) hj
    rw [show pre.size+1+(i-(pre.size+1))=i by omega] at he
    rw [he]
    exact no_s _ (List.getElem_mem hj)

/-- Discover the last `startxref` in the PDF tail and read its byte offset.
The 2048-byte search window is the reader's existing bounded policy. -/
def readStartxref (b : ByteArray) : Except String Nat := do
  let some pos := findStartxref b
    | throw "malformed PDF: no startxref"
  let some (off, _) := parseUInt b (skipWs b (pos+9))
    | throw "malformed PDF: unreadable startxref offset"
  return off

private theorem footer_number (pre : ByteArray) (n : Nat) :
    let b := pre ++ (s!"startxref\n{n}\n%%EOF\n").toUTF8
    parseUInt b (skipWs b (pre.size+9)) =
      some (n,pre.size+10+(toString n).toUTF8.size) := by
  dsimp only
  have hf : pre ++ (s!"startxref\n{n}\n%%EOF\n").toUTF8 =
      pre ++ "startxref\n".toUTF8 ++ (toString n).toUTF8 ++ "\n%%EOF\n".toUTF8 := by
    simp only [utf8_append, toString]
    simp only [ByteArray.append_assoc]
  rw [hf]
  let b := pre ++ "startxref\n".toUTF8 ++ (toString n).toUTF8 ++ "\n%%EOF\n".toUTF8
  have hn : PdfLex.Span b (pre.size+10) (octets (toString n).toUTF8) := by
    have h := PdfLex.Span.of_bytes (pre ++ "startxref\n".toUTF8)
      (toString n).toUTF8 "\n%%EOF\n".toUTF8
    simpa only [b, octets, ByteArray.size_append,
      show "startxref\n".toUTF8.size = 10 from rfl] using h
  have hlf : at? b (pre.size+9) = 10 := by
    have hs := PdfLex.Span.of_bytes pre "startxref\n".toUTF8
      ((toString n).toUTF8 ++ "\n%%EOF\n".toUTF8)
    have h := hs.byte 9 (by decide)
    change at? (pre ++ "startxref\n".toUTF8 ++ ((toString n).toUTF8 ++ "\n%%EOF\n".toUTF8))
      (pre.size+9) = 10 at h
    simpa only [b, ← ByteArray.append_assoc] using h
  have hend : at? b (pre.size+10+(toString n).toUTF8.size) = 10 := by
    change at? ((pre ++ "startxref\n".toUTF8 ++ (toString n).toUTF8) ++ "\n%%EOF\n".toUTF8)
      (pre.size+10+(toString n).toUTF8.size) = _
    have hb : (pre ++ "startxref\n".toUTF8 ++ (toString n).toUTF8).size =
        pre.size+10+(toString n).toUTF8.size := by
      simp only [ByteArray.size_append, show "startxref\n".toUTF8.size = 10 from rfl]
    rw [← hb, ← Nat.add_zero ((pre ++ "startxref\n".toUTF8 ++ (toString n).toUTF8).size),
      at?_append_right]
    rfl
  have hd := hn
  rw [numeric_octets _ (nat_numeric n)] at hd
  have hne : (toString n).toList.map Char.toNat ≠ [] := by simp
  have hp := number_byte (hd.first_number hne (by
    intro c hc
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
    exact nat_numeric n d hd))
  have hskip : skipWs b (pre.size+9) = pre.size+10 := by
    have hb := hn.bound
    have hlen : 0 < (toString n).toUTF8.size := by
      rw [numeric_size _ (nat_numeric n)]
      exact List.length_pos_iff.mpr (Number.nat_nonempty n)
    simpa only [Nat.add_assoc, Nat.reduceAdd] using
      skipWs_whitespace_exact (by rw [hlf]; rfl)
        (by simpa only [Nat.add_assoc, Nat.reduceAdd] using hp.2.1)
        (by simpa only [Nat.add_assoc, Nat.reduceAdd] using hp.2.2.1)
        (by simp only [octets_length] at hb; omega)
  rw [hskip]
  exact parse_nat hn (Or.inr (Or.inl (by rw [hend]; rfl)))

/-- Every 32-bit writer offset is recovered from its exact decimal footer,
regardless of the preceding bytes. The numeric bound implies the whole
footer fits in the reader's search window; it is not a parser premise. -/
theorem readStartxref_footer_exact (pre : ByteArray) (n : Nat) (hn : n < 256^4) :
    readStartxref (pre ++ (s!"startxref\n{n}\n%%EOF\n").toUTF8) = .ok n := by
  simp only [readStartxref, findStartxref_footer_exact pre n hn, footer_number]
  rfl

end LeanTex.Core.PdfRead
