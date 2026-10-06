import LeanTex.Core.Flate
import LeanTex.Core.Flate.BitStreamProof
import LeanTex.Core.Flate.TokenSymbolsProof
import LeanTex.Core.Flate.TokenFrequencies

namespace LeanTex.Core.Flate

theorem BytePrefix.complete {raw out : ByteArray} (hp : BytePrefix raw raw.size out) :
    out = raw :=
  ext_of_getElem? out raw hp.1 (fun i hi => hp.2.2 i (by rwa [hp.1] at hi))

theorem TokensFor.progress {raw : ByteArray} {start finish : Nat} {tokens : Array UInt32}
    (h : TokensFor raw start tokens finish) :
    start + tokens.size ≤ finish ∧ finish ≤ raw.size := by
  induction h with
  | empty hi => simpa using And.intro (Nat.le_refl start) hi
  | literal prior hi ih => simp only [Array.size_push]; omega
  | backref prior hlen href ih =>
    have := href.2.resolve_left (by omega)
    simp only [Array.size_push]
    omega

namespace TokenBlock

theorem symbols_literal_exact (b : UInt8) :
    symbols b.toUInt32 = (b.toNat, none) := by
  have hb : b.toUInt32 < 256 := by
    simpa only [UInt32.lt_iff_toNat_lt, UInt8.toNat_toUInt32, UInt32.reduceToNat] using
      b.toNat_lt
  simp only [symbols, hb, ite_true, UInt8.toNat_toUInt32]

theorem symbols_match_exact (len dist : Nat) (hl : 3 ≤ len ∧ len ≤ 258)
    (hd : 1 ≤ dist ∧ dist ≤ 32768) :
    symbols (matchToken len dist) =
      (257 + lenSymTab[len]?.getD 0, some (distanceSymbol dist)) := by
  have ht : ¬ matchToken len dist < 256 := by
    have := (matchToken_fields_exact len dist hl hd).2.2
    simpa only [UInt32.lt_iff_toNat_lt, UInt32.reduceToNat] using Nat.not_lt.mpr this
  simp only [symbols, ht, ite_false, matchOf_exact len dist hl hd]

theorem symbols_between {raw : ByteArray} {start finish : Nat} {tokens : Array UInt32}
    (ht : TokensFor raw start tokens finish) :
    ∀ t ∈ tokens.toList, (symbols t).1 < 286 ∧
      ∀ s, (symbols t).2 = some s → s < 30 := by
  induction ht with
  | empty => simp
  | @literal i tokens prior hi ih =>
    intro t hm
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | rfl
    · exact ih t hm
    · rw [symbols_literal_exact]
      exact ⟨by have := (raw[i]?.getD 0).toNat_lt; omega, by simp⟩
  | @backref i len dist tokens prior hlen href ih =>
    intro t hm
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | rfl
    · exact ih t hm
    · have hd : 1 ≤ dist ∧ dist ≤ 32768 :=
        ⟨(href.2.resolve_left (by omega)).1, href.1⟩
      rw [symbols_match_exact len dist hlen hd]
      have hl := (length_symbol_contract len hlen).1
      have hd' := (distance_symbol_contract dist hd).1
      change lenSymTab[len]?.getD 0 < 29 at hl
      change distanceSymbol dist < 30 at hd'
      exact ⟨by omega, by intro s h; cases h; exact hd'⟩

theorem alphabets_live {raw : ByteArray} {start finish : Nat} {tokens : Array UInt32}
    (ht : TokensFor raw start tokens finish) :
    ∀ t ∈ tokens.toList, 0 < (alphabets tokens).1[(symbols t).1]?.getD 0 ∧
      ∀ s, (symbols t).2 = some s → 0 < (alphabets tokens).2[s]?.getD 0 := by
  intro t hm
  have hc := (alphabets_contract tokens).2.2.2 t hm
  have hb := symbols_between ht t hm
  exact ⟨hc.1 hb.1, fun s hs => hc.2 s hs (hb.2 s hs)⟩

theorem writeMatch_contract (litLens litCodes distLens distCodes : Array Nat)
    (w : Bw) (len dist di : Nat) (hw : w.Valid)
    (hl : litLens[257 + lenSymTab[len]?.getD 0]?.getD 0 ≤ 16)
    (hd : distLens[di]?.getD 0 ≤ 16)
    (hle : lenExtra[lenSymTab[len]?.getD 0]?.getD 0 ≤ 16)
    (hde : distExtra[di]?.getD 0 ≤ 16) :
    (writeMatch litLens litCodes distLens distCodes w len dist di).Valid ∧
      (writeMatch litLens litCodes distLens distCodes w len dist di).Extends w := by
  let li := lenSymTab[len]?.getD 0
  let a := w.push (litCodes[257 + li]?.getD 0) (litLens[257 + li]?.getD 0)
  let b := a.pushExtra (len - lenBase[li]?.getD 0) (lenExtra[li]?.getD 0)
  let c := b.push (distCodes[di]?.getD 0) (distLens[di]?.getD 0)
  have ha : a.Valid := push_valid w _ _ hw hl
  have hb := pushExtra_contract a (len - lenBase[li]?.getD 0) _ ha hle
  have hc : c.Valid := push_valid b _ _ hb.1 hd
  have he := pushExtra_contract c (dist - distBase[di]?.getD 0)
    (distExtra[di]?.getD 0) hc hde
  exact ⟨he.1, he.2.trans ((push_extends_exact b _ _ hb.1 hd).trans
    (hb.2.trans (push_extends_exact w _ _ hw hl)))⟩

theorem writeEntry_literal_exact (litLens litCodes distLens distCodes : Array Nat)
    (w : Bw) (b : UInt8) :
    writeEntry litLens litCodes distLens distCodes w b.toUInt32 =
      w.push (litCodes[b.toNat]?.getD 0) (litLens[b.toNat]?.getD 0) := by
  have hb : b.toUInt32 < 256 := by
    simpa only [UInt32.lt_iff_toNat_lt, UInt8.toNat_toUInt32, UInt32.reduceToNat] using
      b.toNat_lt
  simp only [writeEntry, hb, ite_true, UInt8.toNat_toUInt32]

theorem writeEntry_match_exact (litLens litCodes distLens distCodes : Array Nat)
    (w : Bw) (len dist : Nat) (hl : 3 ≤ len ∧ len ≤ 258)
    (hd : 1 ≤ dist ∧ dist ≤ 32768) :
    writeEntry litLens litCodes distLens distCodes w (matchToken len dist) =
      writeMatch litLens litCodes distLens distCodes w len dist (distanceSymbol dist) := by
  have ht : ¬ matchToken len dist < 256 := by
    have := (matchToken_fields_exact len dist hl hd).2.2
    simpa only [UInt32.lt_iff_toNat_lt, UInt32.reduceToNat] using Nat.not_lt.mpr this
  simp only [writeEntry, ht, ite_false, matchOf_exact len dist hl hd]

theorem write_contract {raw : ByteArray} {start finish : Nat} {tokens : Array UInt32}
    (litLens litCodes distLens distCodes : Array Nat) (w : Bw)
    (hw : w.Valid) (hl : ∀ s : Nat, litLens[s]?.getD 0 ≤ 16)
    (hd : ∀ s : Nat, distLens[s]?.getD 0 ≤ 16)
    (ht : TokensFor raw start tokens finish) :
    (write litLens litCodes distLens distCodes tokens w).Valid ∧
      (write litLens litCodes distLens distCodes tokens w).Extends w := by
  induction ht with
  | empty => exact ⟨hw, Bw.Extends.refl w⟩
  | @literal i tokens prior hi ih =>
    rw [write, BitStream.write_push_exact, writeEntry_literal_exact]
    exact ⟨push_valid _ _ _ ih.1 (hl _),
      (push_extends_exact _ _ _ ih.1 (hl _)).trans ih.2⟩
  | @backref i len dist tokens prior hlen href ih =>
    have hp := href.2.resolve_left (by omega)
    have hdist : 1 ≤ dist ∧ dist ≤ 32768 := ⟨hp.1, href.1⟩
    have hls := length_symbol_contract len hlen
    have hds := distance_symbol_contract dist hdist
    rw [write, BitStream.write_push_exact, writeEntry_match_exact _ _ _ _ _ _ _ hlen hdist]
    have h := writeMatch_contract litLens litCodes distLens distCodes _ len dist (distanceSymbol dist)
      ih.1 (hl _) (hd _) (by have := hls.2.2.1; omega) (by have := hds.2.2.1; omega)
    exact ⟨h.1, h.2.trans ih.2⟩

/-- The four match fields read back through the production Huffman tables and
extra-bit readers, including zero-width extra fields. -/
theorem writeMatch_read_exact (litFreq distFreq : Array Nat) (w : Bw) (data out : ByteArray)
    (len dist maxOut : Nat) (hw : w.Valid)
    (hlf : litFreq.size ≤ 2 ^ 15) (hdf : distFreq.size ≤ 2 ^ 15)
    (hlen : 3 ≤ len ∧ len ≤ 258) (hdist : 1 ≤ dist ∧ dist ≤ 32768)
    (hls : 0 < litFreq[257 + lenSymTab[len]?.getD 0]?.getD 0)
    (hds : 0 < distFreq[distanceSymbol dist]?.getD 0)
    (hbefore : dist ≤ out.size) (hmax : out.size + len ≤ maxOut)
    (hr : (writeMatch (PackageMerge.lengths litFreq 15)
      (canonCodes (PackageMerge.lengths litFreq 15)) (PackageMerge.lengths distFreq 15)
      (canonCodes (PackageMerge.lengths distFreq 15)) w len dist
      (distanceSymbol dist)).Realizes data) :
    readStep (mkHuff (PackageMerge.lengths litFreq 15))
        (mkHuff (PackageMerge.lengths distFreq 15)) maxOut
        (out, {data, bitPos := w.position}) =
      .ok (.inr (copy out len dist, {data, bitPos :=
        (writeMatch (PackageMerge.lengths litFreq 15)
          (canonCodes (PackageMerge.lengths litFreq 15)) (PackageMerge.lengths distFreq 15)
          (canonCodes (PackageMerge.lengths distFreq 15)) w len dist
          (distanceSymbol dist)).position})) := by
  let litLens := PackageMerge.lengths litFreq 15
  let distLens := PackageMerge.lengths distFreq 15
  let li := lenSymTab[len]?.getD 0
  let di := distanceSymbol dist
  let a := w.push ((canonCodes litLens)[257 + li]?.getD 0) (litLens[257 + li]?.getD 0)
  let b := a.pushExtra (len - lenBase[li]?.getD 0) (lenExtra[li]?.getD 0)
  let c := b.push ((canonCodes distLens)[di]?.getD 0) (distLens[di]?.getD 0)
  let d := c.pushExtra (dist - distBase[di]?.getD 0) (distExtra[di]?.getD 0)
  have hl : litLens[257 + li]?.getD 0 ≤ 16 :=
    Nat.le_trans ((PackageMerge.lengths_contract litFreq 15 (by decide) hlf).1.width_le _)
      (by decide)
  have hd : distLens[di]?.getD 0 ≤ 16 :=
    Nat.le_trans ((PackageMerge.lengths_contract distFreq 15 (by decide) hdf).1.width_le _)
      (by decide)
  have hli := length_symbol_contract len hlen
  have hdi := distance_symbol_contract dist hdist
  have hle : lenExtra[li]?.getD 0 ≤ 16 := Nat.le_trans hli.2.2.1 (by decide)
  have hde : distExtra[di]?.getD 0 ≤ 16 := Nat.le_trans hdi.2.2.1 (by decide)
  have ha : a.Valid := push_valid w _ _ hw hl
  have hb := pushExtra_contract a (len - lenBase[li]?.getD 0) _ ha hle
  have hc : c.Valid := push_valid b _ _ hb.1 hd
  have hx := pushExtra_contract c (dist - distBase[di]?.getD 0) _ hc hde
  have hdr : d.Realizes data := hr
  have hcr : c.Realizes data := hdr.prefix hx.2
  have hbr : b.Realizes data := hcr.prefix (push_extends_exact b _ _ hb.1 hd)
  have har : a.Realizes data := hbr.prefix hb.2
  have hreadL := packageMerge_push_decode_exact litFreq 15 w data (257 + li) hw
    (by decide) hlf hls har
  rw [← push_position_exact w ((canonCodes litLens)[257 + li]?.getD 0) _ hw hl] at hreadL
  change (mkHuff litLens).decode {data, bitPos := w.position} =
    some (257 + li, {data, bitPos := a.position}) at hreadL
  have hreadLE : ({data, bitPos := a.position} : Br).bits (lenExtra[li]?.getD 0) =
      some (len - lenBase[li]?.getD 0, {data, bitPos := b.position}) :=
    pushExtra_bits_exact a data _ _ ha hle hli.2.2.2.2 hbr
  have hreadD := packageMerge_push_decode_exact distFreq 15 b data di hb.1
    (by decide) hdf hds hcr
  rw [← push_position_exact b ((canonCodes distLens)[di]?.getD 0) _ hb.1 hd] at hreadD
  change (mkHuff distLens).decode {data, bitPos := b.position} =
    some (di, {data, bitPos := c.position}) at hreadD
  have hreadDE : ({data, bitPos := c.position} : Br).bits (distExtra[di]?.getD 0) =
      some (dist - distBase[di]?.getD 0, {data, bitPos := d.position}) :=
    pushExtra_bits_exact c data _ _ hc hde hdi.2.2.2.2 hdr
  have hlbase : lenBase[li]? = some (lenBase[li]'hli.1) := getElem?_pos ..
  have hlextra : lenExtra[li]? = some (lenExtra[li]'hli.2.1) := getElem?_pos ..
  have hdbase : distBase[di]? = some (distBase[di]'hdi.1) := getElem?_pos ..
  have hdextra : distExtra[di]? = some (distExtra[di]'hdi.2.1) := getElem?_pos ..
  have hlen' : lenBase[li]?.getD 0 + (len - lenBase[li]?.getD 0) = len :=
    Nat.add_sub_of_le hli.2.2.2.1
  have hdist' : distBase[di]?.getD 0 + (dist - distBase[di]?.getD 0) = dist :=
    Nat.add_sub_of_le hdi.2.2.2.1
  simp only [hlbase, hlextra, Option.getD_some] at hreadLE hlen'
  simp only [hdbase, hdextra, Option.getD_some] at hreadDE hdist'
  change readStep (mkHuff litLens) (mkHuff distLens) maxOut (out, {data, bitPos := w.position}) =
    .ok (.inr (copy out len dist, {data, bitPos := d.position}))
  simp only [readStep, hreadL, show ¬ 257 + li = 256 by omega, beq_iff_eq,
    show ¬ 257 + li < 256 by omega, Nat.add_sub_cancel_left,
    hlbase, hlextra, hreadLE, hreadD, hdbase, hdextra, hreadDE, hlen', hdist',
    show ¬ dist = 0 by omega, show ¬ dist > out.size by omega,
    show ¬ out.size + len > maxOut by omega,
    ↓reduceIte, Bool.or_eq_true, decide_eq_true_eq, false_or, pure, Except.pure]

/-- A decoded literal advances the actual output by exactly that byte. -/
theorem readStep_literal_exact (lit dist : Huff) (out : ByteArray) (r r' : Br)
    (b : UInt8) (maxOut : Nat) (hr : lit.decode r = some (b.toNat, r'))
    (hm : out.size < maxOut) :
    readStep lit dist maxOut (out, r) = .ok (.inr (out.push b, r')) := by
  have hb := b.toNat_lt
  simp only [readStep, hr, beq_iff_eq, show ¬ b.toNat = 256 by omega,
    hb, Nat.not_le.mpr hm, ↓reduceIte, UInt8.ofNat_toNat, pure, Except.pure]

theorem readStep_end_exact (lit dist : Huff) (out : ByteArray) (r r' : Br)
    (maxOut : Nat) (hr : lit.decode r = some (256, r')) :
    readStep lit dist maxOut (out, r) = .ok (.inl (out, r')) := by
  simp only [readStep, hr, beq_iff_eq, ↓reduceIte, pure, Except.pure]

/-- Every actual packed token advances the reader and extends the verified
byte prefix. The trace counts tokens, while the prefix counts output bytes. -/
theorem write_steps_bounded_exact {raw out : ByteArray} {start finish : Nat}
    {tokens : Array UInt32} (maxOut : Nat) (hmax : raw.size ≤ maxOut)
    (litFreq distFreq : Array Nat) (w : Bw) (data : ByteArray)
    (hlf : litFreq.size ≤ 2 ^ 15) (hdf : distFreq.size ≤ 2 ^ 15)
    (hw : w.Valid) (hp : BytePrefix raw start out) (ht : TokensFor raw start tokens finish)
    (hs : ∀ t ∈ tokens.toList, 0 < litFreq[(symbols t).1]?.getD 0 ∧
      ∀ s, (symbols t).2 = some s → 0 < distFreq[s]?.getD 0)
    (hr : (write (PackageMerge.lengths litFreq 15)
      (canonCodes (PackageMerge.lengths litFreq 15)) (PackageMerge.lengths distFreq 15)
      (canonCodes (PackageMerge.lengths distFreq 15)) tokens w).Realizes data) :
    ∃ out', DecodeLoop.Steps
      (readStep (mkHuff (PackageMerge.lengths litFreq 15))
        (mkHuff (PackageMerge.lengths distFreq 15)) maxOut)
      (out, {data, bitPos := w.position}) tokens.size
      (out', {data, bitPos := (write (PackageMerge.lengths litFreq 15)
        (canonCodes (PackageMerge.lengths litFreq 15)) (PackageMerge.lengths distFreq 15)
        (canonCodes (PackageMerge.lengths distFreq 15)) tokens w).position}) ∧
      BytePrefix raw finish out' := by
  let litLens := PackageMerge.lengths litFreq 15
  let distLens := PackageMerge.lengths distFreq 15
  let litCodes := canonCodes litLens
  let distCodes := canonCodes distLens
  have hl : ∀ s : Nat, litLens[s]?.getD 0 ≤ 16 := fun s =>
    Nat.le_trans ((PackageMerge.lengths_contract litFreq 15 (by decide) hlf).1.width_le s)
      (by decide)
  have hd : ∀ s : Nat, distLens[s]?.getD 0 ≤ 16 := fun s =>
    Nat.le_trans ((PackageMerge.lengths_contract distFreq 15 (by decide) hdf).1.width_le s)
      (by decide)
  induction ht with
  | empty => exact ⟨out, .refl _, hp⟩
  | @literal i tokens prior hi ih =>
    let byte := raw[i]?.getD 0
    let beforeWriter := write litLens litCodes distLens distCodes tokens w
    have hv := write_contract litLens litCodes distLens distCodes w hw hl hd prior
    have hwr : write litLens litCodes distLens distCodes (tokens.push byte.toUInt32) w =
        beforeWriter.push (litCodes[byte.toNat]?.getD 0) (litLens[byte.toNat]?.getD 0) := by
      rw [write, BitStream.write_push_exact, writeEntry_literal_exact]
      rfl
    have hreal : (beforeWriter.push (litCodes[byte.toNat]?.getD 0)
        (litLens[byte.toNat]?.getD 0)).Realizes data := hwr ▸ hr
    have hs0 : ∀ t ∈ tokens.toList, 0 < litFreq[(symbols t).1]?.getD 0 ∧
        ∀ s, (symbols t).2 = some s → 0 < distFreq[s]?.getD 0 := by
      intro t hm
      exact hs t (by
        simp only [Array.toList_push, List.mem_append, List.mem_singleton]
        exact Or.inl hm)
    obtain ⟨before, hsteps, hprefix⟩ :=
      ih hs0 (hreal.prefix (push_extends_exact beforeWriter _ _ hv.1 (hl _)))
    have hlast := (hs byte.toUInt32 (by simp [byte])).1
    rw [symbols_literal_exact] at hlast
    have hread := packageMerge_push_decode_exact litFreq 15 beforeWriter data byte.toNat
      hv.1 (by decide) hlf hlast hreal
    rw [← push_position_exact beforeWriter (litCodes[byte.toNat]?.getD 0) _ hv.1 (hl _)]
      at hread
    refine ⟨before.push byte, ?_, hprefix.push hi ?_⟩
    · rw [Array.size_push, hwr]
      exact .snoc hsteps (readStep_literal_exact _ _ _ _ _ byte maxOut hread
        (by rw [hprefix.1]; exact Nat.lt_of_lt_of_le hi hmax))
    · simp only [byte, getElem?_pos raw i hi, Option.getD_some]
  | @backref i len dist tokens prior hlen href ih =>
    let beforeWriter := write litLens litCodes distLens distCodes tokens w
    have hv := write_contract litLens litCodes distLens distCodes w hw hl hd prior
    have hpos := href.2.resolve_left (by omega)
    have hdist : 1 ≤ dist ∧ dist ≤ 32768 := ⟨hpos.1, href.1⟩
    have hli := length_symbol_contract len hlen
    have hdi := distance_symbol_contract dist hdist
    have hx := writeMatch_contract litLens litCodes distLens distCodes beforeWriter
      len dist (distanceSymbol dist) hv.1 (hl _) (hd _)
      (Nat.le_trans hli.2.2.1 (by decide)) (Nat.le_trans hdi.2.2.1 (by decide))
    have hwr : write litLens litCodes distLens distCodes (tokens.push (matchToken len dist)) w =
        writeMatch litLens litCodes distLens distCodes beforeWriter len dist (distanceSymbol dist) := by
      rw [write, BitStream.write_push_exact, writeEntry_match_exact _ _ _ _ _ _ _ hlen hdist]
      rfl
    have hreal : (writeMatch litLens litCodes distLens distCodes beforeWriter
        len dist (distanceSymbol dist)).Realizes data := hwr ▸ hr
    have hs0 : ∀ t ∈ tokens.toList, 0 < litFreq[(symbols t).1]?.getD 0 ∧
        ∀ s, (symbols t).2 = some s → 0 < distFreq[s]?.getD 0 := by
      intro t hm
      exact hs t (by
        simp only [Array.toList_push, List.mem_append, List.mem_singleton]
        exact Or.inl hm)
    obtain ⟨before, hsteps, hprefix⟩ := ih hs0 (hreal.prefix hx.2)
    have hlast := hs (matchToken len dist) (by simp)
    rw [symbols_match_exact len dist hlen hdist] at hlast
    have hread := writeMatch_read_exact litFreq distFreq beforeWriter data before len dist
      maxOut hv.1 hlf hdf hlen hdist hlast.1 (hlast.2 _ rfl)
      (by rw [hprefix.1]; exact hpos.2.1)
      (by rw [hprefix.1]; exact Nat.le_trans hpos.2.2.1 hmax) hreal
    refine ⟨copy before len dist, ?_, backref_copy_exact raw before i len dist hprefix href⟩
    rw [Array.size_push, hwr]
    exact .snoc hsteps hread

theorem write_steps_exact {raw out : ByteArray} {start finish : Nat} {tokens : Array UInt32}
    (litFreq distFreq : Array Nat) (w : Bw) (data : ByteArray)
    (hlf : litFreq.size ≤ 2 ^ 15) (hdf : distFreq.size ≤ 2 ^ 15)
    (hw : w.Valid) (hp : BytePrefix raw start out) (ht : TokensFor raw start tokens finish)
    (hs : ∀ t ∈ tokens.toList, 0 < litFreq[(symbols t).1]?.getD 0 ∧
      ∀ s, (symbols t).2 = some s → 0 < distFreq[s]?.getD 0)
    (hr : (write (PackageMerge.lengths litFreq 15)
      (canonCodes (PackageMerge.lengths litFreq 15)) (PackageMerge.lengths distFreq 15)
      (canonCodes (PackageMerge.lengths distFreq 15)) tokens w).Realizes data) :
    ∃ out', DecodeLoop.Steps
      (readStep (mkHuff (PackageMerge.lengths litFreq 15))
        (mkHuff (PackageMerge.lengths distFreq 15)) raw.size)
      (out, {data, bitPos := w.position}) tokens.size
      (out', {data, bitPos := (write (PackageMerge.lengths litFreq 15)
        (canonCodes (PackageMerge.lengths litFreq 15)) (PackageMerge.lengths distFreq 15)
        (canonCodes (PackageMerge.lengths distFreq 15)) tokens w).position}) ∧
      BytePrefix raw finish out' :=
  write_steps_bounded_exact raw.size (Nat.le_refl _) litFreq distFreq w data
    hlf hdf hw hp ht hs hr

theorem writePayload_contract {raw : ByteArray} {start finish : Nat} {tokens : Array UInt32}
    (litLens distLens : Array Nat) (w : Bw)
    (hw : w.Valid) (hl : ∀ s : Nat, litLens[s]?.getD 0 ≤ 16)
    (hd : ∀ s : Nat, distLens[s]?.getD 0 ≤ 16)
    (ht : TokensFor raw start tokens finish) :
    (writePayload litLens distLens tokens w).Valid ∧
      (writePayload litLens distLens tokens w).Extends w := by
  have hv := write_contract litLens (canonCodes litLens) distLens (canonCodes distLens)
    w hw hl hd ht
  exact ⟨push_valid _ _ _ hv.1 (hl 256),
    (push_extends_exact _ _ _ hv.1 (hl 256)).trans hv.2⟩

/-- A complete compressed payload, with its actual frequency counts, generated
Huffman tables and end marker, reads back to the input. Final-byte realization
allows later fields and the zlib trailer to follow the payload. -/
theorem read_write_bounded_exact (raw : ByteArray) (maxOut : Nat)
    (hmax : raw.size ≤ maxOut) (tokens : Array UInt32)
    (ht : TokensFor raw 0 tokens raw.size) (w : Bw) (data : ByteArray) (hw : w.Valid)
    (hr : (writePayload (PackageMerge.lengths (alphabets tokens).1 15)
      (PackageMerge.lengths (alphabets tokens).2 15) tokens w).Realizes data) :
    read (mkHuff (PackageMerge.lengths (alphabets tokens).1 15))
        (mkHuff (PackageMerge.lengths (alphabets tokens).2 15))
        {data, bitPos := w.position} ByteArray.empty maxOut =
      .ok (raw, {data, bitPos :=
        (writePayload (PackageMerge.lengths (alphabets tokens).1 15)
          (PackageMerge.lengths (alphabets tokens).2 15) tokens w).position}) := by
  let litFreq := (alphabets tokens).1
  let distFreq := (alphabets tokens).2
  let litLens := PackageMerge.lengths litFreq 15
  let distLens := PackageMerge.lengths distFreq 15
  let beforeEnd := write litLens (canonCodes litLens) distLens (canonCodes distLens) tokens w
  have hf := alphabets_contract tokens
  have hlf : litFreq.size ≤ 2 ^ 15 := Nat.le_trans hf.1.2 (by decide)
  have hdf : distFreq.size ≤ 2 ^ 15 := Nat.le_trans hf.2.1.2 (by decide)
  have hl : ∀ s : Nat, litLens[s]?.getD 0 ≤ 16 := fun s =>
    Nat.le_trans ((PackageMerge.lengths_contract litFreq 15 (by decide) hlf).1.width_le s)
      (by decide)
  have hd : ∀ s : Nat, distLens[s]?.getD 0 ≤ 16 := fun s =>
    Nat.le_trans ((PackageMerge.lengths_contract distFreq 15 (by decide) hdf).1.width_le s)
      (by decide)
  have hv : beforeEnd.Valid :=
    (write_contract litLens (canonCodes litLens) distLens (canonCodes distLens)
      w hw hl hd ht).1
  have hx := push_extends_exact beforeEnd ((canonCodes litLens)[256]?.getD 0)
    (litLens[256]?.getD 0) hv (hl 256)
  obtain ⟨out, hsteps, hp⟩ := write_steps_bounded_exact (raw := raw) (out := ByteArray.empty)
    maxOut hmax litFreq distFreq w data hlf hdf hw ⟨rfl, Nat.zero_le _, by simp⟩ ht
    (alphabets_live ht) (hr.prefix hx)
  have hread := packageMerge_push_decode_exact litFreq 15 beforeEnd data 256 hv
    (by decide) hlf hf.2.2.1 hr
  rw [← push_position_exact beforeEnd ((canonCodes litLens)[256]?.getD 0) _ hv (hl 256)]
    at hread
  have hfinish := hsteps.finish
    (.done (readStep_end_exact _ _ out _ _ maxOut hread))
  have h := DecodeLoop.run_exact _ _ _ _ (maxOut + 2) "deflate: block did not end"
    hfinish (by have := ht.progress; omega)
  simpa only [read, writePayload, hp.complete] using h

theorem read_write_exact (raw : ByteArray) (tokens : Array UInt32)
    (ht : TokensFor raw 0 tokens raw.size) (w : Bw) (data : ByteArray) (hw : w.Valid)
    (hr : (writePayload (PackageMerge.lengths (alphabets tokens).1 15)
      (PackageMerge.lengths (alphabets tokens).2 15) tokens w).Realizes data) :
    read (mkHuff (PackageMerge.lengths (alphabets tokens).1 15))
        (mkHuff (PackageMerge.lengths (alphabets tokens).2 15))
        {data, bitPos := w.position} ByteArray.empty raw.size =
      .ok (raw, {data, bitPos :=
        (writePayload (PackageMerge.lengths (alphabets tokens).1 15)
          (PackageMerge.lengths (alphabets tokens).2 15) tokens w).position}) :=
  read_write_bounded_exact raw raw.size (Nat.le_refl _) tokens ht w data hw hr

end TokenBlock
end LeanTex.Core.Flate
