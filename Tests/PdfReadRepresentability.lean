import LeanTex.Core.PdfReadProof

open LeanTex.Core

/-! Domain regression pins complement the universal round-trip theorem.
Rejected cases carry proofs about the independent syntactic domain; the
runtime checks separately witness the former contract's failures. The
domain is sufficient, not a claim that every excluded spelling fails. -/

namespace PdfReadRepresentability

open PdfRead PdfLex

private abbrev Certified := { o : Obj // o.Representable }
private abbrev Rejected := { o : Obj // ¬ o.Representable }

private def badReal (s : String)
    (h : ∃ c ∈ s.toList, numByte c.toNat = false) : Rejected :=
  ⟨.real s, by
    intro hr
    cases hr with
    | real hs =>
      obtain ⟨c,hc,hbad⟩ := h
      have := hs.2 c hc
      simp only [hbad,Bool.false_eq_true] at this⟩

private def badName (s : String) (h : ¬ Obj.NameSpelling s) : Rejected :=
  ⟨.name s, by
    intro hr
    cases hr with
    | name hs => exact h hs⟩

private theorem string_closer {cs : List Nat} (h : Obj.StringSpelling cs) :
    cs.getLast? = some 41 ∨ cs.getLast? = some 62 := by
  cases h <;> simp [List.getLast?_cons]

private def badStringCloser (raw : ByteArray)
    (h : (octets raw).getLast? ≠ some 41 ∧ (octets raw).getLast? ≠ some 62) : Rejected :=
  ⟨.str raw, by
    intro hr
    cases hr with
    | str hs => exact (string_closer hs).elim h.1 h.2⟩

private def dictionaryString : Rejected :=
  ⟨.str "<<>>".toUTF8, by
    intro hr
    cases hr with
    | str hs =>
      change Obj.StringSpelling [60,60,62,62] at hs
      generalize he : ([60,60,62,62] : List Nat) = cs at hs
      cases hs with
      | literal _ => cases he
      | @hex cs hb =>
        have hc : [60,62] = cs := List.append_cancel_right (List.cons.inj he).2
        subst cs
        have hh := hb 60 (by simp)
        simp [hexVal,isWs] at hh⟩

private def rejected : List (String × Rejected) := [
  ("non-numeric real prefix", badReal "a." (by decide)),
  ("trailing real bytes", badReal "1.x" (by decide)),
  ("unclosed literal", badStringCloser "(x".toUTF8 (by decide)),
  ("dictionary masquerading as a string", dictionaryString),
  ("trailing literal bytes", badStringCloser "(a) trailing".toUTF8 (by decide)),
  ("trailing hex bytes", badStringCloser "<a>tail".toUTF8 (by decide)),
  ("name outside the byte alphabet", badName "λ" (by unfold Obj.NameSpelling; decide)),
  ("empty name substitution", badName "" (by unfold Obj.NameSpelling; decide))]

private def array (xs : List Certified) : Certified :=
  ⟨.arr (xs.map Subtype.val).toArray, .arr (by
    intro o ho
    have hm : o ∈ xs.map Subtype.val := by simpa using ho
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hm
    exact x.property)⟩

private def dictionary (key : { s : String // Obj.NameSpelling s })
    (xs : List Certified) : Certified :=
  ⟨.dict (xs.map (fun x => (key.val,x.val))).toArray,
    .dict (by
      intro e he
      have hm : e ∈ xs.map (fun x => (key.val,x.val)) := by simpa using he
      obtain ⟨x,_,rfl⟩ := List.mem_map.mp hm
      exact key.property) (by
      intro e he
      have hm : e ∈ xs.map (fun x => (key.val,x.val)) := by simpa using he
      obtain ⟨x,_,rfl⟩ := List.mem_map.mp hm
      exact x.property)⟩

private def primitives : List Certified := [
  ⟨.null,.null⟩, ⟨.bool false,.bool false⟩, ⟨.bool true,.bool true⟩,
  ⟨.int 0,.int 0⟩, ⟨.int (10^80),.int _⟩, ⟨.int (-(10^80)),.int _⟩,
  ⟨.ref (10^80) (10^80),.ref _ _⟩,
  ⟨.real "-.25",.real (by unfold Obj.RealSpelling; decide)⟩,
  -- Representability describes retention by the scanner, not PDF numeric validity.
  ⟨.real ".",.real (by unfold Obj.RealSpelling; decide)⟩,
  ⟨.name "é",.name (by unfold Obj.NameSpelling; decide)⟩,
  ⟨.name "R",.name (by unfold Obj.NameSpelling; decide)⟩,
  ⟨.str "()".toUTF8,.str (.literal .nil)⟩,
  ⟨.str "<0a ff 1>".toUTF8,.str (by
    change Obj.StringSpelling (60 :: [48,97,32,102,102,32,49] ++ [62])
    exact .hex (by decide))⟩]

/-- Rejection is inherited by both container positions; a valid outer
constructor cannot hide an invalid descendant or dictionary key. -/
private theorem rejected_array {o : Obj} (h : ¬ o.Representable) :
    ¬ (Obj.arr #[o]).Representable := by
  intro hr
  cases hr with
  | arr hs => exact h (hs o (by simp))

private theorem rejected_value {o : Obj} (h : ¬ o.Representable) :
    ¬ (Obj.dict #[("value",o)]).Representable := by
  intro hr
  cases hr with
  | dict _ hs => exact h (hs ("value",o) (by simp))

private theorem rejected_key {s : String} (h : ¬ Obj.NameSpelling s) :
    ¬ (Obj.dict #[(s,.null)]).Representable := by
  intro hr
  cases hr with
  | dict hs _ => exact h (hs (s,.null) (by simp))

private def nestedRejected : List Rejected :=
  (rejected.map fun e => ⟨.arr #[e.2.val],rejected_array e.2.property⟩) ++
  (rejected.map fun e => ⟨.dict #[("value",e.2.val)],rejected_value e.2.property⟩) ++
  [⟨.dict #[("λ",.null)],rejected_key (by unfold Obj.NameSpelling; decide)⟩,
   ⟨.dict #[("",.null)],rejected_key (by unfold Obj.NameSpelling; decide)⟩]

def checks (ref : IO.Ref (List String)) : IO Unit := do
  let t := fun (name : String) (ok : Bool) =>
    unless ok do ref.modify (s!"PDF representability: {name}" :: ·)
  let roundtrip := fun (o : Obj) =>
    (parseVal o.render 0).toOption == some (o,o.render.size)
  for (name,o) in rejected do
    t s!"excluded spelling still witnesses {name}" (!roundtrip o.val)
  for o in nestedRejected do
    t "excluded descendant or key still changes the read value" (!roundtrip o.val)
  let key : { s : String // Obj.NameSpelling s } :=
    ⟨"a/b#é",by unfold Obj.NameSpelling; decide⟩
  let values := array [] :: dictionary key [] :: primitives
  for o in values do
    t "certified primitive or empty container" (roundtrip o.val)
  for x in values do
    for y in values do
      t "adjacent array token kinds" (roundtrip (array [x,y]).val)
      t "adjacent dictionary token kinds" (roundtrip (dictionary key [x,y]).val)
  let mut nested := array values
  for _ in [0:32] do
    nested := dictionary key [array [nested]]
    t "finite nesting has no fixed depth limit" (roundtrip nested.val)

end PdfReadRepresentability

def pdfReadRepresentabilityChecks := PdfReadRepresentability.checks
