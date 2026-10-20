module

public import LeanTex.Core.Ir
import all LeanTex.Core.Ir

/-! `number_gapless_within`: numbering by chapter, the figures and tables of the chapter the counters
stand in take the numbers after its count, one each, with no gap. -/

namespace LeanTex.Core.Ir

mutual

/-- Whether every figure and table among the blocks belongs to chapter `w` begun at `s`. -/
private def floatsInList (w : String) (s : Nat) : List Block → Bool
  | [] => true
  | b :: rest => floatsInOne w s b && floatsInList w s rest

private def floatsInOne (w : String) (s : Nat) : Block → Bool
  | .para _ | .equation _ _ | .section _ _ _ _ | .lines _ | .note _ | .verbatim _ _ _ | .logo _
  | .framefoot _ | .setPalette _ | .setTokens _ | .pagebreak | .rule _ _ _ | .picture _
  | .table _ _ _ _ _ _ | .algorithm _ _ _ | .bibliography _ _ _ | .contents _ _ => true
  | .list _ _ items => floatsInItems w s items.toList
  | .center body | .ragged _ body | .quote _ body | .abstract body | .titled _ _ body
  | .disclosure _ _ body | .role _ body | .link _ body | .spaced _ body | .onSteps _ body
  | .only _ body | .nav _ body | .frame _ _ _ _ body => floatsInList w s body.toList
  | .columns cols => floatsInCols w s cols.toList
  | .altSteps _ firstPage otherPage =>
    floatsInList w s firstPage.toList && floatsInList w s otherPage.toList
  | .float kind num _ body _ =>
    (!(kind == .figure || kind == .table) ||
      ((num.map (·.within)).getD "" == w && (num.map (·.scope)).getD 0 == s)) &&
      floatsInList w s body.toList

private def floatsInItems (w : String) (s : Nat) : List (Array Block) → Bool
  | [] => true
  | item :: rest => floatsInList w s item.toList && floatsInItems w s rest

private def floatsInCols (w : String) (s : Nat) : List (BoxWidth × Array Block) → Bool
  | [] => true
  | (_, body) :: rest => floatsInList w s body.toList && floatsInCols w s rest

end

/-- Two block arrays whose floats bear the same numbers, whatever chapters the numbers name. -/
private def SameNums (a b : Array Block) : Prop :=
  ∀ k out, floatNumsList k out a.toList = floatNumsList k out b.toList

private theorem SameNums.push {a b : Array Block} {x y : Block} (h : SameNums a b)
    (hx : ∀ k out, floatNumsOne k out x = floatNumsOne k out y) :
    SameNums (a.push x) (b.push y) := by
  intro k out
  simp only [Array.toList_push, floatNumsList_append, floatNumsList, h k out, hx]

private theorem floatNumsItems_append (k : FloatKind) (out : List Nat) (l1 l2 : List (Array Block)) :
    floatNumsItems k out (l1 ++ l2) = floatNumsItems k (floatNumsItems k out l1) l2 := by
  induction l1 generalizing out with
  | nil => rfl
  | cons x rest ih => simp [floatNumsItems, ih]

private theorem floatNumsCols_append (k : FloatKind) (out : List Nat)
    (l1 l2 : List (BoxWidth × Array Block)) :
    floatNumsCols k out (l1 ++ l2) = floatNumsCols k (floatNumsCols k out l1) l2 := by
  induction l1 generalizing out with
  | nil => rfl
  | cons x rest ih => simp [floatNumsCols, ih]

/-- The counters a walk by chapter and a walk without it agree, and keep their chapter. -/
private def Agree (t f c : FloatCtr) : Prop := t = f ∧ f.within = c.within ∧ f.scope = c.scope

mutual

private theorem numberFloatList_within (c : FloatCtr) (acc acc' : Array Block) (bs : List Block)
    (h : floatsInList c.within c.scope bs = true) (ha : SameNums acc acc') :
    Agree (numberFloatList true c acc bs).1 (numberFloatList false c acc' bs).1 c ∧
      SameNums (numberFloatList true c acc bs).2 (numberFloatList false c acc' bs).2 := by
  match bs with
  | [] => exact ⟨⟨rfl, rfl, rfl⟩, by simpa [numberFloatList] using ha⟩
  | b :: rest =>
    simp only [floatsInList, Bool.and_eq_true] at h
    obtain ⟨⟨hc, hw, hs⟩, hn⟩ := numberFloatOne_within c b h.1
    have hr : floatsInList (numberFloatOne false c b).1.within (numberFloatOne false c b).1.scope
        rest = true := by rw [hw, hs]; exact h.2
    obtain ⟨⟨hc2, hw2, hs2⟩, hn2⟩ := numberFloatList_within (numberFloatOne false c b).1
      (acc.push (numberFloatOne true c b).2) (acc'.push (numberFloatOne false c b).2) rest hr
      (ha.push hn)
    simp only [numberFloatList]
    rw [hc]
    exact ⟨⟨hc2, hw2.trans hw, hs2.trans hs⟩, hn2⟩
termination_by structural bs

private theorem numberFloatItems_within (c : FloatCtr) (acc acc' : Array (Array Block))
    (items : List (Array Block)) (h : floatsInItems c.within c.scope items = true)
    (ha : ∀ k out, floatNumsItems k out acc.toList = floatNumsItems k out acc'.toList) :
    Agree (numberFloatItems true c acc items).1 (numberFloatItems false c acc' items).1 c ∧
      ∀ k out, floatNumsItems k out (numberFloatItems true c acc items).2.toList =
        floatNumsItems k out (numberFloatItems false c acc' items).2.toList := by
  match items with
  | [] => exact ⟨⟨rfl, rfl, rfl⟩, by simpa [numberFloatItems] using ha⟩
  | item :: rest =>
    simp only [floatsInItems, Bool.and_eq_true] at h
    obtain ⟨⟨hc, hw, hs⟩, hn⟩ := numberFloatList_within c #[] #[] item.toList h.1 (fun _ _ => rfl)
    have hr : floatsInItems (numberFloatList false c #[] item.toList).1.within
        (numberFloatList false c #[] item.toList).1.scope rest = true := by rw [hw, hs]; exact h.2
    obtain ⟨⟨hc2, hw2, hs2⟩, hn2⟩ := numberFloatItems_within
      (numberFloatList false c #[] item.toList).1
      (acc.push (numberFloatList true c #[] item.toList).2)
      (acc'.push (numberFloatList false c #[] item.toList).2) rest hr (by
        intro k out
        simp only [Array.toList_push, floatNumsItems_append, floatNumsItems, ha k out, hn k])
    simp only [numberFloatItems]
    rw [hc]
    exact ⟨⟨hc2, hw2.trans hw, hs2.trans hs⟩, hn2⟩
termination_by structural items

private theorem numberFloatCols_within (c : FloatCtr) (acc acc' : Array (BoxWidth × Array Block))
    (cols : List (BoxWidth × Array Block)) (h : floatsInCols c.within c.scope cols = true)
    (ha : ∀ k out, floatNumsCols k out acc.toList = floatNumsCols k out acc'.toList) :
    Agree (numberFloatCols true c acc cols).1 (numberFloatCols false c acc' cols).1 c ∧
      ∀ k out, floatNumsCols k out (numberFloatCols true c acc cols).2.toList =
        floatNumsCols k out (numberFloatCols false c acc' cols).2.toList := by
  match cols with
  | [] => exact ⟨⟨rfl, rfl, rfl⟩, by simpa [numberFloatCols] using ha⟩
  | (w, body) :: rest =>
    simp only [floatsInCols, Bool.and_eq_true] at h
    obtain ⟨⟨hc, hw, hs⟩, hn⟩ := numberFloatList_within c #[] #[] body.toList h.1 (fun _ _ => rfl)
    have hr : floatsInCols (numberFloatList false c #[] body.toList).1.within
        (numberFloatList false c #[] body.toList).1.scope rest = true := by rw [hw, hs]; exact h.2
    obtain ⟨⟨hc2, hw2, hs2⟩, hn2⟩ := numberFloatCols_within
      (numberFloatList false c #[] body.toList).1
      (acc.push (w, (numberFloatList true c #[] body.toList).2))
      (acc'.push (w, (numberFloatList false c #[] body.toList).2)) rest hr (by
        intro k out
        simp only [Array.toList_push, floatNumsCols_append, floatNumsCols, ha k out, hn k])
    simp only [numberFloatCols]
    rw [hc]
    exact ⟨⟨hc2, hw2.trans hw, hs2.trans hs⟩, hn2⟩
termination_by structural cols

private theorem numberFloatOne_within (c : FloatCtr) (b : Block)
    (h : floatsInOne c.within c.scope b = true) :
    Agree (numberFloatOne true c b).1 (numberFloatOne false c b).1 c ∧
      ∀ k out, floatNumsOne k out (numberFloatOne true c b).2 =
        floatNumsOne k out (numberFloatOne false c b).2 := by
  match b with
  | .para _ | .lines _ | .equation _ _ | .section _ _ _ _ | .note _ | .verbatim _ _ _ | .logo _
  | .algorithm _ _ _ | .bibliography _ _ _ | .contents _ _ | .framefoot _ | .setPalette _
  | .setTokens _ | .pagebreak | .rule _ _ _ | .picture _ | .table _ _ _ _ _ _ =>
    exact ⟨⟨by simp [numberFloatOne], by simp [numberFloatOne], by simp [numberFloatOne]⟩,
      fun _ _ => by simp [numberFloatOne]⟩
  | .list _ _ items =>
    simp only [floatsInOne] at h
    obtain ⟨⟨hc, hw, hs⟩, hn⟩ := numberFloatItems_within c #[] #[] items.toList h (fun _ _ => rfl)
    exact ⟨⟨by simpa [numberFloatOne] using hc, by simpa [numberFloatOne] using hw,
      by simpa [numberFloatOne] using hs⟩, fun k out => by simpa [numberFloatOne, floatNumsOne] using hn k out⟩
  | .columns cols =>
    simp only [floatsInOne] at h
    obtain ⟨⟨hc, hw, hs⟩, hn⟩ := numberFloatCols_within c #[] #[] cols.toList h (fun _ _ => rfl)
    exact ⟨⟨by simpa [numberFloatOne] using hc, by simpa [numberFloatOne] using hw,
      by simpa [numberFloatOne] using hs⟩, fun k out => by simpa [numberFloatOne, floatNumsOne] using hn k out⟩
  | .center body =>
    simp only [floatsInOne] at h
    obtain ⟨⟨hc, hw, hs⟩, hn⟩ := numberFloatList_within c #[] #[] body.toList h (fun _ _ => rfl)
    exact ⟨⟨by simpa [numberFloatOne] using hc, by simpa [numberFloatOne] using hw,
      by simpa [numberFloatOne] using hs⟩, fun k out => by simpa [numberFloatOne, floatNumsOne] using hn k out⟩
  | .ragged _ body =>
    simp only [floatsInOne] at h
    obtain ⟨⟨hc, hw, hs⟩, hn⟩ := numberFloatList_within c #[] #[] body.toList h (fun _ _ => rfl)
    exact ⟨⟨by simpa [numberFloatOne] using hc, by simpa [numberFloatOne] using hw,
      by simpa [numberFloatOne] using hs⟩, fun k out => by simpa [numberFloatOne, floatNumsOne] using hn k out⟩
  | .quote _ body =>
    simp only [floatsInOne] at h
    obtain ⟨⟨hc, hw, hs⟩, hn⟩ := numberFloatList_within c #[] #[] body.toList h (fun _ _ => rfl)
    exact ⟨⟨by simpa [numberFloatOne] using hc, by simpa [numberFloatOne] using hw,
      by simpa [numberFloatOne] using hs⟩, fun k out => by simpa [numberFloatOne, floatNumsOne] using hn k out⟩
  | .abstract body =>
    simp only [floatsInOne] at h
    obtain ⟨⟨hc, hw, hs⟩, hn⟩ := numberFloatList_within c #[] #[] body.toList h (fun _ _ => rfl)
    exact ⟨⟨by simpa [numberFloatOne] using hc, by simpa [numberFloatOne] using hw,
      by simpa [numberFloatOne] using hs⟩, fun k out => by simpa [numberFloatOne, floatNumsOne] using hn k out⟩
  | .titled _ _ body =>
    simp only [floatsInOne] at h
    obtain ⟨⟨hc, hw, hs⟩, hn⟩ := numberFloatList_within c #[] #[] body.toList h (fun _ _ => rfl)
    exact ⟨⟨by simpa [numberFloatOne] using hc, by simpa [numberFloatOne] using hw,
      by simpa [numberFloatOne] using hs⟩, fun k out => by simpa [numberFloatOne, floatNumsOne] using hn k out⟩
  | .disclosure _ _ body =>
    simp only [floatsInOne] at h
    obtain ⟨⟨hc, hw, hs⟩, hn⟩ := numberFloatList_within c #[] #[] body.toList h (fun _ _ => rfl)
    exact ⟨⟨by simpa [numberFloatOne] using hc, by simpa [numberFloatOne] using hw,
      by simpa [numberFloatOne] using hs⟩, fun k out => by simpa [numberFloatOne, floatNumsOne] using hn k out⟩
  | .role _ body =>
    simp only [floatsInOne] at h
    obtain ⟨⟨hc, hw, hs⟩, hn⟩ := numberFloatList_within c #[] #[] body.toList h (fun _ _ => rfl)
    exact ⟨⟨by simpa [numberFloatOne] using hc, by simpa [numberFloatOne] using hw,
      by simpa [numberFloatOne] using hs⟩, fun k out => by simpa [numberFloatOne, floatNumsOne] using hn k out⟩
  | .link _ body =>
    simp only [floatsInOne] at h
    obtain ⟨⟨hc, hw, hs⟩, hn⟩ := numberFloatList_within c #[] #[] body.toList h (fun _ _ => rfl)
    exact ⟨⟨by simpa [numberFloatOne] using hc, by simpa [numberFloatOne] using hw,
      by simpa [numberFloatOne] using hs⟩, fun k out => by simpa [numberFloatOne, floatNumsOne] using hn k out⟩
  | .spaced _ body =>
    simp only [floatsInOne] at h
    obtain ⟨⟨hc, hw, hs⟩, hn⟩ := numberFloatList_within c #[] #[] body.toList h (fun _ _ => rfl)
    exact ⟨⟨by simpa [numberFloatOne] using hc, by simpa [numberFloatOne] using hw,
      by simpa [numberFloatOne] using hs⟩, fun k out => by simpa [numberFloatOne, floatNumsOne] using hn k out⟩
  | .onSteps _ body =>
    simp only [floatsInOne] at h
    obtain ⟨⟨hc, hw, hs⟩, hn⟩ := numberFloatList_within c #[] #[] body.toList h (fun _ _ => rfl)
    exact ⟨⟨by simpa [numberFloatOne] using hc, by simpa [numberFloatOne] using hw,
      by simpa [numberFloatOne] using hs⟩, fun k out => by simpa [numberFloatOne, floatNumsOne] using hn k out⟩
  | .only _ body =>
    simp only [floatsInOne] at h
    obtain ⟨⟨hc, hw, hs⟩, hn⟩ := numberFloatList_within c #[] #[] body.toList h (fun _ _ => rfl)
    exact ⟨⟨by simpa [numberFloatOne] using hc, by simpa [numberFloatOne] using hw,
      by simpa [numberFloatOne] using hs⟩, fun k out => by simpa [numberFloatOne, floatNumsOne] using hn k out⟩
  | .nav _ body =>
    simp only [floatsInOne] at h
    obtain ⟨⟨hc, hw, hs⟩, hn⟩ := numberFloatList_within c #[] #[] body.toList h (fun _ _ => rfl)
    exact ⟨⟨by simpa [numberFloatOne] using hc, by simpa [numberFloatOne] using hw,
      by simpa [numberFloatOne] using hs⟩, fun k out => by simpa [numberFloatOne, floatNumsOne] using hn k out⟩
  | .frame _ _ _ _ body =>
    simp only [floatsInOne] at h
    obtain ⟨⟨hc, hw, hs⟩, hn⟩ := numberFloatList_within c #[] #[] body.toList h (fun _ _ => rfl)
    exact ⟨⟨by simpa [numberFloatOne] using hc, by simpa [numberFloatOne] using hw,
      by simpa [numberFloatOne] using hs⟩, fun k out => by simpa [numberFloatOne, floatNumsOne] using hn k out⟩
  | .altSteps _ firstPage otherPage =>
    simp only [floatsInOne, Bool.and_eq_true] at h
    obtain ⟨⟨hc, hw, hs⟩, hn⟩ :=
      numberFloatList_within c #[] #[] firstPage.toList h.1 (fun _ _ => rfl)
    have hr : floatsInList (numberFloatList false c #[] firstPage.toList).1.within
        (numberFloatList false c #[] firstPage.toList).1.scope otherPage.toList = true := by
      rw [hw, hs]; exact h.2
    obtain ⟨⟨hc2, hw2, hs2⟩, hn2⟩ := numberFloatList_within
      (numberFloatList false c #[] firstPage.toList).1 #[] #[] otherPage.toList hr (fun _ _ => rfl)
    refine ⟨⟨?_, ?_, ?_⟩, fun k out => ?_⟩
    · simp only [numberFloatOne]; rw [hc]; exact hc2
    · simp only [numberFloatOne]; exact hw2.trans hw
    · simp only [numberFloatOne]; exact hs2.trans hs
    · simp only [numberFloatOne, floatNumsOne]; rw [hn k out, hc, hn2]
  | .float kind num capAbove body caption =>
    simp only [floatsInOne, Bool.and_eq_true] at h
    have hreset : ((kind == .figure || kind == .table) && ((num.map (·.within)).getD "" != c.within ||
        (num.map (·.scope)).getD 0 != c.scope)) = false := by
      cases hk : (kind == .figure || kind == .table)
      · rfl
      · have h1 := h.1
        simp only [hk, Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at h1
        simp [h1.1, h1.2]
    have hA : ∀ c2 : FloatCtr, c2.within = c.within → c2.scope = c.scope →
        Agree (numberFloatList true c2 #[] body.toList).1 (numberFloatList false c2 #[] body.toList).1 c2 ∧
          SameNums (numberFloatList true c2 #[] body.toList).2 (numberFloatList false c2 #[] body.toList).2 :=
      fun c2 hw hs => numberFloatList_within c2 #[] #[] body.toList (by rw [hw, hs]; exact h.2)
        (fun _ _ => rfl)
    simp only [numberFloatOne, Bool.true_and, Bool.false_and, hreset, Bool.false_eq_true, ite_false]
    have hwA : (if caption.isEmpty = true then c else c.bump kind).within = c.within ∧
        (if caption.isEmpty = true then c else c.bump kind).scope = c.scope := by
      split <;> cases kind <;> simp [FloatCtr.bump]
    generalize (if caption.isEmpty = true then c else c.bump kind) = cA at hwA ⊢
    obtain ⟨⟨heq, hw, hs⟩, hn⟩ := hA { cA with sub := 0 } hwA.1 hwA.2
    refine ⟨?_, fun k out => ?_⟩
    · rw [heq]
      exact ⟨rfl, hw.trans hwA.1, hs.trans hwA.2⟩
    · cases hcap : caption.isEmpty <;> simp [floatNumsOne, hn k]
termination_by structural b

end

/-- By chapter, the figures and tables of the chapter the counters stand in number on from its
count, one each and gapless, the counter advancing by exactly as many. -/
private theorem number_gapless_within (k : FloatKind) (c : FloatCtr) (bs : List Block)
    (h : floatsInList c.within c.scope bs = true) :
    ∃ n, ((numberFloatList true c #[] bs).1).get k = c.get k + n ∧
      floatNumsList k [] ((numberFloatList true c #[] bs).2).toList = List.range' (c.get k + 1) n := by
  obtain ⟨⟨heq, -, -⟩, hn⟩ := numberFloatList_within c #[] #[] bs h (fun _ _ => rfl)
  obtain ⟨n, hc, hl⟩ := numberFloatList_exact k c #[] [] bs
  refine ⟨n, by rw [heq]; exact hc, ?_⟩
  rw [hn k [], hl]
  rfl

end LeanTex.Core.Ir
