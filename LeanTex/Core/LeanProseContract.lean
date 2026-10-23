module

public import LeanTex.Core.LeanProse
import all LeanTex.Core.LeanProse

/-! # The tables a page says statements through

The core table's lexicon is well formed, a page's table stays well formed with each phrase it
takes, so every statement a page says in words reads back as itself. -/

namespace LeanTex.Core.LeanProse

open LeanTex.Core

/-- The core table's lexicon is well formed, whichever order Lean passes a membership's sides in. -/
public theorem coreTable_contract (collectionFirst : Bool) :
    (coreTable collectionFirst).lexicon.wf = true := by
  cases collectionFirst <;> decide +kernel

private theorem declare_contract {facts : LeanFacts.Facts} {taken : List String} {tb tb' : Table}
    {name text c : String} {t : Template} (h : tb.declare facts taken name text = .ok (c, t, tb')) :
    tb'.lexicon.wf = true := by
  unfold Table.declare at h
  split at h
  · split at h
    · rename_i hwf
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, -, rfl⟩ := h
      exact hwf
    · cases h
  · cases h

private theorem declareStep_contract (facts : LeanFacts.Facts) (acc : Declared)
    (e : String × String) (h : acc.table.lexicon.wf = true) :
    (declareStep facts acc e).table.lexicon.wf = true := by
  unfold declareStep
  split
  · rename_i heq; exact declare_contract heq
  · exact h

private theorem foldl_contract (facts : LeanFacts.Facts) :
    ∀ (l : List (String × String)) (acc : Declared),
      acc.table.lexicon.wf = true → (l.foldl (declareStep facts) acc).table.lexicon.wf = true
  | [], _, h => h
  | e :: rest, acc, h => foldl_contract facts rest _ (declareStep_contract facts acc e h)

/-- A page's table is well formed, whatever phrases its directive declares. -/
public theorem tableFor_contract (facts : LeanFacts.Facts) (declared : List (String × String)) :
    (tableFor facts declared).table.lexicon.wf = true :=
  foldl_contract facts declared _ (coreTable_contract _)

/-- Every statement a page says in words, through the core table or the one its phrases make, reads
back as itself. -/
public theorem page_parse_exact {facts : LeanFacts.Facts} {declared : List (String × String)}
    {d : LeanFacts.Decl} {type : LeanFacts.Term} {s : Stmt Leaf}
    (h : proseOf facts (tableFor facts declared).table d type = .ok s) :
    parse (tableFor facts declared).table.lexicon (render s) = some s :=
  proseOf_parse_exact (tableFor_contract facts declared) h

end LeanTex.Core.LeanProse
