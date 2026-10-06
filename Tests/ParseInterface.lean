module

import LeanTex.Core.Parse

/-! Ordinary consumers use the raw tree, readers, source spelling, wrappers,
and provenance contracts. Delimiter state and scanning helpers stay private.
Only the reductions used by Compat and Elab belong to the interface. -/

open LeanTex.Core
open LeanTex.Core.Parse

namespace Tests.ParseInterface

example : Inhabited Raw := inferInstance
example : BEq Raw := inferInstance
example : Repr Raw := inferInstance

example (p : Pos) (body : Array Raw) : Array Raw :=
  #[.word "alpha" p, .space, .par p, .ctrl "beta" p, .sym '+' p,
    .group body p, .math false body p, .env "gamma" body p,
    .verb "verbatim" "delta" p]

example (raw : Raw) : Option Pos :=
  match raw with
  | .space => none
  | .word _ p | .par p | .ctrl _ p | .sym _ p | .group _ p
  | .math _ _ p | .env _ _ p | .verb _ _ p => some p

example : String → Array Lex.Token → Array Raw × Array Diag := Parse.parse
example : Raw → Option (List MacroOrigin) := Raw.origins?
example : MacroOrigin → Raw → Raw := markMacro
example : MacroOrigin → Array Raw → List Raw → Array Raw := markMacroList
example : List String := envDefiners
example : String → String := splitOpen
example : String → String := splitClose
example : String → Option String := splitOpen?
example : String → Option String := splitClose?
example : String → String → Array Raw → Pos → Array Raw × Diag := settleOpenHalf
example : String → String → Pos → Diag := closeHalfDiag
example : String → Option (String × Nat) := listingOptHead
example : String → Nat → Option (String × Nat) := mintedLangHead
example : String → String := inputEnv
example : String → Option String := inputEnvFile?
example : String := scopeEnv
example : Array Raw → Array Raw := definerWindow

example (origin : MacroOrigin) (raw : Raw) :
    (markMacro origin raw).origins? = raw.origins?.map (origin :: ·) :=
  markMacro_origins_exact origin raw
example (origin : MacroOrigin) (acc : Array Raw) (raws : List Raw) :
    (markMacroList origin acc raws).toList = acc.toList ++ raws.map (markMacro origin) :=
  markMacroList_toList origin acc raws
example (raws : Array Raw) :
    definerWindow (definerWindow raws) = definerWindow raws :=
  definerWindow_fixed_point raws
example (raws : Array Raw) (i : Nat) : i ≤ skipSpaces raws i := skipSpaces_ge raws i
example (body : Array Raw) (p : Pos) :
    rawSrcOne (.env scopeEnv body p) = rawSrcOne (.group body p) :=
  scopeEnv_source_exact body p
example (origin : MacroOrigin) (raws : Array Raw) :
    rawSrc (markMacroList origin #[] raws.toList) = rawSrc raws :=
  markMacroArray_source_exact origin raws
example (origin : MacroOrigin) (raws : List Raw) :
    rawSrcList (raws.map (markMacro origin)) = rawSrcList raws :=
  markMacroList_source_exact origin raws
example (origin : MacroOrigin) (raw : Raw) :
    rawSrcOne (markMacro origin raw) = rawSrcOne raw :=
  markMacro_source_exact origin raw

example (p : Pos) : (Raw.ctrl "alpha" p).origins? = some p.origins := by rfl
example (name : String) :
    inputEnvFile? name =
      (if name.startsWith "input " then some ((name.drop "input ".length).toString)
       else none) := by rfl
example (raws : Array Raw) :
    rawSrc raws = (rawSrcList raws.toList).trimAscii.toString := by rw [rawSrc]
example (raw : Raw) (raws : List Raw) :
    rawSrcList (raw :: raws) = rawSrcOne raw ++ rawSrcList raws := by rfl
example (name : String) (p : Pos) :
    rawSrcOne (.ctrl name p) = "\\" ++ name ++ " " := by rfl
example (raws : Array Raw) (i : Nat) (h : raws.size ≤ i) : skipSpaces raws i = i := by
  rw [skipSpaces.eq_def]
  simp only [show ¬ i < raws.size from Nat.not_lt_of_ge h, dite_false]
-- Elab's scanning contract uses the exported functional induction principle.
example (raws : Array Raw) (i : Nat) : i ≤ skipSpaces raws i := by
  fun_induction skipSpaces raws i <;> omega

example : True := by
  fail_if_success have := Parse.Stop
  fail_if_success have := Parse.Stop.name
  fail_if_success have := Parse.Stop.halfName
  fail_if_success have := Parse.Frame
  fail_if_success have := Parse.Frame.close
  fail_if_success have := Parse.halfStop
  fail_if_success have := Parse.unclosedAtBrace
  fail_if_success have := Parse.unmatchedEnd
  fail_if_success have := Parse.backSkip
  fail_if_success have := Parse.before
  fail_if_success have := Parse.isSym
  fail_if_success have := Parse.definerHeadAt
  fail_if_success have := Parse.definerReach
  fail_if_success have := Parse.envBodyNext
  fail_if_success have := Parse.envBodyNext_window_exact
  fail_if_success have := Parse.err
  fail_if_success have := Parse.envName
  trivial

end Tests.ParseInterface
