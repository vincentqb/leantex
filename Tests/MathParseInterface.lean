import LeanTex.Core.MathParse

/-! Ordinary consumers can construct the formula environment, classify the
reported notes, call both readers and use their containment contract.
Token scanning and recovery state are implementation details. -/

open LeanTex.Core
open LeanTex.Core.Math
open LeanTex.Core.MathParse

namespace Tests.MathParseInterface

example : Repr Note := inferInstance
example : BEq Note := inferInstance

example (resolve : String → Option (Ir.Color × Bool)) (cancel : CancelSpec)
    (missed : Option String) : Env :=
  { ink := resolve, cancel := cancel, cancelMiss := missed }

example (env : Env) :
    (String → Option (Ir.Color × Bool)) × CancelSpec × Option String :=
  (env.ink, env.cancel, env.cancelMiss)

example (note : Note) : String :=
  match note with
  | .ragged message | .styleDropped message | .constructFloored message
  | .inkMissed message => message
  | .inkUsed expression _ _ => expression

example : Bool → Array Parse.Raw → Env → Except String (MList × Array Note) :=
  fun display raws env => parseMath display raws env

example : GridKind → Array Parse.Raw → Env → Except String (MList × Array Note) :=
  fun kind raws env => parseMathRows kind raws env

example : String → Bool := knownCtrl

example (display : Bool) (raws : Array Parse.Raw) (env : Env)
    (formula : MList) (notes : Array Note)
    (parsed : parseMath display raws env = .ok (formula, notes)) :
    ∀ name, Note.constructFloored name ∈ notes →
      ∃ command, name = "\\" ++ command ∧ knownCtrl command = false ∧
        (Ir.floorNamedArgs.lookup command).isSome :=
  mathContain_accounts display raws formula notes parsed

example : True := by
  fail_if_success have := MathParse.greekLiteral
  fail_if_success have := MathParse.charAtom
  fail_if_success have := MathParse.greekSpellings
  fail_if_success have := MathParse.greek_literal_agree
  fail_if_success have := MathParse.greek_literal_covers
  trivial

example : True := by
  fail_if_success have := MathParse.limitOps
  fail_if_success have := MathParse.limitWords
  fail_if_success have := MathParse.textStyleCtrl
  fail_if_success have := MathParse.textNeutralCtrl
  fail_if_success have := MathParse.delimChar
  fail_if_success have := MathParse.cancelCtrl
  fail_if_success have := MathParse.bigCtrl
  trivial

example : True := by
  fail_if_success have := MathParse.MTok
  fail_if_success have := MathParse.flattenList
  fail_if_success have := MathParse.containPlan
  fail_if_success have := MathParse.ContainedName
  fail_if_success have := MathParse.containUnknown
  fail_if_success have := MathParse.PFrame
  fail_if_success have := MathParse.ParserNotes
  fail_if_success have := MathParse.parseToks
  trivial

end Tests.MathParseInterface
