module

import LeanTex.Core.Data

/-! Ordinary clients request sources, expand raw documents, and use the
input-provenance contract. Record bindings and expansion state stay private. -/

open LeanTex.Core
open LeanTex.Core.Parse

namespace Tests.DataInterface

example : String → String := Data.sourceName
example (name : String) : Data.sourceName name = Bib.sourceName name := rfl
example : String → Array Raw → Array (String × Span) := Data.fileRefsAt
example : Array Raw → Array (String × Pos) := Data.fileRefs
example : Array Raw → Bool := Data.hasData
example : String → Array (String × String) → Array Raw → Array Raw × Array Diag :=
  Data.expandData

example (file : String) (raws : Array Raw) : Array (String × String × Pos) :=
  (Data.fileRefsAt file raws).map fun (name, span) => (name, span.file, span.pos)

example (caller file name : String) (body : Array Raw) (pos : Pos)
    (h : inputEnvFile? name = some file) :
    Data.fileRefsAt caller #[.env name body pos] = Data.fileRefsAt file body :=
  Data.fileRefsAt_input_exact caller file name body pos h

example : True := by
  fail_if_success have := Data.dataDecl?
  fail_if_success have := Data.refsList
  fail_if_success have := Data.hasDataList
  fail_if_success have := Data.Store
  fail_if_success have := Data.Store.kinds
  fail_if_success have := Data.Binding
  fail_if_success have := Data.resolveVar
  fail_if_success have := Data.resolvePath
  fail_if_success have := Data.valParsed
  fail_if_success have := Data.bracketSplit
  fail_if_success have := Data.optArg
  fail_if_success have := Data.foreachArgs
  fail_if_success have := Data.St
  fail_if_success have := Data.M
  fail_if_success have := Data.say
  fail_if_success have := Data.install
  fail_if_success have := Data.onData
  fail_if_success have := Data.sayNoRecords
  fail_if_success have := Data.expandList
  fail_if_success have := Data.expandEach
  trivial

end Tests.DataInterface
