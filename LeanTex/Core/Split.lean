module

public section

namespace LeanTex.Core

/-- The pieces of `s` between the characters `p` holds of, empty ones kept, as `String.split`
cuts it (`splitParityChecks`), by a fold the kernel reads. -/
def splitWhere (s : String) (p : Char → Bool) : List String :=
  let (pieces, cur) := s.toList.foldl (init := ((#[] : Array String), ([] : List Char)))
    fun (pieces, cur) c => if p c then (pieces.push (String.ofList cur.reverse), []) else (pieces, c :: cur)
  (pieces.push (String.ofList cur.reverse)).toList

end LeanTex.Core
