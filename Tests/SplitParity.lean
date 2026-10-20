module

public import Tests.Support
public import Tests.Support.Rand
public import LeanTex.Core.Split

public section

/-! The engine's `splitWhere` against Lean's `String.split` over invented texts. -/

namespace Tests.SplitParity

/-- A text of `n` characters drawn from separators, letters and wide scalars. -/
def genText (n : Nat) (s : UInt64) : String × UInt64 := Id.run do
  let alphabet := #['a', ' ', '\t', ',', 'é', '😀', '\n', 'b']
  let mut out := ""
  let mut s := s
  for _ in [0:n] do
    let (k, s') := rand s alphabet.size
    s := s'
    out := out.push (alphabet[k]?.getD 'a')
  return (out, s)

end Tests.SplitParity

open LeanTex.Core Tests.SplitParity in
/-- `splitWhere` cuts every text where `String.split` does, empty pieces kept. -/
def splitParityChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let preds : List (Char → Bool) := [Char.isWhitespace, (fun c => c == ',' || c == ' '), (· == 'z')]
  let edges := ["", " ", "  ", "a", " a ", "a  b", ",a,,b,", "😀 é"]
  let mut misses : Array String := #[]
  for text in edges do
    for p in preds do
      if splitWhere text p != (text.split p).toList.map (·.toString) then misses := misses.push text
  let mut seed : UInt64 := 1021
  for i in [0:2000] do
    let (text, s) := genText (i % 17) seed
    seed := s
    for p in preds do
      if splitWhere text p != (text.split p).toList.map (·.toString) then misses := misses.push text
  t s!"split parity: every text cuts alike in both splitters (differing: {misses.toList.take 5})"
    misses.isEmpty
