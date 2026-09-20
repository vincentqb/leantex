import Std.Data.HashMap
import LeanTex.Core.HyphenData
import LeanTex.Core.Nfc

namespace LeanTex.Core.Hyphen

open Std

/-- Liang patterns: letters → inter-letter weights (odd allows a break),
plus the exception dictionary. English hyphenmins: left 2, right 3. -/
structure Patterns where
  map : HashMap String (Array Nat)
  exceptions : HashMap String (Array Nat)
  maxLen : Nat
  leftMin : Nat := 2
  rightMin : Nat := 3

private def parsePattern (p : String) : String × Array Nat := Id.run do
  let mut letters := ""
  let mut vals : Array Nat := #[0]
  for c in p.toList do
    if c.isDigit then
      vals := vals.set! (vals.size - 1) (c.toNat - '0'.toNat)
    else
      letters := letters.push c
      vals := vals.push 0
  return (letters, vals)

private def parseException (w : String) : String × Array Nat := Id.run do
  let mut word := ""
  let mut breaks : Array Nat := #[]
  for c in w.toList do
    if c == '-' then
      breaks := breaks.push word.length
    else
      word := word.push c
  return (word, breaks)

def load : Patterns := Id.run do
  let mut map : HashMap String (Array Nat) := {}
  let mut maxLen := 0
  for p in HyphenData.patterns.splitOn " " do
    if p != "" then
      let (letters, vals) := parsePattern p
      map := map.insert letters vals
      maxLen := max maxLen letters.length
  let mut exceptions : HashMap String (Array Nat) := {}
  for w in HyphenData.exceptions.splitOn " " do
    if w != "" then
      let (word, breaks) := parseException w
      exceptions := exceptions.insert word breaks
  return { map := map, exceptions := exceptions, maxLen := maxLen }

/-- Break positions (letters before the break) for a lowercase-folded word.
Only positions respecting leftMin/rightMin are returned. -/
def hyphenate (pats : Patterns) (word : String) : Array Nat := Id.run do
  -- Unicode fold, not `Char.toLower`: French and German patterns spell
  -- their letters lowercase, and an ASCII-only fold leaves É beside é.
  let lower := String.ofList (word.toList.map Nfc.toLower)
  let n := lower.length
  if n < pats.leftMin + pats.rightMin then
    return #[]
  if let some breaks := pats.exceptions[lower]? then
    return breaks.filter fun p => p ≥ pats.leftMin && p + pats.rightMin ≤ n
  let wrapped := ("." ++ lower ++ ".").toList.toArray
  let l := wrapped.size
  let mut weights : Array Nat := Array.replicate (l + 1) 0
  for start in [0:l] do
    for len in [1:pats.maxLen + 1] do
      if start + len ≤ l then
        let sub := String.ofList ((wrapped.extract start (start + len)).toList)
        if let some vals := pats.map[sub]? then
          for k in [0:vals.size] do
            let idx := start + k
            if weights[idx]! < vals[k]! then
              weights := weights.set! idx vals[k]!
  let mut breaks : Array Nat := #[]
  -- wrapped gap i sits after wrapped[0..i); word position = i - 1
  for i in [2:l] do
    if weights[i]! % 2 == 1 then
      let p := i - 1
      if p ≥ pats.leftMin && p + pats.rightMin ≤ n then
        breaks := breaks.push p
  return breaks

end LeanTex.Core.Hyphen
