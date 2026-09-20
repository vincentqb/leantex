import Std.Data.HashMap
import LeanTex.Core.HyphenData
import LeanTex.Core.HyphenDataFr
import LeanTex.Core.HyphenDataDe
import LeanTex.Core.LocaleData
import LeanTex.Core.Nfc

namespace LeanTex.Core.Hyphen

open Std

/-- Liang patterns: letters → inter-letter weights (odd allows a break),
plus the exception dictionary. The hyphenation minima are locale data
(babel ini `lefthyphenmin`/`righthyphenmin`): the shortest fragment a
break may leave on each side. -/
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

/-- Build one language's table from its generated pattern strings and its
locale's hyphenation minima. -/
def load' (patternData exceptionData : String) (leftMin rightMin : Nat) :
    Patterns := Id.run do
  let mut map : HashMap String (Array Nat) := {}
  let mut maxLen := 0
  for p in patternData.splitOn " " do
    if p != "" then
      let (letters, vals) := parsePattern p
      map := map.insert letters vals
      maxLen := max maxLen letters.length
  let mut exceptions : HashMap String (Array Nat) := {}
  for w in exceptionData.splitOn " " do
    if w != "" then
      let (word, breaks) := parseException w
      exceptions := exceptions.insert word breaks
  return { map, exceptions, maxLen, leftMin, rightMin }

-- Each language's table is a `Thunk` (call-by-need): a zero-argument
-- constant is computed at process start, and parsing three pattern sets
-- there cost every run ~40 ms whichever language it used. Only the
-- selected table builds, once.

def english : Thunk Patterns := Thunk.mk fun _ =>
  load' HyphenData.patterns HyphenData.exceptions
    Locale.en.leftMin Locale.en.rightMin

def french : Thunk Patterns := Thunk.mk fun _ =>
  load' HyphenDataFr.patterns HyphenDataFr.exceptions
    Locale.fr.leftMin Locale.fr.rightMin

def german : Thunk Patterns := Thunk.mk fun _ =>
  load' HyphenDataDe.patterns HyphenDataDe.exceptions
    Locale.de.leftMin Locale.de.rightMin

/-- The pattern table a BCP 47 tag selects: a language with a locale
record but no landed table would be honestly unhyphenated rather than
wrongly English. (German's 272 KB literal was gated on compile cost;
measured at 0.65 s against the English file's 0.72 s, it lands.) -/
def forTag (tag : String) : Option Patterns :=
  match (Locale.forTag tag).map (·.tag) with
  | some "en" => some english.get
  | some "fr" => some french.get
  | some "de" => some german.get
  | _ => none

/-- The candidate break weights of the pattern walk, before the minima
filter: every odd inter-letter weight, over the dot-wrapped word. -/
private def rawBreaks (pats : Patterns) (lower : String) : Array Nat := Id.run do
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
      breaks := breaks.push (i - 1)
  return breaks

/-- Break positions (letters before the break) for a word, folded to
lowercase (Unicode fold: the fr patterns spell é directly). Only positions
respecting leftMin/rightMin are returned — the shape is one final filter,
which is what `hyphenate_respects_min` reads. -/
def hyphenate (pats : Patterns) (word : String) : Array Nat :=
  let lower := String.ofList (word.toList.map Nfc.toLower)
  let candidates :=
    if lower.length < pats.leftMin + pats.rightMin then #[]
    else match pats.exceptions[lower]? with
      | some breaks => breaks
      | none => rawBreaks pats lower
  candidates.filter fun p => p ≥ pats.leftMin && p + pats.rightMin ≤ lower.length

/-- Every break respects the locale's hyphenation minima: at least
`leftMin` letters stay before the hyphen and `rightMin` after (babel ini
`lefthyphenmin`/`righthyphenmin`; TeX's `\lefthyphenmin` semantics). What
makes German's 2/2 safe to vary per locale. -/
theorem hyphenate_respects_min (pats : Patterns) (word : String) :
    ∀ p ∈ hyphenate pats word,
      pats.leftMin ≤ p ∧
        p + pats.rightMin ≤ (word.toList.map Nfc.toLower).length := by
  intro p hp
  unfold hyphenate at hp
  have := Array.mem_filter.mp hp
  have hpred := this.2
  simp only [ge_iff_le, Bool.and_eq_true, decide_eq_true_eq] at hpred
  have hlen : (String.ofList (word.toList.map Nfc.toLower)).length
      = (word.toList.map Nfc.toLower).length := by
    simp [String.length_ofList]
  omega

end LeanTex.Core.Hyphen
