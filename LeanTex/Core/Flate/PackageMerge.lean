module

import LeanTex.Core.Flate.Progress

namespace LeanTex.Core.Flate.PackageMerge

/-- Adjacent packages are paired without carrying their symbol sets. -/
def pairWeights (weights : Array Nat) : Array Nat := Id.run do
  let mut pairs : Array Nat := #[]
  for k in [0:weights.size / 2] do
    pairs := pairs.push (weights[2 * k]?.getD 0 + weights[2 * k + 1]?.getD 0)
  return pairs

/-- Merges the leaves with the previous level's pairs, flagging each item's provenance; a tie prefers a leaf. -/
def merge (items pairs : Array Nat) : Array Nat × Array Bool := Id.run do
  let mut weights : Array Nat := Array.mkEmpty (items.size + pairs.size)
  let mut flags : Array Bool := Array.mkEmpty (items.size + pairs.size)
  let mut a := 0
  let mut b := 0
  for _ in [0:items.size + pairs.size] do
    if a < items.size && (b ≥ pairs.size || items[a]?.getD 0 ≤ pairs[b]?.getD 0) then
      weights := weights.push (items[a]?.getD 0)
      flags := flags.push true
      a := a + 1
    else if b < pairs.size then
      weights := weights.push (pairs[b]?.getD 0)
      flags := flags.push false
      b := b + 1
  return (weights, flags)

/-- The package lists, from the smallest denomination to the largest. -/
def levels (items : Array Nat) (limit : Nat) : Array (Array Bool) := Id.run do
  let mut weights := items
  let mut flags := Array.replicate items.size true
  let mut out : Array (Array Bool) := #[]
  for _ in [1:limit] do
    out := out.push flags
    (weights, flags) := merge items (pairWeights weights)
  return out.push flags

/-- Counts the leaves and packages in the selected prefix. -/
def selected (flags : Array Bool) (take : Nat) : Nat × Nat := Id.run do
  let mut leaves := 0
  let mut pairs := 0
  for j in [0:take] do
    if flags[j]?.getD true then leaves := leaves + 1 else pairs := pairs + 1
  return (leaves, pairs)

/-- Adds one bit to the length of each of the first `leaves` symbols of `sorted`. -/
def addBits (sorted lens : Array Nat) (leaves : Nat) : Array Nat := Id.run do
  let mut lens := lens
  for j in [0:leaves] do
    let s := sorted[j]?.getD 0
    lens := lens.set! s (lens[s]?.getD 0 + 1)
  return lens

/-- Expands the selected packages, counting each selected leaf once per level. -/
def backtrace (sorted : Array Nat) (size : Nat) (levels : Array (Array Bool)) :
    Array Nat := Id.run do
  let mut lens := Array.replicate size 0
  let mut take := 2 * sorted.size - 2
  for li in [0:levels.size] do
    let flags := levels[levels.size - 1 - li]?.getD #[]
    let (leaves, pairs) := selected flags take
    lens := addBits sorted lens leaves
    take := 2 * pairs
    if take == 0 then break
  return lens

/-- Length-limited package-merge; a one-symbol alphabet takes the one-bit code (RFC 1951 §3.2.7). -/
public def lengths (freqs : Array Nat) (limit : Nat) : Array Nat := Id.run do
  let syms := (Array.range freqs.size).filter fun s => freqs[s]?.getD 0 > 0
  let n := syms.size
  if n == 0 then
    return Array.replicate freqs.size 0
  if n == 1 then
    return (Array.replicate freqs.size 0).set! (syms[0]?.getD 0) 1
  let sorted := (syms.toList.mergeSort fun a b => freqs[a]?.getD 0 ≤ freqs[b]?.getD 0).toArray
  let items := sorted.map fun s => freqs[s]?.getD 0
  return backtrace sorted freqs.size (levels items limit)

end LeanTex.Core.Flate.PackageMerge
