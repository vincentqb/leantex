module

import LeanTex.Core.Flate.Progress

namespace LeanTex.Core.Flate.PackageMerge

/-- Adjacent packages are paired without carrying their symbol sets. -/
def pairWeights (weights : Array Nat) : Array Nat := Id.run do
  let mut pairs : Array Nat := #[]
  for k in [0:weights.size / 2] do
    pairs := pairs.push (weights[2 * k]?.getD 0 + weights[2 * k + 1]?.getD 0)
  return pairs

/-- Merge the original leaves with the preceding level's pairs. The flag is
the provenance the backtrace reads; weight ties prefer a leaf. -/
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

/-- Count the two kinds of coin in the selected prefix. -/
def selected (flags : Array Bool) (take : Nat) : Nat × Nat := Id.run do
  let mut leaves := 0
  let mut pairs := 0
  for j in [0:take] do
    if flags[j]?.getD true then leaves := leaves + 1 else pairs := pairs + 1
  return (leaves, pairs)

/-- A selected leaf buys one bit for its symbol. A level's leaves occur in
the original sorted order, so only their count is needed. -/
def addBits (sorted lens : Array Nat) (leaves : Nat) : Array Nat := Id.run do
  let mut lens := lens
  for j in [0:leaves] do
    let s := sorted[j]?.getD 0
    lens := lens.set! s (lens[s]?.getD 0 + 1)
  return lens

/-- Expand the selected packages, counting each selected leaf once per
level. All working collections remain arrays. -/
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

/-- Length-limited package-merge. Each selected leaf increases the length
of its symbol; a one-symbol alphabet uses the one-bit code required by
RFC 1951 §3.2.7. The alphabet must fit `limit` bits. -/
public def lengths (freqs : Array Nat) (limit : Nat) : Array Nat := Id.run do
  let syms := (Array.range freqs.size).filter fun s => freqs[s]?.getD 0 > 0
  let n := syms.size
  if n == 0 then
    return Array.replicate freqs.size 0
  if n == 1 then
    return (Array.replicate freqs.size 0).set! (syms[0]?.getD 0) 1
  let sorted := syms.qsort fun a b => (freqs[a]?.getD 0) < (freqs[b]?.getD 0)
  let items := sorted.map fun s => freqs[s]?.getD 0
  return backtrace sorted freqs.size (levels items limit)

end LeanTex.Core.Flate.PackageMerge
