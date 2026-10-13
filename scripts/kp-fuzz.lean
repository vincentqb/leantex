/-
Randomized differential test: the pruned Knuth-Plass DP's demerits equal the brute-force
minimum.
Usage: lake env lean --run scripts/kp-fuzz.lean [iterations]
-/
import LeanTex

open LeanTex.Core LeanTex.Core.Layout

/-- xorshift64*: deterministic, dependency-free. -/
private def nextRand (s : UInt64) : UInt64 × UInt64 :=
  let x := s ^^^ (s >>> 12)
  let x := x ^^^ (x <<< 25)
  let x := x ^^^ (x >>> 27)
  (x, x * 2685821657736338717)

private structure Gen where
  seed : UInt64

private def Gen.next (g : Gen) (bound : Nat) : Nat × Gen :=
  let (s, v) := nextRand g.seed
  ((v % UInt64.ofNat bound).toNat, { seed := s })

/-- A random paragraph's items: boxes separated by glue, occasional flagged hyphen
penalties and forced breaks, each box one glyph from a pool spanning the protrusion
table's classes. -/
private def randItems (g : Gen) : Array Item × Gen := Id.run do
  let pool : Array Char := #['a', 'A', 'y', '1', '.', ',', '-', '‘', '”', 'x']
  let mut g := g
  let (nWords, g') := g.next 5
  g := g'
  let mut items : Array Item := #[]
  for i in [0:nWords + 2] do
    if i > 0 then
      let (kind, g') := g.next 10
      g := g'
      if kind < 6 then
        let (sw, g'') := g.next 8
        g := g''
        items := items.push (.glue {
          width := Dim.pt (sw + 4)
          stretch := Dim.pt (sw / 2 + 1)
          shrink := Dim.pt (sw / 3 + 1)
        })
      else if kind < 9 then
        items := items.push (.pen (Dim.pt 3) hyphenPenalty true 0 Ir.Color.black
          #[(0, '-', Dim.pt 3)])
      else
        items := items.push (.glue { fil := true })
        items := items.push (.pen 0 forcedCost false 0 Ir.Color.black #[])
    let (w, g') := g.next 60
    g := g'
    let (ci, g'') := g.next pool.size
    g := g''
    items := items.push (.box (Dim.pt (w + 10)) 0 Ir.Color.black none
      #[(0, pool[ci]!, Dim.pt (w + 10))] (Dim.pt 10) {} {} 0 none (.leaf 0))
  items := items.push (.glue { fil := true })
  items := items.push (.pen 0 forcedCost false 0 Ir.Color.black #[])
  return (items, g)

private def seqCost (items : Array Item) (target : Dim.Sp)
    (protrude expand fil : Bool) (breaks : List Nat) (runt : Bool := false) (bg : Dim.Sp := 0) :
    Option Int := Id.run do
  let mut prev : Nat := 0
  let mut first := true
  let mut prevFlagged := false
  let mut total : Int := 0
  for b in breaks do
    let a := if first then lineStart items 0 else lineStart items (prev + 1)
    -- A line holds content: `kp`'s own `a ≤ j` gate refuses an empty line, so the oracle does too.
    if a > b then
      return none
    for k in [a:b] do
      if isForced items k then
        return none
    let m := measure items a b protrude
    total := total + lineDemerits items { m with stretch := m.stretch + bg } target b expand fil
    if prevFlagged && isFlagged items b then
      total := total + doubleHyphenDemerits
    if prevFlagged && b == items.size - 1 then
      total := total + finalHyphenDemerits
    if runt && b == items.size - 1 && oneWordLine items a b then
      total := total + runtDemerits
    prev := b
    prevFlagged := isFlagged items b
    first := false
  if breaks.getLast? != some (items.size - 1) then
    return none
  return some total

/-- The brute-force minimum over every legal break sequence and, among its ties, the one
TeX keeps: each break's predecessor the latest of equal demerits (tex.web §855). -/
private def bruteBest (items : Array Item) (target : Dim.Sp)
    (protrude expand fil : Bool) (runt : Bool := false) (bg : Dim.Sp := 0) :
    Option (Int × List Nat) := Id.run do
  let n := items.size
  let legal := (List.range n).filter (canBreakAt items ·)
  let optional' := legal.filter (· != n - 1)
  let later (a b : List Nat) : Bool :=
    let ra := a.reverse
    let rb := b.reverse
    let rec go : List Nat → List Nat → Bool
      | x :: xs, y :: ys => if x != y then x > y else go xs ys
      | _ :: _, [] => true
      | [], _ => false
    go ra rb
  let mut best : Option (Int × List Nat) := none
  for mask in [0:2 ^ optional'.length] do
    let mut chosen : List Nat := []
    for (b, idx) in optional'.zipIdx do
      if mask / 2 ^ idx % 2 == 1 then
        chosen := chosen ++ [b]
    let seq := chosen ++ [n - 1]
    if let some c := seqCost items target protrude expand fil seq runt bg then
      match best with
      | some (b0, s0) =>
        if c < b0 || (c == b0 && later seq s0) then best := some (c, seq)
      | none => best := some (c, seq)
  return best

/-- `kp`'s prefix-sum measure agrees with the direct `measure` from every line start to
every legal breakpoint, with and without the protrusion term. -/
private def measuresAgree (items : Array Item) : Bool := Id.run do
  let sums := kpSums items
  for a in [0:items.size] do
    for j in [a:items.size] do
      if a == lineStart items a && canBreakAt items j then
        for protrude in [false, true] do
          let direct := measure items a j protrude
          let viaKp := kpMeasure items sums a j protrude
          if direct.natural != viaKp.natural || direct.stretch != viaKp.stretch ||
              direct.shrink != viaKp.shrink || direct.fil != viaKp.fil ||
              direct.boxW != viaKp.boxW then
            return false
  return true

def main (args : List String) : IO UInt32 := do
  let iters := (args.head?.bind (·.toNat?)).getD 300
  let mut g : Gen := { seed := 0x2545F4914F6CDD1D }
  let mut failures := 0
  for i in [0:iters] do
    let (items, g') := randItems g
    g := g'
    let (tw, g'') := g.next 200
    g := g''
    let target := Dim.pt (tw + 40)
    -- Justified, ragged, `\raggedright` and centred: optimal under every toggle, TeX's tie kept.
    for (shape, fil, runt) in [(items, false, false), (raggedItems items, false, false),
        (items, true, false), (items, true, true)] do
      for (protrude, expand) in [(false, false), (true, false), (false, true), (true, true)] do
        for bg in [(0 : Dim.Sp), Dim.pt 2, Dim.pt 20] do
          let kpBreaks := (kp shape target protrude expand bg fil runt).toList
          let kpCost := seqCost shape target protrude expand fil kpBreaks runt bg
          let brute := bruteBest shape target protrude expand fil runt bg
          unless kpCost.isSome && kpCost == brute.map (·.1) do
            failures := failures + 1
            IO.eprintln s!"FAIL case {i} (protrude={protrude}, expand={expand}, fil={fil}, \
runt={runt}, bg={bg}): target={target} kp={kpCost} brute={brute.map (·.1)}"
            IO.eprintln s!"  breaks={kpBreaks}"
            IO.eprintln s!"  items={shape.size}"
          if fil && kpCost == brute.map (·.1) && some kpBreaks != brute.map (·.2) then
            failures := failures + 1
            IO.eprintln s!"FAIL case {i} (protrude={protrude}, expand={expand}, bg={bg}): \
the fil tie keeps {kpBreaks}, TeX keeps {brute.map (·.2)}"
    unless measuresAgree items do
      failures := failures + 1
      IO.eprintln s!"FAIL case {i}: prefix-sum measure disagrees with direct measure"
  if failures == 0 then
    IO.println s!"kp-fuzz: {iters} random paragraphs, all optimal (justified, ragged, \
LaTeX's fil ragged and centred, their ties as TeX keeps them)"
    return 0
  else
    IO.eprintln s!"kp-fuzz: {failures} failures in {iters} cases"
    return 1
