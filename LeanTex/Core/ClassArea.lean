module

public import LeanTex.Core.Dim

/-! The text area a LaTeX class sets on its paper: the standard classes' and memoir's size files,
and KOMA-Script's typearea. -/

namespace LeanTex.Core.Ir

open Dim (Length)

/-- Where a class's text area comes from. -/
public inductive AreaRule where
  /-- The engine's own page: the class leaves it to the document. -/
  | engine
  /-- The size files LaTeX's standard classes load: article's and report's `size1x.clo`. -/
  | sizeFile
  /-- book.cls's `bk1x.clo`. -/
  | book
  /-- memoir's `mem1x.clo`. -/
  | memoir
  /-- KOMA-Script's typearea. -/
  | typearea
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The text block a class sets, and its furniture's distances from it. -/
public structure TextArea where
  width : Length
  height : Length
  /-- From the paper's top edge to the text block's. -/
  top : Length
  /-- A recto's left margin against its right where the class splits the free width otherwise than
  the kernel's centred or two-sided 2:3 split. -/
  sides : Option (Length × Length)
  headsep : Length
  footskip : Length
  /-- `\maxdepth`, half the size file's `\topskip`. -/
  maxDepth : Length
  deriving Repr, BEq, Inhabited

/-- What a class's area reads: the paper, the size option (10, 11 or 12), the body's
`\baselineskip`, the sides, and typearea's `DIV` (0 its default, 1 and 2 `calc`, 3
`classic`), `BCOR`, and whether the head and the foot count in the text area. -/
public structure AreaInput where
  paperW : Length
  paperH : Length
  option : Nat
  baselineskip : Length
  twoside : Bool
  div : Nat
  bcor : Length
  headinclude : Bool
  footinclude : Bool
  deriving Repr, BEq, Inhabited

/-- The size option whose file a body size reads: 10, 11 or 12, the nearest. -/
public def sizeOptionOf (size : Length) : Nat :=
  if size < Dim.pt 21 / 2 then 10 else if size < Dim.pt 23 / 2 then 11 else 12

/-- TeX's `\@settopoint`: a length truncated to whole points. -/
public def toPoint (x : Length) : Length :=
  ⟨x.units.tdiv (Dim.pt 1).units * (Dim.pt 1).units⟩

/-- A size file's widest text, head height, head separation and foot skip. -/
private structure SizeFile where
  width : Length
  headheight : Length
  headsep : Length
  footskip : Length

/-- size1x.clo's, bk1x.clo's and mem1x.clo's values; memoir's width is `1.14\lxvchars` truncated
as TeX's arithmetic leaves it. -/
private def sizeFileOf (rule : AreaRule) (option : Nat) : SizeFile :=
  let n := if option ≤ 10 then 0 else if option == 11 then 1 else 2
  let pick {α : Type} (a b c : α) : α := if n == 0 then a else if n == 1 then b else c
  let bookSep := pick (Dim.inch 1 / 4) (Dim.inch 11 / 40) (Dim.inch 11 / 40)
  let bookFoot := pick (Dim.inch 35 / 100) (Dim.inch 38 / 100) (Dim.pt 30)
  match rule with
  | .book =>
    { width := pick (Dim.pt 345) (Dim.pt 360) (Dim.pt 390), headheight := Dim.pt 12,
      headsep := bookSep, footskip := bookFoot }
  | .memoir =>
    { width := pick (Dim.pt 341) (Dim.pt 369) (Dim.pt 383),
      headheight := pick (Dim.pt 12) (Dim.pt 136 / 10) (Dim.pt 145 / 10),
      headsep := bookSep, footskip := bookFoot }
  | _ =>
    { width := pick (Dim.pt 345) (Dim.pt 360) (Dim.pt 390), headheight := Dim.pt 12,
      headsep := Dim.pt 25, footskip := Dim.pt 30 }

/-- The least `topskip` plus whole baselines reaching `target`, as typearea's loop sets
`\textheight`. -/
public def linesReaching (target topskip skip : Length) : Length :=
  if target ≤ topskip || skip ≤ 0 then topskip
  else
    let n : Int := (target - topskip) / skip
    if topskip + skip * n < target then topskip + skip * (n + 1) else topskip + skip * n

/-- The standard classes' and memoir's area: the size file's width within the paper's less two
inches, whole baselines under the paper's less three and a half, and the top margin, each truncated
to points; the files split the side margins as the kernel does. -/
private def sizeFileArea (f : SizeFile) (i : AreaInput) : TextArea :=
  let width := toPoint (min f.width (i.paperW - Dim.inch 2))
  let topskip := Dim.pt (max 10 (min 12 i.option))
  let lines := (i.paperH - Dim.inch 2 - Dim.inch 3 / 2) / i.baselineskip
  let height := i.baselineskip * lines + topskip
  let top := toPoint ((i.paperH - Dim.inch 2 - f.headheight - f.headsep - height - f.footskip) / 2)
  { width, height, top := Dim.inch 1 + top + f.headheight + f.headsep, sides := none,
    headsep := f.headsep, footskip := f.footskip, maxDepth := topskip / 2 }

/-- Latin Modern Roman's lowercase and uppercase alphabets at a class's `\normalsize`, which
typearea's `DIV=calc` measures (lualatex 1.24: 127.62 and 186.2pt at 10pt, 139.744 and 203.889pt at
10.95pt, 149.892 and 218.688pt at 12pt). -/
private def alphabets (option : Nat) : Length × Length :=
  if option ≤ 10 then (Dim.pt 127620 / 1000, Dim.pt 186200 / 1000)
  else if option == 11 then (Dim.pt 139744 / 1000, Dim.pt 203889 / 1000)
  else (Dim.pt 149892 / 1000, Dim.pt 218688 / 1000)

/-- typearea's `\ta@modiv`: the stripes `x` holds of `y`, at least four. -/
private def stripes (x y : Length) : Nat :=
  if y ≤ 0 then 4 else max 4 (x / y).toNat

/-- The stripes typearea's `DIV` names on a paper, its head's height and separation and its foot
skip given: A4's table at 10, 11 and 12pt, else the good line width of `calc`, or `classic`'s from
the paper's proportion. -/
private def divOf (i : AreaInput) (hh hs fs : Length) : Nat :=
  let hs := if i.headinclude then 0 else hh + hs
  let fs := if i.footinclude then 0 else fs
  let a4 := Dim.mm 207 ≤ i.paperW && i.paperW ≤ Dim.mm 213 && Dim.mm 294 ≤ i.paperH &&
    i.paperH ≤ Dim.mm 300
  let div := if i.div != 0 then i.div
    else if a4 && i.option == 10 then 8 else if a4 && i.option == 11 then 10
    else if a4 && i.option == 12 then 12 else 2
  let div := if div != 3 then div
    else if i.paperW - i.bcor + hs + fs > i.paperH then 1
    else stripes i.paperH ((i.paperH - i.paperW + i.bcor) / 3)
  if div ≥ 4 then div else
    let (lower, upper) := alphabets i.option
    let good := if lower > Dim.pt 200 then lower * 253846 / 100000 + upper * 11538 / 100000
      else (lower * 66 + upper * 3) / 26
    let hblk := i.paperW - good
    let hblk := if hblk < 0 then Dim.mm 5 * 3 else hblk
    let d := stripes i.paperW (hblk / 3)
    if i.paperH / (d : Int) - hs < Dim.mm 5 then
      stripes i.paperH ((Dim.mm 15 + hs + fs) / 3)
    else d

/-- typearea's area: `DIV` stripes of the paper less the binding correction, three of them the side
margins, the top one stripe down and the height the least whole baselines the rest leaves, less an
included head or foot. -/
private def typeareaOf (i : AreaInput) : TextArea :=
  let hh := i.baselineskip * 5 / 4
  let hs := i.baselineskip * 3 / 2
  let fs := i.baselineskip * 7 / 2
  let div := divOf i hh hs fs
  let hblk := (i.paperW - i.bcor) / (div : Int)
  let vblk := i.paperH / (div : Int)
  let head := if i.headinclude then hh + hs else 0
  let foot := if i.footinclude then fs else 0
  { width := i.paperW - i.bcor - 3 * hblk
    height := linesReaching (i.paperH - 3 * vblk - head - foot) (Dim.pt (max 10 (min 12 i.option)))
      i.baselineskip
    top := vblk + head
    sides := if i.twoside then some (hblk + i.bcor, 2 * hblk)
      else if i.bcor != 0 then some (hblk * 3 / 2 + i.bcor, hblk * 3 / 2) else none
    headsep := hs, footskip := fs, maxDepth := Dim.pt (max 10 (min 12 i.option)) / 2 }

/-- The area a class's rule sets; `none` where the engine's page stands. -/
public def AreaRule.area? (rule : AreaRule) (i : AreaInput) : Option TextArea :=
  match rule with
  | .engine => none
  | .typearea => some (typeareaOf i)
  | r => some (sizeFileArea (sizeFileOf r i.option) i)

/-- The heights typearea's loop sets reach their target, short of it by less than a baseline. -/
public theorem linesReaching_least (target topskip skip : Length) (h : 0 < skip)
    (ht : topskip < target) :
    target ≤ linesReaching target topskip skip ∧ linesReaching target topskip skip - skip < target := by
  have hn : (decide (target ≤ topskip) || decide (skip ≤ 0)) = false := by
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
    exact ⟨Length.not_le.mpr ht, Length.not_le.mpr h⟩
  simp only [linesReaching, hn, Bool.false_eq_true, ite_false]
  have hp : 0 < skip.units := h
  have e := Int.emod_def (target.units - topskip.units) skip.units
  have r0 := Int.emod_nonneg (target.units - topskip.units) (Int.ne_of_gt hp)
  have r1 := Int.emod_lt_of_pos (target.units - topskip.units) hp
  split
  · length_units
    rw [Int.mul_add, Int.mul_one] at *
    generalize skip.units * ((target.units - topskip.units) / skip.units) = m at *
    omega
  · length_units
    generalize skip.units * ((target.units - topskip.units) / skip.units) = m at *
    omega

end LeanTex.Core.Ir
