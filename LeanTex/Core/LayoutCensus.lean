module

public import LeanTex.Core.Layout

namespace LeanTex.Core.Layout.Census

/-- Raw glyphs for one source leaf, retaining whitespace and page order. -/
public def leafPages (pages : Array PageOut) (k : Nat) : List Char :=
  pages.toList.flatMap fun p =>
    (p.lines.filter fun l => l.leaf == some k).toList.flatMap LineOut.glyphChars

/-- Raw glyphs of counted body lines, retaining whitespace and page order. -/
public def bodyPages (pages : Array PageOut) : List Char :=
  pages.toList.flatMap fun p =>
    (p.lines.filter (·.counted)).toList.flatMap LineOut.glyphChars

private theorem attributed_leaf_filter_exact (lines : Array LineOut) (k : Nat) :
    ((lines.filter fun l => l.leaf.isSome).filter fun l => l.leaf == some k) =
      lines.filter (fun l => l.leaf == some k) := by
  rw [Array.filter_filter]
  apply congrArg (fun p : LineOut → Bool => lines.filter p)
  funext l
  cases l.leaf <;> simp

public theorem runPost_leaf_exact (sh : Shipped) (k : Nat) :
    leafPages (runPost sh).pages k = leafPages sh.pages k := by
  have h := congrArg
    (fun pages : Array (Array LineOut) =>
      pages.toList.flatMap fun lines =>
        (lines.filter fun l => l.leaf == some k).toList.flatMap LineOut.glyphChars)
    (runPost_attributed_projects sh)
  simpa only [leafPages, Array.toList_map, List.flatMap_map,
    attributed_leaf_filter_exact] using h

public theorem runPost_body_exact (sh : Shipped) :
    bodyPages (runPost sh).pages = bodyPages sh.pages := by
  have h := congrArg
    (fun pages : Array (Array LineOut) =>
      pages.toList.flatMap fun lines => lines.toList.flatMap LineOut.glyphChars)
    (runPost_counted_projects sh)
  simpa only [bodyPages, Array.toList_map, List.flatMap_map] using h

end LeanTex.Core.Layout.Census
