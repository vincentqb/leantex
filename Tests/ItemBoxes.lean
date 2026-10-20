module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests.ItemBoxes

/-- An article whose body is `body`. -/
private def article (pre body : String) : String :=
  "\\documentclass{article}\n" ++ pre ++ "\\begin{document}\n" ++ body ++ "\n\\end{document}\n"

private def linesOf (oneFace : Font.FontSet) (src : String) : Array Layout.LineOut :=
  bodyLines (layoutOf oneFace (elabStr src).1)

/-- The first body line holding `w`. -/
private def lineWith (ls : Array Layout.LineOut) (w : String) : Option Layout.LineOut :=
  ls.find? fun l => hasStr (lineText l) w

/-- The pages holding a line with `w`. -/
private def pagesWith (out : Layout.Out) (w : String) : List Nat :=
  (out.pages.toList.zipIdx.filter fun (p, _) => p.lines.any fun l => hasStr (lineText l) w).map (·.2)

/-- A tabular opening an item stands its label by its first row, its last or its middle on the
math axis, the two one box no page breaks, and a description's label before a listing at the item's
indent, as lualatex sets them. -/
def checks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let rows (a b c : String) := s!"{a} & x\\\\ {b} & y\\\\ {c} & z\\end\{tabular}\n"
  let ls := linesOf oneFace (article "" ("\\begin{itemize}\n\\item \\begin{tabular}[t]{ll}" ++
    rows "Alpha" "Bravo" "Charlie" ++ "\\item \\begin{tabular}[b]{ll}" ++ rows "Delta" "Echo" "Foxtrot" ++
    "\\item \\begin{tabular}{ll}" ++ rows "Golf" "Hotel" "India" ++ "\\end{itemize}"))
  let bullets := ls.filter fun l => (lineText l).trimAscii.toString == "•"
  let y (w : String) := (lineWith ls w).map (·.y)
  -- lualatex: the bullet on the first row, on the last, and 0.1pt below the middle one.
  t s!"item boxes: a tabular's position sets its label's line: {ls.map lineText}"
    (match bullets.toList, y "Alpha", y "Foxtrot", y "Hotel" with
      | [b1, b2, b3], some a, some f, some h =>
        b1.y == a && b2.y == f && (b3.y - h).abs ≤ Dim.pt 1 / 5
      | _, _, _, _ => false)
  -- lualatex: the label and its tabular move to the next page whole.
  let split := (List.range 30).all fun k =>
    let paras := String.intercalate "\n\n" ((List.range (20 + k)).map fun i =>
      s!"Filler paragraph {i} with words enough to fill a line of the measure.")
    let body := String.join ((List.range 12).map fun i => s!"Row{i} & Cell{i}\\\\\n")
    let out := layoutOf oneFace (elabStr (article "" (paras ++
      "\n\\begin{itemize}\n\\item \\begin{tabular}{ll}\n" ++ body ++ "\\end{tabular}\n\\end{itemize}"))).1
    let pages := pagesWith out "Row0" ++ pagesWith out "Row11" ++ pagesWith out "•"
    pages.length == 3 && pages.all (· == pages.headD 0)
  t "item boxes: a tabular opening an item never breaks across pages" split
  -- lualatex: a description's label before a listing at the item's indent, the code after it.
  let lst := linesOf oneFace (article "\\usepackage{listings}\n" ("\\begin{description}\n" ++
    "\\item[Juliet] \\begin{lstlisting}\nkilo = 1\nlima = 2\n\\end{lstlisting}\n\\end{description}"))
  t s!"item boxes: a description label before a listing stands at the item's indent: {lst.map lineText}"
    (match lineWith lst "Juliet", lineWith lst "lima" with
      | some j, some l => glyphX j 'J' == glyphX l 'l'
      | _, _ => false)

end Tests.ItemBoxes
