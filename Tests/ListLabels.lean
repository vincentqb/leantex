module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests.ListLabels

/-- An article whose body is `body`. -/
private def article (pre body : String) : String :=
  "\\documentclass{article}\n" ++ pre ++ "\\begin{document}\n" ++ body ++ "\n\\end{document}\n"

private def linesOf (oneFace : Font.FontSet) (src : String) : Array Layout.LineOut :=
  bodyLines (layoutOf oneFace (elabStr src).1)

/-- The first body line holding `w`. -/
private def lineWith (ls : Array Layout.LineOut) (w : String) : Option Layout.LineOut :=
  ls.find? fun l => hasStr (lineText l) w

private def texts (ls : Array Layout.LineOut) : Array String := ls.map lineText

/-- enumitem's label, start, resume and leftmargin keys, a class's redefined label, and a second
`\setlist` replacing the first, set as lualatex sets them. -/
def checks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let pre := "\\usepackage{enumitem}\n"
  -- lualatex: each item's label its template's at its number.
  let tmpl := linesOf oneFace (article pre ("\\begin{enumerate}[label=(\\alph*)]\n\\item Alpha.\n" ++
    "\\item Bravo.\n\\end{enumerate}"))
  t s!"list labels: a per-list template labels each item: {texts tmpl}"
    ((lineWith tmpl "Alpha").any (fun l => hasStr (lineText l) "(a)") &&
      (lineWith tmpl "Bravo").any (fun l => hasStr (lineText l) "(b)"))
  -- lualatex: start=4 numbers 4 and 5, and resume goes on at 6.
  let started := linesOf oneFace (article pre ("\\begin{enumerate}[start=4]\n\\item Charlie.\n" ++
    "\\item Delta.\n\\end{enumerate}\nEcho.\n\\begin{enumerate}[resume]\n\\item Foxtrot.\n" ++
    "\\end{enumerate}"))
  t s!"list labels: start and resume number past one: {texts started}"
    ((lineWith started "Charlie").any (fun l => hasStr (lineText l) "4.") &&
      (lineWith started "Delta").any (fun l => hasStr (lineText l) "5.") &&
      (lineWith started "Foxtrot").any (fun l => hasStr (lineText l) "6."))
  -- lualatex: a redefined \labelenumi and a \setlist label template label the items.
  let classLabel := linesOf oneFace (article "\\renewcommand{\\labelenumi}{(\\alph{enumi})}\n"
    "\\begin{enumerate}\n\\item Golf.\n\\item Hotel.\n\\end{enumerate}")
  t s!"list labels: a redefined labelenumi labels the items: {texts classLabel}"
    ((lineWith classLabel "Hotel").any (fun l => hasStr (lineText l) "(b)"))
  let declared := linesOf oneFace (article (pre ++ "\\setlist[enumerate]{label=\\Roman*.}\n")
    "\\begin{enumerate}\n\\item India.\n\\item Juliet.\n\\end{enumerate}")
  t s!"list labels: a setlist template labels the items: {texts declared}"
    ((lineWith declared "Juliet").any (fun l => hasStr (lineText l) "II."))
  -- lualatex: leftmargin=* stands a bullet and a widest label at the outer margin, and a
  -- description's next lines at it.
  let star := linesOf oneFace (article pre ("Kilo words.\n\n\\begin{itemize}[leftmargin=*]\n" ++
    "\\item Lima.\n\\end{itemize}\n\\begin{enumerate}[leftmargin=*, label=(\\roman*), widest=i]\n" ++
    "\\item Mike.\n\\end{enumerate}\n\\begin{description}[leftmargin=*]\n\\item[November] " ++
    String.intercalate " " (List.replicate 30 "oscar") ++ "\n\\end{description}"))
  let left := (lineWith star "Kilo").map (·.x)
  let oscars := star.filter fun l => hasStr (lineText l) "oscar"
  t s!"list labels: leftmargin=* sets the widest label at the outer margin: {texts star}"
    (left.isSome && ((lineWith star "Lima").bind (glyphX · '•')) == left &&
      ((lineWith star "Mike").bind (glyphX · '(')) == left &&
      (oscars[1]?.map (·.x)) == left)
  -- lualatex: a second unstarred \setlist for a scope clears the first's label and margin.
  let plain := linesOf oneFace (article pre "\\begin{itemize}\n\\item Papa.\n\\end{itemize}")
  let replaced := linesOf oneFace (article (pre ++ "\\setlist[itemize]{label=x, leftmargin=4em}\n" ++
    "\\setlist[itemize]{itemsep=0pt}\n") "\\begin{itemize}\n\\item Papa.\n\\end{itemize}")
  t s!"list labels: a second setlist replaces the first's label and margin: {texts replaced}"
    (match lineWith plain "Papa", lineWith replaced "Papa" with
      | some a, some b => lineText a == lineText b && glyphX a 'P' == glyphX b 'P'
      | _, _ => false)

end Tests.ListLabels
