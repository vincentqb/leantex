module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests.ItemRefs

/-- The text the document's last paragraph sets. -/
private def lastText (src : String) : String :=
  let (doc, _) := elabStr src
  match doc.body.back? with
  | some (.para xs) => Ir.plainText xs
  | _ => ""

/-- A `\label` in an enumerate item names the item's number as its class or enumitem's `ref` sets it,
the levels around a nested one prefixing theirs, and a `\newlist` list sets as the kind it copies. -/
def checks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- lualatex: 1 1a 1(a)i 2 (a) (a) A, the itemize's label the section's 1.
  let src := "\\documentclass{article}\n\\usepackage{enumitem}\n\\begin{document}\n\\section{Alpha}\n" ++
    "\\begin{enumerate}\n\\item Bravo.\\label{a}\n\\begin{enumerate}\n\\item Charlie.\\label{b}\n" ++
    "\\begin{enumerate}\n\\item Delta.\\label{c}\n\\end{enumerate}\n\\end{enumerate}\n" ++
    "\\item Echo.\\label{d}\n\\end{enumerate}\n\\begin{enumerate}[label=(\\alph*)]\n\\item Golf.\\label{e}\n" ++
    "\\end{enumerate}\n\\begin{enumerate}[label=\\alph*), ref=(\\alph*)]\n\\item Hotel.\\label{f}\n" ++
    "\\end{enumerate}\n\\renewcommand{\\theenumi}{\\Alph{enumi}}\n\\begin{enumerate}\n\\item India.\\label{g}\n" ++
    "\\end{enumerate}\n\\begin{itemize}\n\\item Juliet.\\label{h}\n\\end{itemize}\n\n" ++
    "\\ref{a} \\ref{b} \\ref{c} \\ref{d} \\ref{e} \\ref{f} \\ref{g} \\ref{h}.\n\\end{document}\n"
  let shown := lastText src
  t s!"item refs: a label names its item's number: {shown}" (shown == "1 1a 1(a)i 2 (a) (a) A 1.")
  -- lualatex: a \newlist list sets as the enumerate it copies, its setlist label on each item.
  let (doc, ds) := elabStr ("\\documentclass{article}\n\\usepackage{enumitem}\n" ++
    "\\newlist{steps}{enumerate}{2}\n\\setlist[steps]{label=Step \\arabic*:}\n\\begin{document}\n" ++
    "\\begin{steps}\n\\item Kilo.\n\\item Lima.\n\\end{steps}\n\\end{document}\n")
  let txt := Ir.plainText (doc.body.foldl (fun (acc : Array Ir.Inline) b => match b with
    | .list _ _ items => acc ++ items.foldl (fun (a : Array Ir.Inline) (it : Array Ir.Block) => match it[0]? with
      | some (Ir.Block.para c) => a ++ c
      | _ => a) #[]
    | _ => acc) #[])
  t s!"item refs: a newlist list sets as the kind it copies, its keys read: {txt}"
    (hasStr txt "Step 2:" && !ds.any fun d => d.code == "W0301" || d.code == "W0302")

end Tests.ItemRefs
