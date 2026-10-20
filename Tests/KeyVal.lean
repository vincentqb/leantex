module

public import Tests.Support
import LeanTex.Core.KeyVal

public section

open LeanTex.Core

namespace Tests

/-- Option lists as kvsetkeys and `\@for` read them, and spellings they read alike setting one
page. -/
def keyValChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  t "keyval: a comma inside braces separates nothing"
    (KeyVal.items "a=1,b={2,3},c" == #["a=1", "b={2,3}", "c"])
  t "keyval: a value's surrounding spaces and braces go"
    (KeyVal.entry " b = {2,3} " == ("b", some "2,3"))
  t "keyval: an equals sign inside braces is the value's"
    (KeyVal.entry "a={p=q}" == ("a", some "p=q"))
  t "keyval: a control symbol separates nothing"
    (KeyVal.items "a=x\\,y,b" == #["a=x\\,y", "b"])
  t "keyval: two groups keep their braces" (KeyVal.entry "a = {x}{y}" == ("a", some "{x}{y}"))
  t "keyval: an empty group is an empty value" (KeyVal.entry "a={}" == ("a", some ""))
  t "keyval: a bare key has no value" (KeyVal.entry " a " == ("a", none))
  t "keyval: escaped braces make no group" (KeyVal.unbrace "\\{x\\}" == "\\{x\\}")
  t "keyval: \\@for keeps an empty item and the spaces around a group"
    (KeyVal.split "a, {b,c} ,,d" == #["a", " {b,c} ", "", "d"])
  t "keyval: BibTeX's reading counts an escaped brace"
    (KeyVal.splitBraced (· == ',') "a\\{,b},c" == #["a\\{,b}", "c"])
  t "keyval: one level of braces goes, the inner spaces stay, as kvsetkeys and l3keys read"
    (KeyVal.entry "a={{v}}" == ("a", some "{v}") && KeyVal.entry "a={ v }" == ("a", some " v "))
  t "keyval: a second equals sign stays in the value, as kvsetkeys reads"
    (KeyVal.entry "a=p=q" == ("a", some "p=q"))
  t "keyval: a wholly braced item is its contents, as keyval, kvsetkeys and pgfkeys read"
    (KeyVal.entry "{k=v}" == ("k", some "v") && KeyVal.entry " {t} " == ("t", none))
  t "keyval: a raw entry keeps its value's braces" (KeyVal.rawEntry "a = {x}" == ("a", some "{x}"))
  t "keyval: a braced empty value is written, a missing one is not"
    (KeyVal.pair? "a={}" == some ("a", "") && KeyVal.pair? "a=" == none)
  t "keyval: a value cut inside parentheses leaves unbalanced pieces, braces aside"
    (KeyVal.unbalanced "draft)" && KeyVal.unbalanced "pdftitle=Results (part 1" &&
      !KeyVal.unbalanced "pdftitle={Results (part 1, draft)}" &&
      !KeyVal.unbalanced "pdfcreator={6\" ruler}")
  let titled := elabStr (dvDoc "\\hypersetup{pdftitle=Results (part 1, draft)}\n" "Words.")
  t "keyval: a comma inside parentheses ends a value, and the piece after it is named"
    (titled.1.info.title == some "Results (part 1" &&
      titled.2.any fun d => d.code == "W0101" && hasStr (saidText d) "'draft)'")
  t "keyval: a braced or uncut value with a lone delimiter is named nowhere"
    ((elabStr (dvDoc "\\hypersetup{pdfcreator={Notes :-)}, pdfproducer=Tool (beta}\n"
      "Words.")).2.all (·.code != "W0101"))
  let listed := elabStr (dvDoc "\\usepackage{enumitem}\n\\setlist[itemize]{itemsep=9pt, label=(\\alph*, x)}\n" "Words.")
  t "keyval: a list key cut inside parentheses names its piece"
    (listed.2.any fun d => d.code == "W0104" && hasStr (saidText d) "x)")
  t "keyval: a blank icon label keeps the icon's own name"
    ((elabStr (dvDoc "\\usepackage{fontawesome5}\n" "\\faIcon[label={}]{star}")).2.any
      fun d => d.code == "W0110" && hasStr (saidText d) "blank")
  let metadata := elabStr ("\\DocumentMetadata{=x, lang=fr}\n" ++ dvDoc "" "Words.")
  t "keyval: a metadata entry with an empty key is named whole"
    (metadata.2.any fun d => d.code == "W0101" && hasStr (saidText d) "=x")
  t "keyval: a spaced frame option is the tight one"
    ((elabStr (dvDeck "" "\\begin{frame}[fragile = true]Words.\\end{frame}")).2.all
      fun d => !hasStr d.message "fragile")
  t "keyval: a spaced covered fraction is the tight one"
    ((elabStr (dvDeck "\\setbeamercovered{transparent = 30}\n" "Words.")).2.all
      (·.code != "W0104"))
  let quoted := docHtmlOf (elabStr (dvDoc "\\usepackage{tikz}\n"
    "\\begin{tikzpicture}[alt={\"Whole\"}]\\draw (0,0) -- (1,1);\\end{tikzpicture}")).1
  t "keyval: a picture's quoted alternative keeps its quotes"
    (hasStr quoted "&quot;Whole&quot;")
  let lang (pre : String) := (elabStr (dvDoc pre "Words.")).1.info.language
  t "keyval: a braced metadata language is the bare one"
    (lang "\\DocumentMetadata{lang = {de-DE}}\n" == some "de-DE" &&
      lang "\\DocumentMetadata{lang=de-DE}\n" == some "de-DE")
  match ← shippedFira with
  | none => t "keyval: the shipped Fira Sans parses" false
  | some fonts =>
    let page (pre : String) := shippedLinesOf fonts (elabStr (dvDoc pre
      "Words before.\n\\begin{itemize}\n\\item One.\n\\item Two.\n\\end{itemize}")).1
    let spaced := page "\\usepackage{enumitem}\n\\setlist[itemize]{itemsep = 9pt}\n"
    t "keyval: a key spaced from its value sets the page the tight spelling sets"
      (spaced == page "\\usepackage{enumitem}\n\\setlist[itemize]{itemsep=9pt}\n" &&
        spaced != page "\\usepackage{enumitem}\n")
    let braced := page "\\usepackage[margin={3cm}]{geometry}\n"
    t "keyval: a braced margin sets the page the bare spelling sets"
      (braced == page "\\usepackage[margin=3cm]{geometry}\n" && braced != page "")
    let pair := page "\\usepackage[margin={2cm,4cm}]{geometry}\n"
    t "keyval: a margin pair sets geometry's horizontal and vertical margins"
      (pair == page "\\usepackage[hmargin=2cm,vmargin=4cm]{geometry}\n" &&
        pair != page "\\usepackage[margin=2cm]{geometry}\n")
    t "keyval: an equal side pair is the symmetric margin"
      (page "\\usepackage[hmargin={2cm,2cm}]{geometry}\n" ==
        page "\\usepackage[hmargin=2cm]{geometry}\n" &&
        page "\\usepackage[hmargin={2cm,2cm}]{geometry}\n" != page "")
    t "keyval: a later margin overrides an earlier pair, in order"
      (page "\\usepackage[hmargin={2cm,2cm},margin=1cm]{geometry}\n" ==
        page "\\usepackage[margin=1cm]{geometry}\n")
    t "keyval: a margin pair holding TeX arithmetic is named, and the page still ships"
      ((elabStr (dvDoc "\\usepackage[margin={2cm,\\dimexpr 1in+2pt\\relax}]{geometry}\n"
        "Words.")).2.all (·.severity != .error))
    let a5 (cls : String) := shippedLinesOf fonts (elabStr (cls ++
      "\\begin{document}\nWords in a paragraph.\n\\end{document}")).1
    t "keyval: a spaced paper option is the tight one"
      (a5 "\\documentclass[paper = a5]{scrartcl}\n" == a5 "\\documentclass[paper=a5]{scrartcl}\n" &&
        a5 "\\documentclass[paper = a5]{scrartcl}\n" != a5 "\\documentclass{scrartcl}\n")
    let captioned (pre : String) := shippedLinesOf fonts (elabStr (dvDoc pre
      "\\begin{figure}\nx\n\\caption{An invented caption long enough to run past one line of \
the measure, so that its margin moves where its words break.}\n\\end{figure}")).1
    let caption := captioned "\\usepackage{caption}\n\\captionsetup{margin={2cm}}\n"
    t "keyval: a braced caption margin sets the page the bare spelling sets"
      (caption == captioned "\\usepackage{caption}\n\\captionsetup{margin=2cm}\n" &&
        caption != captioned "\\usepackage{caption}\n")
    let deck (cls body : String) := shippedLinesOf fonts (elabStr (cls ++
      "\\begin{document}\n" ++ body ++ "\n\\end{document}")).1
    let wide := deck "\\documentclass[aspectratio = 169]{beamer}\n" "\\begin{frame}Words.\\end{frame}"
    t "keyval: a spaced class option sets the stage the tight spelling sets"
      (wide == deck "\\documentclass[aspectratio=169]{beamer}\n" "\\begin{frame}Words.\\end{frame}" &&
        wide != deck "\\documentclass{beamer}\n" "\\begin{frame}Words.\\end{frame}")
    let top := deck "\\documentclass{beamer}\n" "\\begin{frame}[{t}]Words.\\end{frame}"
    t "keyval: a braced frame option is the bare one"
      (top == deck "\\documentclass{beamer}\n" "\\begin{frame}[t]Words.\\end{frame}" &&
        top != deck "\\documentclass{beamer}\n" "\\begin{frame}Words.\\end{frame}")

end Tests
