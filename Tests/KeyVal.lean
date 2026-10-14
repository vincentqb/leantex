module

public import Tests.Support
import LeanTex.Core.KeyVal

public section

open LeanTex.Core

namespace Tests

/-- Option lists as LaTeX's keyval and `\@for` read them, and spellings keyval reads alike setting
one page. -/
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

end Tests
