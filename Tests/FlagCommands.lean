module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests.FlagCommands

/-- A source and its control ship the same pages, web page and text, the source's diagnostics
carrying exactly `codes` beyond its notes. -/
private def flagArtifacts (ref : IO.Ref (List String)) (fonts : Font.FontSet)
    (label pre body control : String) (codes : List String := []) : IO Unit := do
  let source := dvDoc ("\\pagestyle{empty}\\usepackage{etoolbox}" ++ pre) body
  let expected := dvDoc "\\pagestyle{empty}" control
  let (ds, actual, html, text) := sourceArtifacts fonts source
  let (_, wanted, wantedHtml, wantedText) := sourceArtifacts fonts expected
  let t := check ref
  let said := (ds.filter (·.severity != .note)).toList.map (·.code)
  t s!"flag commands {label}: diagnostics {said}" (said == codes)
  t s!"flag commands {label}: shipped PDF pages" (reprStr actual.pages == reprStr wanted.pages)
  t s!"flag commands {label}: typed HTML" (html == wantedHtml)
  t s!"flag commands {label}: visible text ({text})" (text == wantedText)

/-- etoolbox's booleans and toggles are declared, set and tested where their commands stand, as
LuaLaTeX sets them: a test keeps one branch, a group's end restores a setting, a boolean is the
`\newif` flag of its name, and a flag nothing declares keeps no branch. -/
def flagCommandChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  flagArtifacts ref fonts "toggle set and tested" "\\newtoggle{probe}\\toggletrue{probe}"
    "\\iftoggle{probe}{Yes}{No}/\\togglefalse{probe}\\iftoggle{probe}{Yes}{No}/\\nottoggle{probe}{Not}{Is}"
    "Yes/No/Not"
  flagArtifacts ref fonts "toggle starts false" "\\newtoggle{probe}"
    "\\iftoggle{probe}{Yes}{No}" "No"
  flagArtifacts ref fonts "settoggle reads its value" "\\newtoggle{probe}"
    "\\settoggle{probe}{true}\\iftoggle{probe}{Yes}{No}/\\settoggle{probe}{false}\\iftoggle{probe}{Yes}{No}"
    "Yes/No"
  flagArtifacts ref fonts "providetoggle keeps a standing value"
    "\\newtoggle{probe}\\toggletrue{probe}\\providetoggle{probe}" "\\iftoggle{probe}{Yes}{No}" "Yes"
  flagArtifacts ref fonts "a group's end restores the toggle" "\\newtoggle{probe}"
    "{\\toggletrue{probe}\\iftoggle{probe}{In}{Out}}/\\iftoggle{probe}{In}{Out}" "{In}/Out"
  flagArtifacts ref fonts "a macro tests the toggle at each use"
    "\\newtoggle{probe}\\newcommand\\state{\\iftoggle{probe}{On}{Off}}"
    "\\state/\\toggletrue{probe}\\state" "Off/On"
  flagArtifacts ref fonts "boolean set and tested" "\\newbool{probe}"
    "\\ifbool{probe}{Yes}{No}/\\booltrue{probe}\\ifbool{probe}{Yes}{No}/\\notbool{probe}{Not}{Is}/\\setbool{probe}{false}\\ifbool{probe}{Yes}{No}"
    "No/Yes/Is/No"
  flagArtifacts ref fonts "a boolean is its newif flag" "\\newbool{probe}\\booltrue{probe}"
    "\\ifprobe Yes\\else No\\fi/\\probefalse\\ifbool{probe}{Yes}{No}" "Yes/No"
  flagArtifacts ref fonts "a newif flag is a boolean" "\\newif\\ifprobe\\probetrue"
    "\\ifbool{probe}{Yes}{No}" "Yes"
  flagArtifacts ref fonts "toggles and booleans are apart" "\\newtoggle{probe}\\newbool{probe}"
    "\\toggletrue{probe}\\ifbool{probe}{Yes}{No}/\\iftoggle{probe}{Yes}{No}" "No/Yes"
  flagArtifacts ref fonts "an undeclared toggle keeps neither branch" ""
    "A\\iftoggle{probe}{Yes}{No}Z" "AZ" (codes := ["W0104"])
  flagArtifacts ref fonts "a value other than true or false sets nothing"
    "\\newtoggle{probe}\\toggletrue{probe}" "\\settoggle{probe}{maybe}\\iftoggle{probe}{Yes}{No}"
    "Yes" (codes := ["W0104"])
  flagArtifacts ref fonts "a second declaration keeps the value"
    "\\newtoggle{probe}\\toggletrue{probe}\\newtoggle{probe}" "\\iftoggle{probe}{Yes}{No}" "Yes"
    (codes := ["W0104"])

end Tests.FlagCommands
