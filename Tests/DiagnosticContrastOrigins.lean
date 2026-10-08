module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests

/-- Color repair, refusal, and repeated-use accounting retain the authored
site, including colors redeclared in later palette epochs. -/
def diagnosticContrastOriginChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let file := "chapters/colors.tex"
  let elaborateSource (source : String) : Array Diag :=
    (Elab.runRawsSpanned file (Parse.parse file (Lex.lex file source).1).1).2.1
  let atSource (d : Diag) (line : Nat) (trigger : String) : Bool :=
    d.span.any (fun s => s.file == file && s.pos.line == line) &&
      d.trigger == some trigger
  let doc (palette body : String) : String :=
    "\\documentclass{article}\n" ++ palette ++ "\n\\begin{document}\n" ++
      body ++ "\n\\end{document}"
  let repair := elaborateSource (doc "\\palette{washed = #888888}"
    "\\textcolor{washed}{first}")
  t "contrast origin: a repaired use retains its command"
    (repair.any fun d => d.code == "N0022" && atSource d 4 "\\textcolor")
  let repeated := (elaborateSource (doc "\\palette{washed = #DDDDDD}"
    "\\textcolor{washed}{first}\n\n\\textcolor{washed}{second}")).filter
      (·.code == "W0315")
  t "contrast origin: repeated accounting retains one warning and its site count"
    (match repeated.toList with
      | [warning, note] =>
        atSource warning 4 "\\textcolor" && atSource note 4 "\\textcolor" &&
          warning.severity == .warning && warning.sites == 2 &&
          note.severity == .note && note.sites == 0 &&
          warning.subject.isSome && warning.subject == note.subject
      | _ => false)
  let foreground := elaborateSource (doc "\\palette{fg = #888888}" "body")
  t "contrast origin: a repaired foreground names its declaration"
    (foreground.any fun d => d.code == "N0022" && atSource d 2 "\\palette")
  let epoch := elaborateSource (doc "\\palette{washed = #DDDDDD}"
    ("\\textcolor{washed}{first}\n\n\\palette{washed = #888888}\n" ++
      "\\textcolor{washed}{second}"))
  t "contrast origin: an epoch's new value uses its own source"
    (epoch.any fun d => d.code == "N0022" && atSource d 7 "\\textcolor")
  let ground := elaborateSource (doc
    "\\palette{fg = #FFFFFF, bg = #000000, washed = #888888}"
    ("\\textcolor{washed}{first}\n\n\\palette{fg = #000000, bg = #FFFFFF}\n" ++
      "\\textcolor{washed}{second}"))
  t "contrast origin: equal ink on a different ground uses the later source"
    (ground.any fun d => d.code == "N0022" && atSource d 7 "\\textcolor")
  let anonymous := elaborateSource (doc "\\palette{fg = #23373B, bg = #FAFAFA}"
    "\\textcolor{fg!60!bg}{first}")
  t "contrast origin: a reweighted mix retains its source"
    (anonymous.any fun d => d.code == "N0022" && atSource d 4 "\\textcolor")
  let beamer := elaborateSource ("\\documentclass{beamer}\n" ++
    "\\definecolor{softink}{HTML}{888888}\n" ++
    "\\setbeamercolor{block title}{fg=softink,bg=white}\n" ++
    "\\begin{document}\n\\begin{frame}\n" ++
    "\\begin{block}{Heading}body\\end{block}\n\\end{frame}\n\\end{document}")
  t "contrast origin: a translated block role names its declaration"
    (beamer.any fun d => d.code == "N0022" && atSource d 3 "\\setbeamercolor")

end Tests
