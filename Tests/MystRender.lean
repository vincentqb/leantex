module

public import Tests.Support

public section

open LeanTex.Core LeanTex.Cli

namespace Tests.MystRender

/-- A fixture of the template corpus read and elaborated as the driver builds it. -/
private def build (name : String) : IO (Ir.Doc × Array Diag) := do
  let path := s!"testdata/myst-template/{name}.md"
  let src ← Input.readDocument path (← IO.FS.readBinFile path)
  let (doc, ds) := Elab.runExecuted path src.executed
  return (doc, src.diags ++ ds)

/-- A markdown document set through the MyST template its front matter declares, and the losses a
template absent or remote is named by, the document set without it. -/
def checks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let (doc, ds) ← build "paper"
  let c := censusOf #[] (layoutOf fonts doc)
  t s!"template: the front matter's title, authors, date and abstract part set by the template, then its body ({censusText c})"
    (["Kilo & Lima, 50% Invented", "Ada Example", "Bo Sample", "2026", "An invented abstract with emphasis.",
      "Draft copy.", "Papa", "Body text of invented words."].all (pageHas c 0 ·) &&
      (lineYOf c 0 "Draft copy.").any fun y => (lineYOf c 0 "Body text").any (y < ·))
  t s!"template: no front matter key the template reads is named unread ({ds.map (·.message)})"
    (ds.all fun d => !(d.code == "W0307" || d.subject == some "md:template"))
  let (doc, ds) ← build "absent"
  let c := censusOf #[] (layoutOf fonts doc)
  t "template: an absent template is named once and the document sets as itself"
    ((ds.filter (·.subject == some "md:template")).size == 1 && pageHas c 0 "Kilo" && pageHas c 0 "Body text.")
  let (_, ds) ← build "remote"
  t s!"template: a remote template is never fetched, named, and the parts no template reads named ({ds.map (·.message)})"
    (ds.any (fun d => d.subject == some "md:template" && d.detail.any (hasStr · "never fetched")) &&
      ds.any (·.subject == some "md:meta:parts"))
  let (doc, ds) ← build "cited"
  let c := censusOf #[] (layoutOf fonts doc)
  t s!"template: a part's citation is read as one, and the template's own bibliography set aside for the document's, named ({censusText c})"
    (pageHas c 0 "An abstract citing" && !pageHas c 0 "@zzkey" && pageHas c 0 "Body citing" &&
      ds.any (·.subject == some "md:template:bibliography"))
  let (_, ds) ← build "absent"
  t "template: the template set aside is named on its own, before any issue of its reading"
    ((ds.find? fun d => d.subject.any (·.startsWith "md:template")).any (·.subject == some "md:template"))
  t "template: a splice request is a word no source spells"
    ((MystRender.spliceName "CONTENT").any (· == ' ') && MystRender.spliceOf? (MystRender.spliceName "x") == some "x")

end Tests.MystRender
