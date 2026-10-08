module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests

private def singletonAttr (attrs : Array (String × String)) (key : String) : String :=
  ((attrs.find? (·.1 == key)).map (·.2)).getD ""

/-- The emitted page must connect a one-reveal frame to its selector rules.
Reading only `data-steps` falsely certified the old page: its section had
no numbered state, and a one-reveal deck emitted no membership rules.
The browser witness checks the same pages with and without motion. -/
def overlaySingletonHtmlChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  for (property, off, moving) in
      [("animation", "none", "reveal 1s"), ("transition", "none", "opacity 1s"),
       ("scroll-behavior", "auto", "smooth")] do
    let rule : HtmlDoc.DeckRule := { selector := [.lit ".probe"], decls := [(property, off)] }
    t s!"motion guard: static {property} needs no second reset"
      (HtmlDoc.motionGuarded [] rule)
    t s!"motion guard: active {property} still requires a reduce witness"
      (!(HtmlDoc.motionGuarded [] { rule with decls := [(property, moving)] }))
  for (spec, selected) in
      [("0", false), ("0-0", false), ("1", true), ("1-", true),
       ("0-", true), ("1,1", true)] do
    for mixed in [false, true] do
      let extra := if mixed then
          "\n\\begin{frame}{Second}\\uncover<2>{Clock}\\end{frame}" else ""
      let (doc, ds) := elabStr (deck169Body
        ("\\begin{frame}{Single}\\uncover<" ++ spec ++
          ">{Marker}\\end{frame}" ++ extra))
      let label := s!"singleton HTML <{spec}> mixed={mixed}"
      t (label ++ " supported source") (ds.all fun d => d.severity == .note)
      let (head, tree, _) := HtmlDoc.emitTree {} doc
      let elements := elemAttrsList (fun _ => true) #[] tree.toList
      let stages := elements.filter fun (tag, attrs) =>
        tag == "section" && singletonAttr attrs "data-frame-number" == "1"
      t (label ++ " one stage with its own reveal state")
        (stages.size == 1 && stages.all fun (_, attrs) =>
          singletonAttr attrs "data-snapped" == "1" &&
          attrs.any (·.1 == "data-snap"))
      let carriers := elements.filter fun (_, attrs) =>
        (singletonAttr attrs "class").splitOn " " |>.contains "step-set"
      t (label ++ " exact finite membership")
        (carriers.size == 1 && carriers.all fun (_, attrs) =>
          singletonAttr attrs "data-steps" == (if selected then "1" else ""))
      let html := Html.document "en" head tree
      t (label ++ " state has a matching screen rule")
        ((html.splitOn ("html[data-deck-script] [data-snapped=\"1\"] " ++
          ".step-set:not([data-steps~=\"1\"]) { opacity: ")).length == 2)
      t (label ++ " reduced motion restores full ink")
        ((html.splitOn ("html[data-deck-script] [data-snapped] " ++
          ".step-set[data-steps] { opacity: 100%; }")).length == 2)
      t (label ++ " body preserved once") (treeOccurs tree "Marker" == 1)

end Tests
