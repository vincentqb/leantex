module

public import Tests.Support

public section

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-! The styling API's closure: every design token the engine declares as a CSS custom property is
read by some rule of the emitted stylesheets, judged over the corpus. -/

/-- Every token name a shipped bundle declares: the set the engine answers for, as against a
document's own `\tokens` names. -/
def engineTokenNames : List String :=
  (Theme.builtin.flatMap fun th =>
    th.tokens.entries.toList.map (·.1)).eraseDups

/-- A custom property's declaration site, as `tokenVars` spells it; the colon anchors the name. -/
def declaresToken (html name : String) : Bool := hasStr html s!"--{name}:"

/-- A reference to the property from a rule or an inline style, bare or with a fallback; the
delimiter anchors the name. -/
def readsToken (html name : String) : Bool :=
  hasStr html s!"var(--{name})" || hasStr html s!"var(--{name},"

/-- The engine tokens no rule reads anywhere in the corpus, each with its reason: a ratchet read
both ways. -/
def htmlUnreadTokenOffences : List (String × String) := []

/-- The `--ltx-*` colour properties a page reads with no fallback: each
`var(--ltx-<name>)` it spells, a rule's read or an alias's target. -/
def ltxBareReads (html : String) : List String :=
  ((html.splitOn "var(--ltx-").drop 1).filterMap fun piece =>
    let cs := piece.toList
    let name := cs.takeWhile fun c => c.isAlphanum || c == '-' || c == '_'
    if (cs.drop name.length).head? == some ')' then some (String.ofList name) else none

/-- The colour properties a page reads with no fallback and never declares, each leaving its rule
invalid at computed-value time. -/
def ltxDanglingReads (html : String) : List String :=
  (ltxBareReads html).eraseDups.filter fun n => !hasStr html s!"--ltx-{n}:"

/-- A design token the engine emits is read by some rule, and a colour property read without a
fallback is declared, on every shipped page. -/
def htmlTokenClosureChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  for (n, _) in htmlUnreadTokenOffences do
    t s!"unread token row {n}: names an engine token"
      (engineTokenNames.contains n)
  t "property closure: the judge names a bare read the page never declares"
    (ltxDanglingReads "a { color: var(--ltx-zz) }" == ["zz"] &&
      ltxDanglingReads "a { color: var(--ltx-zz, #000) }" == [] &&
      ltxDanglingReads ":root { --ltx-zz: #000; } a { color: var(--ltx-zz) }" == [] &&
      ltxDanglingReads ":root { --ltx-zz: var(--ltx-yy); }" == ["yy"])
  let mut pages : List String := []
  for n in goldenNames do
    let (doc, _) ← goldenDoc n
    let html := (HtmlDoc.emit {} doc).1
    t s!"property closure {n}: every colour property read without a fallback is declared"
      (ltxDanglingReads html).isEmpty
    pages := html :: pages
  for tok in engineTokenNames do
    let declared := pages.any fun h => declaresToken h tok
    let read := pages.any fun h => readsToken h tok
    if htmlUnreadTokenOffences.any fun (f, _) => f == tok then
      t s!"token closure {tok}: the recorded offence no longer fires — a rule \
now reads it; delete its row" (declared && !read)
    else
      t s!"token closure {tok}: declared as a custom property by some fixture, \
so some rule must reference it" (!declared || read)

/-- The role properties a page declares (`--ltx-<role>: …`), by property. -/
def roleDeclsIn (html : String) : List String :=
  (((html.splitOn "--ltx-").drop 1).filterMap fun piece =>
    let name := String.ofList (piece.toList.takeWhile fun c => c.isAlphanum || c == '-' || c == '_')
    let rest := (piece.toList.drop name.length).dropWhile (· == ' ')
    if rest.head? == some ':' then some ("--ltx-" ++ name) else none).filter
      fun n => (HtmlDoc.roleOfVar? n).isSome

/-- The role properties a page reads (`var(--ltx-<role>`), with or without
a fallback. -/
def roleReadsIn (html : String) : List String :=
  (HtmlDoc.varReads html).toList.filter fun n => (HtmlDoc.roleOfVar? n).isSome

/-- A page declares exactly the colour roles it reads, on every shipped page, and a planted pair
holds the judge to both directions. -/
def htmlRoleClosureChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let judge (html : String) : List String × List String :=
    let decls := roleDeclsIn html
    let reads := roleReadsIn html
    ((reads.filter (!decls.contains ·)).eraseDups, (decls.filter (!reads.contains ·)).eraseDups)
  t "role closure: the judge names an undeclared read and an unread declaration"
    (judge ":root { --ltx-bg: #fff; } a { color: var(--ltx-fg, #000) }" ==
      (["--ltx-fg"], ["--ltx-bg"]) &&
     judge ":root { --ltx-bg: #fff; --ltx-fg: var(--ltx-bg); } a { color: var(--ltx-fg) }" ==
      ([], []))
  for n in goldenNames do
    let (doc, _) ← goldenDoc n
    let html := (HtmlDoc.emit {} doc).1
    let (undeclared, unread) := judge html
    t s!"role closure {n}: every role read is declared ({undeclared})" undeclared.isEmpty
    t s!"role closure {n}: every declared role is read ({unread})" unread.isEmpty

/-- A length register named as TeX names internals publishes no custom property, while a plainly
named token keeps its own. -/
def htmlInternalTokenChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (doc, ds) := elabStr
    ("\\documentclass{article}\n\\makeatletter\n\\newlength{\\probe@len}\n" ++
     "\\newdimen\\probe@dim\n\\newlength{\\probeplain}\n\\setlength{\\probe@len}{7pt}\n" ++
     "\\setlength{\\parskip}{\\probe@len}\n\\makeatother\n" ++
     "\\begin{document}\nPlaceholder words.\n\nMore placeholder words.\n\\end{document}\n")
  t s!"internal tokens: the probe elaborates with no loss above a note ({ds.map (·.code)})"
    (ds.all fun d => d.severity == Severity.note)
  let (head, body, _) := HtmlDoc.emitTree {} doc
  let refusals := (HtmlResource.requests head body).filterMap fun
    | .refused why => some why
    | _ => none
  t s!"internal tokens: the stylesheet requests nothing it refuses ({refusals})" refusals.isEmpty
  let sheet := treeCssList "" (head.toList ++ body.toList)
  t "internal tokens: a token named in plain letters keeps its property"
    (hasStr sheet "--probeplain:")
  t "internal tokens: no property carries an internal name" (!hasStr sheet "@len" && !hasStr sheet "@dim")

/-- The title page's five gaps, on one synthetic document, each reference their own property with
the resolved length as the fallback, while a computed gap references none. -/
def htmlSourcedGapChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (doc, ds) := elabStr (deck169
    ("\\usetheme{moloch}\n" ++
     "\\title{Placeholder Title}\\subtitle{Placeholder Subtitle}\n" ++
     "\\author{Pat Placeholder}\\institute{example.org}\\date{Placeholder date}\n")
    "\\maketitle\n")
  -- `\usetheme` is a compat spelling, so its N0100 note is expected; nothing above a note may fire.
  t "sourced gaps: the probe elaborates with no loss above a note"
    (ds.all fun d => d.severity == Severity.note)
  let html := (HtmlDoc.emit {} doc).1
  -- Without the fallback a gap would collapse to zero wherever the document's table lacks the name.
  for (tok, fallback) in
      [("subtitlegap", "0.3em"), ("separatorgap", "0.8em"),
       ("authorgap", "0.5em"), ("institutegap", "1em"),
       ("separatorheight", "0.5pt")] do
    t s!"sourced gap {tok}: the rule defers to the property, resolved value \
as the fallback" (hasStr html s!"var(--{tok}, {fallback})")
  -- Read on the element's own inline style: the static stylesheet defers plenty of its own margins.
  let (bDoc, bDs) := elabStr (dvDoc "" "\\block[before = 7pt]{Placeholder body.}")
  t "sourced gaps: the computed-gap probe elaborates clean" (bDs.isEmpty)
  let bHtml := (HtmlDoc.emit {} bDoc).1
  t "sourced gaps: a computed gap prints its length and references no property"
    (hasStr bHtml "style=\"margin-top: 7pt\"" &&
      !hasStr bHtml "style=\"margin-top: var(")
