module

public import Tests.Artifact
import LeanTex.Core.Marker

public section

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-! The log-only control gate: LaTeX's package and class diagnostics are consumed before inline
elaboration and ship no ink, the family held against `Compat.ctrlRows` with an owed count that
only falls. -/

/-- The LaTeX controls that write the log or the terminal and contribute no ink, each with its
public definition's arity; `\MessageBreak` is arity 0. -/
def logOnlyControls : List (String × Nat) :=
  [("PackageWarning", 2), ("PackageWarningNoLine", 2), ("PackageInfo", 2),
   ("PackageInfoNoLine", 2), ("PackageError", 3),
   ("ClassWarning", 2), ("ClassWarningNoLine", 2), ("ClassInfo", 2),
   ("ClassInfoNoLine", 2), ("ClassError", 3),
   ("GenericWarning", 2), ("GenericInfo", 2), ("GenericError", 4),
   ("MessageBreak", 0), ("typeout", 1), ("wlog", 1),
   ("@latex@warning", 1), ("@latex@info", 1), ("@latex@error", 2)]

/-- The most members of `logOnlyControls` that may still reach unknown-command recovery: a ratchet
that may only fall. -/
def logOnlyOwedBaseline : Nat := 19

/-- The synthetic package name and message every probe uses, each holding a reserved character, so a
recovered group would error. -/
def logOnlyPkg : String := "example_pkg"

def logOnlyMsg : String := "ignored_message"

/-- The message strings as they reach the page if a group is recovered, the reserved character
dropped. -/
def logOnlyInkStrings : List String := ["examplepkg", "ignoredmessage"]

/-- `n` groups for a probe: the package name first, then the message,
then filler, so a wrong arity leaves a recognisable residue. -/
def logOnlyGroups (n : Nat) : String := Id.run do
  let mut out := ""
  for i in [0:n] do
    out := out ++ "{" ++ (if i == 0 then logOnlyPkg else if i == 1 then logOnlyMsg
      else s!"filler_{i}") ++ "}"
  return out

/-- A control in the body, and the same control deferred through `\AtBeginDocument`. -/
def logOnlyBodySrc (name : String) (n : Nat) : String :=
  "\\documentclass{article}\n\\begin{document}\nx \\" ++ name ++ logOnlyGroups n ++
    "\n\\end{document}"

def logOnlyHookSrc (name : String) (n : Nat) : String :=
  "\\documentclass{article}\n\\AtBeginDocument{\\" ++ name ++ logOnlyGroups n ++
    "}\n\\begin{document}\nx\n\\end{document}"

/-- Whether the document carries nothing but `x` in its body, furniture and metadata. -/
def logOnlyQuiet (d : Ir.Doc) : Bool :=
  (match d.body with
    | #[.para xs] => Ir.plainText xs == "x"
    | _ => false)
  && d.head.isNone && d.foot.isNone && d.logo.isNone
  && d.logoLeft.isNone && d.logoRight.isNone && d.headline.isNone
  && d.info.title.isNone

/-- Whether a construct's consumption is accounted by name: N0100 under `ctrl:nothing:<name>`, or
W0387 under `ctrl:<name>`, read off `Diag.subject`. -/
def logOnlyAccounted (name : String) (ds : Array Diag) : Bool :=
  ds.any fun d =>
    (d.code == "N0100" && d.subject == some ("ctrl:nothing:" ++ name))
    || (d.code == "W0387" && d.subject == some ("ctrl:" ++ name))

/-- Every log-only control the engine consumes, probed in the body and through a deferred hook,
leaves no ink, warning or error, is named, and has its LaTeX arity. -/
def logOnlySurfaceChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let listed := logOnlyControls.filter fun (n, _) => (Compat.ctrlRow? n).isSome
  let owed := logOnlyControls.filter fun (n, _) => (Compat.ctrlRow? n).isNone
  t s!"log-only controls: the arity of every consumed row is LaTeX's \
({listed.map (·.1)})"
    (listed.all fun (n, arity) => (Compat.ctrlRow? n).map (·.sig.length) == some arity)
  t s!"log-only controls: {owed.length} of {logOnlyControls.length} still reach body \
recovery, over the recorded {logOnlyOwedBaseline} ({owed.map (·.1)})"
    (owed.length ≤ logOnlyOwedBaseline)
  t s!"log-only controls: the owed baseline {logOnlyOwedBaseline} has been overtaken by \
{owed.length} — lower it" (logOnlyOwedBaseline ≤ logOnlyControls.length)
  for (name, arity) in listed do
    for (where_, src) in [("in the body", logOnlyBodySrc name arity),
        ("deferred through \\AtBeginDocument", logOnlyHookSrc name arity)] do
      let (d, ds) := elabStr src
      t s!"log-only \\{name} {where_}: the document carries no ink of its groups"
        (logOnlyQuiet d)
      t s!"log-only \\{name} {where_}: no unknown-command warning"
        (ds.all fun x => x.code != "W0301" && x.code != "W0302")
      t s!"log-only \\{name} {where_}: no error from the reserved characters \
({(ds.filter (·.severity == .error)).toList.map (·.code)})"
        (ds.all (·.severity != .error))
      t s!"log-only \\{name} {where_}: its consumption is accounted by name"
        (logOnlyAccounted name ds)

/-- No consumed control's log prose is painted in a produced PDF, while the same strings set as body
text are found. -/
def logOnlyArtifactChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet)
    (pats : Hyphen.Patterns) : IO Unit := do
  let t := check ref
  let inkOf (src : String) : Option String :=
    let (d, _) := elabStr src
    let g := Layout.Geom.ofPage d.page
    let out := layoutOf oneFace d g (some pats)
    match readArtifact (driverPdf oneFace g d out) with
    | .error _ => none
    | .ok pages => some (String.join (pages.toList.flatMap fun p =>
        p.runs.toList.map (·.text)))
  -- The positive control: the strings are found when a document really sets them.
  let control := "\\documentclass{article}\n\\begin{document}\nx " ++
    logOnlyPkg.replace "_" "" ++ " " ++ logOnlyMsg.replace "_" "" ++ "\n\\end{document}"
  match inkOf control with
  | none => t "log-only artifact control: the file reads back" false
  | some ink =>
    t s!"log-only artifact control: the reading finds the strings when they are body text"
      (logOnlyInkStrings.all fun s => hasStr ink s)
  for (name, arity) in logOnlyControls.filter
      fun (n, _) => (Compat.ctrlRow? n).isSome do
    for (where_, src) in [("in the body", logOnlyBodySrc name arity),
        ("deferred through \\AtBeginDocument", logOnlyHookSrc name arity)] do
      match inkOf src with
      | none => t s!"log-only artifact \\{name} {where_}: the file reads back" false
      | some ink =>
        t s!"log-only artifact \\{name} {where_}: the page paints none of its log prose"
          (logOnlyInkStrings.all fun s => !hasStr ink s)

def logOnlyChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet)
    (pats : Hyphen.Patterns) : IO Unit := do
  logOnlySurfaceChecks ref
  logOnlyArtifactChecks ref oneFace pats

/-- The discard arms, one usage per call that writes a discard, with the key each owes: preamble,
body, key. -/
def discardSites : List (String × String × String) :=
  [("\\usepackage{hyperref}\n", "", "usepackage:hyperref"),
   ("\\RequirePackage{url}\n", "", "RequirePackage:url"),
   ("\\usepackage{crop}\n", "", "usepackage:crop"),
   ("\\usepackage[left]{lineno}\n", "", "usepackage:lineno"),
   ("\\newcommand{\\zzkept}{a}\n\\providecommand{\\zzkept}{b}\n", "",
     "providecommand:zzkept"),
   ("\\providecommand{\\section}{}\n", "", "providecommand:section"),
   ("\\usepackage{babel}\n", "", "usepackage:babel"),
   ("\\pagestyle{fancy}\n", "", "pagestyle:fancy"),
   ("\\fontseries{b}\n", "", "fontseries:b"),
   ("\\selectlanguage{french}\n", "", "selectlanguage:french"),
   ("\\usefonttheme{professionalfonts}\n", "", "usefonttheme"),
   ("\\setbeameroption{hide notes}\n", "", "setbeameroption"),
   ("\\KOMAoptions{headsepline=false}\n", "", "KOMAoptions"),
   ("\\sectionlinesformat{}\n", "", "sectionlinesformat"),
   ("", "\\printbibliography", "printbibliography")]

def compatDiscardChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let keyed (ds : Array Diag) (key : String) : Array Diag :=
    ds.filter fun d => d.code == "N0100" && d.subject == some ("ctrl:nothing:" ++ key)
  for (pre, body, key) in discardSites do
    let (_, ds) := elabStr (dvDoc pre body)
    t s!"discard {key}: the note is keyed as a discard"
      ((keyed ds key).size == 1)
  let (_, inert) := elabStr (dvDoc "\\makeatletter\n" "")
  t "discard makeatletter: the inert table's note is keyed as a discard"
    ((keyed inert "makeatletter").size == 1)
  let (_, plain) := elabStr (dvDoc "\\pagestyle{plain}\n" "")
  let notes := plain.filter (·.code == "N0100")
  t "discard: a translation's note carries no discard key"
    (!notes.isEmpty && notes.all fun d => !(d.subject.any (·.startsWith "ctrl:nothing:")))
  let (_, two) := elabStr (dvDoc "\\usepackage{hyperref}\n\\usepackage{url}\n" "")
  t "discard: two packages are two keys, one site each"
    ((keyed two "usepackage:hyperref").all (·.sites == 1) &&
      (keyed two "usepackage:url").all (·.sites == 1) &&
      (keyed two "usepackage:hyperref").size == 1 && (keyed two "usepackage:url").size == 1)

/-- The fragment-keeping arms, one row per shape of loss: what it exercises, its key (`ctrl:<key>`),
and a usage. -/
def fragmentArms : List (String × String × String) :=
  [("a span that does not open its cell", "multicolumn:misplaced",
      "\\begin{tabular}{lll}\na \\multicolumn{2}{c}{Mid} & d & e \\\\\n\\end{tabular}"),
   ("a span in a group", "multicolumn:misplaced",
      "\\begin{tabular}{lll}\n{\\multicolumn{2}{c}{Grp}} & d & e \\\\\n\\end{tabular}"),
   ("a count that is not a numeral", "multicolumn:unread",
      "\\begin{tabular}{lll}\n\\multicolumn{\\relax}{c}{Wide} & b & c \\\\\n\\end{tabular}")]

def compatFragmentChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let own (ds : Array Diag) (key : String) : Array Diag :=
    ds.filter (·.subject == some ("ctrl:" ++ key))
  for (what, key, usage) in fragmentArms do
    let (_, ds) := elabStr (dvDoc "" usage)
    t s!"fragment arm, {what}: what it drops is named under its own key"
      ((own ds key).size == 1 && (own ds key).all (·.severity == .warning))
    let (_, twice) := elabStr (dvDoc "" (usage ++ "\n\n" ++ usage))
    t s!"fragment arm, {what}: two sites are one named loss, counted twice"
      ((own twice key).size == 2 && ((own twice key).map (·.sites)).toList == [2, 0] &&
        ((own twice key).filter (·.severity == .warning)).size == 1)
  let (oneDoc, _) := elabStr (dvDoc "" "\\begin{tabular}{lll}\n\\multicolumn{1}{r}{Right} & b & c \\\\\n\\end{tabular}")
  t "fragment arm, one column: the row's cells stay in their columns"
    (match oneDoc.body with
     | #[.table _ _ _ rows _ _] => rows.map (·.map Ir.plainText) == #[#["Right", "b", "c"]]
     | _ => false)
  let (defDoc, defDs) := elabStr (dvDoc "\\newcommand{\\zzhead}[1]{\\multicolumn{2}{c}{#1}}\n"
    "\\begin{tabular}{lll}\n\\zzhead{Heading} & z \\\\\na & b & c \\\\\n\\end{tabular}")
  t "fragment arm: a parameter in the kept text is the definition's parameter"
    (!defDs.any (·.code == "E0311") &&
      match defDoc.body with
      | #[.table _ _ _ rows _ _] => (rows[0]?.bind (·[0]?)).map Ir.plainText == some "Heading"
      | _ => false)
  let (grpDoc, grpDs) := elabStr (dvDoc "\\newcommand{\\zzg}[1]{{\\multicolumn{2}{c}{#1}}}\n"
    "\\begin{tabular}{lll}\n\\zzg{Grp} & d & e \\\\\n\\end{tabular}")
  let grpText := Ir.blocksText grpDoc.body
  t "a span a definition wraps in a group keeps its text and is named, never unknown"
    (!grpDs.any (·.code == "W0301") &&
      grpDs.any (·.subject == some "ctrl:multicolumn:misplaced") &&
      (grpText.splitOn "Grp").length == 2 && (grpText.splitOn "2 c").length == 1)
  for (what, row, want) in [
      ("a leading span", "\\multicolumn{2}{c}{Span} & d", #["Span", "", "d"]),
      ("a trailing span", "a & \\multicolumn{2}{c}{Span}", #["a", "Span", ""]),
      ("a full-row span", "\\multicolumn{3}{c}{Span}", #["Span", "", ""])] do
    let (spanDoc, _) := elabStr (dvDoc "" s!"\\begin\{tabular}\{lll}\n{row} \\\\\n\\end\{tabular}")
    t s!"a {what}: the text fills its head cell, and a later cell keeps its column"
      (match spanDoc.body with
       | #[.table _ _ _ rows _ _] => rows.map (·.map Ir.plainText) == #[want]
       | _ => false)

/-- Span probes, as (what, preamble, body). -/
def spanAccountingProbes : List (String × String × String) :=
  [("a leading span", "",
      "\\begin{tabular}{lll}\n\\multicolumn{2}{c}{Span} & d \\\\\na & b & c \\\\\n\\end{tabular}"),
   ("a trailing span", "",
      "\\begin{tabular}{lll}\na & \\multicolumn{2}{c}{Span} \\\\\na & b & c \\\\\n\\end{tabular}"),
   ("a full-row span", "",
      "\\begin{tabular}{lll}\n\\multicolumn{3}{c}{Span} \\\\\na & b & c \\\\\n\\end{tabular}"),
   ("a span through a definition", "\\newcommand{\\zzspan}[1]{\\multicolumn{2}{c}{#1}}\n",
      "\\begin{tabular}{lll}\n\\zzspan{Span} & d \\\\\na & b & c \\\\\n\\end{tabular}"),
   ("a one-column realignment", "",
      "\\begin{tabular}{lll}\n\\multicolumn{1}{r}{Right} & b & c \\\\\n\\end{tabular}")]

/-- The probes that print two lines for one span, with what owes the merge. -/
def spanAccounting : List (String × String) := []

def spanAccountingChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let visible (ds : Array Diag) (p : String → Bool) : Bool :=
    ds.any fun d => d.code == "W0337" && d.severity == .warning && (d.subject.map p).getD false
  for (what, pre, body) in spanAccountingProbes do
    let (_, ds) := elabStr (dvDoc pre body)
    let doubled := visible ds (·.startsWith "ctrl:multicolumn") &&
      visible ds (· == "tabular:ragged")
    t s!"span accounting {what}: a set span prints no W0337"
      (!visible ds fun _ => true)
    if spanAccounting.any (·.1 == what) then
      t s!"span accounting {what}: the row still describes two lines for one span"
        doubled
    else
      t s!"span accounting {what}: one span, one visible line" (!doubled)
  for (what, _) in spanAccounting do
    t s!"span accounting {what}: the row names a probe"
      (spanAccountingProbes.any (·.1 == what))

mutual

/-- Every element of an emitted tree carrying the attribute `key`, as its subtree text and the
attribute's value. -/
def attrRunsOne (key : String) (acc : Array (String × String)) :
    Html.Node → Array (String × String)
  | .text _ => acc
  | .style _ => acc
  | .script _ _ => acc
  | .elem t attrs kids =>
    let acc := match attrs.find? (·.1 == key) with
      | some (_, v) => acc.push (nodeTextOne "" (.elem t attrs kids), v)
      | none => acc
    attrRunsList key acc kids.toList

def attrRunsList (key : String) (acc : Array (String × String)) :
    List Html.Node → Array (String × String)
  | [] => acc
  | k :: rest => attrRunsList key (attrRunsOne key acc k) rest

end

def compatMarkerChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let markers := [Marker.name .series "", Marker.name .lang "", Marker.name .ink ""]
  let namesMarker (d : Diag) : Bool :=
    d.subject.any fun s => markers.any fun m => hasStr s m
  let docOf (pre : String) : Ir.Doc × Array Diag :=
    elabStr (dvDoc pre "Alpha bravo.\n\nCharlie delta.")
  for (what, decl) in [("a font series", "\\fontseries{b}\n"),
      ("a language switch", "\\selectlanguage{french}\n"),
      ("a colour", "\\color{red}\n")] do
    let (_, ds) := docOf decl
    t s!"preamble marker, {what}: no diagnostic names Compat's own spelling"
      (!ds.any namesMarker)
    t s!"preamble marker, {what}: the known construct is not called unknown"
      (ds.all (·.code != "W0301"))
    -- The preamble reader's silence rests on Compat's one note at the same site.
    t s!"preamble marker, {what}: the construct's own note accounts for it"
      ((ds.filter (·.code == "N0100")).size == 1)
  let noteOf (src : String) (key : String) : Array Diag :=
    (elabStr src).2.filter fun d => d.code == "N0100" &&
      d.subject == some ("ctrl:nothing:" ++ key)
  for (what, decl, key) in [("a font series", "\\fontseries{b}", "fontseries:b"),
      ("a language switch", "\\selectlanguage{french}", "selectlanguage:french")] do
    t s!"preamble marker, {what}: its note is a discard, keyed as one"
      ((noteOf (dvDoc (decl ++ "\n") "Alpha.") key).size == 1)
    for (where_, src) in [("in the body", dvDoc "" (decl ++ " Alpha.")),
        ("in a \\begin{document} hook", dvDoc s!"\\AtBeginDocument\{{decl}}\n" "Alpha."),
        ("inside a preamble definition",
          dvDoc s!"\\newcommand\{\\zzdecl}\{{decl}}\n" "\\zzdecl Alpha."),
        ("inside a \\title argument", dvDoc s!"\\title\{{decl} Plain}\n" "\\maketitle Alpha."),
        ("in a running-head field",
          dvDoc s!"\\usepackage\{scrlayer-scrpage}\n\\ihead\{{decl} Head}\n" "Alpha.")] do
      t s!"preamble marker, {what} {where_}: its note is a translation, not a discard"
        (noteOf src key).isEmpty
  -- LaTeX resets these at `\begin{document}`: the document is the one
  -- without them.
  t "preamble marker: a font series reaches no text, as LaTeX's does not"
    ((docOf "\\fontseries{b}\n").1 == (docOf "").1)
  t "preamble marker: a language switch reaches no text, as babel's does not"
    ((docOf "\\selectlanguage{french}\n").1 == (docOf "").1)
  -- `\enquote` reads its quotes through the main language, so a leaked switch shows there.
  let quoted (pre : String) : Ir.Doc :=
    (elabStr (dvDoc pre "Alpha \\enquote{bravo} charlie.")).1
  let babelOf (other main : String) : String :=
    s!"\\usepackage[{other},{main}]\{babel}\n\\usepackage\{csquotes}\n"
  for (main, other) in [("english", "french"), ("french", "english")] do
    t s!"preamble marker: a switch to {other} reaches no quote \
when {main} is the main language"
      (quoted (babelOf other main ++ s!"\\selectlanguage\{{other}}\n") ==
        quoted (babelOf other main))
  let door := babelOf "english" "french" ++ "\\AtBeginDocument{\\selectlanguage{english}}\n"
  t "preamble marker: a switch in a \\begin{document} hook still reaches the body"
    (quoted door != quoted (babelOf "english" "french"))
  t "preamble marker: a switch in a \\begin{document} hook keeps the main language's quotes"
    (Ir.blockTextList "" (quoted door).body.toList ==
      Ir.blockTextList "" (quoted (babelOf "english" "french")).body.toList)
  -- LaTeX keeps the colour: the document is the one whose `\begin{document}`
  -- hook sets it.
  t "preamble marker: a colour is the body's first declaration, as in LaTeX"
    ((docOf "\\color{red}\n").1 == (docOf "\\AtBeginDocument{\\color{red}}\n").1)
  let (defDoc, _) := elabStr (dvDoc "\\newcommand{\\zzheavy}{\\fontseries{b}\\selectfont}\n"
    "Alpha {\\zzheavy bravo} charlie.")
  let series := Ir.foldBlocks (fun n _ => n) (fun n i => match i with
    | .styled (.series _) _ => n + 1
    | _ => n) 0 defDoc.body
  t "preamble marker: a series inside a preamble definition still applies where it is used"
    (series == 1)
  let (langDoc, _) := elabStr (dvDoc "\\newcommand{\\zzfrench}{\\selectlanguage{french}}\n"
    "Alpha.\n\n\\zzfrench Bravo.")
  let tagged := Ir.foldBlocks (fun n _ => n) (fun n i => match i with
    | .styled (.lang "fr") _ => n + 1
    | _ => n) 0 langDoc.body
  t "preamble marker: a language switch inside a preamble definition still applies where it is used"
    (tagged == 1)
  -- Two copies of one face: the bold weight's own index tells whether the series reached a run.
  let some data ← findFont
    | failures ref "preamble marker: the shipped test face is missing"
  let .ok font := Font.parse data
    | failures ref "preamble marker: the shipped test face is unparsable"
  let weighted : Font.FontSet := {
    fonts := #[font, font]
    index := ((List.range 3).flatMap fun slot =>
      [((slot, 400, false), 0), ((slot, 700, false), 1),
       ((slot, 400, true), 0), ((slot, 700, true), 1)]).toArray }
  let faceOf (src word : String) : Option Nat :=
    (allLines (layoutOf weighted (elabStr src).1)).findSome? fun l =>
      l.segs.findSome? fun s => match s with
        | .run idx _ _ _ glyphs _ _ _ _ _ _ =>
          if glyphs.foldl (fun acc (_, c, _) => acc.push c) "" == word then some idx else none
        | _ => none
  let htmlRuns (src key : String) : Array (String × String) :=
    let (_, body, _) := HtmlDoc.emitTree {} (elabStr src).1
    attrRunsList key #[] body.toList
  let bold (src word : String) : Bool :=
    (htmlRuns src "style").any fun (txt, v) => txt == word && hasStr v "font-weight: 700"
  let author := dvDoc
    "\\title{Plain title}\n\\author{{\\fontseries{b}\\selectfont Ada} Example}\n\\date{}\n"
    "\\maketitle\nAlpha bravo."
  t "preamble marker: a series in an \\author argument sets the grouped name in the bold face"
    (faceOf author "Ada" == some 1 && faceOf author "Example" == some 0)
  t "preamble marker: a series in an \\author argument ships the grouped name bold in the HTML"
    (bold author "Ada")
  let running := dvDoc ("\\usepackage{scrlayer-scrpage}\n\\pagestyle{scrheadings}\n" ++
    "\\ihead{{\\fontseries{b}\\selectfont Head} note}\n") "Alpha bravo."
  t "preamble marker: a series in a running-head field sets the grouped word in the bold face"
    (faceOf running "Head" == some 1 && faceOf running "note" == some 0)
  let titled := dvDoc
    "\\title{{\\fontseries{b}\\selectfont Bold} title}\n\\author{Ada Example}\n\\date{}\n"
    "\\maketitle\nAlpha bravo."
  t "preamble marker: a series in a \\title argument ships the grouped word bold in the HTML"
    (bold titled "Bold")
  let french := dvDoc
    ("\\usepackage[french,english]{babel}\n\\title{\\selectlanguage{french}Le titre}\n" ++
      "\\author{Ada Example}\n\\date{}\n") "\\maketitle\nAlpha bravo."
  t "preamble marker: a language switch in a \\title argument tags the title in the HTML"
    ((htmlRuns french "lang").any fun (txt, v) => txt == "Le titre" && v == "fr")
  for (main, other, title) in [("english", "french", "Le titre"),
      ("french", "english", "The title")] do
    let src (switch : String) : String :=
      dvDoc (babelOf other main ++ s!"\\title\{{switch}{title}}\n\\author\{Ada Example}\n\\date\{}\n")
        "\\maketitle\nAlpha \\enquote{bravo} charlie."
    t s!"preamble marker: a switch to {other} in a \\title argument reaches \
no quote when {main} is the main language"
      (pageTextOf weighted (src s!"\\selectlanguage\{{other}}") == pageTextOf weighted (src ""))

def compatAccountingChecks (ref : IO.Ref (List String)) : IO Unit := do
  compatDiscardChecks ref
  compatFragmentChecks ref
  spanAccountingChecks ref
  compatMarkerChecks ref
