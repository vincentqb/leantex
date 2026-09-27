import Tests.Artifact

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-! # The log-only control gate

LaTeX's package and class diagnostics write TeX's log and the terminal.
They contribute no document ink, so their argument groups must be consumed
before inline elaboration — a group recovered as body text ships the log
prose on the page, and a reserved character in that prose becomes a hard
error for a message no reader was ever meant to see.

`Compat.meaningFree` is the table that consumes them, and it grew six rows
for this reason. Two things were missing and are supplied here.

**The table had no mechanical coverage.** A row could be added with any
arity, any reason, covering any command, and nothing would check it — the
one hand-written loop that covered the six was written by the same commit
that added them. `nativePackages` carries exactly this obligation and
enforces it twice (the hook rejects an entry with no index file, `lake
test` probes every row); `meaningFree` carried none. So the gate below is
table-driven: every log-only control the table lists is probed in both
positions that matter, and its declared arity is held against the public
LaTeX definition. A seventh row gets the same treatment as the first six
without anyone remembering to write a test.

**The family is larger than the table.** `\PackageError` and `\ClassError`
take three groups, `\typeout` and `\wlog` one, `\GenericError` four; none
is consumed, and `\PackageError` reproduces the identical failure through
the identical deferred hook. Enumerating the family and counting what is
still owed turns a silent gap into a number that may only fall, so the
next reproducer is a row to flip rather than a defect to rediscover.

**The claim is a page claim.** "Out of body text" is an assertion about
ink, and the elaboration-tier test that carries it reads `Ir.Doc`, which
cannot see a leak into furniture, a page number, or an image. The artifact
half below reads the painted glyph runs of a produced PDF and asks whether
the log prose is among them, with a positive control proving the reading
can see those very strings when they are ordinary body text. -/

/-- The LaTeX controls that write the log or the terminal and contribute no
document ink, each with the arity of its public definition (`lterror.dtx`
for the `Package*`/`Class*`/`Generic*` family, `latex.ltx` for `\wlog`,
`ltdefns.dtx` for `\typeout`). `\MessageBreak` is arity 0: outside a
message LaTeX `\let`s it to `\relax`.

The list is the *family*, not the engine's progress through it. What the
engine has actually consumed is `Compat.meaningFree`; the two are held
against each other below, in both directions. -/
def logOnlyControls : List (String × Nat) :=
  [("PackageWarning", 2), ("PackageWarningNoLine", 2), ("PackageInfo", 2),
   ("PackageInfoNoLine", 2), ("PackageError", 3),
   ("ClassWarning", 2), ("ClassWarningNoLine", 2), ("ClassInfo", 2),
   ("ClassInfoNoLine", 2), ("ClassError", 3),
   ("GenericWarning", 2), ("GenericInfo", 2), ("GenericError", 4),
   ("MessageBreak", 0), ("typeout", 1), ("wlog", 1),
   ("@latex@warning", 1), ("@latex@info", 1), ("@latex@error", 2)]

/-- The most members of `logOnlyControls` that may still reach ordinary
unknown-command recovery, where their groups become body text. A ratchet,
in the shape `bangBaseline` uses: consuming one lowers it, and nothing may
raise it. The named members are printed by the check that reads this, so
what is owed is visible without grepping.

Nineteen: the engine consumes none of the family on this commit's base.
The six `Package*`/`Class*` warning and info spellings land in
`Compat.meaningFree` on a later commit, which lowers it to thirteen. -/
def logOnlyOwedBaseline : Nat := 19

/-- The synthetic package name and message every probe uses. Both carry a
reserved character on purpose: that is what turned a recovered log group
into a hard error, so its absence is the sharpest evidence the group was
consumed rather than merely tidied. -/
def logOnlyPkg : String := "example_pkg"

def logOnlyMsg : String := "ignored_message"

/-- The message strings as they reach the page if a group is recovered:
the elaborator drops the reserved character, so the ink to look for is the
name without its underscore. -/
def logOnlyInkStrings : List String := ["examplepkg", "ignoredmessage"]

/-- `n` groups for a probe: the package name first, then the message,
then filler, so a wrong arity leaves a recognisable residue. -/
def logOnlyGroups (n : Nat) : String := Id.run do
  let mut out := ""
  for i in [0:n] do
    out := out ++ "{" ++ (if i == 0 then logOnlyPkg else if i == 1 then logOnlyMsg
      else s!"filler_{i}") ++ "}"
  return out

/-- A control in the body, and the same control deferred through
`\AtBeginDocument` — the position the defect was reported in, where the
preamble's own handling no longer applies. -/
def logOnlyBodySrc (name : String) (n : Nat) : String :=
  "\\documentclass{article}\n\\begin{document}\nx \\" ++ name ++ logOnlyGroups n ++
    "\n\\end{document}"

def logOnlyHookSrc (name : String) (n : Nat) : String :=
  "\\documentclass{article}\n\\AtBeginDocument{\\" ++ name ++ logOnlyGroups n ++
    "}\n\\begin{document}\nx\n\\end{document}"

/-- Does this document's body carry nothing but `x`, in furniture and
metadata as well as prose? `Ir.plainText` is a census of characters, so a
leak that becomes a running head, a title, a page number, a fill or an
image passes an assertion written over the body alone. The engine's own
furniture and metadata surface is read here too, because a "fix" that
routed a log message into `\runninghead` would ship it on every page. -/
def logOnlyQuiet (d : Ir.Doc) : Bool :=
  (match d.body with
    | #[.para xs] => Ir.plainText xs == "x"
    | _ => false)
  && d.head.isNone && d.foot.isNone && d.logo.isNone
  && d.logoLeft.isNone && d.logoRight.isNone && d.headline.isNone
  && d.info.title.isNone

/-- Is this construct's consumption accounted *by name*? Two accountings
are legitimate and the invariant is that one of them fired, not which:
`Compat.became` earns the silence with an N0100 when the table carries a
justification, and a table row whose justification is `none` — the `Error`
spellings, where a signal is genuinely lost — is named by W0387 instead.
A control that consumed its groups and said neither still fails, which is
the loss this gate exists to catch.

Both are recognised by `Diag.subject`, never by the text they render:
AGENTS.md's `_named` rule is that matching is the structured subject, and
message text is the golden's business. The two doors namespace their keys
differently because they are different losses about the same control —
`ctrl:nothing:<name>` for the translated silence, `ctrl:<name>` for the
guard — so this asks for either, and asking for *some* N0100 would not do:
that is satisfied by `\AtBeginDocument`'s own note and passes on a
document that never names the control. -/
def logOnlyAccounted (name : String) (ds : Array Diag) : Bool :=
  ds.any fun d =>
    (d.code == "N0100" && d.subject == some ("ctrl:nothing:" ++ name))
    || (d.code == "W0387" && d.subject == some ("ctrl:" ++ name))

/-- The surface half: every log-only control the engine claims to consume
is probed in the body and through a deferred hook, and must leave nothing
behind — no ink anywhere in the document, no unknown-command warning, no
error from the reserved characters, and an accounting that names it. The
arity the table declares is held against the public LaTeX definition,
which is the check that stops `\PackageError` from entering at two groups
and inking its help text. -/
def logOnlySurfaceChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let listed := logOnlyControls.filter fun (n, _) => (Compat.meaningFree.lookup n).isSome
  let owed := logOnlyControls.filter fun (n, _) => (Compat.meaningFree.lookup n).isNone
  t s!"log-only controls: the arity of every consumed row is LaTeX's \
({listed.map (·.1)})"
    (listed.all fun (n, arity) => (Compat.meaningFree.lookup n).map (·.1) == some arity)
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

/-- The artifact half: the page claim the subject line makes. Every
consumed control is built the way the driver builds a document and its
painted glyph runs are read back; none of them may spell the log prose.
The positive control is the same strings as ordinary body text — it must
be *found*, which is what makes a silent pass above evidence rather than
an absence of evidence. -/
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
  -- The positive control: these strings are visible to the reading when a
  -- document really sets them.
  let control := "\\documentclass{article}\n\\begin{document}\nx " ++
    logOnlyPkg.replace "_" "" ++ " " ++ logOnlyMsg.replace "_" "" ++ "\n\\end{document}"
  match inkOf control with
  | none => t "log-only artifact control: the file reads back" false
  | some ink =>
    t s!"log-only artifact control: the reading finds the strings when they are body text"
      (logOnlyInkStrings.all fun s => hasStr ink s)
  for (name, arity) in logOnlyControls.filter
      fun (n, _) => (Compat.meaningFree.lookup n).isSome do
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


/-! # A discard is keyed as a discard

`became` is the translation note, `'\X' → <native>`. A construct that reads
to nothing used the same note with its target spelled "nothing: …" and no
subject, so to every consumer of `Diag.subject` a discard and a translation
were one shape: the census could not count a discard's sites, and nothing
structured told the two apart. `discard` is now the one writer of that
shape, and its subject is `ctrl:nothing:<key>`, sub-keyed by the argument
that decided the discard, so two discards are two census keys. -/

/-- The discard arms, one usage for each call that writes a discard (the
inert table's rows are the `makeatletter` row below), with the key each
owes: preamble, body, key. -/
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
    t s!"discard {key} (fails on base): the note is keyed as a discard"
      ((keyed ds key).size == 1)
  -- The inert table's rows were keyed before: the shape the others join.
  let (_, inert) := elabStr (dvDoc "\\makeatletter\n" "")
  t "discard makeatletter: the inert table's note is keyed as a discard"
    ((keyed inert "makeatletter").size == 1)
  -- A translation onto a native construct is the other shape, and never
  -- carries the discard key.
  let (_, plain) := elabStr (dvDoc "\\pagestyle{plain}\n" "")
  let notes := plain.filter (·.code == "N0100")
  t "discard: a translation's note carries no discard key"
    (!notes.isEmpty && notes.all fun d => !(d.subject.any (·.startsWith "ctrl:nothing:")))
  -- Sub-keyed by the argument that decided it: two packages are two
  -- discards, each one site, never one discard counted twice.
  let (_, two) := elabStr (dvDoc "\\usepackage{hyperref}\n\\usepackage{url}\n" "")
  t "discard (fails on base): two packages are two keys, one site each"
    ((keyed two "usepackage:hyperref").all (·.sites == 1) &&
      (keyed two "usepackage:url").all (·.sites == 1) &&
      (keyed two "usepackage:hyperref").size == 1 && (keyed two "usepackage:url").size == 1)

/-! # Arguments a rewrite reads and keeps only part of

The silence guard (`Compat.account`, `rewriteCtrl_accounts`) holds an arm to
account for what it consumed only when its replacement is empty. An arm that
keeps a fragment of what it read and drops the rest passes the guard whatever
it does with the rest: `\multicolumn{n}{align}{text}` kept `text`, dropped
the span and the alignment, and no code named the construct — the one
diagnostic was the table's padded-row warning, keyed to the table, and a
one-column realignment drew nothing at all. The kept group was also never
walked, so a definition's `#1` inside it shipped as a reserved-character
error and a stray digit. These rows are the census the guard cannot take. -/

/-- The fragment-keeping arms, one row per shape of loss: what the row
exercises, the key the loss owes (`ctrl:<key>`), and a usage. A new
fragment-keeping arm, or a new shape of an old one, enters here. -/
def fragmentArms : List (String × String × String) :=
  [("a span", "multicolumn",
      "\\begin{tabular}{lll}\n\\multicolumn{2}{c}{Spanning} & d \\\\\na & b & c \\\\\n\\end{tabular}"),
   ("one column", "multicolumn:1",
      "\\begin{tabular}{lll}\n\\multicolumn{1}{r}{Right} & b & c \\\\\n\\end{tabular}"),
   ("a count that is not a numeral", "multicolumn:unread",
      "\\begin{tabular}{lll}\n\\multicolumn{\\relax}{c}{Wide} & b & c \\\\\n\\end{tabular}")]

def compatFragmentChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let own (ds : Array Diag) (key : String) : Array Diag :=
    ds.filter (·.subject == some ("ctrl:" ++ key))
  for (what, key, usage) in fragmentArms do
    let (_, ds) := elabStr (dvDoc "" usage)
    t s!"fragment arm, {what} (fails on base): what it drops is named under its own key"
      ((own ds key).size == 1 && (own ds key).all (·.severity == .warning))
    -- Counted, not repeated: two sites are one visible line reading two.
    let (_, twice) := elabStr (dvDoc "" (usage ++ "\n\n" ++ usage))
    t s!"fragment arm, {what} (fails on base): two sites are one named loss, counted twice"
      ((own twice key).size == 2 && ((own twice key).map (·.sites)).toList == [2, 0] &&
        ((own twice key).filter (·.severity == .warning)).size == 1)
  -- A one-column realignment moves nothing: the row keeps its grid.
  let (oneDoc, _) := elabStr (dvDoc "" "\\begin{tabular}{lll}\n\\multicolumn{1}{r}{Right} & b & c \\\\\n\\end{tabular}")
  t "fragment arm, one column: the row's cells stay in their columns"
    (match oneDoc.body with
     | #[.table _ _ _ rows _] => rows.map (·.map Ir.plainText) == #[#["Right", "b", "c"]]
     | _ => false)
  -- The kept text is walked like any group: inside a definition body, its
  -- `#1` is the definition's parameter.
  let (defDoc, defDs) := elabStr (dvDoc "\\newcommand{\\zzhead}[1]{\\multicolumn{2}{c}{#1}}\n"
    "\\begin{tabular}{lll}\n\\zzhead{Heading} & z \\\\\na & b & c \\\\\n\\end{tabular}")
  t "fragment arm (fails on base): a parameter in the kept text is the definition's parameter"
    (!defDs.any (·.code == "E0311") &&
      match defDoc.body with
      | #[.table _ _ _ rows _] => (rows[0]?.bind (·[0]?)).map Ir.plainText == some "Heading"
      | _ => false)
  -- What the span line says, held at each shape of span: its text fills
  -- one cell, and any cell written after it moves left by the columns it
  -- spanned beyond the first — none at a row's end, where nothing moves.
  for (what, row, want) in [
      ("a leading span", "\\multicolumn{2}{c}{Span} & d", #["Span", "d", ""]),
      ("a trailing span", "a & \\multicolumn{2}{c}{Span}", #["a", "Span", ""]),
      ("a full-row span", "\\multicolumn{3}{c}{Span}", #["Span", "", ""])] do
    let (spanDoc, _) := elabStr (dvDoc "" s!"\\begin\{tabular}\{lll}\n{row} \\\\\n\\end\{tabular}")
    t s!"fragment arm, {what}: the text fills one cell, and only a later cell moves"
      (match spanDoc.body with
       | #[.table _ _ _ rows _] => rows.map (·.map Ir.plainText) == #[want]
       | _ => false)

/-! # One span, one visible line

A span of n leaves its row n−1 cells short, because the IR has no cell
span, so one `\multicolumn` prints two W0337 lines: its own, at the
command, and the table's padded-row line, at the table — two spans, which
`siteCollisions` cannot pair, and two warnings under `--werror` for one
construct. The rows below are the shapes that do so today, each with the
change that owes the merge, read in both directions: a row whose probe
prints one line is stale, and a probe printing two with no row fails. -/

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

/-- The probes that print two lines for one span today, with what owes the
merge. -/
def spanAccounting : List (String × String) :=
  let owner := "LeanTex/Core/Ir.lean and Elab's tabularArm: a cell that spans its \
columns leaves no short row, so the padded-row line has nothing left to name"
  [("a leading span", owner), ("a trailing span", owner), ("a full-row span", owner),
   ("a span through a definition", owner)]

def spanAccountingChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let visible (ds : Array Diag) (key : String) : Bool :=
    ds.any fun d => d.code == "W0337" && d.severity == .warning && d.subject == some key
  for (what, pre, body) in spanAccountingProbes do
    let (_, ds) := elabStr (dvDoc pre body)
    let doubled := visible ds "ctrl:multicolumn" && visible ds "tabular:ragged"
    if spanAccounting.any (·.1 == what) then
      t s!"span accounting {what} (fails on base): the row still describes two lines for one span"
        doubled
    else
      t s!"span accounting {what}: one span, one visible line" (!doubled)
  for (what, _) in spanAccounting do
    t s!"span accounting {what}: the row names a probe"
      (spanAccountingProbes.any (·.1 == what))

/-! # Compat's markers in the preamble

Three arms translate into an unforgeable marker the elaborator reads:
`@series:` (`\fontseries`), `@lang:` (`\selectlanguage`) and `@ink:`
(`\color`). `@` never lexes into a control word, so no document can write
one. The preamble reader knew none of them, so each reached it as an unknown
command and the warning quoted the marker — `unknown command '\@series:b'`,
a name no document wrote, for a construct the engine knows.

What each means there was measured against lualatex (TeX Live 2026):
`\begin{document}` selects the normal font and babel's main language, and
keeps the colour. So a series or a language written in the preamble proper
— its top level — reaches no text, and the document is the one without it —
an `\enquote` in the body included, whose quotes are the main language's
under csquotes' default — while `\color` is in force where the body begins,
the reading a `\begin{document}` hook body already gets here. Inside a
preamble group the same construct is set with the group: lualatex sets a
series in an `\author`, a `\title` or a running-head field, and a language
in a `\title`. Read as documents compared whole, never as words, and where
the claim is what a page shows, off the laid-out page and the emitted HTML
tree. -/

mutual

/-- Every element of an emitted tree carrying the attribute `key`, as its
subtree text and the attribute's value: which run a weight or a language
lands on is a fact of the typed tree, never of a rendered string. -/
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
  let markers := ["@series:", "@lang:", "@ink:"]
  let namesMarker (d : Diag) : Bool :=
    d.subject.any fun s => markers.any fun m => hasStr s m
  let docOf (pre : String) : Ir.Doc × Array Diag :=
    elabStr (dvDoc pre "Alpha bravo.\n\nCharlie delta.")
  for (what, decl) in [("a font series", "\\fontseries{b}\n"),
      ("a language switch", "\\selectlanguage{french}\n"),
      ("a colour", "\\color{red}\n")] do
    let (_, ds) := docOf decl
    t s!"preamble marker, {what} (fails on base): no diagnostic names Compat's own spelling"
      (!ds.any namesMarker)
    t s!"preamble marker, {what} (fails on base): the known construct is not called unknown"
      (ds.all (·.code != "W0301"))
    -- The premise the preamble reader's silence rests on: the construct's
    -- accounting is the one note Compat wrote at the same site.
    t s!"preamble marker, {what}: the construct's own note accounts for it"
      ((ds.filter (·.code == "N0100")).size == 1)
  -- What the preamble proper reads to nothing is a discard, keyed as one, and
  -- the same construct where it reaches text keeps its translation: in the
  -- body, in a `\begin{document}` hook, and inside a definition.
  let noteOf (src : String) (key : String) : Array Diag :=
    (elabStr src).2.filter fun d => d.code == "N0100" &&
      d.subject == some ("ctrl:nothing:" ++ key)
  for (what, decl, key) in [("a font series", "\\fontseries{b}", "fontseries:b"),
      ("a language switch", "\\selectlanguage{french}", "selectlanguage:french")] do
    t s!"preamble marker, {what} (fails on base): its note is a discard, keyed as one"
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
  -- `\enquote` reads its quotes through the main language, so a body that
  -- holds one is where a leaked switch shows. Both mirror cases, compared
  -- whole: lualatex sets the main language's quotes either way.
  let quoted (pre : String) : Ir.Doc :=
    (elabStr (dvDoc pre "Alpha \\enquote{bravo} charlie.")).1
  let babelOf (other main : String) : String :=
    s!"\\usepackage[{other},{main}]\{babel}\n\\usepackage\{csquotes}\n"
  for (main, other) in [("english", "french"), ("french", "english")] do
    t s!"preamble marker (fails on base): a switch to {other} reaches no quote \
when {main} is the main language"
      (quoted (babelOf other main ++ s!"\\selectlanguage\{{other}}\n") ==
        quoted (babelOf other main))
  -- The `\begin{document}` door stays: its switch reaches the body's
  -- language, and the quotes stay the main language's, as lualatex gives.
  let door := babelOf "english" "french" ++ "\\AtBeginDocument{\\selectlanguage{english}}\n"
  t "preamble marker: a switch in a \\begin{document} hook still reaches the body"
    (quoted door != quoted (babelOf "english" "french"))
  t "preamble marker: a switch in a \\begin{document} hook keeps the main language's quotes"
    (Ir.blockTextList "" (quoted door).body.toList ==
      Ir.blockTextList "" (quoted (babelOf "english" "french")).body.toList)
  -- LaTeX keeps the colour: the document is the one whose `\begin{document}`
  -- hook sets it.
  t "preamble marker (fails on base): a colour is the body's first declaration, as in LaTeX"
    ((docOf "\\color{red}\n").1 == (docOf "\\AtBeginDocument{\\color{red}}\n").1)
  -- Inside a definition the marker is the body's business, read where the
  -- command is used: the preamble reading is the preamble proper's alone.
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
  -- The preamble proper is its top level. Inside a preamble group — an
  -- argument the document sets later, or a running-head field — the
  -- construct keeps its body meaning, and the page sets the group's text
  -- under it, as lualatex does. Two copies of one face on the weight axis:
  -- the bold weight has its own index, so the face a run shipped in says
  -- whether the series reached it.
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
        | .run idx _ _ _ glyphs _ _ _ _ _ =>
          if glyphs.foldl (fun acc (_, c) => acc.push c) "" == word then some idx else none
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
  -- The switch is set inside the argument, so the body's quotes stay the
  -- main language's, as lualatex gives, in both mirror cases.
  for (main, other, title) in [("english", "french", "Le titre"),
      ("french", "english", "The title")] do
    let src (switch : String) : String :=
      dvDoc (babelOf other main ++ s!"\\title\{{switch}{title}}\n\\author\{Ada Example}\n\\date\{}\n")
        "\\maketitle\nAlpha \\enquote{bravo} charlie."
    t s!"preamble marker (fails on base): a switch to {other} in a \\title argument reaches \
no quote when {main} is the main language"
      (pageTextOf weighted (src s!"\\selectlanguage\{{other}}") == pageTextOf weighted (src ""))

/-- The compat accounting blocks. -/
def compatAccountingChecks (ref : IO.Ref (List String)) : IO Unit := do
  compatDiscardChecks ref
  compatFragmentChecks ref
  spanAccountingChecks ref
  compatMarkerChecks ref
