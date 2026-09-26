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

/-- The discard arms, one usage each, with the key each owes: preamble,
body, key. -/
def discardSites : List (String × String × String) :=
  [("\\usepackage{hyperref}\n", "", "usepackage:hyperref"),
   ("\\RequirePackage{url}\n", "", "RequirePackage:url"),
   ("\\usepackage{crop}\n", "", "usepackage:crop"),
   ("\\usepackage[left]{lineno}\n", "", "usepackage:lineno"),
   ("\\newcommand{\\zzkept}{a}\n\\providecommand{\\zzkept}{b}\n", "",
     "providecommand:zzkept"),
   ("\\pagestyle{fancy}\n", "", "pagestyle:fancy"),
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

/-- The compat accounting blocks. -/
def compatAccountingChecks (ref : IO.Ref (List String)) : IO Unit := do
  compatDiscardChecks ref
