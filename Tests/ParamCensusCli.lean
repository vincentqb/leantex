module

public import Tests.ParamCensus
public import Lean.Data.Json.Parser
public import Lean.Data.Json

public section

open LeanTex.Core LeanTex.Cli

/-! The settings census over what the binary writes: `\output`'s keys, `\fonts`' slots, a code
page's directive and an inclusion's keys, each read where some file the build writes changes, or
named. -/

namespace Tests.ParamCensus

/-- A document as the binary reads it: its main file and the text files beside it. -/
structure Tree where
  main : String
  files : List (String × String) := []

/-- What a diagnostic says, as the census reads it. -/
structure Said where
  severity : String
  code : String
  subject : Option String
  message : String
  deriving BEq

/-- The diagnostics of a porcelain run, as the census reads them. -/
def saidOf (stdout : String) : Array Said :=
  (((stdout.splitOn "\n").filter (!·.isEmpty)).filterMap fun l =>
    (Lean.Json.parse l).toOption.bind fun j =>
      if j.getObjValAs? String "event" != .ok "diagnostic" then none
      else some { severity := (j.getObjValAs? String "severity").toOption.getD ""
                  code := (j.getObjValAs? String "code").toOption.getD ""
                  subject := (j.getObjValAs? String "subject").toOption
                  message := (j.getObjValAs? String "message").toOption.getD "" }).toArray

/-- What a build writes: each file under its output directory with its bytes, its exit status and
its diagnostics. -/
structure Built where
  files : Array (String × ByteArray)
  exit : UInt32
  said : Array Said

/-- The files under a directory, each by its path below it, in path order. -/
def filesUnder (root : System.FilePath) : IO (Array (String × ByteArray)) := do
  unless ← root.isDir do return #[]
  let mut out := #[]
  for p in ← root.walkDir do
    unless ← p.isDir do
      let rel := ((p.toString.drop (root.toString.length + 1)).toString)
      out := out.push (rel, ← IO.FS.readBinFile p)
  return out.qsort (·.1 < ·.1)

/-- A tree built by the binary in its own directory under `root`, with the census's font directory
beside it and no home, tools or font override; the host's system font directories stay scanned,
the same for every build of a row. -/
def builtIn (root : System.FilePath) (n : Nat) (tree : Tree) : IO Built := do
  let dir := root / s!"b{n}"
  IO.FS.createDirAll dir
  for (name, text) in tree.files do
    let path := dir / name
    if let some parent := path.parent then IO.FS.createDirAll parent
    IO.FS.writeFile path text
  let binary ← IO.FS.realPath ".lake/build/bin/leantex"
  let cache := dir / "cache"
  let run ← IO.Process.output {
    cmd := binary.toString, cwd := some dir
    args := #[tree.main, "-o", "out/", "--porcelain", "--font-dir", (root / "fonts").toString]
    env := #[("LEANTEX_FONT", none), ("XDG_CACHE_HOME", some cache.toString),
      ("HOME", some (cache / "home").toString), ("PATH", some (cache / "no-tools").toString),
      ("LEANTEX_FONT_PATH", none)] }
  return { files := ← filesUnder (dir / "out"), exit := run.exitCode, said := saidOf run.stdout }

/-- Whether a subject is keyed by a setting, or is the setting's own name. -/
def keyedOrIs (key subject : String) : Bool := subject == key || keyedBy key subject

/-- A setting's verdict over two builds: whether a written file changed under the same exit,
whether a warning or an error keyed by it or its inert row's note names it, and whether one names
it unread although a written file changed. -/
def builtJudge (base trial : Built) (key : String) (inert : Bool) : Bool × Bool × Bool :=
  let fresh := trial.said.filter fun d => !base.said.contains d
  let shows := trial.files.map (·.1) != base.files.map (·.1) ||
    (trial.files.zip base.files).any fun (a, b) => a.2 != b.2
  let changed := shows && trial.exit == base.exit
  let warned := fresh.filter fun d =>
    (d.severity == "warning" || d.severity == "error") && d.subject.any (keyedOrIs key)
  let noted := if inert then fresh.filter fun d =>
      d.code == "N0100" && hasStr d.message "→ nothing:" && d.subject.any (keyedOrIs key)
    else #[]
  let unread := warned.any (fun d => unreadCodes.contains d.code &&
      !d.subject.any (·.startsWith "partial:")) || (warned.isEmpty && !noted.isEmpty)
  (changed, !warned.isEmpty || !noted.isEmpty, changed && unread)

/-- One reader's vocabulary over binary builds: each setting, the trees it is tried in (`none`
without it), the name its diagnostics carry, its inert rows and the trees it is tried in. -/
structure BuiltRow where
  reader : String
  settings : List String
  docs : List (Option String → Tree)
  keyOf : String → String := fun s => (KeyVal.entry s).1
  inert : String → Bool := fun _ => false
  tries : String → Nat → Bool := fun _ _ => true

/-- Each setting of a row with its verdict in each tree, every build run at once under `root`. -/
def builtRowJudged (root : System.FilePath) (start : Nat) (row : BuiltRow) :
    IO (List (String × List (Task (Bool × Bool × Bool)))) := do
  let mut n := start
  let mut bases : Array (Nat × (Option String → Tree) × Task (Except IO.Error Built)) := #[]
  for (d, i) in row.docs.zipIdx do
    bases := bases.push (i, d, ← IO.asTask (builtIn root n (d none)) .dedicated)
    n := n + 1
  let mut out := []
  for s in row.settings do
    let mut tasks := []
    for (i, d, base) in bases do
      unless row.tries s i do continue
      let k := n
      n := n + 1
      let trial ← IO.asTask (builtIn root k (d (some s))) .dedicated
      tasks := tasks ++ [base.bind fun b => trial.map fun t =>
        match b, t with
        | .ok b, .ok t => builtJudge b t (row.keyOf s) (row.inert s)
        | _, _ => (false, false, false)]
    out := out ++ [(s, tasks)]
  return out

/-- The faces every build reads from the census's font directory beside it, `slots` its own. -/
def censusFonts (slots : String := "body = \"Source Serif Pro\", sans = \"Fira Sans\", \
mono = \"Source Code Pro\", math = \"Fira Math\"") : String :=
  s!"\\fonts\{ dir = \"../fonts\", {slots} }"

/-- A plain article holding a section, a footnote, a link, mathematics, sans and typewriter text and
a listing, the census's faces and `pre` in its preamble. -/
def cliArticle (pre : String) (body : String := "") (fonts : String := censusFonts)
    (cls : String := "article") : String :=
  s!"\\documentclass\{{cls}}\n{fonts}\n{pre}\n\\begin\{document}\n\\section\{Opening words}\n" ++
    "Plain words with a footnote\\footnote{Note words.}, a link \\href{https://example.org}{to a " ++
    "place}, $a^2 + b^2 = c^2$, \\textsf{sans words}, \\texttt{typewriter words}, \\textbf{bold " ++
    "words} and \\textit{italic words}.\n\\begin{verbatim}\ndef probe(x):\n    return x + 1\n" ++
    s!"\\end\{verbatim}\n{body}\n\\end\{document}\n"

/-- `\output`'s keys and values: a format where the class builds another, and every other key
beside all three formats; a contract fact where the class's artifacts do not already realize it. -/
def outputRow : BuiltRow :=
  let all := "formats = pdf, html, md"
  let decl (lead : String) (o : Option String) : String :=
    match lead, o with
    | "", none => ""
    | "", some s => s!"\\output\{ {s} }"
    | l, none => s!"\\output\{ {l} }"
    | l, some s => s!"\\output\{ {l} }\n\\output\{ {s} }"
  let tree (cls lead : String) (o : Option String) : Tree :=
    { main := "doc.tex", files := [("doc.tex", cliArticle (decl lead o) (cls := cls)),
        ("probe.css", "p { letter-spacing: 0.1em; }\n")] }
  { reader := "\\output"
    settings := ["formats = pdf", "formats = html", "formats = md", "formats = html, md"] ++
      PdfContract.Profile.names.map ("profiles = " ++ ·) ++
      Ir.Scheme.all.map (fun s => s!"schemes = {s.name}") ++
      ["css = own", "css = bulma", "css = none", "stylesheet = \"probe.css\"", "md = \"llms.txt\"",
       "alternatives = required", "color = srgb", "fonts = embedded", "fonts = none",
       invented ++ " = 1"]
    tries := fun s i =>
      if s == "formats = pdf" then i == 1
      else if (KeyVal.entry s).1 == "formats" then i == 0
      else if s == "fonts = embedded" then i == 3
      else if s == "css = bulma" then i == 4
      else i == 2
    docs := [tree "article" "", tree "webpage" "", tree "article" all,
      tree "article" (all ++ ", css = own"), tree "article" (all ++ ", stylesheet = \"probe.css\"")] }

/-- A body setting text in every slot and series a `\fonts` key names, and mathematics in each
alphabet a source key names, under `fonts`. -/
def slotsArticle (fonts : String) (math : String :=
    "$\\mathrm{d}\\mathit{e}\\mathbf{f}\\mathsf{g}\\mathtt{h} + x^2$") : String :=
  s!"\\documentclass\{article}\n{fonts}\n\\begin\{document}\n" ++
    "Body words, \\textbf{bold words}, \\textit{italic words}, \\textbf{\\textit{bold italic " ++
    "words}} and {\\fontseries{sb}\\selectfont semibold words}; \\textsf{sans words}, " ++
    "\\textsf{\\textbf{bold sans}} and \\textsf{\\textit{italic sans}}; \\texttt{typewriter " ++
    s!"words}, \\texttt\{\\textbf\{bold typewriter}} and \\texttt\{\\textit\{italic typewriter}}; {math}.\n" ++
    "\\end{document}\n"

/-- `\fonts`' slots, their aliases and variants, a declared family, a directory and the math
alphabets' sources, each beside the census's directory, in a body setting text in each. -/
def fontsRow : BuiltRow :=
  let decl (lead : String) (o : Option String) : String :=
    s!"\\fonts\{ dir = \"../fonts\"{lead}{(o.map (", " ++ ·)).getD ""} }"
  let face (k v : String) : String := s!"{k} = \"{v}\""
  -- Every slot stands declared, so no host face is the engine's pick.
  let slots := ", body = \"Open Sans\", sans = \"Open Sans\", mono = \"Open Sans\", math = \"Fira Math\""
  let variants := ["body.bold", "body.italic", "body.bolditalic", "body.upright", "body.sb",
    "body.b.italic"].map (face · "Source Serif Pro Bold") ++
    ["sans.bold", "sans.italic", "mono.bold", "mono.italic"].map (face · "Source Serif Pro Italic")
  { reader := "\\fonts"
    settings := ["body", "rm"].map (face · "Source Serif Pro") ++ ["sans", "sf"].map (face · "Fira Sans") ++
      ["mono", "tt"].map (face · "Source Code Pro") ++ [face "math" "Fira Sans"] ++ variants ++
      [face "family.probe" "Fira Sans", face "dir" "elsewhere"] ++
      ["mathrm", "mathit", "mathbf", "mathsf", "mathtt"].map (· ++ " = sym") ++ [face invented "x"]
    -- The second document's mathematics stands in the one math face the census ships, the engine's
    -- own pick; the third's sans and typewriter slots read the body's family.
    tries := fun s i =>
      let k := (KeyVal.entry s).1
      if k == "math" then i == 1
      else if k.startsWith "sans." || k.startsWith "mono." then i == 2
      else i == 0
    docs := [fun o => { main := "doc.tex", files := [("doc.tex", slotsArticle (decl slots o))] },
      fun o => { main := "doc.tex", files := [("doc.tex", slotsArticle
        (decl ", body = \"Open Sans\", sans = \"Open Sans\", mono = \"Open Sans\"" o) "$1 + 2 = 3$")] },
      fun o => { main := "doc.tex", files := [("doc.tex", slotsArticle
        (decl ", body = \"Open Sans\", math = \"Fira Math\"" o))] }] }

/-- A Lean page as a project holds it: the census's file of statements, `first` its first line, its
facts beneath the project's build directory and a bibliography beside it. -/
def leanProject (src facts first : String) (exported : Bool := true) : List (String × String) :=
  let lines := src.splitOn "\n"
  [("proj/lakefile.toml", "name = \"proj\"\n"),
   ("proj/statements.lean", "\n".intercalate (first :: lines.drop 1)),
   ("proj/alt.facts", facts), ("alt.facts", facts), ("proj/refs.bib", refsBib)] ++
    if exported then [("proj/.lake/build/leantex/statements.facts", facts)] else []

/-- The keys a Lean page's directive and an inclusion read for what the page shows, each with a
value it takes. -/
def showSettings : List String :=
  ["show = math", "show = math, code", "show = code, math", "show = prose", "show = docs",
   "decls = height_double", "proofs = collapse", "proofs = remove", "link = https://example.org/{name}",
   "facts = alt.facts", "bibliography = refs.bib", "biblio-style = plain",
   "phrase.Tide.height = {the height after #2 steps of #1}", invented ++ " = 1"]

/-- Whether a show setting is tried beside a base: a view where the page shows code alone, a chosen
declaration, proof form or link where it shows statements, a phrase where it says them in words, a
facts path where it shows statements no export answers. -/
def showTries (s : String) (i : Nat) : Bool :=
  let k := (KeyVal.entry s).1
  if k.startsWith "phrase." then i == 2
  else if k == "facts" then i == 3
  else if ["decls", "proofs", "link"].contains k then i == 1
  else i == 0

/-- A Lean page's directive: `\output`'s keys, a theme and what the page shows, on a page showing
its code, its statements or their words. -/
def directiveRow (src facts : String) : BuiltRow :=
  let line (base : String) (o : Option String) : String :=
    match base, o with
    | "", none => "-- leantex:"
    | "", some s => s!"-- leantex: {s}"
    | b, none => s!"-- leantex: {b}"
    | b, some s => s!"-- leantex: {b}, {s}"
  let tree (base : String) (exported : Bool) (o : Option String) : Tree :=
    { main := "proj/statements.lean", files := leanProject src facts (line base o) exported }
  let cites (listed : Bool) (o : Option String) : Tree :=
    { main := "notes/cites.lean"
      files := [("notes/lakefile.toml", "name = \"notes\"\n"),
        ("notes/cites.lean", s!"{line "" o}\n/-! # Cited notes\n\nWords resting on [key1] and " ++
          "more words. -/\n\ntheorem probe_true : True := trivial\n"),
        (if listed then "notes/docs/references.bib" else "notes/refs.bib", refsBib)] }
  let outputKeys := ["schemes = dark", "css = none", "md = \"llms.txt\""]
  { reader := "-- leantex:"
    settings := ["formats = pdf, html", "theme = gemini"] ++ outputKeys ++ showSettings
    tries := fun s i =>
      if outputKeys.contains s then i == 4
      else if (KeyVal.entry s).1 == "biblio-style" then i == 5
      else if (KeyVal.entry s).1 == "bibliography" then i == 6
      else showTries s i
    docs := [tree "" true, tree "show = math, code" true, tree "show = prose" true,
      tree "show = math, code" false, tree "formats = pdf, html, md" true, cites true,
      cites false] }

/-- An inclusion's options, as `\inputlean` and a markdown division spell them, on an inclusion of
code, of statements and of their words. -/
def inclusionRows (src facts : String) : List BuiltRow :=
  let files (exported : Bool) := leanProject src facts "-- a page of statements" exported
  let tex (base : String) (exported : Bool) (o : Option String) : Tree :=
    let opts := match base, o with
      | "", none => ""
      | "", some s => s!"[{s}]"
      | b, none => s!"[{b}]"
      | b, some s => s!"[{b}, {s}]"
    { main := "doc.tex", files := ("doc.tex", cliArticle s!"\\usepackage\{leantex}"
        s!"\\inputlean{opts}\{proj/statements.lean}") :: files exported }
  let attr (s : String) : String :=
    match KeyVal.entry s with
    | (k, some v) => s!"{k}=\"{Code.unwrapValue v}\""
    | (k, none) => k
  let md (base : String) (exported : Bool) (o : Option String) : Tree :=
    let attrs := (if base.isEmpty then [] else [attr base]) ++ (o.map attr).toList
    { main := "doc.md", files := ("doc.md", "# Probe page\n\nWords.\n\n::: {.lean file=\"proj/statements.lean\"" ++
        String.join (attrs.map (" " ++ ·)) ++ "}\n:::\n") :: files exported }
  [{ reader := "\\inputlean"
     settings := ["code", "math", "prose", "docs"] ++ showSettings
     tries := showTries
     docs := [tex "" true, tex "show = {math, code}" true, tex "show = prose" true,
       tex "show = {math, code}" false] },
   { reader := "::: {.lean}"
     settings := showSettings
     tries := showTries
     docs := [md "" true, md "show = {math, code}" true, md "show = prose" true,
       md "show = {math, code}" false] }]

/-- Every census row the binary builds, over the census's Lean file of statements and its facts. -/
def builtRows (src facts : String) : List BuiltRow :=
  let included := inclusionRows src facts
  [outputRow, fontsRow, directiveRow src facts] ++ included

/-- The census over binary builds: every setting of every row is read or named, and none read is
named unread. -/
def builtCensusChecks (ref : IO.Ref (List String)) : IO Unit := do
  let build ← IO.Process.output { cmd := "lake", args := #["build", "leantex", "-q"] }
  check ref s!"settings census: the binary builds\n{build.stdout}{build.stderr}" (build.exitCode == 0)
  unless build.exitCode == 0 do return
  IO.FS.withTempDir fun root => do
    let root ← IO.FS.realPath root
    IO.FS.createDirAll (root / "fonts")
    for e in ← System.FilePath.readDir "testdata/corpus/fonts" do
      IO.FS.writeBinFile (root / "fonts" / e.fileName) (← IO.FS.readBinFile e.path)
    let src ← IO.FS.readFile leanFixture
    let facts ← IO.FS.readFile leanFacts
    let mut start := 0
    -- One row's builds at a time, each row judged before the next starts.
    for row in builtRows src facts do
      let js ← builtRowJudged root start row
      start := start + 1000
      let faults := rowFaults { reader := row.reader, settings := row.settings, docs := [] } js
      check ref s!"settings census {row.reader}: every setting is read or named\
{String.join (faults.map ("\n  " ++ ·))}" faults.isEmpty

end Tests.ParamCensus
