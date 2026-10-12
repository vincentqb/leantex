module

public import Tests.Support
import LeanTex.Cli.PublicationPaths

public section

namespace Tests

/-- **Every artifact reaches the directory its path names, and one that
cannot be written is a named loss.** A PDF or markdown twin whose directory
does not exist yet is written with its directory made, as the page always
was, and a destination no one can write (its directory a regular file) is
E0004 under its path, once, with the system's words: the run fails with no
uncaught exception. Both ended in an uncaught exception. -/
def publicationWriteChecks (ref : IO.Ref (List String)) : IO Unit := do
  let binary ← IO.FS.realPath ".lake/build/bin/leantex"
  let font ← IO.FS.realPath "testdata/corpus/fonts/OpenSans-Regular.ttf"
  IO.FS.withTempDir fun dir => do
    let source (output : String) :=
      "\\documentclass{article}\n" ++ output ++ "\\begin{document}\nAn invented write probe.\n\\end{document}\n"
    let run (output : String) (args : Array String) := do
      IO.FS.writeFile (dir / "source.tex") (source output)
      IO.Process.output {
        cmd := binary.toString, cwd := some dir, args := #["source.tex"] ++ args,
        env := #[("LEANTEX_FONT", some font.toString),
          ("XDG_CACHE_HOME", some (dir / "cache").toString)] }
    let pdf ← run "" #["-o", "fresh/deeper/out.pdf"]
    check ref s!"publication writes: a PDF's missing directory is made ({pdf.exitCode}): {pdf.stderr}"
      (pdf.exitCode == 0 && (← (dir / "fresh" / "deeper" / "out.pdf").pathExists))
    let md ← run "\\output{ formats = md }\n" #["-o", "fresh-md/notes.md"]
    check ref s!"publication writes: a markdown twin's missing directory is made ({md.exitCode}): {md.stderr}"
      (md.exitCode == 0 && (← (dir / "fresh-md" / "notes.md").pathExists))
    -- A directory standing where the PDF goes: the page and the twin are
    -- written, and the PDF alone is the loss.
    IO.FS.createDirAll (dir / "partial" / "source.pdf")
    let some3 ← run "\\output{ formats = html, md, pdf }\n" #["-o", "partial/", "--porcelain"]
    let lines := (some3.stdout.splitOn "\n").filter (hasStr · "\"E0004\"")
    check ref s!"publication writes: one unwritable artifact is the one loss, and the others are written ({some3.exitCode}): {some3.stdout}"
      (some3.exitCode != 0 && lines.length == 1 && lines.all (hasStr · "partial/source.pdf") &&
        (← (dir / "partial" / "source.html").pathExists) && (← (dir / "partial" / "source.md").pathExists))
    let summary := (some3.stdout.splitOn "\n").filter (hasStr · "\"event\":\"summary\"")
    check ref s!"publication writes: the failed run's summary names what it wrote ({summary})"
      (summary.length == 1 && summary.all fun l => hasStr l "\"output\":" &&
        hasStr l "partial/source.html" && hasStr l "partial/source.md" && !hasStr l "partial/source.pdf")
    -- A declared name with a directory: the alternate link reads the twin
    -- from the page's directory, where it is written.
    let linked ← run "\\output{ formats = html, md, md = \"notes/the twin#1.md\" }\n" #["-o", "linked/"]
    let pageFile := dir / "linked" / "source.html"
    let page ← if ← pageFile.pathExists then IO.FS.readFile pageFile else pure ""
    check ref s!"publication writes: the alternate link names the twin from the page's directory ({linked.exitCode}): {linked.stderr}"
      (linked.exitCode == 0 && (← (dir / "linked" / "notes" / "the twin#1.md").pathExists) &&
        hasStr page "type=\"text/markdown\" href=\"notes/the%20twin%231.md\"")
    let href := LeanTex.Cli.PublicationPaths.nameHref
    let placed := LeanTex.Cli.PublicationPaths.placed
    check ref "publication writes: a twin's link reads its name lexically, encodes what a URL reads otherwise, and names no directory"
      (href "./notes//a b#c?d%e:f\\g.md" == some "notes/a%20b%23c%3Fd%25e%3Af%5Cg.md" &&
        href "../up/é (1).md" == some "../up/é%20(1).md" && href "link/../t2.md" == some "t2.md" &&
        href "/rooted/x.md" == none && ["", ".", "..", "sub/", "x.md/", "a/..", "x/."].all (href · == none))
    check ref "publication writes: a twin lands where its link points"
      (placed "out" "link/../t2.md" == "out/t2.md" && placed "out" "../up.md" == "up.md" &&
        placed "." "../x.md" == "../x.md" && placed "/w/out" "notes/x.md" == "/w/out/notes/x.md" &&
        placed "out" "/abs/x.md" == "/abs/x.md" && placed "out" "sub/" == "out/sub/")
    -- A twin declared by an absolute name is written there, and the page,
    -- which has no address for it that -o would not change, links none.
    let elsewhere := dir / "elsewhere" / "twin.md"
    let rooted ← run s!"\\output\{ formats = html, md, md = \"{elsewhere}\" }\n" #["-o", "rooted/"]
    let rootedPage := dir / "rooted" / "source.html"
    let rootedText ← if ← rootedPage.pathExists then IO.FS.readFile rootedPage else pure ""
    check ref s!"publication writes: a twin declared by an absolute name is written there and not linked ({rooted.exitCode}): {rooted.stderr}"
      (rooted.exitCode == 0 && (← elsewhere.pathExists) && !rootedText.isEmpty &&
        !hasStr rootedText "text/markdown")
    -- A declared name that walks back through a link: the twin lands where
    -- the link points, the page's own directory, not through the link.
    IO.FS.createDirAll (dir / "real-target" / "inner")
    IO.FS.createDirAll (dir / "through")
    symlink (dir / "real-target" / "inner") (dir / "through" / "link")
    let through ← run "\\output{ formats = html, md, md = \"link/../t2.md\" }\n" #["-o", "through/"]
    let throughPage := dir / "through" / "source.html"
    let throughText ← if ← throughPage.pathExists then IO.FS.readFile throughPage else pure ""
    check ref s!"publication writes: a twin named back through a link lands where its link points ({through.exitCode}): {through.stderr}"
      (through.exitCode == 0 && (← (dir / "through" / "t2.md").pathExists) &&
        !(← (dir / "real-target" / "t2.md").pathExists) &&
        hasStr throughText "type=\"text/markdown\" href=\"t2.md\"")
    -- A declared name that names a directory: no twin can be written there,
    -- and the page links none.
    let named ← run "\\output{ formats = html, md, md = \"sub/\" }\n" #["-o", "dir-twin/", "--porcelain"]
    let namedPage := dir / "dir-twin" / "source.html"
    let namedText ← if ← namedPage.pathExists then IO.FS.readFile namedPage else pure ""
    check ref s!"publication writes: a twin name that names a directory is E0004 and no link ({named.exitCode}): {named.stdout}"
      (named.exitCode != 0 && hasStr named.stdout "\"E0004\"" && !namedText.isEmpty &&
        !hasStr namedText "text/markdown")
    IO.FS.writeFile (dir / "blocker") "a regular file where a directory would go"
    let blocked ← run "" #["-o", "blocker/out.pdf", "--porcelain"]
    let said := blocked.stdout ++ blocked.stderr
    check ref s!"publication writes: an unwritable destination is E0004 under its path, not an uncaught exception ({blocked.exitCode}): {said}"
      (blocked.exitCode != 0 && hasStr said "E0004" && hasStr said "blocker/out.pdf" &&
        !hasStr said "uncaught exception")

/-- A host whose files are a table: each name's metadata and real path,
and nothing else — any other question is refused. -/
def tableWorld (files : List (String × LeanTex.Cli.World.Metadata × String)) :
    (q : LeanTex.Cli.World.Ask) → LeanTex.Cli.World.Reply q
  | .metadata p => match files.lookup p with
    | some (m, _) => .ok m
    | none => .error .absent
  | .stat p => match files.lookup p with
    | some (m, real) =>
      .ok { kind := m.kind, size := m.size, mtimeSec := m.mtimeSec, mtimeNsec := m.mtimeNsec,
            real := real }
    | none => .error .absent
  | .env _ => none
  | .cwd => .error .denied
  | .readFile _ => .error .denied
  | .listDir _ => .error .denied
  | .run _ => { ran := .unstarted "refused", out := "", err := "", complete := false, outputs := #[] }
  | .writeAtomic .. => .error .denied
  | .createDirAll _ => .error .denied

open LeanTex.Cli in
/-- **The preflight's decision, over a host given as a table.** A
destination that is an input's file by its real path is `same`; one that
resolves apart from a multiply-linked input agreeing with it on every
metadata fact is `linked`; one that resolves apart from a singly-linked
file of the same size and time is no clash. It resolves only an input
whose metadata agrees with a standing destination's, asks of an input
named twice once, and with no destination standing asks nothing of any
input: the preflight's cost is a stat per input on a rebuild, and nothing
on a first build. -/
def overwritePlanChecks (ref : IO.Ref (List String)) : IO Unit := do
  let one : World.Metadata := { kind := .file, size := 10, mtimeSec := 5, mtimeNsec := 7, links := 1 }
  let two := { one with links := 2 }
  let dest := #[("Markdown", "out.md")]
  let decide (files : List (String × World.Metadata × String)) (inputs : Array String) :=
    (PublicationPaths.overwrite dest inputs).run (tableWorld files)
  let asked (files : List (String × World.Metadata × String)) (inputs : Array String) :=
    (PublicationPaths.overwrite dest inputs).asks (tableWorld files)
  check ref "publication plan: a destination resolving to an input's path is that input"
    (decide [("out.md", one, "/w/doc.md"), ("doc.md", one, "/w/doc.md")] #["doc.md"] ==
      some (.same "Markdown" "out.md" "doc.md"))
  check ref "publication plan: a multiply-linked input agreeing with the destination may be it"
    (decide [("out.md", two, "/w/out.md"), ("doc.md", two, "/w/doc.md")] #["doc.md"] ==
      some (.linked "Markdown" "out.md" "doc.md"))
  check ref "publication plan: a singly-linked file of the same size and time is another file"
    (decide [("out.md", one, "/w/out.md"), ("doc.md", one, "/w/doc.md")] #["doc.md"] == none)
  check ref "publication plan: with no destination standing, no input is asked about"
    (asked [("doc.md", one, "/w/doc.md")] #["doc.md", "face.otf"] == [.metadata "out.md"])
  check ref "publication plan: an input whose metadata differs is never resolved"
    (asked [("out.md", one, "/w/out.md"), ("doc.md", { one with size := 11 }, "/w/doc.md")]
        #["doc.md"] == [.metadata "out.md", .stat "out.md", .metadata "doc.md"])
  check ref "publication plan: an input named twice is asked about once"
    ((asked [("out.md", one, "/w/out.md"), ("doc.md", one, "/w/doc.md")]
        #["doc.md", "doc.md"]).count (.metadata "doc.md") == 1)

/-- **No artifact is written over one of the build's inputs.** A
destination that is the document, another name of it — a link to it, a
link to the directory above it, a hard link — or a file the document reads
— an include, its bibliography, an image, its face, a face its font
directory holds — or a resource it declares — its stylesheet or icon, in a
build of any formats — is E0005 before anything is written, whatever the
run accepts: every input keeps its bytes and no artifact appears. A
destination that is none of them still publishes, beside a stylesheet no
file stands at, a bibliography no file stands for, and an unrelated hard
link. The defect: `leantex doc.md -o doc.md` replaced the source with its
markdown twin, and `\output{ md = "doc.tex" }` replaced the source it was
built from. -/
def publicationInputChecks (ref : IO.Ref (List String)) : IO Unit := do
  let font ← IO.FS.realPath "testdata/corpus/fonts/OpenSans-Regular.ttf"
  let spare ← IO.FS.realPath "testdata/corpus/fonts/SourceSerifPro-Regular.otf"
  let png ← IO.FS.realPath "testdata/corpus/rects.png"
  IO.FS.withTempDir fun root => do
    let root ← IO.FS.realPath root
    let tex (preamble body : String) : String :=
      "\\documentclass{article}\n" ++ preamble ++ "\\begin{document}\n" ++ body ++
        "\n\\end{document}\n"
    -- Every file under a case's directory, one level of real directories
    -- down; a link is kept by its name, its target compared where it stands.
    let snapshot (dir : System.FilePath) : IO (Array (String × ByteArray)) := do
      let mut out : Array (String × ByteArray) := #[]
      for e in ← dir.readDir do
        let md ← e.path.symlinkMetadata
        if md.type == .dir then
          for f in ← e.path.readDir do
            out := out.push (e.fileName ++ "/" ++ f.fileName, ← IO.FS.readBinFile f.path)
        else if md.type == .symlink then out := out.push (e.fileName, ByteArray.empty)
        else out := out.push (e.fileName, ← IO.FS.readBinFile e.path)
      return out.qsort (·.1 < ·.1)
    let prepare (name : String) (files : List (String × String))
        (links : List (String × String × Bool)) : IO System.FilePath := do
      let dir := root / (name.replace " " "-").replace "'" ""
      IO.FS.createDirAll (dir / "fonts")
      for (file, text) in files do IO.FS.writeFile (dir / file) text
      IO.FS.writeBinFile (dir / "figure.png") (← IO.FS.readBinFile png)
      IO.FS.writeBinFile (dir / "face.ttf") (← IO.FS.readBinFile font)
      IO.FS.writeBinFile (dir / "fonts" / "Spare.otf") (← IO.FS.readBinFile spare)
      for (target, link, hard) in links do
        if hard then IO.FS.hardLink (dir / target) (dir / link)
        else symlink (if target == "." then dir else dir / target) (dir / link)
      return dir
    -- A source whose markdown twin differs from it, so a write over it shows.
    let note := "# An invented note\n\nA *probe* line.\n\n* one\n* two\n"
    -- The cases: the source and the files beside it, the arguments, the
    -- files the build reads that must keep their bytes, and the links to make.
    let cases : List (String × List (String × String) × Array String × List String ×
        List (String × String × Bool)) := [
      ("a markdown source written onto itself", [("doc.md", note)],
        #["doc.md", "-o", "doc.md"], ["doc.md"], []),
      ("a twin named after its own source",
        [("doc.tex", tex "\\output{ formats = pdf, md, md = \"doc.tex\" }\n" "An invented probe.")],
        #["doc.tex"], ["doc.tex"], []),
      ("a link to the source", [("doc.md", note)],
        #["doc.md", "-o", "alias.md"], ["doc.md"], [("doc.md", "alias.md", false)]),
      ("a link to the source's directory", [("doc.md", note)],
        #["doc.md", "-o", "up/doc.md"], ["doc.md"], [(".", "up", false)]),
      ("a hard link of the source", [("doc.md", note)],
        #["doc.md", "-o", "hard.md"], ["doc.md"], [("doc.md", "hard.md", true)]),
      ("an include",
        [("doc.tex", tex "\\output{ formats = md, md = \"chapter.tex\" }\n" "\\input{chapter}"),
         ("chapter.tex", "An invented \\emph{chapter}.\n")],
        #["doc.tex"], ["doc.tex", "chapter.tex"], []),
      ("a bibliography",
        [("doc.tex", tex "\\output{ formats = md, md = \"refs.bib\" }\n"
            "An invented claim~\\cite{probe}.\n\\bibliographystyle{plain}\n\\bibliography{refs}"),
         ("refs.bib", "@misc{probe, title = {An Invented Title}, year = {2001}}\n")],
        #["doc.tex", "--best-effort"], ["refs.bib"], []),
      ("an image",
        [("doc.tex", tex "\\output{ formats = md, md = \"figure.png\" }\n"
            "\\includegraphics[alt={Invented rectangles}]{figure}")],
        #["doc.tex"], ["figure.png"], []),
      ("the face the build sets in",
        [("doc.tex", tex "\\output{ formats = md, md = \"face.ttf\" }\n" "An invented probe.")],
        #["doc.tex"], ["face.ttf"], []),
      ("a face the run's font directory holds",
        [("doc.tex", tex "\\output{ formats = md, md = \"fonts/Spare.otf\" }\n" "An invented probe.")],
        #["doc.tex", "--font-dir", "fonts"], ["fonts/Spare.otf"], []),
      ("the declared stylesheet",
        [("doc.tex", tex "\\output{ formats = html, md, stylesheet = \"site.css\", md = \"site.css\" }\n"
            "An invented probe."),
         ("site.css", "p { color: rgb(1, 2, 3) }\n")],
        #["doc.tex"], ["site.css"], []),
      ("the stylesheet a build with no page declares",
        [("doc.tex", tex "\\output{ formats = pdf, md, stylesheet = \"site.css\", md = \"site.css\" }\n"
            "An invented probe."),
         ("site.css", "p { color: rgb(1, 2, 3) }\n")],
        #["doc.tex"], ["site.css"], []),
      ("the stylesheet a twin-only build declares",
        [("doc.tex", tex "\\output{ formats = md, stylesheet = \"site.css\", md = \"site.css\" }\n"
            "An invented probe."),
         ("site.css", "p { color: rgb(1, 2, 3) }\n")],
        #["doc.tex"], ["site.css"], []),
      ("the declared icon",
        [("doc.tex", tex "\\pdfmeta{ favicon = \"figure.png\" }\n\\output{ formats = html, md, md = \"figure.png\" }\n"
            "An invented probe.")],
        #["doc.tex"], ["figure.png"], []),
      ("the icon a build with no page declares",
        [("doc.tex", tex "\\pdfmeta{ favicon = \"figure.png\" }\n\\output{ formats = pdf, md, md = \"figure.png\" }\n"
            "An invented probe.")],
        #["doc.tex"], ["figure.png"], [])]
    for (name, files, args, guarded, links) in cases do
      let dir ← prepare name files links
      let before ← snapshot dir
      let run ← engineRun dir (args ++ #["--porcelain"]) (dir / "face.ttf") (root / "cache")
      let after ← snapshot dir
      let refused := run.stdout.splitOn "\n" |>.filter (hasStr · "\"E0005\"")
      check ref s!"publication inputs: {name} is refused as E0005 ({run.exitCode}): {run.stdout}{run.stderr}"
        (run.exitCode != 0 && refused.length == 1)
      check ref s!"publication inputs: {name} leaves every file as it was"
        (guarded.all (fun g => before.any (·.1 == g)) && after == before)
    -- Destinations that are no input publish, whatever the inputs a run
    -- with no use for them names.
    let publishes : List (String × List (String × String) × Array String × String ×
        List (String × String × Bool)) := [
      ("a distinct destination beside its source", [("doc.md", note)],
        #["doc.md", "-o", "twin.md"], "twin.md", []),
      ("a stylesheet no file stands at",
        [("doc.tex", tex "\\output{ formats = pdf, stylesheet = \"doc.tex/site.css\" }\n"
            "An invented probe.")],
        #["doc.tex"], "doc.pdf", []),
      ("a bibliography no file stands for",
        [("doc.tex", tex "" "An invented claim~\\cite{probe}.\n\\bibliographystyle{plain}\n\\bibliography{doc.tex/refs}")],
        #["doc.tex", "--best-effort"], "doc.pdf", []),
      ("an unrelated hard-linked destination", [("doc.md", note), ("other.md", "An unrelated file.\n")],
        #["doc.md", "-o", "out.md"], "out.md", [("other.md", "out.md", true)])]
    for (name, files, args, output, links) in publishes do
      let dir ← prepare name files links
      let run ← engineRun dir args (dir / "face.ttf") (root / "cache")
      check ref s!"publication inputs: {name} publishes ({run.exitCode}): {run.stderr}"
        (run.exitCode == 0 && (← (dir / output).pathExists))
      if let some (_, text) := files.find? (·.1 == "doc.md") then
        check ref s!"publication inputs: {name} keeps its source"
          ((← IO.FS.readFile (dir / "doc.md")) == text)

/-- **An output name the engine cannot write is a typed refusal.** `-o`
naming a file whose extension names no format is E0006, through the
diagnostic stream — a porcelain record under `--porcelain`, the rendered
form otherwise — exit 3, nothing written, and its help lists every
extension a run can take (`Emit.all`), each of which `emitOfPath` reads
back. The defect: the refusal was a line on plain standard error, outside
the porcelain stream, and it named `*.pdf` and `*.html` but not `.md`. -/
def outputNameChecks (ref : IO.Ref (List String)) : IO Unit := do
  let font ← IO.FS.realPath "testdata/corpus/fonts/OpenSans-Regular.ttf"
  let extensions := LeanTex.Cli.Emit.all.map fun e => "." ++ e.ext
  check ref "output names: the help's output line lists every format's extension"
    (hasStr LeanTex.Cli.helpText ("output file (" ++ " | ".intercalate extensions ++ ")"))
  check ref "output names: a name with no format's extension names no format"
    (LeanTex.Cli.emitOfPath "notes.tex" == none && LeanTex.Cli.emitOfPath "notes" == none)
  IO.FS.withTempDir fun dir => do
    IO.FS.writeFile (dir / "source.tex")
      "\\documentclass{article}\n\\begin{document}\nAn invented name probe.\n\\end{document}\n"
    let run (args : Array String) :=
      engineRun dir (#["source.tex", "-o", "notes.tex"] ++ args) font (dir / "cache")
    let porcelain ← run #["--porcelain"]
    let records := (porcelain.stdout.splitOn "\n").filter (!·.isEmpty)
    let refusal := records.filter (hasStr · "\"code\":\"E0006\"")
    check ref s!"output names: an unknown extension is one E0006 record and exit 3 ({porcelain.exitCode}): {porcelain.stdout}{porcelain.stderr}"
      (porcelain.exitCode == 3 && refusal.length == 1 && porcelain.stderr.isEmpty &&
        records.all fun r => r.startsWith "{")
    check ref s!"output names: the refusal lists every extension a run can take: {refusal}"
      (!refusal.isEmpty && refusal.all fun r => LeanTex.Cli.Emit.all.all fun e => hasStr r ("'." ++ e.ext ++ "'"))
    let human ← run #[]
    check ref s!"output names: the rendered refusal reaches standard error as E0006 ({human.exitCode}): {human.stderr}"
      (human.exitCode == 3 && hasStr human.stderr "[E0006]" && hasStr human.stderr "notes.tex" &&
        human.stdout.isEmpty)
    check ref "output names: nothing is written for a refused name"
      (!(← (dir / "notes.tex").pathExists) && !(← (dir / "source.pdf").pathExists))
    for e in LeanTex.Cli.Emit.all do
      let name := "notes." ++ e.ext
      let built ← engineRun dir #["source.tex", "-o", name] font (dir / "cache")
      check ref s!"output names: a name ending in '.{e.ext}' builds ({built.exitCode}): {built.stderr}"
        (built.exitCode == 0 && (← (dir / name).pathExists))

/-- Different formats must reach independent files. The CLI must reject a
collision before any write, including existing-file and directory aliases;
accepting diagnostics cannot authorize overwriting a different artifact. -/
def publicationPathChecks (ref : IO.Ref (List String)) : IO Unit := do
  let binary ← IO.FS.realPath ".lake/build/bin/leantex"
  let font ← IO.FS.realPath "testdata/corpus/fonts/OpenSans-Regular.ttf"
  IO.FS.withTempDir fun dir => do
    let source (formats name : String) :=
      "\\documentclass{article}\n\\output{ formats = " ++ formats ++
      ", md = \"" ++ name ++ "\" }\n\\begin{document}\nAn invented publication probe.\\end{document}\n"
    let run (input output : System.FilePath) (args : Array String := #[]) :=
      IO.Process.output {
        cmd := binary.toString, cwd := some input,
        args := #["source.tex", "-o", output.toString ++ "/"] ++ args,
        env := #[("LEANTEX_FONT", some font.toString),
          ("XDG_CACHE_HOME", some (dir / "cache").toString)] }
    for (name, formats, target) in [
        ("literal", "html, md", "source.html"),
        ("dot", "html, md", "./source.html"),
        ("parent", "html, md", "../output/source.html"),
        ("three formats", "html, pdf, md", "source.html"),
        ("pdf", "pdf, md", "source.pdf")] do
      let input := dir / name
      let output := input / "output"
      IO.FS.createDirAll input
      IO.FS.writeFile (input / "source.tex") (source formats target)
      let before ← run input output
      check ref ("publication paths: refuses " ++ name ++ " before creating output")
        (before.exitCode != 0 && hasStr (before.stdout ++ before.stderr) "E0003" &&
          !(← output.pathExists))
      IO.FS.createDirAll output
      IO.FS.writeFile (output / "source.html") "existing HTML"
      IO.FS.writeFile (output / "source.pdf") "existing PDF"
      let after ← run input output #["--best-effort"]
      check ref ("publication paths: preserves existing artifacts for " ++ name)
        (after.exitCode != 0 && hasStr (after.stdout ++ after.stderr) "E0003" &&
          (← IO.FS.readBinFile (output / "source.html")) == "existing HTML".toUTF8 &&
          (← IO.FS.readBinFile (output / "source.pdf")) == "existing PDF".toUTF8)
    for (name, target) in [
        ("directory alias", "../alias/source.html"),
        ("file alias", "alias.html"),
        ("hard link", "alias.html"),
        ("dangling file alias", "alias.html")] do
      let input := dir / name
      let output := input / "output"
      IO.FS.createDirAll output
      IO.FS.writeFile (input / "source.tex") (source "html, md" target)
      let original := output / "source.html"
      if name != "dangling file alias" then IO.FS.writeFile original "existing HTML"
      if name == "hard link" then
        IO.FS.hardLink original (output / "alias.html")
      else
        let (linkSource, linkTarget) := if name == "directory alias" then (output, input / "alias")
          else (original, output / "alias.html")
        symlink linkSource linkTarget
      let result ← run input output
      let present ← original.pathExists
      let bytes ← if present then IO.FS.readBinFile original else pure ByteArray.empty
      check ref ("publication paths: refuses " ++ name ++ " without clobbering")
        (result.exitCode != 0 && hasStr (result.stdout ++ result.stderr) "E0003" &&
          (if name == "dangling file alias" then !present
            else bytes == "existing HTML".toUTF8))
    let input := dir / "distinct"
    let output := input / "output"
    IO.FS.createDirAll input
    IO.FS.writeFile (input / "source.tex") (source "html, pdf, md" "notes.md")
    let result ← run input output
    check ref "publication paths: distinct formats still publish"
      (result.exitCode == 0 && (← (output / "source.html").pathExists) &&
        (← (output / "source.pdf").pathExists) && (← (output / "notes.md").pathExists))
    if result.exitCode == 0 then
      check ref "publication paths: each destination retains its declared format"
        (hasStr (← IO.FS.readFile (output / "source.html")).toLower "<!doctype html>" &&
          (← IO.FS.readBinFile (output / "source.pdf")).data[:5].toArray == "%PDF-".toUTF8.data &&
          hasStr (← IO.FS.readFile (output / "notes.md")) "An invented publication probe.")

end Tests
