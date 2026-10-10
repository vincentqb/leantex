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
