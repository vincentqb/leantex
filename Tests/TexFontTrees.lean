module

public import LeanTex.Cli.TexFontTrees
public import LeanTex.Cli.Host
public import Tests.Support

public section

open LeanTex.Cli LeanTex.Cli.World

namespace Tests

/-- A regular file whose real path is `real`. -/
def fileAt (real : String) : Stat := { kind := .file, size := 1, mtimeSec := 0, mtimeNsec := 0, real }

/-- A directory, its own real path. -/
def dirAt (real : String) : Stat := { kind := .dir, size := 0, mtimeSec := 0, mtimeNsec := 0, real }

/-- The rule's directories on a host of `stats` alone, `PATH` set to `path`
and `/` the working directory. -/
def treeRoots (path : Option String) (home : Option String) (stats : List (String × Stat)) :
    List String :=
  let facts : List Fact := (⟨.env "PATH", path⟩ : Fact) :: (⟨.cwd, .ok "/"⟩ : Fact) ::
    stats.map fun (p, st) => (⟨.stat p, .ok st⟩ : Fact)
  (TexFontTrees.roots home).run (World.traceWorld facts World.quiet)

/-- The rule over invented layouts: the program found through its links, its
trees by the layout it sits in, OpenType directories before TrueType ones,
and only directories that exist, each once. -/
def texFontTreeLayoutChecks (ref : IO.Ref (List String)) : IO Unit := do
  let tl := [("/links/lualatex", fileAt "/tl/2099/bin/x86_64-linux/luahbtex"),
    ("/tl/2099/texmf-dist/fonts/opentype", dirAt "/tl/2099/texmf-dist/fonts/opentype"),
    ("/tl/2099/texmf-dist/fonts/truetype", dirAt "/tl/2099/texmf-dist/fonts/truetype"),
    ("/tl/texmf-local/fonts/truetype", dirAt "/tl/texmf-local/fonts/truetype"),
    ("/people/ada/texmf/fonts/opentype", dirAt "/people/ada/texmf/fonts/opentype"),
    ("/people/ada/Library/texmf/fonts/truetype", dirAt "/people/ada/Library/texmf/fonts/truetype"),
    ("/texmf/fonts/opentype", dirAt "/texmf/fonts/opentype")]
  check ref "tex fonts: TeX Live's layout, the user's, the site's and the distribution's trees"
    (treeRoots (some "/links:/usr/bin") (some "/people/ada") tl ==
      ["/people/ada/texmf/fonts/opentype", "/tl/2099/texmf-dist/fonts/opentype",
       "/people/ada/Library/texmf/fonts/truetype", "/tl/texmf-local/fonts/truetype",
       "/tl/2099/texmf-dist/fonts/truetype"])
  check ref "tex fonts: no home, or an empty one, is no user's tree"
    (treeRoots (some "/links") none tl ==
      ["/tl/2099/texmf-dist/fonts/opentype", "/tl/texmf-local/fonts/truetype",
       "/tl/2099/texmf-dist/fonts/truetype"] &&
     treeRoots (some "/links") (some "") tl == treeRoots (some "/links") none tl)
  let fedora := [("/usr/bin/lualatex", fileAt "/usr/bin/luahbtex"),
    ("/usr/share/texlive/texmf-dist/fonts/opentype", dirAt "/usr/share/texlive/texmf-dist/fonts/opentype"),
    ("/usr/share/texlive/texmf-local/fonts/truetype", dirAt "/usr/share/texlive/texmf-local/fonts/truetype")]
  check ref "tex fonts: a package's trees and site tree under share/texlive"
    (treeRoots (some "/usr/bin") none fedora ==
      ["/usr/share/texlive/texmf-dist/fonts/opentype", "/usr/share/texlive/texmf-local/fonts/truetype"])
  let debian := [("/usr/bin/lualatex", fileAt "/usr/bin/luahbtex"),
    ("/usr/share/texmf/fonts/opentype", dirAt "/usr/share/texmf/fonts/opentype"),
    ("/usr/share/texlive/texmf-dist/fonts/opentype", dirAt "/usr/share/texlive/texmf-dist/fonts/opentype"),
    ("/usr/local/share/texmf/fonts/opentype", dirAt "/usr/local/share/texmf/fonts/opentype")]
  check ref "tex fonts: Debian's share/texmf before its texmf-dist, its site tree in /usr/local"
    (treeRoots (some "/usr/bin") none debian ==
      ["/usr/local/share/texmf/fonts/opentype", "/usr/share/texmf/fonts/opentype",
       "/usr/share/texlive/texmf-dist/fonts/opentype"])
  check ref "tex fonts: a tree two layouts name is searched once"
    (treeRoots (some "/usr/bin") (some "/usr/share") debian ==
      ["/usr/share/texmf/fonts/opentype", "/usr/local/share/texmf/fonts/opentype",
       "/usr/share/texlive/texmf-dist/fonts/opentype"])
  let nix := [("/run/profile/bin/lualatex", fileAt "/store/env/bin/lualatex"),
    ("/store/env/share/texmf/fonts/opentype", dirAt "/store/dist/fonts/opentype"),
    ("/store/env/share/texmf-dist/fonts/opentype", dirAt "/store/dist/fonts/opentype")]
  check ref "tex fonts: a wrapper whose prefix links its tree in, searched once as first spelled"
    (treeRoots (some "/run/profile/bin") none nix == ["/store/env/share/texmf/fonts/opentype"])
  let ports := [("/opt/local/bin/lualatex", fileAt "/opt/local/libexec/texlive/binaries/luahbtex"),
    ("/opt/local/share/texmf-texlive/fonts/opentype", dirAt "/opt/local/share/texmf-texlive/fonts/opentype"),
    ("/opt/local/share/texmf/fonts/truetype", dirAt "/opt/local/share/texmf/fonts/truetype"),
    ("/opt/local/share/texmf-local/fonts/opentype", dirAt "/opt/local/share/texmf-local/fonts/opentype")]
  check ref "tex fonts: MacPorts' trees beside its binaries' libexec"
    (treeRoots (some "/opt/local/bin") none ports ==
      ["/opt/local/share/texmf-local/fonts/opentype", "/opt/local/share/texmf-texlive/fonts/opentype",
       "/opt/local/share/texmf/fonts/truetype"])
  let freebsd := [("/usr/local/bin/luatex", fileAt "/usr/local/bin/luatex"),
    ("/usr/local/share/texmf-dist/fonts/opentype", dirAt "/usr/local/share/texmf-dist/fonts/opentype"),
    ("/usr/local/share/texmf-local/fonts/opentype", dirAt "/usr/local/share/texmf-local/fonts/opentype")]
  check ref "tex fonts: luatex names the distribution without lualatex, its site tree under share"
    (treeRoots (some "/usr/local/bin") none freebsd ==
      ["/usr/local/share/texmf-local/fonts/opentype", "/usr/local/share/texmf-dist/fonts/opentype"])
  check ref "tex fonts: luatex outranks tex"
    (treeRoots (some "/a:/usr/local/bin") none (freebsd ++ [("/a/tex", fileAt "/other/bin/tex"),
      ("/other/share/texmf-dist/fonts/opentype", dirAt "/other/share/texmf-dist/fonts/opentype")]) ==
      ["/usr/local/share/texmf-local/fonts/opentype", "/usr/local/share/texmf-dist/fonts/opentype"])
  let brew := [("/brew/bin/lualatex", fileAt "/brew/Cellar/texlive/1/bin/luahbtex"),
    ("/brew/Cellar/texlive/1/share/texmf-dist/fonts/truetype",
      dirAt "/brew/Cellar/texlive/1/share/texmf-dist/fonts/truetype"),
    ("/brew/Cellar/texmf-local/fonts/opentype", dirAt "/brew/Cellar/texmf-local/fonts/opentype")]
  check ref "tex fonts: a linked prefix's trees under share, its site's beside it"
    (treeRoots (some "/brew/bin") none brew ==
      ["/brew/Cellar/texmf-local/fonts/opentype", "/brew/Cellar/texlive/1/share/texmf-dist/fonts/truetype"])
  let two := [("/a/tex", fileAt "/other/bin/tex"),
    ("/other/share/texmf-dist/fonts/opentype", dirAt "/other/share/texmf-dist/fonts/opentype")] ++ fedora
  check ref "tex fonts: the first lualatex on PATH names the distribution"
    (treeRoots (some "/usr/bin:/brew/bin") none (fedora ++ brew) ==
      ["/usr/share/texlive/texmf-dist/fonts/opentype", "/usr/share/texlive/texmf-local/fonts/truetype"] &&
     treeRoots (some "/brew/bin:/usr/bin") none (fedora ++ brew) ==
      ["/brew/Cellar/texmf-local/fonts/opentype", "/brew/Cellar/texlive/1/share/texmf-dist/fonts/truetype"])
  check ref "tex fonts: lualatex outranks an earlier tex"
    (treeRoots (some "/a:/usr/bin") none two ==
      ["/usr/share/texlive/texmf-dist/fonts/opentype", "/usr/share/texlive/texmf-local/fonts/truetype"])
  check ref "tex fonts: tex names the distribution when nothing else does"
    (treeRoots (some "/a") none two == ["/other/share/texmf-dist/fonts/opentype"])
  let odd := [("/a/lualatex", dirAt "/a/lualatex"), ("/b/lualatex", fileAt "/b/lualatex"),
    ("/share/texmf-dist/fonts/opentype", fileAt "/share/texmf-dist/fonts/opentype"),
    ("/share/texmf-dist/fonts/truetype", dirAt "/share/texmf-dist/fonts/truetype")]
  check ref "tex fonts: a directory on PATH named lualatex is passed over, a file is no tree"
    (treeRoots (some "/a:/b") none odd == ["/share/texmf-dist/fonts/truetype"])
  check ref "tex fonts: no TeX program on PATH, or no PATH, is no tree"
    (treeRoots (some "/nowhere") (some "/people/ada") tl == [] &&
      treeRoots none (some "/people/ada") tl == [])
  check ref "tex fonts: a program at the root names its trees with single slashes"
    (TexFontTrees.trees "/lualatex" none ==
      ["/texmf-local", "/share/texlive/texmf-local", "/share/texmf-local", "/local/share/texmf",
       "/share/texmf-local", "/share/texmf", "/share/texmf", "/texmf-dist", "/share/texmf-dist",
       "/share/texlive/texmf-dist", "/share/texmf-texlive"])
  check ref "tex fonts: a parent of a path"
    (TexFontTrees.parent "/a/b" == "/a" && TexFontTrees.parent "/a" == "/" &&
      TexFontTrees.parent "/" == "/")

/-- The rule on a layout laid out on disk, links and all: the font scan
finds the faces of its trees. -/
def texFontTreeDiskChecks (ref : IO.Ref (List String)) : IO Unit := do
  let corpus ← IO.FS.realPath testFonts
  IO.FS.withTempDir fun tmp => do
    let root := (← IO.FS.realPath tmp).toString
    let bin := root ++ "/tl/2099/bin/x86_64-linux"
    IO.FS.createDirAll bin
    IO.FS.createDirAll (root ++ "/links")
    IO.FS.writeFile (bin ++ "/luahbtex") "never run\n"
    symlink "luahbtex" (bin ++ "/lualatex")
    symlink "../tl/2099/bin/x86_64-linux/lualatex" (root ++ "/links/lualatex")
    let dist := root ++ "/tl/2099/texmf-dist/fonts/truetype/invented"
    let user := root ++ "/people/ada/texmf/fonts/opentype/invented"
    IO.FS.createDirAll dist
    IO.FS.createDirAll user
    IO.FS.writeBinFile (dist ++ "/OpenSans-Regular.ttf") (← IO.FS.readBinFile (corpus / "OpenSans-Regular.ttf"))
    IO.FS.writeBinFile (user ++ "/FiraSans-Regular.otf") (← IO.FS.readBinFile (corpus / "FiraSans-Regular.otf"))
    let roots ← World.under (root ++ "/links:" ++ root ++ "/nowhere") (.ok root)
      (TexFontTrees.roots (some (root ++ "/people/ada")))
    check ref s!"tex fonts on disk: the trees beside the linked program: {roots}"
      (roots == [root ++ "/people/ada/texmf/fonts/opentype", root ++ "/tl/2099/texmf-dist/fonts/truetype"])
    let families := LeanTex.Core.FontDb.families (← FontDiscovery.scanRootsIn none roots)
    check ref s!"tex fonts on disk: the scan finds both trees' faces: {families}"
      (families.contains "Fira Sans" && families.contains "Open Sans")

/-- A build and a font listing by `binary` under a `PATH` holding only a
`lualatex`, a `kpsewhich` and an `sh` that each leave a mark when run, in
TeX Live's layout with the invented Example Icons in its tree, which the
document declares as its mono family, the child's environment the
scenario's alone: the build's and the listing's outputs, and the marks
left. -/
def texFontTreeMarks (binary : String) : IO (IO.Process.Output × IO.Process.Output × List String) := do
  let corpus ← IO.FS.realPath testFonts
  IO.FS.withTempDir fun tmp => do
    let root := (← IO.FS.realPath tmp).toString
    let marks := root ++ "/marks"
    IO.FS.createDirAll marks
    let bin := root ++ "/tl/2099/bin/x86_64-linux"
    for name in ["lualatex", "kpsewhich", "sh"] do
      writeScript (bin ++ "/" ++ name) s!"#!/bin/sh\necho ran > {marks}/{name}\nexit 1\n"
    let tree := root ++ "/tl/2099/texmf-dist/fonts/truetype/invented"
    IO.FS.createDirAll tree
    IO.FS.writeBinFile (tree ++ "/ExampleIcons-Regular.ttf")
      (← IO.FS.readBinFile (corpus / "ExampleIcons-Regular.ttf"))
    let doc := root ++ "/doc"
    IO.FS.createDirAll (doc ++ "/fonts")
    IO.FS.writeBinFile (doc ++ "/fonts/OpenSans-Regular.ttf")
      (← IO.FS.readBinFile (corpus / "OpenSans-Regular.ttf"))
    IO.FS.writeFile (doc ++ "/page.tex") (String.intercalate "\n" [
      "\\documentclass{article}", "\\fonts{dir=\"fonts\", body=\"Open Sans\", mono=\"Example Icons\"}",
      "\\begin{document}", "Plain", "\\end{document}"])
    let env : Array (String × Option String) := #[("PATH", some bin),
      ("HOME", some (root ++ "/people/ada")), ("XDG_CACHE_HOME", some (root ++ "/cache"))]
    let run (args : Array String) : IO IO.Process.Output :=
      IO.Process.output { cmd := binary, args, cwd := some doc, inheritEnv := false, env }
    let built ← run #[doc ++ "/page.tex", "-o", doc ++ "/page.pdf"]
    let listed ← run #["fonts"]
    let left ← System.FilePath.readDir marks
    return (built, listed, (left.map (·.fileName)).toList.mergeSort (· ≤ ·))

/-- No process starts for the TeX font directories, and the driver searches
them (`texFontTreeMarks`): the build resolves, and the font listing names,
the family only the TeX tree holds. The driver before the rule ran `sh`
there on every build, failed the build with E0403 and listed no family of
that tree. -/
def texFontTreeNoProcessChecks (ref : IO.Ref (List String)) : IO Unit := do
  let make ← IO.Process.output { cmd := "lake", args := #["build", "leantex", "-q"] }
  check ref s!"tex fonts no process: the CLI builds: {make.stdout}{make.stderr}" (make.exitCode == 0)
  if make.exitCode != 0 then return
  let (built, listed, left) ← texFontTreeMarks (← IO.FS.realPath ".lake/build/bin/leantex").toString
  check ref s!"tex fonts no process: the build resolves the TeX tree's family: {built.stdout}{built.stderr}"
    (built.exitCode == 0)
  check ref s!"tex fonts no process: the listing names the TeX tree's family: {listed.stdout}"
    (listed.exitCode == 0 && (listed.stdout.splitOn "\n").contains "Example Icons")
  check ref s!"tex fonts no process: nothing ran lualatex, kpsewhich or sh: {left}" left.isEmpty

def texFontTreeChecks (ref : IO.Ref (List String)) : IO Unit := do
  texFontTreeLayoutChecks ref
  texFontTreeDiskChecks ref
  texFontTreeNoProcessChecks ref

end Tests
