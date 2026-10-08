module

public import Tests.Support

public section

open LeanTex.Core LeanTex.Cli

namespace Tests

/-- A file effect has the origin of the declaration that requested it:
filename, line, column and macro ancestry travel together. Input wrappers
switch only the filename of their contents and restore the caller for the
following siblings. An unreadable top-level file has no declaration site;
malformed included bytes have their own measured site instead. -/
def inputOriginsChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let parse (file text : String) := (Parse.parse file (Lex.lex file text).1).1
  let sameOrigin (d : Diag) (expected : Span) := d.span.any fun actual =>
    actual == expected && actual.pos.origins == expected.pos.origins
  let oneAt (ds : Array Diag) (kind : DiagCode) (expected : Span) :=
    let found := ds.filter (·.kind == kind)
    found.size == 1 && found.all (sameOrigin · expected)
  IO.FS.withTempDir fun dir => do
    let file := (dir / "host.tex").toString
    let caller := (dir / "caller.tex").toString
    let unreadable := (dir / "directory.tex").toString
    IO.FS.createDir unreadable
    for path in [unreadable, (dir / "absent.tex").toString] do
      let result ← Input.readSource path
      t "input origins: top-level filesystem failure has no invented source span"
        (match result with
        | .error d => d.kind == .E0001 && d.span.isNone
        | .ok _ => false)
    let p : Pos :=
      { line := 17, col := 9, origins := [⟨23, "readfragment"⟩, ⟨11, "outer"⟩] }
    let (_, directDs) ← Input.readInput dir file "directory.tex" p
    t "input origins: direct unreadable include preserves the complete request position"
      (oneAt directDs .E0001 ⟨file, p⟩)
    let .error sourceError ← Input.readSource unreadable |
      failures ref "input origins: unreadable directory unexpectedly read as a source"
    t "input origins: attaching the include site preserves the filesystem diagnostic"
      (directDs.size == 1 && directDs.all fun d => { d with span := none } == sourceError)
    IO.FS.writeBinFile (dir / "invalid.tex") ("first\nxy".toUTF8 ++ bytes [0xFF])
    for command in ["input", "include", "markdownInput"] do
      for nested in [false, true] do
        for (name, kind) in [("directory.tex", DiagCode.E0001),
            ("absent.tex", DiagCode.E0502), ("invalid.tex", DiagCode.E0002)] do
          let text := "% requesting source\n\n\n    \\" ++ command ++ "{" ++ name ++ "}\n"
          IO.FS.writeFile caller text
          let root := if nested then "% host\n \\input{caller}\n" else text
          let (_, ds, _) ← Input.expandInputs file (parse file root)
          let expected : Span := if kind == .E0002 then
              ⟨(dir / name).toString, { line := 2, col := 3 }⟩
            else ⟨if nested then caller else file, { line := 4, col := 5 }⟩
          t s!"input origins: {command}/{nested}/{name} names the measured source site"
            (oneAt ds kind expected)
      -- Eight successful reads reach the ninth request, whose source is
      -- the last included file, not the root or the requested destination.
      for n in [0:8] do
        let next := if n == 7 then "\\" ++ command ++ "{absent.tex}"
          else s!"\\input\{level{n + 1}.tex}"
        IO.FS.writeFile (dir / s!"level{n}.tex") ("% level\n\n\n\n      " ++ next)
      let (_, depthDs, _) ← Input.expandInputs file (parse file "\n \\input{level0.tex}")
      t s!"input origins: {command} depth refusal points to the exhausted request"
        (oneAt depthDs .E0501 ⟨(dir / "level7.tex").toString, { line := 5, col := 7 }⟩)
      t s!"input origins: {command} depth refusal does not read its destination"
        (depthDs.all (·.kind != .E0502))
    let child := (dir / "child.tex").toString
    let deep := (dir / "deep.tex").toString
    let sibling := (dir / "sibling.tex").toString
    let decl (name : String) (pos : Pos) (spaced : Bool := false) : Array Parse.Raw :=
      #[.ctrl "data" pos] ++ (if spaced then #[.space] else #[]) ++
        #[.group #[.word ("file=\"" ++ name ++ "\"") pos] pos]
    let wrapperPos : Pos := { line := 40, col := 41 }
    let first : Pos := { line := 5, col := 7, origins := [⟨19, "records"⟩] }
    let childBody := decl "shared" first ++
      #[.env "center" #[.group (decl "grouped" { line := 6, col := 8 } true)
          wrapperPos] wrapperPos,
        .env (Parse.inputEnv deep)
          (decl "deep-only" { line := 9, col := 11 } ++
            decl "shared" { line := 10, col := 12 }) wrapperPos] ++
      decl "child-after" { line := 13, col := 15 }
    let raws := decl "root-before" { line := 2, col := 3 } ++
      #[.env (Parse.inputEnv child) childBody wrapperPos,
        .env (Parse.inputEnv sibling) (decl "sibling-only" { line := 17, col := 19 })
          wrapperPos] ++
      decl "root-after" { line := 21, col := 23 } ++ decl "shared" { line := 25, col := 27 } ++
      parse file "\\data{@entry{sample,title={Invented}}}"
    let (_, dataDs) ← Input.resolveData file raws
    let missing := dataDs.filter (·.kind == .E0365)
    let expected : Array (String × Span) := #[
      ("root-before", ⟨file, { line := 2, col := 3 }⟩),
      ("shared", ⟨child, first⟩),
      ("grouped", ⟨child, { line := 6, col := 8 }⟩),
      ("deep-only", ⟨deep, { line := 9, col := 11 }⟩),
      ("child-after", ⟨child, { line := 13, col := 15 }⟩),
      ("sibling-only", ⟨sibling, { line := 17, col := 19 }⟩),
      ("root-after", ⟨file, { line := 21, col := 23 }⟩)]
    t "data origins: only distinct file declarations request reads"
      (missing.size == expected.size)
    for h : i in [:expected.size] do
      let (name, origin) := expected[i]
      t s!"data origins: {name} retains its declaration origin in first-read order"
        (missing[i]?.any fun d => sameOrigin d origin &&
          d == DriverDiag.dataMissing name (dir / Data.sourceName name).toString (some origin))
    IO.FS.writeFile child "% child\n\n   \\data{file=child-records}\n\\input{deep}\n  \\data{file=after-deep}"
    IO.FS.writeFile deep "% deep\n\n\n     \\data{file=deep-records}"
    let source := "% host\n\\input{child}\n\n \\data{file=host-records}"
    let (executed, inputDs, _) ← Input.expandInputs file (parse file source)
    t "data origins: nested synthetic inputs execute successfully" inputDs.isEmpty
    let (_, executedDs) ← Input.resolveData file executed.raws
    let missing := executedDs.filter (·.kind == .E0365)
    let expected : Array Span := #[⟨child, { line := 3, col := 4 }⟩,
      ⟨deep, { line := 4, col := 6 }⟩, ⟨child, { line := 5, col := 3 }⟩,
      ⟨file, { line := 4, col := 2 }⟩]
    t "data origins: executed includes keep exactly four distinct requests"
      (missing.size == expected.size)
    for h : i in [:expected.size] do
      t s!"data origins: executed request {i} retains its file and local position"
        (missing[i]?.any (sameOrigin · expected[i]))

end Tests
