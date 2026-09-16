import LeanTex

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

instance [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

def failures : IO.Ref (List String) → String → IO Unit :=
  fun ref name => ref.modify (name :: ·)

def check (ref : IO.Ref (List String)) (name : String) (ok : Bool) : IO Unit := do
  unless ok do failures ref name

def bytes (l : List UInt8) : ByteArray := ⟨l.toArray⟩

def errKindAt (bs : ByteArray) : Option (Nat × ErrKind) :=
  (validate bs).map fun e => (e.offset, e.kind)

def toks (s : String) : List Lex.Tok :=
  ((Lex.lex "t" s).1.map (·.tok)).toList

def elabStr (s : String) : Ir.Doc × Array Diag :=
  Elab.run "t" s

def errCodes (s : String) : List String :=
  ((elabStr s).2.filter (·.severity == .error)).toList.map (·.code)

def goldenNames : List String :=
  ["paragraphs", "layout", "declared", "fonts", "palette", "tokens", "fill",
   "links", "resume", "talk"]

-- KP test helpers: word/glue/forced-break item builders and a brute-force
-- optimum to cross-check the DP against.

inductive Piece where
  | W (w : Int)
  | G
  | H (w : Int)
  | B

open Piece in
def mkItems (ps : List Piece) : Array Layout.Item := Id.run do
  let mut items : Array Layout.Item := #[]
  for p in ps do
    match p with
    | .W w => items := items.push (.box (Dim.pt w) 0 Ir.Color.black none #[] (Dim.pt 10))
    | .G => items := items.push (.glue { width := Dim.pt 10, stretch := Dim.pt 5, shrink := Dim.pt 3 })
    | .H w => items := items.push (.pen (Dim.pt w) Layout.hyphenPenalty true 0 Ir.Color.black #[])
    | .B =>
      items := items.push (.glue { fil := true })
      items := items.push (.pen 0 Layout.forcedCost false 0 Ir.Color.black #[])
  items := items.push (.glue { fil := true })
  items := items.push (.pen 0 Layout.forcedCost false 0 Ir.Color.black #[])
  return items

def W (w : Int) : Piece := .W w
def G : Piece := .G
def H (w : Int := 3) : Piece := .H w
def BRK : List Piece := [.B]

/-- Total demerits of a specific break sequence (must end at the final
forced penalty), or none when it spans a forced break. -/
def seqCost (items : Array Layout.Item) (target : Dim.Sp) (breaks : List Nat) :
    Option Int := Id.run do
  let mut prev : Nat := 0
  let mut first := true
  let mut prevFlagged := false
  let mut total : Int := 0
  for b in breaks do
    let a := if first then Layout.lineStart items 0 else Layout.lineStart items (prev + 1)
    for k in [a:b] do
      if Layout.isForced items k then
        return none
    let m := Layout.measure items a b
    total := total + Layout.lineDemerits items m target b
    if prevFlagged && Layout.isFlagged items b then
      total := total + Layout.doubleHyphenDemerits
    prev := b
    prevFlagged := Layout.isFlagged items b
    first := false
  if breaks.getLast? != some (items.size - 1) then
    return none
  return some total

/-- Minimum cost over every legal break sequence (exponential; tiny inputs). -/
def bruteBest (items : Array Layout.Item) (target : Dim.Sp) : Option Int := Id.run do
  let n := items.size
  let legal := (List.range n).filter (Layout.canBreakAt items)
  let mut best : Option Int := none
  -- enumerate subsets of legal breakpoints that end at the final penalty
  let optional' := legal.filter (· != n - 1)
  let m := optional'.length
  for mask in [0:2 ^ m] do
    let mut chosen : List Nat := []
    for (b, idx) in optional'.zipIdx do
      if mask / 2 ^ idx % 2 == 1 then
        chosen := chosen ++ [b]
    match seqCost items target (chosen ++ [n - 1]) with
    | some c =>
      match best with
      | some b0 => if c < b0 then best := some c
      | none => best := some c
    | none => pure ()
  return best

def findFont : IO (Option ByteArray) := do
  for p in ["/usr/share/fonts/dejavu/DejaVuSans.ttf",
            "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf"] do
    if ← System.FilePath.pathExists p then
      return some (← IO.FS.readBinFile p)
  return none

/-- Does a produced file contain this ASCII run? PDF content streams are the
only witness that a face or a size reached the output, and the file as a whole
is not valid UTF-8, so the search is over bytes. -/
def bytesContain (hay : ByteArray) (needle : String) : Bool := Id.run do
  let n := needle.toUTF8
  if n.size == 0 || hay.size < n.size then return false
  for i in [0:hay.size - n.size + 1] do
    let mut ok := true
    for j in [0:n.size] do
      if hay[i + j]! != n[j]! then
        ok := false
        break
    if ok then return true
  return false

/-- Re-verify a produced PDF's cross-reference stream: every type-1 entry
must point at `N 0 obj`. Returns the number of verified offsets. -/
def checkXref (pdf : ByteArray) : Except String Nat := do
  let ascii (a b : Nat) : String :=
    String.ofList (((pdf.extract a (min b pdf.size)).toList).map fun v =>
      Char.ofNat (min v.toNat 127))
  let findLast (pat : String) : Option Nat := Id.run do
    let p := pat.toUTF8
    if pdf.size < p.size then
      return none
    for back in [0:pdf.size - p.size + 1] do
      let i := pdf.size - p.size - back
      let mut ok := true
      for k in [0:p.size] do
        if pdf[i + k]! != p[k]! then
          ok := false
          break
      if ok then
        return some i
    return none
  let find (start : Nat) (pat : String) : Option Nat := Id.run do
    let p := pat.toUTF8
    for i in [start:pdf.size - p.size + 1] do
      let mut ok := true
      for k in [0:p.size] do
        if pdf[i + k]! != p[k]! then
          ok := false
          break
      if ok then
        return some i
    return none
  let some sx := findLast "startxref" | throw "no startxref"
  let numStr := (ascii (sx + 10) (sx + 30)).splitOn "\n" |>.head!
  let some xrefOff := numStr.toNat? | throw s!"bad startxref '{numStr}'"
  let head := ascii xrefOff (xrefOff + 300)
  unless (head.splitOn " 0 obj").length ≥ 2 do
    throw "startxref does not point at an object"
  unless (head.splitOn "/Type /XRef").length ≥ 2 do
    throw "xref object is not an XRef stream"
  let some sizePart := (head.splitOn "/Size ").getLast? | throw "no /Size"
  let some size := (sizePart.splitOn " ").head?.bind (·.toNat?) | throw "bad /Size"
  let some streamAbs := find xrefOff "stream\n" | throw "no stream data"
  let dataOff := streamAbs + "stream\n".length
  let mut verified := 0
  for id in [1:size] do
    let row := dataOff + 7 * id
    let kind := (pdf[row]!).toNat
    if kind == 1 then
      let off := ((pdf[row+1]!).toNat * 256 + (pdf[row+2]!).toNat) * 65536 +
        (pdf[row+3]!).toNat * 256 + (pdf[row+4]!).toNat
      let expect := s!"{id} 0 obj"
      let got := ascii off (off + expect.utf8ByteSize)
      unless got == expect do
        throw s!"object {id}: offset {off} holds {got.quote}, expected {expect.quote}"
      verified := verified + 1
  return verified

def firstDiff (expected actual : String) : String := Id.run do
  let e := expected.splitOn "\n"
  let a := actual.splitOn "\n"
  for i in [0:max e.length a.length] do
    let el := e[i]?.getD "<missing>"
    let al := a[i]?.getD "<missing>"
    if el != al then
      return s!"line {i + 1}:\n  expected: {el.quote}\n  actual:   {al.quote}"
  return "no difference"

def runGoldens (update : Bool) (fail : String → IO Unit) : IO Unit := do
  if update then
    IO.FS.createDirAll "tests/golden"
  for n in goldenNames do
    let src ← IO.FS.readFile s!"tests/corpus/{n}.tex"
    let (doc, diags) := Elab.run s!"{n}.tex" src
    let out := Ir.dump doc diags
    let path := s!"tests/golden/{n}.txt"
    if update then
      IO.FS.writeFile path out
      IO.println s!"updated {path}"
    else
      let golden ← try
        pure (some (← IO.FS.readFile path))
      catch _ =>
        pure none
      match golden with
      | none => fail s!"golden {n}: missing {path} (run: lake exe Tests --update)"
      | some g =>
        unless g == out do
          fail s!"golden {n}: mismatch, {firstDiff g out} (if intended, run: lake exe Tests --update)"

def main (args : List String) : IO UInt32 := do
  let update := args.contains "--update"
  let ref ← IO.mkRef ([] : List String)
  let t := check ref

  -- utf8: valid inputs
  t "utf8 empty" (validate (bytes []) == none)
  t "utf8 ascii" (validate "hello, world".toUTF8 == none)
  t "utf8 multibyte" (validate "naïve — αβγ — 🎉".toUTF8 == none)

  -- utf8: each error class, with offset
  t "utf8 bare continuation" (errKindAt (bytes [0x68, 0x80]) == some (1, .invalidStart 0x80))
  t "utf8 overlong 2-byte" (errKindAt (bytes [0xC0, 0x80]) == some (0, .overlong))
  t "utf8 overlong 3-byte" (errKindAt (bytes [0xE0, 0x9F, 0x80]) == some (0, .overlong))
  t "utf8 overlong 4-byte" (errKindAt (bytes [0xF0, 0x8F, 0x80, 0x80]) == some (0, .overlong))
  t "utf8 surrogate" (errKindAt (bytes [0xED, 0xA0, 0x80]) == some (0, .surrogate))
  t "utf8 out of range" (errKindAt (bytes [0xF4, 0x90, 0x80, 0x80]) == some (0, .outOfRange))
  t "utf8 truncated" (errKindAt (bytes [0x61, 0xC3]) == some (1, .truncated))
  t "utf8 bad continuation" (errKindAt (bytes [0xC3, 0x28]) == some (0, .invalidContinuation 0x28))

  -- utf8: error position tracks lines and columns
  let afterNewlines := bytes ("ab\ncd\n".toUTF8.toList ++ [0xFF])
  t "utf8 position" ((validate afterNewlines).map (fun e => (e.pos.line, e.pos.col)) == some (3, 1))

  -- utf8: agreement with core decoder on every vector above
  for (name, v) in [
      ("empty", bytes []), ("ascii", "hello".toUTF8), ("multi", "🎉é".toUTF8),
      ("cont", bytes [0x80]), ("overlong", bytes [0xC0, 0x80]),
      ("surrogate", bytes [0xED, 0xA0, 0x80]),
      ("range", bytes [0xF4, 0x90, 0x80, 0x80]), ("trunc", bytes [0xC3])] do
    t s!"utf8 agrees with core ({name})"
      ((validate v == none) == (String.fromUTF8? v).isSome)

  -- args
  t "args empty is help" (parse [] == .ok { cmd := .help })
  t "args build" (parse ["build", "a.tex"] == .ok { cmd := .build "a.tex" })
  t "args verbosity accumulates" (parse ["-v", "-vv", "build", "a.tex"] ==
    .ok { cmd := .build "a.tex", verbosity := 3 })
  t "args verbosity clamps" ((parse ["-vvvvv", "build", "a.tex"]).map (·.verbosity) == .ok 3)
  t "args porcelain quiet" (parse ["--porcelain", "-q", "build", "a.tex"] ==
    .ok { cmd := .build "a.tex", quiet := true, porcelain := true })
  t "args color eq" ((parse ["--color=never", "build", "a.tex"]).map (·.color) == .ok .never)
  t "args color sep" ((parse ["--color", "always", "version"]).map (·.color) == .ok .always)
  t "args color bad" ((parse ["--color=sometimes"]).isOk == false)
  t "args q v conflict" ((parse ["-q", "-v", "build", "a.tex"]).isOk == false)
  t "args unknown flag" ((parse ["--frobnicate"]).isOk == false)
  t "args build missing file" ((parse ["build"]).isOk == false)
  t "args trailing junk" ((parse ["build", "a.tex", "b.tex"]).isOk == false)
  t "args help flag wins" ((parse ["--help", "build", "a.tex"]).map (·.cmd) == .ok .help)
  -- Flags belong after the command too: a command takes the next positional,
  -- not the next token, or every flag written where people write it is eaten
  -- as the filename.
  t "args flag after command" (parse ["build", "--color", "never", "a.tex"] ==
    .ok { cmd := .build "a.tex", color := .never })
  t "args emit list" ((parse ["build", "--emit", "pdf,html", "a.tex"]).map (·.emit) ==
    .ok #[.pdf, .html])
  t "args emit eq after command"
    ((parse ["build", "--emit=html", "a.tex"]).map (·.emit) == .ok #[.html])
  t "args emit default is pdf" ((parse ["build", "a.tex"]).map (·.emit) == .ok #[.pdf])
  t "args emit bad" ((parse ["build", "--emit", "ps", "a.tex"]).isOk == false)
  t "args css after command"
    ((parse ["build", "--css", "bulma", "a.tex"]).map (·.css) == .ok .bulma)
  t "args css bad" ((parse ["build", "--css", "tailwind", "a.tex"]).isOk == false)
  t "args math boundary"
    ((parse ["build", "--math-boundary", "katex", "a.tex"]).map (·.mathBoundary) ==
      .ok (some "katex"))

  -- render: porcelain is stable, escaped JSONL
  let d : Diag := {
    severity := .error
    code := "E0002"
    message := "bad \"quote\"\nline"
    span := some ⟨"a.tex", ⟨3, 7⟩⟩
    help := some "fix it"
  }
  t "porcelain diag" (Render.porcelainDiag d ==
    "{\"event\":\"diagnostic\",\"severity\":\"error\",\"code\":\"E0002\"," ++
    "\"message\":\"bad \\\"quote\\\"\\nline\",\"file\":\"a.tex\",\"line\":3,\"col\":7," ++
    "\"help\":\"fix it\"}")
  t "porcelain summary" (Render.porcelainSummary "a.tex" false 2 17 ==
    "{\"event\":\"summary\",\"file\":\"a.tex\",\"ok\":false,\"errors\":2,\"ms\":17}")

  -- render: human, no color
  t "human diag plain" (Render.human false d ==
    "error[E0002]: bad \"quote\"\nline\n  --> a.tex:3:7\n  help: fix it")

  -- lex
  t "lex words and space" (toks "ab cd" == [.word "ab", .space, .word "cd"])
  t "lex par" (toks "a\n\nb" == [.word "a", .par, .word "b"])
  t "lex newline is space" (toks "a\nb" == [.word "a", .space, .word "b"])
  t "lex comment joins lines" (toks "a%c\nb" == [.word "a", .word "b"])
  t "lex ctrl word swallows space" (toks "\\emph  x" == [.ctrl "emph", .word "x"])
  t "lex ctrl word keeps blank line" (toks "\\par\n\nx" == [.ctrl "par", .par, .word "x"])
  t "lex ctrl symbol" (toks "\\%x" == [.ctrl "%", .word "x"])
  t "lex specials" (toks "{a}$m$[o]" ==
    [.lbrace, .word "a", .rbrace, .math, .word "m", .math, .sym '[', .word "o", .sym ']'])
  t "lex unicode word" (toks "naïve" == [.word "naïve"])
  t "lex position" (((Lex.lex "t" "a\nbé c").1.map fun tk => (tk.pos.line, tk.pos.col)).toList ==
    [(1, 1), (1, 2), (2, 1), (2, 3), (2, 4)])

  -- parse
  let praw (s : String) : Array Parse.Raw × Array Diag :=
    let (tk, _) := Lex.lex "t" s
    Parse.parse "t" tk
  t "parse group nesting" (((praw "{a{b}}").1.map fun r =>
    match r with
    | .group body _ => s!"group/{body.size}"
    | _ => "?") == #["group/2"])
  t "parse unclosed group" (((praw "{a").2.map (·.code)) == #["E0201"])
  t "parse stray rbrace" (((praw "a}b").2.map (·.code)) == #["E0202"])
  t "parse env" (((praw "\\begin{itemize}\\item a\\end{itemize}").1.map fun r =>
    match r with
    | .env n body _ => s!"env {n}/{body.size}"
    | _ => "?") == #["env itemize/2"])
  t "parse env mismatch" (((praw "\\begin{a}x\\end{b}").2.map (·.code)) == #["E0205"])
  t "parse display math" (((praw "\\[x\\]").1.map fun r =>
    match r with
    | .math true _ _ => "display"
    | _ => "?") == #["display"])

  -- elab: clean documents
  let (doc1, d1) := elabStr "hello $x$ world"
  t "elab snippet clean" (d1.isEmpty && doc1.body ==
    #[.para #[.text "hello ", .math false "x", .text " world"]])
  let (doc2, d2) := elabStr "\\textbf{a} {\\itshape b c} d"
  t "elab styles" (d2.isEmpty && doc2.body ==
    #[.para #[.styled .bold #[.text "a"], .text " ", .styled .italic #[.text "b c"], .text " d"]])
  let (doc3, d3) := elabStr "a\n\nb"
  t "elab paragraphs split" (d3.isEmpty && doc3.body ==
    #[.para #[.text "a"], .para #[.text "b"]])
  let (doc4, d4) := elabStr "\\section*{Work}\ntext"
  t "elab section star" (d4.isEmpty && doc4.body ==
    #[.section 1 true #[.text "Work"], .para #[.text "text"]])
  let (doc5, d5) := elabStr "\\begin{itemize}\\item a\\item b\\end{itemize}"
  t "elab itemize" (d5.isEmpty && doc5.body ==
    #[.list false #[#[.para #[.text "a"]], #[.para #[.text "b"]]]])
  let (doc6, d6) := elabStr "\\documentclass[x=1]{article}\n\\begin{document}\nhi\n\\end{document}"
  t "elab documentclass" (d6.isEmpty && doc6.docClass == "article" && doc6.classOptions == "x=1")

  -- elab: define and call
  let defRole := "\\documentclass{article}\n" ++
    "\\define \\role(who: text, team?: text) {\\textbf{\\who}\\ifgiven{\\team}{ (\\team)}}\n" ++
    "\\begin{document}\n"
  let (doc7, d7) := elabStr (defRole ++ "\\role{Ada}[Compute]\n\\end{document}")
  t "elab define call optional given" (d7.isEmpty && doc7.body ==
    #[.para #[.styled .bold #[.text "Ada"], .text " (Compute)"]])
  let (doc8, d8) := elabStr (defRole ++ "\\role{Ada}\n\\end{document}")
  t "elab define call optional omitted" (d8.isEmpty && doc8.body ==
    #[.para #[.styled .bold #[.text "Ada"]]])
  t "elab define text param rejects math" (errCodes (defRole ++ "\\role{$x$}\n\\end{document}") ==
    ["E0305"])
  t "elab self reference is unknown" (errCodes
    ("\\define \\x() {\\x}\n\\begin{document}\\x\\end{document}") == ["E0301"])
  t "elab forward reference is unknown" (errCodes
    ("\\define \\a() {\\b}\n\\define \\b() {y}\n\\begin{document}\\a\\end{document}") == ["E0301"])
  t "elab later definition sees earlier" (errCodes
    ("\\define \\b() {y}\n\\define \\a() {\\b}\n\\begin{document}\\a\\end{document}") == [])

  -- elab: diagnostics
  t "elab unknown command" (errCodes "\\frobnicate" == ["E0301"])
  t "elab reserved M5" (errCodes ("\\documentclass{article}\\figure{x}" ++
    "\\begin{document}y\\end{document}") == ["E0307"])
  t "elab reserved char" (errCodes "a & b" == ["E0311"])
  t "elab redefine builtin" (errCodes "\\define \\textbf() {x}\n\\begin{document}y\\end{document}" ==
    ["E0303"])
  t "elab trailing content warns" (((elabStr
    "\\begin{document}x\\end{document} y").2.map (·.code)) == #["W0001"])

  -- goldens
  runGoldens update (failures ref)

  -- dim
  t "sp pt string" ((Dim.pt 10).toPtString == "10" && (Dim.pt 3 / 2).toPtString == "1.5")

  -- knuth–plass: DP result equals brute-force minimum over all break sequences
  let cases : List (String × Array Layout.Item × Dim.Sp) := [
    ("three words", mkItems [W 100, G, W 100, G, W 100], Dim.pt 250),
    ("four words", mkItems [W 50, G, W 60, G, W 70, G, W 80], Dim.pt 150),
    ("forced mid", mkItems ([W 100, G, W 100] ++ BRK ++ [W 100]), Dim.pt 250),
    ("overfull word", mkItems [W 300], Dim.pt 100),
    ("tight fit", mkItems [W 80, G, W 80, G, W 80, G, W 80, G, W 80], Dim.pt 170),
    ("hyphen choice", mkItems [W 60, G, W 40, H, W 50, G, W 60], Dim.pt 120),
    ("double hyphen", mkItems [W 70, H, W 70, H, W 70, H, W 70], Dim.pt 80),
    ("hyphen vs glue", mkItems [W 50, G, W 30, H, W 30, G, W 50, G, W 40], Dim.pt 100)]
  for (name, items, target) in cases do
    let kpBreaks := (Layout.kp items target).toList
    let kpCost := seqCost items target kpBreaks
    let brute := bruteBest items target
    t s!"kp optimal ({name})" (kpCost.isSome && kpCost == brute && !kpBreaks.isEmpty)

  -- Hyphenation. Expectations are real TeX \showhyphens output with the SAME
  -- pattern set the engine embeds (luatex + hyph-en-us.tex, hyphenmins 2/3);
  -- plain lualatex is a different oracle because TeX Live maps `english` to
  -- hyphen.tex, Knuth's frozen subset. \showhyphens lists every admissible
  -- break, not one chosen rendering. Full 552-word check: scripts/hyphen-diff.sh
  let pats := Hyphen.load
  let hyph (w : String) : String := Id.run do
    let breaks := Hyphen.hyphenate pats w
    let mut out := ""
    for (c, i) in w.toList.zipIdx do
      if i > 0 && breaks.contains i then
        out := out.push '-'
      out := out.push c
    return out
  t "hyphen patterns loaded" (pats.map.size > 4000)
  t "hyphen incomprehensibility" (hyph "incomprehensibility" == "in-com-pre-hen-si-bil-ity")
  t "hyphen internationalization" (hyph "internationalization" == "in-ter-na-tion-al-iza-tion")
  t "hyphen algorithm" (hyph "algorithm" == "al-go-rithm")
  t "hyphen paragraph" (hyph "paragraph" == "para-graph")
  t "hyphen typesetting" (hyph "typesetting" == "type-set-ting")
  t "hyphen hyphenation" (hyph "hyphenation" == "hy-phen-ation")
  t "hyphen long word" (hyph "floccinaucinihilipilification" ==
    "floc-cin-aucini-hilip-il-i-fi-ca-tion")
  t "hyphen exception dictionary" (hyph "associate" == "as-so-ciate")
  t "hyphen short word untouched" (hyph "cat" == "cat")
  t "hyphen capitalized" (hyph "Paragraph" == "Para-graph")
  -- These three pin the pattern set: Knuth's hyphen.tex gives def-i-ni-tion,
  -- mono-tone, and no break at all in toolchain.
  t "hyphen set is ushyphmax (definition)" (hyph "definition" == "de-f-i-n-i-tion")
  t "hyphen set is ushyphmax (monotone)" (hyph "monotone" == "mo-not-one")
  t "hyphen set is ushyphmax (toolchain)" (hyph "toolchain" == "tool-chain")
  -- leftMin=2 / rightMin=3 are enforced, so no break may strand 1 letter or 2.
  t "hyphen respects hyphenmins" ((Hyphen.hyphenate pats "typesetting").all
    fun p => p ≥ 2 && p + 3 ≤ 11)

  -- declarations: \page, \pdfmeta, \assert
  let declSrc := "\\documentclass{article}\n" ++
    "\\page{ size = a5, margin = 0.5in }\n" ++
    "\\pdfmeta{ title = \"T\", author = \"A\" }\n" ++
    "\\assert{ pages == 1 }\n" ++
    "\\assert{ fonts.all_embedded }\n" ++
    "\\begin{document}hi\\end{document}"
  let (declDoc, declDs) := elabStr declSrc
  t "decl source clean" declDs.isEmpty
  t "decl page size" (declDoc.page.width == Dim.pt 420 && declDoc.page.height == Dim.pt 595)
  t "decl margin both axes"
    (declDoc.page.vmargin == Dim.inch 1 / 2 && declDoc.page.hmargin == Dim.inch 1 / 2)
  t "decl metadata" (declDoc.info.title == some "T" && declDoc.info.author == some "A")
  t "decl assertions parsed" (declDoc.asserts.size == 2)

  -- dimension parsing is exact
  t "decl dim in" (Decl.parseValue "0.5in" == some (.dim (Dim.inch 1 / 2)))
  t "decl dim pt" (Decl.parseValue "12pt" == some (.dim (Dim.pt 12)))
  t "decl dim cm" (Decl.parseValue "2.54cm" == some (.dim (Dim.inch 1)))
  t "decl dim mm" (Decl.parseValue "25.4mm" == some (.dim (Dim.inch 1)))
  t "decl string" (Decl.parseValue "\"a b\"" == some (.str "a b"))
  t "decl ident" (Decl.parseValue "letter" == some (.ident "letter"))
  t "decl int" (Decl.parseValue "3" == some (.int 3))
  t "decl rejects junk" (Decl.parseValue "12 furlongs" == none)

  -- declaration diagnostics, one code each
  t "decl unknown size" (errCodes ("\\documentclass{article}\n\\page{ size = tabloid }\n" ++
    "\\begin{document}x\\end{document}") == ["E0324"])
  t "decl unknown key" (errCodes ("\\documentclass{article}\n\\page{ bogus = 1pt }\n" ++
    "\\begin{document}x\\end{document}") == ["E0322"])
  t "decl wrong type" (errCodes ("\\documentclass{article}\n\\page{ vmargin = \"x\" }\n" ++
    "\\begin{document}x\\end{document}") == ["E0323"])
  t "decl bad assertion" (errCodes ("\\documentclass{article}\n\\assert{ pages =~ 1 }\n" ++
    "\\begin{document}x\\end{document}") == ["E0325"])
  t "decl needs a block" (errCodes ("\\documentclass{article}\n\\page\n" ++
    "\\begin{document}x\\end{document}") == ["E0304"])

  -- assertions are judged against what shipped
  let shipped : Check.Shipped := { pages := 2, fontsEmbedded := true }
  let mkAssert (k : Ir.AssertKind) : Ir.Assertion := { kind := k, span := none }
  t "assert pages eq holds" ((Check.one shipped (mkAssert (.pages .eq 2))).isNone)
  t "assert pages eq fails" ((Check.one shipped (mkAssert (.pages .eq 1))).isSome)
  t "assert pages le holds" ((Check.one shipped (mkAssert (.pages .le 3))).isNone)
  t "assert pages gt fails" ((Check.one shipped (mkAssert (.pages .gt 5))).isSome)
  t "assert fonts holds" ((Check.one shipped (mkAssert .fontsAllEmbedded)).isNone)
  t "assert fonts fails"
    ((Check.one { shipped with fontsEmbedded := false } (mkAssert .fontsAllEmbedded)).isSome)
  t "assert failure names the actual"
    (((Check.one shipped (mkAssert (.pages .eq 1))).map (·.message)).any
      fun m => (m.splitOn "actual: 2").length == 2)
  t "assert all reports every failure"
    ((Check.all shipped #[mkAssert (.pages .eq 1), mkAssert (.pages .eq 2),
      mkAssert (.pages .lt 1)]).size == 2)

  -- \tokens: font-relative lengths, derived tokens, and \block spacing
  let tokSrc := "\\documentclass{article}\n" ++
    "\\tokens{ rhythm = 2ex plus 0.5ex, sep = 0.75 * rhythm, slab = 18pt }\n" ++
    "\\begin{document}\\block[before = sep]{x}\\end{document}"
  let (tokDoc, tokDs) := elabStr tokSrc
  t "tokens source clean" tokDs.isEmpty
  t "tokens ex is symbolic" (tokDoc.tokens.find? "rhythm" ==
    some { width := { ex := 2000 }, stretch := { ex := 500 } })
  t "tokens derived scales earlier" (tokDoc.tokens.find? "sep" ==
    some { width := { ex := 1500 }, stretch := { ex := 375 } })
  t "tokens absolute" (tokDoc.tokens.find? "slab" ==
    some { width := Dim.Length.ofSp (Dim.pt 18) })
  t "block carries declared spacing" (tokDoc.body.any fun b =>
    match b with
    | .spaced before _ => before.width.ex == 1500
    | _ => false)
  -- A bare name is a well-formed value of the wrong type (E0323); text that
  -- parses as nothing at all is E0321. Both rejected, code says which.
  t "tokens reject wrong type" (errCodes ("\\documentclass{article}\\tokens{ a = wat }" ++
    "\\begin{document}x\\end{document}") == ["E0323"])
  t "tokens reject junk" (errCodes
    ("\\documentclass{article}\\tokens{ a = 3 furlongs }" ++
     "\\begin{document}x\\end{document}") == ["E0321"])
  t "block unknown key" (errCodes ("\\documentclass{article}" ++
    "\\begin{document}\\block[after = 1pt]{x}\\end{document}") == ["E0322"])
  t "block needs a body" (errCodes ("\\documentclass{article}" ++
    "\\begin{document}\\block\\end{document}") == ["E0304"])

  -- Length resolution against real font metrics
  t "length resolve ex" ((Dim.Length.mk 0 0 1000).resolve (Dim.pt 10) (Dim.pt 5) ==
    Dim.pt 5)
  t "length resolve em" ((Dim.Length.mk 0 1500 0).resolve (Dim.pt 10) (Dim.pt 5) ==
    Dim.pt 15)
  t "length resolve mixed"
    ((Dim.Length.mk (Dim.pt 2) 1000 1000).resolve (Dim.pt 10) (Dim.pt 4) == Dim.pt 16)

  -- text symbols keep the space after them, unlike other control words
  t "symbol keeps space" (toks "a \\middot b" ==
    [.word "a", .space, .ctrl "middot", .space, .word "b"])
  t "command still eats space" (toks "a \\textbf b" ==
    [.word "a", .space, .ctrl "textbf", .word "b"])
  let (symDoc, symDs) := elabStr "a \\middot b \\ldots"
  t "symbol elaborates" (symDs.isEmpty && symDoc.body ==
    #[.para #[.text "a · b …"]])

  -- smart punctuation: what the author typed is what they meant
  t "smart en dash" ((elabStr "2021--2024").1.body == #[.para #[.text "2021–2024"]])
  t "smart em dash" ((elabStr "a---b").1.body == #[.para #[.text "a—b"]])
  t "smart ellipsis" ((elabStr "wait...").1.body == #[.para #[.text "wait…"]])
  t "smart quotes directional"
    ((elabStr "say \"hi\" and don't").1.body == #[.para #[.text "say “hi” and don’t"]])
  t "mono keeps punctuation literal"
    ((elabStr "\\texttt{a--b}").1.body ==
      #[.para #[.styled .mono #[.text "a--b"]]])

  -- links, running content, and block-producing user commands
  let (linkDoc, linkDs) := elabStr "\\href{https://example.org}{text}"
  t "href source clean" linkDs.isEmpty
  t "href wraps body" (linkDoc.body ==
    #[.para #[.link "https://example.org" #[.text "text"]]])
  let (bareDoc, bareDs) := elabStr "\\href{https://example.org}"
  t "href bare prints its url" (bareDs.isEmpty && bareDoc.body ==
    #[.para #[.link "https://example.org" #[.text "https://example.org"]]])
  let runSrc := "\\documentclass{article}\n" ++
    "\\runninghead{Title \\hfill \\pagenumber}\n" ++
    "\\runningfoot{page \\pagenumber\\ of \\pagecount}\n" ++
    "\\begin{document}x\\end{document}"
  let (runDoc, runDs) := elabStr runSrc
  t "running content clean" runDs.isEmpty
  t "running head parsed" (runDoc.head.isSome && runDoc.foot.isSome)
  t "running head has a page number"
    ((runDoc.head.getD #[]).any fun x => x == .pageNumber)
  let blockMacro := "\\documentclass{article}\n" ++
    "\\define \\entry(a: text) {\\block[before = 3pt]{\\textbf{\\a}}}\n" ++
    "\\begin{document}\\entry{One}\\entry{Two}\\end{document}"
  let (bmDoc, bmDs) := elabStr blockMacro
  t "block-producing macro clean" bmDs.isEmpty
  t "block-producing macro yields blocks" (bmDoc.body.size == 2 &&
    bmDoc.body.all fun b => match b with
      | .spaced _ _ => true
      | _ => false)
  -- An inline-only macro must stay inline, or it would split the paragraph.
  let inlineMacro := "\\documentclass{article}\n" ++
    "\\define \\who(a: text) {\\textbf{\\a}}\n" ++
    "\\begin{document}\\who{Ada} wrote it\\end{document}"
  let (imDoc, _) := elabStr inlineMacro
  t "inline macro does not split the paragraph" (imDoc.body.size == 1)

  -- HTML backend
  let escaped := Html.escapeText "a <script> & \"x\""
  t "html escapes text" (escaped == "a &lt;script&gt; &amp; \"x\"")
  t "html escapes attributes" (Html.escapeAttr "a\"b<c" == "a&quot;b&lt;c")
  t "html void element has no closing tag"
    (Html.render (Html.elem "br" #[]) 0 == "<br>\n")
  t "html phrasing content stays on one line"
    (Html.render (Html.elem "p" #[Html.text "a ", Html.elem "em" #[Html.text "b"],
      Html.text ", c"]) 0 == "<p>a <em>b</em>, c</p>\n")
  t "html style payload cannot close its own tag"
    (((Html.render (Html.Node.style "x</style>bad") 0).splitOn "</style>").length == 2)

  let (htmlDoc, _) := elabStr ("\\documentclass{article}\n" ++
    "\\palette{ primary = #7C3AED }\n" ++
    "\\pdfmeta{ title = \"T\" }\n" ++
    "\\begin{document}\n" ++
    "\\section{Head}\n" ++
    "A \\textbf{bold} word, \\textcolor{primary}{coloured}, and a " ++
    "\\href{https://example.org}{link}.\n\n" ++
    "\\begin{itemize}\\item One\\end{itemize}\n" ++
    "\\end{document}")
  let (page, pageDiags) := HtmlDoc.emit {} htmlDoc
  t "html emit clean" pageDiags.isEmpty
  t "html has doctype" (page.startsWith "<!DOCTYPE html>")
  t "html sets the title" ((page.splitOn "<title>T</title>").length == 2)
  t "html section becomes h2" ((page.splitOn "<h2>Head</h2>").length == 2)
  t "html bold becomes strong" ((page.splitOn "<strong>bold</strong>").length == 2)
  t "html colour references the token"
    ((page.splitOn "var(--primary, #7c3aed)").length == 2)
  t "html link has href"
    ((page.splitOn "<a href=\"https://example.org\">link</a>").length == 2)
  t "html single-para item is not wrapped"
    ((page.splitOn "<li>One</li>").length == 2)
  t "html inlines the stylesheet" ((page.splitOn "<style>").length == 2)
  t "html declares the generator" ((page.splitOn "content=\"leantex\"").length == 2)

  -- Running content is paged furniture: HTML says so rather than dropping it.
  let (_, runHtmlDiags) := HtmlDoc.emit {} runDoc
  t "html warns about running content" (runHtmlDiags.any (·.code == "W0007"))

  -- Bulma interop binds our tokens to the framework's own properties.
  let (bulmaPage, _) := HtmlDoc.emit { css := .bulma } htmlDoc
  t "bulma mode binds primary" ((bulmaPage.splitOn "--bulma-primary").length == 2)
  t "bulma mode ships no base sheet" ((bulmaPage.splitOn "--measure").length == 1)
  let (barePage, _) := HtmlDoc.emit { css := .none } htmlDoc
  t "css none emits no style element" ((barePage.splitOn "<style>").length == 1)

  -- A stretched row broken by `\\` becomes a column of rows. A <br> cannot end
  -- a flex line, so the break has to be structural or the second line lands
  -- beside the first -- where the PDF puts it below.
  let (rowDoc, _) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "left \\hfill right\\\\second\\end{document}")
  let (rowPage, _) := HtmlDoc.emit {} rowDoc
  t "broken stretched row becomes rows"
    ((rowPage.splitOn "class=\"entry-row\"").length == 3)
  t "broken stretched row keeps no br" ((rowPage.splitOn "<br>").length == 1)
  -- An unbroken one stays a single row.
  let (oneRowDoc, _) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "left \\hfill right\\end{document}")
  t "unbroken stretched row stays one row"
    (((HtmlDoc.emit {} oneRowDoc).1.splitOn "class=\"entry\"").length == 2)

  -- \hfill and control-symbol spaces
  -- \hfill takes no argument but still swallows the following space: a space
  -- after the stretch would be visible at the far margin.
  let (fillDoc, fillDs) := elabStr "a \\hfill b"
  t "hfill source clean" fillDs.isEmpty
  t "hfill becomes an inline fill" (fillDoc.body ==
    #[.para #[.text "a ", .fill, .text "b"]])
  t "thin space escape" ((elabStr "a\\,b").1.body ==
    #[.para #[.text "a b"]])

  -- \palette and colour
  let palSrc := "\\documentclass{article}\n" ++
    "\\palette{ primary = #7C3AED, short = #abc }\n" ++
    "\\begin{document}\\textcolor{primary}{x} {\\short y} z\\end{document}"
  let (palDoc, palDs) := elabStr palSrc
  t "palette source clean" palDs.isEmpty
  t "palette parsed" (palDoc.palette.find? "primary" ==
    some { r := 0x7C, g := 0x3A, b := 0xED })
  t "palette short hex expands" (palDoc.palette.find? "short" ==
    some { r := 0xAA, g := 0xBB, b := 0xCC })
  t "palette textcolor wraps" (palDoc.body.any fun b =>
    match b with
    | .para content => content.any fun x =>
      match x with
      | .colored c name body => c.r == 0x7C && name == some "primary" && body.size == 1
      | _ => false
    | _ => false)
  t "palette unknown name" (errCodes ("\\documentclass{article}\\palette{a = #fff}" ++
    "\\begin{document}\\textcolor{nope}{x}\\end{document}") == ["E0326"])
  -- A palette name binds a following group as its argument. It used to colour
  -- everything to the end of the group, so `\primary{Alex} Doe` painted Doe too.
  let palSrc (body : String) : Ir.Doc :=
    (Elab.run "t" ("\\documentclass{article}\\palette{mut = #888888}" ++
      "\\begin{document}" ++ body ++ "\\end{document}")).1
  t "palette name takes its group as an argument"
    ((palSrc "\\mut{in} out").body == #[.para #[
      .colored { r := 0x88, g := 0x88, b := 0x88 } (some "mut") #[.text "in"],
      .text " out"]])
  t "palette name with no group runs to the end of the group"
    ((palSrc "{\\mut in} out").body == #[.para #[
      .colored { r := 0x88, g := 0x88, b := 0x88 } (some "mut") #[.text "in"],
      .text " out"]])
  t "palette wrong type" (errCodes ("\\documentclass{article}\\palette{a = 3pt}" ++
    "\\begin{document}x\\end{document}") == ["E0323"])
  t "palette cannot shadow builtin" (errCodes
    ("\\documentclass{article}\\palette{textbf = #fff}" ++
     "\\begin{document}x\\end{document}") == ["E0303"])
  t "color value parsed" (Decl.parseValue "#7C3AED" == some (.color 0x7C 0x3A 0xED))
  t "color rejects bad hex" (Decl.parseValue "#12345" == none)
  t "color pdf components" ((Ir.Color.mk 255 0 128).pdfComponents == "1 0 0.502")
  t "color black components" (Ir.Color.black.pdfComponents == "0 0 0")

  -- \fonts declarations and family resolution
  let fontsSrc := "\\documentclass{article}\n" ++
    "\\fonts{ body = \"DejaVu Serif\", sf = \"DejaVu Sans\" }\n" ++
    "\\begin{document}x\\end{document}"
  let (fDoc, fDs) := elabStr fontsSrc
  t "fonts source clean" fDs.isEmpty
  t "fonts body" (fDoc.fonts.body == some "DejaVu Serif")
  t "fonts sf alias maps to sans" (fDoc.fonts.sans == some "DejaVu Sans")
  t "fonts mono unset" (fDoc.fonts.mono == none)
  t "fonts wrong type" (errCodes ("\\documentclass{article}\\fonts{ body = 12 }" ++
    "\\begin{document}x\\end{document}") == ["E0323"])
  t "fonts unknown key" (errCodes ("\\documentclass{article}\\fonts{ script = \"X\" }" ++
    "\\begin{document}x\\end{document}") == ["E0322"])

  let faces ← FontDb.scan
  t "fontdb finds faces" (faces.size > 0)
  t "fontdb finds dejavu" ((FontDb.families faces).any (· == "DejaVu Serif"))
  -- The plain face must win over same-family condensed/extra variants.
  match FontDb.resolve faces "DejaVu Serif" { bold := true } with
  | some (face, exact) =>
    t "fontdb bold is exact" exact
    t "fontdb bold is not condensed"
      ((face.path.splitOn "Condensed").length == 1)
    t "fontdb bold flagged" face.bold
  | none => failures ref "fontdb: DejaVu Serif Bold not found"
  match FontDb.resolve faces "DejaVu Serif" { bold := true, italic := true } with
  | some (face, exact) => t "fontdb bold italic" (exact && face.bold && face.italic)
  | none => failures ref "fontdb: DejaVu Serif BoldItalic not found"
  t "fontdb unknown family" (FontDb.resolve faces "No Such Family Here" {} |>.isNone)

  -- font parsing on the system font
  match ← findFont with
  | none =>
    failures ref "font: no DejaVu Sans on this host (needed for M2 tests)"
  | some fontData =>
    match Font.parse fontData with
    | .error e => failures ref s!"font parse: {e}"
    | .ok font =>
      t "font name" (font.psName == "DejaVuSans")
      t "font upem" (font.unitsPerEm == 2048)
      t "font gid A" (font.gid 'A' |>.isSome)
      t "font advance A" (font.advance 'A' > 0)
      t "font greek" (font.gid 'α' |>.isSome)
      t "font missing emoji" (font.gid '🎉' |>.isNone)
      t "font family" (font.family == "DejaVu Sans")
      t "font not bold" (!font.isBold && !font.isItalic)

      -- A parser is fed arbitrary files, so it has to be total over them. Every
      -- byte read used to go through `b[i]!`, which aborts the process: one
      -- font in a TeX Live tree took the whole run down with it.
      t "font parse rejects garbage"
        ((Font.parse (ByteArray.mk #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])).isOk == false)
      t "font parse rejects an empty file" ((Font.parse (ByteArray.mk #[])).isOk == false)
      -- Truncation at every length must return a verdict rather than abort.
      -- Reaching the assertion at all is the property: a panic would take the
      -- whole run down. Some truncations parse legitimately -- the metrics
      -- tables can all survive when only glyph data is lost.
      let verdicts := (List.range 64).map fun k =>
        (Font.parse (fontData.extract 0 (fontData.size * k / 64))).isOk
      t "font parse is total over truncations" (verdicts.length == 64)
      t "font parse rejects short truncations" (verdicts.take 8 |>.all (· == false))
      -- A valid font with a table header claiming more than the file holds.
      let lying := Id.run do
        let mut b := fontData.extract 0 (min fontData.size 4096)
        -- the first table entry's length field, made absurd
        for i in [0:4] do
          b := b.set! (12 + 12 + i) 0x7f
        return b
      t "font parse rejects a table that overruns the file"
        ((Font.parse lying).isOk == false)
      -- `classify` is what a family scan uses, and it must agree with `parse`
      -- about what a face is called. It used to be `parse` fed a sparse image
      -- with the metric tables missing, which is how the scan read out of
      -- bounds in the first place.
      match Font.classify fontData with
      | .error e => failures ref s!"font classify: {e}"
      | .ok c =>
        t "classify agrees with parse on family" (c.family == font.family)
        t "classify agrees with parse on subfamily" (c.subfamily == font.subfamily)
        t "classify agrees with parse on style"
          (c.isBold == font.isBold && c.isItalic == font.isItalic &&
           c.weight == font.weight && c.isFixedPitch == font.isFixedPitch)
      t "classify is total over truncations"
        (((List.range 64).map fun k =>
          (Font.classify (fontData.extract 0 (fontData.size * k / 64))).isOk).length == 64)

      -- A one-face set: every slot and variant maps to index 0.
      let oneFace : Font.FontSet := {
        fonts := #[font]
        index := ((List.range 3).flatMap fun slot =>
          [((slot, false, false), 0), ((slot, true, false), 0),
           ((slot, false, true), 0), ((slot, true, true), 0)]).toArray
      }
      t "fontset lookup body" (oneFace.lookup 0 false false == 0)
      t "fontset lookup falls back" (oneFace.lookup 2 true true == 0)

      -- layout: hyphenation is materialized only at a chosen break; headings
      -- and list markers carry visual structure into the positioned page.
      let (hyDoc, hyDs) := Elab.run "t" "incomprehensibility"
      t "layout hyphen source clean" hyDs.isEmpty
      let narrow : Layout.Geom := {
        pageW := Dim.pt 90
        pageH := Dim.pt 200
        hmargin := Dim.pt 10
        vmargin := Dim.pt 10
        fontSize := Dim.pt 10
      }
      let hyOut := Layout.run narrow oneFace (some pats) hyDoc
      let hyphenRendered := hyOut.pages.any fun p => p.lines.any fun l =>
        l.segs.any fun s => match s with
          | .run _ _ _ _ glyphs _ => glyphs.any (·.2 == '-')
          | .gap _ => false
      t "layout chosen hyphen renders" (hyOut.pages[0]!.lines.size > 1 && hyphenRendered)
      t "layout hyphen avoids overfull" (!hyOut.diags.any (·.code == "W0005"))

      let visualSrc := "\\section{Heading}\nBody text.\n\n" ++
        "\\begin{itemize}\\item A list item.\\end{itemize}"
      let (visualDoc, visualDs) := Elab.run "t" visualSrc
      t "layout visual source clean" visualDs.isEmpty
      let visualOut := Layout.run ({} : Layout.Geom) oneFace (some pats) visualDoc
      let hasSectionSize := visualOut.pages.any fun p =>
        p.lines.any (·.size == Dim.pt 14)
      let hasListMarker := visualOut.pages.any fun p => p.lines.any fun l =>
        l.segs.any fun s => match s with
          | .run _ _ _ _ glyphs _ => glyphs.any (·.2 == '–')
          | .gap _ => false
      t "layout section size" hasSectionSize
      t "layout list marker" hasListMarker

      -- pdf: build a tiny document and re-verify the xref stream offsets
      let (doc, eds) := Elab.run "t" "hello world, a small pdf self check"
      t "pdf source clean" eds.isEmpty
      let geom : Layout.Geom := {}
      let out := Layout.run geom oneFace none doc
      t "pdf one page" (out.pages.size == 1)
      let pdf := Pdf.write geom oneFace out.pages
      t "pdf header" (String.fromUTF8! (pdf.extract 0 8) == "%PDF-2.0")
      t "pdf eof" (String.fromUTF8! (pdf.extract (pdf.size - 6) pdf.size) == "%%EOF\n")
      match checkXref pdf with
      | .ok n => t s!"pdf xref valid" (n > 0)
      | .error e => failures ref s!"pdf xref: {e}"

      -- Faces and sizes have to survive into the content stream, and only the
      -- bytes can say so: a regression once embedded one face where six
      -- belonged while every other test still passed.
      let twoFace : Font.FontSet := {
        fonts := #[font, font]
        index := ((List.range 3).flatMap fun slot =>
          let idx := if slot == 1 then 1 else 0
          [((slot, false, false), idx), ((slot, true, false), idx),
           ((slot, false, true), idx), ((slot, true, true), idx)]).toArray
      }
      let (bigDoc, bigDs) := Elab.run "t"
        "plain {\\sffamily other face} and {\\Huge big} and {\\small little}"
      t "size scale source clean" bigDs.isEmpty
      let bigPdf := Pdf.write geom twoFace (Layout.run geom twoFace none bigDoc).pages
      t "pdf references a second face" (bytesContain bigPdf "/F2 ")
      t "pdf sets Huge at 2.488x" (bytesContain bigPdf "24.88 Tf")
      t "pdf sets small at 0.9x" (bytesContain bigPdf "9 Tf")
      t "pdf keeps the body size" (bytesContain bigPdf "10 Tf")
      -- One face only: nothing unused is embedded, so no /F2 exists.
      let plainPdf := Pdf.write geom oneFace (Layout.run geom oneFace none bigDoc).pages
      t "pdf embeds no unused face" (!bytesContain plainPdf "/F2 ")

      -- Fixed-width spaces are kerns. Looking up a glyph at U+2009 drops the
      -- space, because a Type 1-derived face has none -- and warns instead of
      -- setting it.
      let widthOf (src : String) : Dim.Sp :=
        let (d, _) := Elab.run "t" src
        (((Layout.run geom oneFace none d).pages.flatMap (·.lines))[0]?.map
          (·.setWidth)).getD 0
      let plainW := widthOf "ab"
      let thinW := widthOf "a\\,b"
      t "thin space widens the line" (thinW == plainW + geom.fontSize / 6)
      t "thin space warns about nothing"
        ((Layout.run geom oneFace none (Elab.run "t" "a\\,b").1).diags.isEmpty)
      t "no-break space is an unbreakable interword space"
        (widthOf "a\\nbsp b" > plainW)
      -- `~` is what LaTeX authors actually type for it.
      t "tilde is a no-break space"
        ((Elab.run "t" "a~b").1.body == #[.para #[.text "a\u00a0b"]])
      t "tilde does not break the line" (widthOf "a~b" == widthOf "a\u00a0b")
      t "escaped tilde is a literal tilde"
        ((Elab.run "t" "a\\~b").1.body == #[.para #[.text "a~b"]])

      -- Small caps are synthesised: lowercase raised and set smaller, in runs
      -- that carry their own size. `\scshape` used to do nothing at all.
      let scOut := Layout.run geom oneFace none (Elab.run "t" "\\scshape aB").1
      let scRuns := (scOut.pages.flatMap (·.lines)).flatMap (·.segs.filterMap fun s =>
        match s with
        | .run _ _ _ _ glyphs size => some (glyphs.map (·.2), size)
        | .gap _ => none)
      t "small caps raises lowercase"
        (scRuns.all fun (cs, _) => cs.all fun c => !c.isLower)
      t "small caps sets the raised run smaller"
        (scRuns.any (·.2 == geom.fontSize * Layout.smallCapScale / 1000) &&
         scRuns.any (·.2 == geom.fontSize))

      -- `\hfill` on a paragraph's last line must reach the margin. The
      -- line-running fill is also fil glue, and sharing the leftover with it
      -- puts the right-hand text halfway there -- which is what LaTeX does and
      -- what nobody setting a row of dates wants.
      let measureOf (src : String) : Array Dim.Sp :=
        let (d, _) := Elab.run "t" src
        ((Layout.run geom oneFace none d).pages.flatMap (·.lines)).map (·.setWidth)
      let lastLine := measureOf "Left \\hfill Right"
      t "hfill reaches the margin on a final line"
        (lastLine.size == 1 && lastLine[0]! == geom.textWidth)
      let brokenLine := measureOf "Left \\hfill Right\\\\Second"
      t "hfill reaches the margin before a break"
        (brokenLine.size == 2 && brokenLine[0]! == geom.textWidth)
      -- Without an \hfill the last line stays ragged: the fill still fills.
      t "no hfill leaves the last line short"
        (brokenLine.size == 2 && brokenLine[1]! < geom.textWidth)

  let failed := (← ref.get).reverse
  if failed.isEmpty then
    IO.println "tests: all passed"
    return 0
  else
    for name in failed do
      IO.eprintln s!"FAIL {name}"
    IO.eprintln s!"tests: {failed.length} failed"
    return 1
