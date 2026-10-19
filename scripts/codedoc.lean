/- The code-file reader's classifier: its documentation comments in testdata/codedoc/cases against
each language's own parser's. `lake env lean --run scripts/codedoc.lean` asks python3 and lean
again; `--check` reads the committed oracle alone; `--selftest` tests the record and the comparison. -/
import LeanTex
import scripts.Board

open LeanTex.Core Scoreboard

def casesDir : String := "testdata/codedoc/cases"
def oraclePath : String := "testdata/codedoc/oracle.tsv"
def reviewedPath : String := "testdata/codedoc/shell-reviewed.tsv"
def verdictPath : String := "testdata/codedoc/verdicts.tsv"

/-- A documentation comment: its source range in characters and its text. -/
structure Doc where
  start : Nat
  stop : Nat
  text : String
deriving BEq, Repr, Inhabited

/-- The deliberate differences from a language's own parser, each with its reason. -/
def divergences : List (String × String) :=
  [("lean-indented.lean", "a docstring that does not open its line stays in the code: the reader \
takes documentation where Lean's layout puts a top-level declaration, at a line's start, since an \
indented one is a field's, a constructor's or a local definition's as often as a declaration's")]

/-- The tab-separated record's escape for one field. -/
def escapeField (s : String) : String := Id.run do
  let mut out := if s.startsWith "#" then "\\" else ""
  for c in s.toList do
    out := match c with
      | '\\' => out.append "\\\\"
      | '\t' => out.append "\\t"
      | '\n' => out.append "\\n"
      | '\r' => out.append "\\r"
      | c => out.push c
  return out

def unescapeField (s : String) : String := Id.run do
  let cs := s.toList.toArray
  let mut out := ""
  let mut i := 0
  for _ in [0:cs.size + 1] do
    if i ≥ cs.size then break
    if cs.getD i ' ' == '\\' && i + 1 < cs.size then
      out := out.push (match cs.getD (i + 1) ' ' with
        | 't' => '\t'
        | 'n' => '\n'
        | 'r' => '\r'
        | c => c)
      i := i + 2
    else
      out := out.push (cs.getD i ' ')
      i := i + 1
  return out

/-- An oracle's answer for every case: a case with no documentation comment is its name and `-`. -/
def renderAnswers (answers : Array (String × Array Doc)) : String :=
  answers.foldl (fun acc (name, docs) =>
    let n := escapeField name
    if docs.isEmpty then acc ++ n ++ "\t-\n"
    else docs.foldl (fun acc d =>
      acc ++ s!"{n}\t{d.start}\t{d.stop}\t{escapeField d.text}\n") acc) ""

def parseAnswers (text : String) : Except String (Array (String × Array Doc)) := do
  let mut out : Array (String × Array Doc) := #[]
  for line in text.splitOn "\n" do
    if line.isEmpty || line.startsWith "#" then continue
    let (name, doc) ← match line.splitOn "\t" with
      | [name, "-"] => pure (unescapeField name, none)
      | [name, a, b, t] =>
        match a.toNat?, b.toNat? with
        | some a, some b =>
          pure (unescapeField name, some { start := a, stop := b, text := unescapeField t })
        | _, _ => throw s!"unreadable range: {line}"
      | _ => throw s!"unreadable row: {line}"
    match out.findIdx? (·.1 == name), doc with
    | some i, some d =>
      if (out[i]?.map (·.2.isEmpty)).getD false then
        throw s!"case {name} is listed with no comment and with one"
      out := out.modify i fun (n, ds) => (n, ds.push d)
    | some _, none => throw s!"case {name} is listed with no comment and with one"
    | none, some d => out := out.push (name, #[d])
    | none, none => out := out.push (name, #[])
  return out

/-- A case's language, from its extension. -/
def langOf (name : String) : Option Ir.CodeLang :=
  match Ir.Surface.ofPath name with
  | .code l => some l
  | .tex | .markdown => none

/-- The text a reader's or a parser's comment is compared by: a docstring's value for Python and
the shell, the body between the delimiters for Lean. -/
def readerText (lang : Ir.CodeLang) (seg : Code.Seg) : String :=
  match lang.row.docs with
  | .lean => String.ofList ((seg.text.drop 3).reverse.drop 2).reverse
  | .python | .leading _ | .comments _ => (Code.proseIn lang seg.text 1 0).text

/-- The documentation comments the reader takes from a case. -/
def readerDocs (lang : Ir.CodeLang) (src : String) : Array Doc :=
  ((Code.segmentsOf lang src).filter Code.Seg.isProse).toArray.map fun seg =>
    { start := seg.start, stop := seg.start + seg.text.length, text := readerText lang seg }

/-- A case's verdict and its note. -/
def verdictOf (name : String) (reader oracle : Array Doc) : String × String :=
  if reader == oracle then ("match", "")
  else match divergences.lookup name with
    | some _ => ("divergence", "")
    | none => ("owed", s!"reader {reader.size} comments, parser {oracle.size}")

def renderVerdicts (rows : Array (String × String × String)) : String :=
  "# One row per case in testdata/codedoc/cases: case, verdict, note.\n\
# verdicts: match | divergence | owed. Written only by scripts/codedoc.lean.\n" ++
  rows.foldl (fun acc (n, v, note) => acc ++ s!"{n}\t{v}\t{note}\n") ""

/-- The program Python's own parser answers the oracle with. -/
def pythonOracle : String := r#"import ast, sys

def esc(s):
    return s.replace('\\', '\\\\').replace('\t', '\\t').replace('\n', '\\n').replace('\r', '\\r')

for path in sys.argv[1:]:
    with open(path, encoding='utf-8', newline='') as f:
        src = f.read()
    lines = src.split('\n')
    starts = [0]
    for line in lines[:-1]:
        starts.append(starts[-1] + len(line) + 1)
    def off(lineno, col):
        return starts[lineno - 1] + len(lines[lineno - 1].encode('utf-8')[:col].decode('utf-8'))
    rows = []
    for node in ast.walk(ast.parse(src)):
        if isinstance(node, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            doc = ast.get_docstring(node)
            if doc is not None:
                c = node.body[0].value
                rows.append((off(c.lineno, c.col_offset), off(c.end_lineno, c.end_col_offset), doc))
    name = path.rsplit('/', 1)[-1]
    if not rows:
        print(f"{name}\t-")
    for a, b, d in sorted(rows):
        print(f"{name}\t{a}\t{b}\t{esc(d)}")
"#

/-- The program Lean's own command parser answers the oracle with, run as `lean` elaborates a file:
every module doc, and every docstring a command opens with, through `mutual` and `… in`. -/
def leanOracle : String := r#"import Lean
open Lean Elab Command

def docAt? (stx : Syntax) : Option Syntax :=
  [stx, stx[0], stx[0][0], stx[0][0][0]].find? fun s =>
    s.getKind == ``Lean.Parser.Command.docComment

def innermost (stx : Syntax) : Syntax := Id.run do
  let mut s := stx
  for _ in [0:16] do
    if s.getKind == ``Lean.Parser.Command.in then s := s[2] else break
  return s

def esc (s : String) : String :=
  ((s.replace "\\" "\\\\").replace "\t" "\\t").replace "\n" "\\n" |>.replace "\r" "\\r"

run_cmd do
  let env ← getEnv
  let paths := ((← IO.getEnv "CODEDOC_CASES").getD "").splitOn ":" |>.filter (!·.isEmpty)
  for path in paths do
    let src ← IO.FS.readFile path
    let name := (path.splitOn "/").getLast!
    let ictx := Parser.mkInputContext src path
    let (_, st0, msgs0) ← Parser.parseHeader ictx
    let mut st := st0
    let mut msgs := msgs0
    let mut found := false
    for _ in [0:src.utf8ByteSize + 1] do
      if ictx.atEnd st.pos then break
      let (cmd, st', msgs') := Parser.parseCommand ictx { env, options := {} } st msgs
      st := st'
      msgs := msgs'
      let cmds := if cmd.getKind == ``Lean.Parser.Command.mutual then cmd[1].getArgs else #[cmd]
      for c in cmds do
        let c := innermost c
        let doc := if c.getKind == ``Lean.Parser.Command.moduleDoc then some c else docAt? c
        if let some d := doc then
          if let (some a, some b) := (d.getPos?, d.getTailPos?) then
            let text := String.Pos.Raw.extract src a b
            let body := String.ofList ((text.toList.drop 3).reverse.drop 2).reverse
            IO.println s!"{name}\t{(String.Pos.Raw.extract src 0 a).length}\t\
{(String.Pos.Raw.extract src 0 b).length}\t{esc body}"
            found := true
    if msgs.hasErrors then throwError s!"{name}: Lean's parser reports errors"
    unless found do IO.println s!"{name}\t-"
"#

def die (code : UInt32) (msg : String) : IO UInt32 := do
  IO.eprintln msg
  return code

/-- The cases, by name, with their text. -/
def loadCases : IO (Array (String × String)) := do
  let mut out := #[]
  for e in ← System.FilePath.readDir casesDir do
    if (langOf e.fileName).isSome then
      out := out.push (e.fileName, (← LeanTex.Cli.Input.readSource e.path.toString) |>.toOption
        |>.map (fun b => (Encoding.readMarkdown e.path.toString b).text) |>.getD "")
  return out.qsort (·.1 < ·.1)

/-- One external parser's answers for the named cases. -/
def ask (cmd : String) (args : Array String) (env : Array (String × Option String) := #[]) :
    IO (Except String (Array (String × Array Doc))) := do
  let out ← IO.Process.output { cmd, args, env }
  if out.exitCode != 0 then return .error s!"{cmd} exited {out.exitCode}: {out.stderr}"
  return parseAnswers out.stdout

/-- The versions of the parsers the oracle asks, for its provenance line. -/
def parserVersions : IO String := do
  let version (cmd : String) : IO String := do
    let out ← IO.Process.output { cmd, args := #["--version"] }
    return (out.stdout ++ out.stderr).trimAscii.toString.replace "\n" " "
  return s!"{← version "python3"}; {← version "lean"}"

/-- The oracle, asked again: Python's and Lean's parsers, and the hand-written shell rows. -/
def askOracle (cases : Array (String × String)) : IO (Except String (Array (String × Array Doc))) := do
  let paths (l : Ir.CodeLang) := (cases.filter (langOf ·.1 == some l)).map fun (n, _) =>
    s!"{casesDir}/{n}"
  let py ← ask "python3" (#["-I", "-B", "-c", pythonOracle] ++ paths .python)
  let lean ← IO.FS.withTempDir fun dir => do
    IO.FS.writeFile (dir / "oracle.lean") leanOracle
    ask "lean" #[(dir / "oracle.lean").toString]
      #[("CODEDOC_CASES", some (":".intercalate (paths .lean).toList))]
  let shell := parseAnswers (← IO.FS.readFile reviewedPath)
  match py, lean, shell with
  | .ok p, .ok l, .ok s => return .ok ((p ++ l ++ s).qsort (·.1 < ·.1))
  | .error e, _, _ | _, .error e, _ | _, _, .error e => return .error e

/-- Every way the tables disagree with the cases: a case the oracle or the hand-written shell rows
do not answer, a row naming no case, a divergence that no longer diverges or names no case. -/
def tableFaults (cases : Array (String × String)) (oracle : Array (String × Array Doc))
    (reviewed : Array (String × Array Doc)) : Array String := Id.run do
  let mut out := #[]
  for (n, _) in cases do
    unless oracle.any (·.1 == n) do out := out.push s!"case {n} has no oracle answer"
    if langOf n == some .bash && !reviewed.any (·.1 == n) then
      out := out.push s!"shell case {n} has no reviewed row"
  for (n, _) in oracle do
    unless cases.any (·.1 == n) do out := out.push s!"oracle row {n} names no case"
  for (n, _) in reviewed do
    unless cases.any (·.1 == n) do out := out.push s!"reviewed row {n} names no case"
  for (n, _) in divergences do
    match cases.find? (·.1 == n), oracle.find? (·.1 == n) with
    | some (_, src), some (_, docs) =>
      if let some l := langOf n then
        if readerDocs l src == docs then
          out := out.push s!"divergence {n} no longer diverges: delete its row"
    | _, _ => out := out.push s!"divergence {n} names no case"
  return out

def classify (cases : Array (String × String)) (oracle : Array (String × Array Doc)) :
    Array (String × String × String) :=
  cases.filterMap fun (n, src) => do
    let l ← langOf n
    let docs := ((oracle.find? (·.1 == n)).map (·.2)).getD #[]
    let (v, note) := verdictOf n (readerDocs l src) docs
    return (n, v, note)

/-- The languages a parser of their own answers for. -/
def oracleLangs : List Ir.CodeLang := [.lean, .python, .bash]

/-- A language's tier item: its listing language, but the shell's and Lean's own names. -/
def langItem (l : Ir.CodeLang) : String :=
  if l == .bash then "shell" else if l == .lean then "lean" else l.listing

def tierRows (rows : Array (String × String × String)) : Array Row :=
  oracleLangs.toArray.flatMap fun l =>
    let mine := rows.filter fun (n, _, _) => langOf n == some l
    #[{ item := s!"{langItem l}.cases", value := (mine.size : Int) },
      { item := s!"{langItem l}.match", value := ((mine.filter (·.2.1 == "match")).size : Int) }]

def provenance (rows : Array (String × String × String)) : Array String :=
  let count (v : String) := (rows.filter (·.2.1 == v)).size
  #[s!"# cases: {rows.size} in {casesDir}; oracle {oraclePath}",
    s!"# verdicts ({verdictPath}): match {count "match"}, divergence {count "divergence"}, \
owed {count "owed"}"]

def selftest : IO UInt32 := tierSelftest "codedoc" fun no => do
  let answers : Array (String × Array Doc) :=
    #[("a.py", #[]), ("", #[]), ("#c.sh", #[{ start := 1, stop := 2, text := "#t" }]),
      ("b.lean", #[{ start := 0, stop := 4, text := "" },
      { start := 5, stop := 9, text := "tab\there\nline\\end" }])]
  no "record: every field, an empty name, text and answer and a leading # included, round-trips"
    ((parseAnswers (renderAnswers answers)).toOption == some answers)
  no "record: a row with a half range is refused" ((parseAnswers "x.py\t1\t\tt\n").toOption.isNone)
  no "record: a case listed with no comment and with one is refused, in either order"
    ((parseAnswers "x.py\t-\nx.py\t1\t2\tt\n").toOption.isNone &&
      (parseAnswers "x.py\t1\t2\tt\nx.py\t-\n").toOption.isNone)
  let src := "def f():\n    \"\"\"Doc.\"\"\"\n"
  let reader := readerDocs .python src
  no s!"comparison: the reader's docstring is the one Python finds ({repr reader})"
    (reader == #[{ start := 13, stop := 23, text := "Doc." }])
  no "comparison: a range one character off is a difference"
    ((verdictOf "x.py" reader #[{ start := 14, stop := 23, text := "Doc." }]).1 == "owed")
  no "comparison: a text one character off is a difference"
    ((verdictOf "x.py" reader #[{ start := 13, stop := 23, text := "Doc" }]).1 == "owed")
  no "comparison: a missing comment is a difference" ((verdictOf "x.py" reader #[]).1 == "owed")
  let faults := tableFaults #[("a.sh", "# x\n"), ("b.py", "")] #[("a.sh", #[]), ("c.py", #[])] #[]
  no s!"tables: a case with no oracle answer, a stray row and an unreviewed shell case fault \
({faults})"
    (faults.contains "case b.py has no oracle answer" && faults.contains "oracle row c.py names no case" &&
      faults.contains "shell case a.sh has no reviewed row")
  no "tables: every divergence names a case that diverges"
    ((tableFaults #[] #[] #[]).size == divergences.length)

def run (args : List String) : IO UInt32 := do
  let cases ← loadCases
  let checking := args.contains "--check"
  let oracle ← if checking then
      match parseAnswers (← IO.FS.readFile oraclePath) with
      | .ok o => pure o
      | .error e => return ← die 1 s!"codedoc: {oraclePath}: {e}"
    else match ← askOracle cases with
      | .ok o => pure o
      | .error e => return ← die 1 s!"codedoc: the oracle did not answer: {e}"
  let reviewed ← match parseAnswers (← IO.FS.readFile reviewedPath) with
    | .ok r => pure r
    | .error e => return ← die 1 s!"codedoc: {reviewedPath}: {e}"
  let shellOracle := oracle.filter (langOf ·.1 == some .bash)
  let faults := tableFaults cases oracle reviewed ++
    (if shellOracle == reviewed.qsort (·.1 < ·.1) then #[] else
      #[s!"the shell rows of {oraclePath} are not {reviewedPath}'s; regenerate"])
  for f in faults do IO.eprintln s!"codedoc: {f}"
  unless faults.isEmpty do return ← die 1 s!"codedoc: {faults.size} table faults"
  let rows := classify cases oracle
  let tier (a : List String) : IO UInt32 :=
    tierMain "codedoc" (.pairs "match" "cases") (pure (provenance rows, tierRows rows)) selftest a
  if checking then
    let committed ← IO.FS.readFile verdictPath
    if committed != renderVerdicts rows then
      for (n, v, _) in rows do
        unless (committed.splitOn "\n").any (·.startsWith s!"{n}\t{v}\t") do
          IO.eprintln s!"codedoc: case {n} is now {v}, which {verdictPath} does not record"
      return ← die 1 s!"codedoc: {verdictPath} is not the verdicts this tree earns; regenerate"
    let rc ← tier ["--check"]
    if rc != 0 then return rc
    IO.println s!"codedoc --check: ok ({rows.size} cases)"
    return 0
  let rc ← tier []
  if rc != 0 then return ← die rc s!"codedoc: the tier was not written, so neither are the tables"
  IO.FS.writeFile oraclePath ("# Each case's documentation comments as its language's own parser \
finds them: case, start, stop, text. Written only by scripts/codedoc.lean.\n# parsers: " ++
    (← parserVersions) ++ "\n" ++ renderAnswers oracle)
  IO.FS.writeFile verdictPath (renderVerdicts rows)
  return 0

def main (args : List String) : IO UInt32 :=
  match args with
  | ["--selftest"] => selftest
  | ["--check"] | [] => run args
  | _ => die 2 "usage: codedoc [--check | --selftest]"
