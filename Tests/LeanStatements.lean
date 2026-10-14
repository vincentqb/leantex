module

public import Tests.Support
public import Tests.CodeDoc
public import LeanTex.Cli.LeanExport

public section

open LeanTex.Core LeanTex.Cli LeanTex.Cli.World

/-! Lean statements, on invented words: a core-only file's committed answer read whole, each view a
directive declares, every listing exact, the table's spellings, and the export's cache as the policy
says. -/

namespace Tests.LeanStatements

def fixture : String := "testdata/codedoc/lean/statements.lean"
def answerFile : String := "testdata/codedoc/lean/statements.answer"

/-- A declaration's statement formulas as TeX source, each with whether a word space follows it. -/
def spacedFormulasOf (facts : LeanFacts.Facts) (name : String) : Array (String × Bool) :=
  match facts.decls.find? (·.name == name) with
  | some d => match d.type with
    | some t => (LeanStatement.statementMath facts d t).map fun (m, spaced) =>
        (Parse.rawSrc (LeanStatement.Math.listRaws {} #[] m.toList), spaced)
    | none => #[]
  | none => #[]

/-- A declaration's statement formulas as TeX source. -/
def formulasOf (facts : LeanFacts.Facts) (name : String) : Array String :=
  (spacedFormulasOf facts name).map (·.1)

/-- A term from its head and arguments, for the table's own cases. -/
def app (c : String) (args : List LeanFacts.Term) : LeanFacts.Term := .apps (.const c) args

def var (i : Nat) : LeanFacts.Term := .apps (.bvar i) []

/-- One formula from a term under bound names, with the binders given. -/
def texOf (t : LeanFacts.Term) (ctx : List String)
    (binders : List (String × Array LeanFacts.Binder) := []) : String :=
  let lk : LeanStatement.Lookup :=
    { binders := fun c => binders.lookup c, shown := id, collectionFirst := true }
  Parse.rawSrc (LeanStatement.Math.listRaws {} #[] (LeanStatement.render lk ctx t).math.toList)

/-- The source line a statement stands just before: the line its declaration's command opens on,
or past the docstring that line opens. -/
def headLine (src : String) (line : Nat) : String :=
  let ls := (src.splitOn "\n").drop (line - 1)
  match ls with
  | first :: _ =>
    if first.trimAscii.toString.startsWith "/--" then
      let rest := ls.dropWhile fun l => (l.splitOn "-/").length < 2
      (rest.drop 1).headD ""
    else first
  | [] => ""

/-- A world for the export's program: files by path, a `lake` on PATH or not, the version the
project's Lean gives, and one reply to every export run. -/
def world (files : List (String × ByteArray)) (lake : Bool) (version : Ended)
    (run : ToolCall → Ended) : (q : Ask) → Reply q
  | .env name => if name == "PATH" then some "/bin" else if name == "HOME" then some "/h" else none
  | .cwd => .ok "/work"
  | .stat path =>
    if (lake && path == "/bin/lake") || files.any (·.1 == path) then
      .ok { kind := .file, size := 0, mtimeSec := 0, mtimeNsec := 0, real := path }
    else .error .absent
  | .metadata _ => .error .absent
  | .readFile path => match files.lookup path with
    | some b => .ok b
    | none => .error .absent
  | .listDir _ => .error .absent
  | .run call => if call.args.contains "--version" then version else run call
  | .writeAtomic _ _ => .ok ()
  | .createDirAll _ => .ok ()

/-- A run that wrote `answer` and exited `code`, saying `out`. -/
def ended (code : Nat) (out : String) (answer : Option ByteArray) : Ended :=
  { ran := .exited code, out, err := "", complete := true, outputs := #[("answer.jsonl", answer)] }

def versionSaid (v : String) : Ended := ended 0 s!"Lean (version {v}, x86_64, commit c, Release)\n" none

def exportRuns (qs : List Ask) : Nat :=
  (qs.filter fun q => match q with
    | .run call => !call.args.contains "--version"
    | _ => false).length

def writes (qs : List Ask) : List String := qs.filterMap fun
  | .writeAtomic path _ => some path
  | _ => none

/-- A page's shipped lines: whether each is set in the typewriter face alone, and its ink. -/
def pageLines (fonts : Font.FontSet) (doc : Ir.Doc) : Array (Bool × String) :=
  (bodyLines (layoutOf fonts doc)).map fun l => (Tests.CodeDoc.monoLine l, lineInk l)

def leanStatementChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let src ← fixtureText fixture
  let answer ← IO.FS.readFile answerFile
  let facts ← match LeanFacts.decode answer with
    | .ok f => pure f
    | .error why => do t s!"statements: the committed answer reads ({why})" false; return
  t "statements: the committed answer holds every declaration the file writes, and the one Lean refused"
    (facts.decls.size == 34 && facts.errors == 4 && facts.failed.map (·.name) == #["refused"])
  let rows := (← IO.FS.readFile "testdata/codedoc/lean/answers.tsv").splitOn "\n"
  t "statements: the committed answer was asked through this export, of this file, by its Lean"
    ((Code.leanImports? src).any fun imports => rows.contains
      s!"statements.lean\t{Flate.contentKey (LeanExport.source imports).toUTF8}\t{Flate.contentKey src.toUTF8}\t{facts.lean}")
  t "statements: the answer carries each declaration's module, signature and proof spans"
    ((facts.decls.find? (·.name == "Tide.height")).any fun d =>
      d.moduleName == "testdata.codedoc.lean.statements" && d.signature == some ((9, 11), (9, 31)) &&
        d.proof == some ((9, 32), (9, 43)))
  t "statements: a declaration under `… in` opens where its outermost `… in` does"
    ((facts.decls.find? (·.name == "Tide.succ_eq")).any fun d => d.head == (56, 0) && d.start == (57, 0))
  t "statements: a theorem resting on an unproved one is unproved, as its own is"
    ((facts.decls.filter (!·.proved)).map (·.name) == #["Tide.placeholder", "Tide.rests", "Tide.unfinished"])
  -- The export's spellings, against the committed answer.
  let spells (name : String) (want : Array String) : IO Unit :=
    t s!"statements: {name} reads {want} ({formulasOf facts name})" (formulasOf facts name == want)
  spells "Tide.height_double" #["\\forall rise,{}", "n\\in \\mathbb {N},", "\\operatorname {height}(rise,{}",
    "2\\cdot {}", "n)={}", "2\\cdot {}", "\\operatorname {height}(rise,{}", "n)"]
  spells "Tide.height_pos" #["0<{}", "rise\\to {}", "0<{}", "n\\to {}", "0<{}",
    "\\operatorname {height}(rise,{}", "n)"]
  spells "Tide.exists_step" #["\\exists n\\in \\mathbb {N},", "n+{}", "2={}", "5"]
  spells "Tide.le_or_gt" #["\\forall a,{}", "b\\in \\mathbb {N},", "a\\leq {}", "b\\lor {}", "b<{}", "a"]
  spells "Tide.swap_and" #["\\forall p,{}", "q\\in \\operatorname {Prop},", "p\\land {}",
    "q\\leftrightarrow {}", "q\\land {}", "p"]
  spells "Tide.not_both" #["\\forall p\\in \\operatorname {Prop},", "\\lnot (p\\land \\lnot p)"]
  spells "Tide.neg_neg'" #["\\forall z\\in \\mathbb {Z},", "-(-z)={}", "z"]
  spells "Tide.pow_succ'" #["\\forall a,{}", "n\\in \\mathbb {N},", "a^{n+1}={}", "a^{n}\\cdot {}", "a"]
  spells "Tide.div_mod" #["\\forall a,{}", "b\\in \\mathbb {N},", "b\\cdot {}", "(a/b)+{}", "a\\bmod {}",
    "b={}", "a"]
  spells "Tide.total" #["\\operatorname {total}:", "α\\to {}", "\\operatorname {List}(α)\\to {}", "α"]
  spells "Tide.strict_hyp" #["(\\forall n\\in \\mathbb {N},n=0)\\to {}", "\\operatorname {False}"]
  spells "Tide.imp_iff" #["\\forall p,{}", "q\\in \\operatorname {Prop},", "p\\to {}", "(q\\leftrightarrow q)"]
  spells "Tide.depth_val" #["\\operatorname {depth}={}", "7"]
  spells "Tide.holds_ex" #["\\operatorname {holds}(\\exists n\\in \\mathbb {N},n=0)"]
  spells "Tide.fixes" #["\\forall f\\in (\\mathbb {N}\\to \\mathbb {N}),", "f(0)={}", "0\\to {}",
    "f(f(0))={}", "0"]
  spells "Tide.iff_nest" #["\\forall p\\in \\operatorname {Prop},", "p\\leftrightarrow {}",
    "(p\\leftrightarrow \\operatorname {True})"]
  spells "Tide.same" #["\\operatorname {same}:", "\\forall α\\in \\operatorname {Type}u,", "α\\to {}", "α"]
  spells "Tide.pos_ne" #["n>{}", "0\\to {}", "n\\neq {}", "0"]
  spells "Tide.nz" #["\\forall n\\in \\mathbb {N},", "\\operatorname {NeZero}(n)\\to {}", "n\\neq {}", "0"]
  spells "Tide.dep_hyp" #["\\forall n\\in \\mathbb {N},", "(h:0<n)\\to {}", "\\operatorname {Fin.val}(",
    "\\operatorname {Fin.mk}(0,{}", "h))={}", "0"]
  spells "Tide.nested_dep" #["\\forall f\\in (\\forall n\\in \\mathbb {N},n>0\\to \\mathbb {N}),",
    "(\\forall n\\in \\mathbb {N},(h:n>0)\\to f(n,h)=n)\\to {}", "f(1,{}", "\\operatorname {Nat.one\\_ pos})={}",
    "1"]
  spells "Tide.chars_len" #["\\operatorname {String.length}(\\text {\"a\\textasciitilde b\\textasciicircum c\\textbackslash \\textbackslash d\\textbackslash n\\textbackslash t\\textbackslash \"\\textbraceleft \\textbraceright \\textunderscore \\# \\textdollar \\% \\& \"})={}", "17"]
  let exImplicit := app "Exists" [app "Nat" [], .lam "n" .explicit (app "Nat" [])
    (.pi "m" .implicit false (app "Nat" []) (app "LE.le" [app "Nat" [], app "instLENat" [], var 0, var 1]))]
  let exDecl : LeanFacts.Decl :=
    { name := "ex_implicit", kind := .theorem, start := (1, 0), stop := (1, 0), type := some exImplicit }
  t "statements: an implicit binder inside an existential's body is a quantifier there, not hidden"
    (((LeanStatement.statementMath facts exDecl exImplicit).map fun (m, _) =>
        Parse.rawSrc (LeanStatement.Math.listRaws {} #[] m.toList)) ==
      #["\\exists n\\in \\mathbb {N},", "\\forall m\\in \\mathbb {N},", "m\\leq {}", "n"])
  t "statements: membership sets its element first, a constant outside the table by its name"
    ((formulasOf facts "Tide.mem_cons").toList.drop 2 == ["x\\in {}", "\\operatorname {List.cons}(x,{}", "xs)"])
  t "statements: a word space follows a quantifier's head and a definition's name alone"
    (facts.decls.all fun d => (spacedFormulasOf facts d.name).all fun (f, spaced) =>
      spaced == (f.endsWith "," || f.endsWith ":"))
  -- The table, where no core file reaches.
  t "statements: the number sets are blackboard letters"
    (["Nat", "Int", "Rat", "Real", "Complex"].map (fun c => texOf (app c []) []) ==
      ["\\mathbb {N}", "\\mathbb {Z}", "\\mathbb {Q}", "\\mathbb {R}", "\\mathbb {C}"])
  t "statements: a sum inside a product is parenthesized, a product inside a sum is not"
    (texOf (app "HMul.hMul" [app "HAdd.hAdd" [var 0, var 1], var 2]) ["c", "b", "a"] ==
        "(c+b)\\cdot a" &&
      texOf (app "HAdd.hAdd" [app "HMul.hMul" [var 0, var 1], var 2]) ["c", "b", "a"] == "c\\cdot b+a")
  t "statements: either side of an equivalence that is one is parenthesized"
    (texOf (app "Iff" [app "Iff" [var 3, var 2], app "Iff" [var 1, var 0]]) ["d", "c", "b", "a"] ==
      "(a\\leftrightarrow b)\\leftrightarrow (c\\leftrightarrow d)")
  t "statements: an argument a constant's binders mark implicit is hidden"
    (texOf (app "f" [app "Nat" [], var 0]) ["x"] [("f", #[.implicit, .explicit])] == "\\operatorname {f}(x)")
  t "statements: a binder among several arguments is parenthesized"
    (texOf (app "g" [.lam "x" .explicit (app "Nat" []) (var 0), var 0]) ["y"] ==
      "\\operatorname {g}((x\\mapsto x),y)")
  t "statements: a name mathematics cannot spell sets as text, subscript digits lower, TeX's own characters escaped"
    (texOf (var 0) ["x₁"] == "x_{1}" && texOf (var 0) ["«odd name»"] == "\\text {«odd name»}" &&
      texOf (.apps (.str "a%b$c") []) [] == "\\text {\"a\\% b\\textdollar c\"}")
  t "statements: a string sets as Lean writes it, its quotes and control characters escaped"
    (texOf (.apps (.str "q\"\n\x01") []) [] ==
      "\\text {\"q\\textbackslash \"\\textbackslash n\\textbackslash x01\"}")
  t "statements: a sort one level up sets as a type of that level, as Lean shows it"
    ((["0", "1", "2", "u + 1", "u + 2", "(max u v) + 1", "u", "max u v"].map fun l =>
        texOf (.apps (.sort l) []) []) ==
      ["\\operatorname {Prop}", "\\operatorname {Type}", "\\operatorname {Type}1",
       "\\operatorname {Type}u", "\\operatorname {Type}(\\text {u + 1})",
       "\\operatorname {Type}\\text {(max u v)}", "\\operatorname {Sort}u",
       "\\operatorname {Sort}(\\text {max u v})"])
  t "statements: a constant shows relative to its declaration's namespace unless two would show alike"
    (LeanStatement.shownNames "A.B.thm" #["A.B.f", "A.g"] "A.B.f" == "f" &&
      LeanStatement.shownNames "A.B.thm" #["A.B.f", "A.g"] "A.g" == "g" &&
      LeanStatement.shownNames "A.thm" #["A.f", "f"] "A.f" == "A.f" &&
      LeanStatement.shownNames "A.thm" #["A.f", "f"] "f" == "f")
  -- The page under each view the directive declares.
  let some text ← loadTestFont "OpenSans-Regular.ttf" | t "statements: the text face loads" false
  let some mono ← loadTestFont "SourceCodePro-Regular.otf" | t "statements: the mono face loads" false
  let fonts ← mathSetOf (slotPairOf 2 text mono)
  let withShow (views : String) : String :=
    "-- leantex: " ++ views ++ "\n" ++ "\n".intercalate ((src.splitOn "\n").drop 1)
  let readWith (views : String) (given : Option LeanFacts.Facts) : Ir.Doc × Array Diag :=
    let (raws, ds) := Surface.readCode .lean "statements.lean" (withShow views) given
    Elab.runRaws "statements.lean" raws ds
  let readAs (views : String) : Ir.Doc × Array Diag := readWith views (some facts)
  let (doc, ds) := readAs "show = math, code"
  let codeOnly := Code.codeOf (Code.segmentsOf .lean src)
  t "statements: the listings hold the file's code exactly, statements between them"
    (String.join ((Tests.CodeDoc.listings doc).toList.map fun (_, c) => (c.drop 1).toString) ==
      String.ofList codeOnly)
  t s!"statements: each statement Lean did not give is named once, in source order ({ds.map (·.subject)})"
    ((ds.filter (·.kind == .W0414)).map (·.subject) == #[some "lean:Tide.placeholder", some "lean:refused"])
  let out := layoutOf fonts doc
  let lines := (bodyLines out).map fun l => (Tests.CodeDoc.monoLine l, lineInk l)
  let shown := facts.decls.filter fun d => (d.type.map (·.elaborated)).getD false
  let opening (ink : String) : List String := (ink.trimAscii.toString.splitOn " ").take 2
  for d in shown do
    let label := s!"{d.kind.label} ({d.name}"
    match lines.findIdx? fun (mono, ink) => !mono && ink.startsWith label with
    | none => t s!"statements: {d.name}'s statement ships" false
    | some i =>
      let next := (lines.extract (i + 1) lines.size).find? (·.1)
      t s!"statements: {d.name}'s statement stands just before its code ({next})"
        (next.any fun (_, ink) => opening ink == opening (headLine src d.head.1))
  t "statements: a theorem Lean holds unproved is marked so"
    (lines.any fun (_, ink) => ink.startsWith "Theorem (Tide.unfinished, unproved).")
  t "statements: a statement Lean did not give does not ship"
    (!lines.any fun (_, ink) => ink.startsWith "Theorem (Tide.placeholder")
  let quoted := "\"a~b^c\\\\d\\n\\t\\\"{}_#$%&\""
  let (charsDoc, charsDs) := readWith "show = math"
    (some { facts with decls := facts.decls.filter (·.name == "Tide.chars_len"), failed := #[] })
  let charsOut := layoutOf fonts charsDoc
  t s!"statements: a string's characters ship as Lean writes them, on the page and in its MathML"
    ((bodyLines charsOut).any (fun l => (lineInk l).startsWith "Theorem (Tide.chars_len)." &&
        ((lineInk l).splitOn quoted).length == 2) &&
      (Tests.CodeDoc.elemTexts "mi" charsDoc).contains quoted &&
      !charsDs.any (·.kind == .W0012) && !charsOut.diags.any (·.kind == .E0405))
  let longAt := lines.findIdx? fun (mono, ink) => !mono && ink.startsWith "Theorem (Tide.long_sum)."
  t s!"statements: a long statement breaks inside its binder group and its equation, every line inside the measure ({out.diags.filter (·.kind == .W0005) |>.map (·.message)})"
    (!out.diags.any (·.kind == .W0005) &&
      longAt.any fun i => (lines[i + 1]?.any fun (mono, ink) => !mono && !ink.startsWith "Theorem"))
  let mathElems := (elemNodesList (· == "math") #[] (docNodesOf doc).toList).size
  t s!"statements: the web page sets every formula as MathML ({mathElems})"
    (mathElems == (shown.toList.map fun d => (formulasOf facts d.name).size).sum)
  let (codeDoc, codeDs) := readAs "show = code"
  t "statements: a page that shows code alone sets no statement and names no loss, whatever Lean said"
    (!(pageLines fonts codeDoc).any (fun (_, ink) => ink.startsWith "Theorem (") &&
      !codeDs.any (·.kind == .W0414))
  let (mathDoc, mathDs) := readAs "show = math"
  let mathLines := pageLines fonts mathDoc
  let fallback := (Tests.CodeDoc.listings mathDoc).map (·.2.trimAscii.toString)
  t s!"statements: a page that shows math alone sets statements, its title, no prose, and the code of each declaration Lean gave no statement for in its place ({fallback})"
    (mathLines.any (fun (_, ink) => ink.startsWith "Theorem (Tide.height_double).") &&
      mathDoc.info.title == some "Tide arithmetic" &&
      !mathLines.any (fun (_, ink) => ink.startsWith "Rising twice") &&
      fallback == #["theorem placeholder (n : Nat) : n = Nat.notAThing n := rfl",
        "theorem refused (n : Nat) : n + (1 : String) = n := rfl"] &&
      (mathDs.filter (·.kind == .W0414)).all fun d => (d.message.splitOn "in its place").length == 2 ||
        (d.message.splitOn "in place of a statement").length == 2)
  let (unansweredDoc, unansweredDs) := readWith "show = math" none
  t "statements: a page that shows math alone shows the file's code when Lean gave no answer"
    ((Tests.CodeDoc.listings unansweredDoc).size == (Tests.CodeDoc.listings codeDoc).size &&
      !(pageLines fonts unansweredDoc).any (fun (_, ink) => ink.startsWith "Theorem (") &&
      !unansweredDs.any (·.kind == .W0414))
  let afterLines := pageLines fonts (readAs "show = code, math").1
  t "statements: code before math sets each statement after its declaration's last line"
    ((afterLines.findIdx? fun (mono, ink) => !mono && ink.startsWith "Theorem (Tide.height_double).").any
      fun i => (afterLines[i - 1]?.map fun (mono, ink) =>
        mono && ink.trimAscii.toString.startsWith "unfold height; exact").getD false)
  let (chosenDoc, chosenDs) := readAs "show = math, code, decls = Tide.height, swap_and, nothere"
  let chosen := (pageLines fonts chosenDoc).filter fun (mono, ink) => !mono && ink.startsWith "Theorem ("
  t s!"statements: decls selects the statements set, and names one Lean does not hold ({chosen.size})"
    ((pageLines fonts chosenDoc).any (fun (_, ink) => ink.startsWith "Definition (Tide.height).") &&
      chosen.size == 1 && chosenDs.any (·.subject == some "lean:nothere"))
  let (proseDoc, proseDs) := readAs "show = prose"
  t "statements: a view the engine does not set is named, and the page shows code"
    (proseDs.any (fun d => d.kind == .W0110 && d.subject == some "code:show:prose") &&
      (pageLines fonts proseDoc).any (·.1))
  -- The answer, read whole or refused whole.
  let refused (body : String) : Bool := (LeanFacts.decode body).toOption.isNone
  let header := "{\"leantex-lean-export\":1,\"lean\":\"4.34.1\",\"errors\":0}\n"
  t "statements: an answer with no declarations reads as none"
    ((LeanFacts.decode (header ++ "{\"leantex-lean-export-end\":0}\n")).toOption.map (·.decls.size) == some 0)
  let record (type : String) : String :=
    header ++ "{\"name\":\"a\",\"module\":\"\",\"kind\":\"theorem\",\"range\":[1,0,1,1],\"head\":[1,0]," ++
      "\"signature\":null,\"proof\":null,\"proved\":true,\"type\":" ++ type ++ "}\n" ++
      "{\"leantex-lean-export-end\":1}\n"
  t "statements: an answer cut short, miscounted, of another schema, with a node read twice or a binder marked neither way is refused"
    (refused header && refused (header ++ "{\"leantex-lean-export-end\":1}\n") &&
      refused ("{\"leantex-lean-export\":2,\"lean\":\"x\",\"errors\":0}\n{\"leantex-lean-export-end\":0}\n") &&
      refused (record "[[\"const\",\"True\"],[\"app\",0,0]]") &&
      refused (record "[[\"const\",\"True\"],[\"const\",\"True\"],[\"pi\",\"x\",\"d\",0,1,2]]") &&
      !refused (record "[[\"const\",\"True\"],[\"const\",\"True\"],[\"pi\",\"x\",\"d\",0,1,1]]"))
  -- The cache, as the policy says.
  let bytes := src.toUTF8
  let program := LeanExport.factsFor "statements.lean" bytes src
  let good := ended 0 "" (some answer.toUTF8)
  let v := versionSaid "4.34.1"
  let cold := world [] true v fun _ => good
  t "cache: a cold file asks Lean once, keeps the answer, and reads it"
    (exportRuns (program.asks cold) == 1 && (writes (program.asks cold)).length == 1 &&
      (program.run cold).1 == some facts)
  let slot := (writes (program.asks cold)).headD ""
  let warm := world [(slot, ConvCache.encode (.ok answer.toUTF8))] true v fun _ => good
  t "cache: a kept answer serves once Lean says who it is, with no export run and the same facts"
    (exportRuns (program.asks warm) == 0 && (program.run warm).1 == some facts)
  let stale := world [(slot, ConvCache.encode (.ok "{\"leantex".toUTF8))] true v fun _ => good
  t "cache: a kept answer this reader no longer reads is asked again, and the new answer kept"
    (exportRuns (program.asks stale) == 1 && (writes (program.asks stale)) == [slot] &&
      (program.run stale).1 == some facts)
  let otherLean := world [] true (versionSaid "4.33.1") fun _ => good
  t "cache: another Lean keeps its answer apart"
    (writes (program.asks otherLean) != writes (program.asks cold))
  let moved := LeanExport.factsFor "elsewhere.lean" bytes src
  t "cache: the same bytes at another path keep their answer apart"
    (writes (moved.asks cold) != writes (program.asks cold))
  let said := "<scratch>/export.lean:2:0: error: unknown module prefix 'Zz'"
  let refusing := world [] true v fun _ => ended 1 said none
  let (none, refusalDs) := program.run refusing | t "cache: a refusal gives no facts" false
  t s!"cache: Lean's refusal of the export is kept and named once in Lean's words ({refusalDs.map (·.message)})"
    ((writes (program.asks refusing)).length == 1 && refusalDs.size == 1 &&
      refusalDs.all fun d => d.kind == .W0414 && (d.message.splitOn "unknown module prefix 'Zz'").length == 2 &&
        (d.message.splitOn "<scratch>").length == 1)
  let replayed := world [(slot, ConvCache.encode (.error "unknown module prefix 'Zz'"))] true v
    fun _ => good
  t "cache: a kept refusal replays the identical note with no export run"
    (exportRuns (program.asks replayed) == 0 &&
      (program.run replayed).2.map (·.message) == refusalDs.map (·.message))
  for (label, reply) in [
      ("a stopped run", { good with ran := .overran 240, outputs := #[("answer.jsonl", none)] }),
      ("a run that never started", { good with ran := .unstarted "spawn failed", outputs := #[("answer.jsonl", none)] }),
      ("an exit the machine forced", ended 137 said none),
      ("an export that could not read or write a file", ended 127 "" none),
      ("a failed exit with no error of the export's", ended 1 "warning: a line\n" none),
      ("a clean exit whose answer does not read", ended 0 "" (some "{\"leantex".toUTF8))] do
    let w := world [] true v fun _ => reply
    t s!"cache: {label} is named and kept nowhere"
      ((writes (program.asks w)).isEmpty && (program.run w).1.isNone && (program.run w).2.size == 1)
  t "cache: the export stops apart, with an exit no refusal reads, when it cannot read the file or write its answer"
    ((LeanExport.program.splitOn "IO.Process.exit 127").length == 3)
  let silent := world [] true (ended 1 "" none) fun _ => good
  t "cache: a Lean that will not say who it is is never asked about the file, and nothing is read or kept"
    (exportRuns (program.asks silent) == 0 && (writes (program.asks silent)).isEmpty &&
      (program.run silent).2.map (·.kind) == #[.W0414])
  let nolake := world [] false v fun _ => good
  t "cache: with no lake on PATH the code stands alone, named once, nothing kept"
    (exportRuns (program.asks nolake) == 0 && (writes (program.asks nolake)).isEmpty &&
      (program.run nolake).2.map (·.kind) == #[.W0414])
  let projectSrc := "import Tide.Base\n" ++ src
  let projectProgram := LeanExport.factsFor "statements.lean" projectSrc.toUTF8 projectSrc
  let unbuilt := world [("/work/lakefile.toml", "name = \"t\"".toUTF8)] true v fun _ => good
  t "cache: a file importing a project module with no build trace is asked, and its answer not kept"
    (exportRuns (projectProgram.asks unbuilt) == 1 && (writes (projectProgram.asks unbuilt)).isEmpty)
  let manifest := "{\"packages\":[{\"name\":\"tidelib\"}]}".toUTF8
  let unfetched := world [("/work/lakefile.toml", "name = \"t\"".toUTF8),
    ("/work/lake-manifest.json", manifest)] true v fun _ => good
  t "cache: a project whose packages are not fetched is not asked"
    (exportRuns (program.asks unfetched) == 0 && (program.run unfetched).2.map (·.kind) == #[.W0414])
  for (name, lakefile) in [("lakefile.toml", "name = \"t\"\n\n[[require]]\nname = \"tidelib\"\n"),
      ("lakefile.lean", "import Lake\nopen Lake DSL\n\nrequire tidelib from git \"../tidelib\"\n")] do
    let unresolved := world [(s!"/work/{name}", lakefile.toUTF8)] true v fun _ => good
    t s!"cache: a project whose {name} requires a package and that has no manifest is not asked, so nothing is fetched"
      (exportRuns (program.asks unresolved) == 0 && (program.asks unresolved).all (fun q => match q with
        | .run _ => false
        | _ => true) && (program.run unresolved).2.map (·.kind) == #[.W0414])

end Tests.LeanStatements
