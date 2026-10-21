module

public import Tests.Support
public import Tests.CodeDoc
public import LeanTex.Cli.LeanFactsFile

public section

open LeanTex.Core LeanTex.Cli LeanTex.Cli.World

/-! Lean statements, on invented words: a core-only file's committed facts read whole, each view a
directive declares, every listing exact, the table's spellings, and the facts file read where the
exporter writes it or a document declares it, never asked of Lean. -/

namespace Tests.LeanStatements

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

/-- A term's formulas standing alone, as TeX source. -/
def piecesOf (t : LeanFacts.Term) (ctx : List String)
    (binders : List (String × Array LeanFacts.Binder) := []) : List String :=
  let lk : LeanStatement.Lookup :=
    { binders := fun c => binders.lookup c, shown := id, collectionFirst := true }
  (LeanStatement.formulasOf lk ctx t).map fun m => Parse.rawSrc (LeanStatement.Math.listRaws {} #[] m.toList)

/-- A run that wrote `answer` and exited `code`, saying `out`. -/
def ended (code : Nat) (out : String) (answer : Option ByteArray) : Ended :=
  { ran := .exited code, out, err := "", complete := true, outputs := #[("answer.jsonl", answer)] }

/-- Whether a program's questions run a tool. -/
def runs (qs : List Ask) : Bool := qs.any fun q => match q with
  | .run _ => true
  | _ => false

def leanStatementChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let src ← fixtureText leanFixture
  let answer ← IO.FS.readFile leanFacts
  let facts ← match LeanFacts.decode answer with
    | .ok f => pure f
    | .error why => do t s!"statements: the committed facts read ({why})" false; return
  t "statements: the committed facts hold every declaration the file writes, and the one Lean refused"
    (facts.decls.size == 39 && facts.errors == 4 && facts.failed.map (·.name) == #["refused"])
  let rows := (← IO.FS.readFile "testdata/codedoc/lean/answers.tsv").splitOn "\n"
  let mut exporter := ""
  for f in ["export/LeantexExport/Program.lean", "export/LeantexExport/Header.lean", "export/Main.lean"] do
    exporter := exporter ++ (← IO.FS.readFile f) ++ "\u0000"
  t "statements: the committed facts were written by this exporter, of this file, by their Lean"
    (rows.contains
      s!"statements.lean\t{Flate.contentKey exporter.toUTF8}\t{Flate.contentKey src.toUTF8}\t{facts.lean}")
  t "statements: the committed facts line up with the file they were written of"
    (LeanFacts.alignedWith facts src)
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
  spells "Tide.height_double" #["\\forall \\mathit {rise},{}", "\\mathit {n}:\\mathbb {N},",
    "\\mathrm {height}\\  \\mathit {rise}\\  (\\mathrm {2}\\cdot \\mathit {n})={}",
    "\\mathrm {2}\\cdot {}", "\\mathrm {height}\\  \\mathit {rise}\\  \\mathit {n}"]
  spells "Tide.height_pos" #["\\mathrm {0}<{}", "\\mathit {rise}\\to {}", "\\mathrm {0}<{}",
    "\\mathit {n}\\to {}", "\\mathrm {0}<{}",
    "\\mathrm {height}\\  \\mathit {rise}\\  \\mathit {n}"]
  spells "Tide.exists_step" #["\\exists \\mathit {n}:\\mathbb {N},", "\\mathit {n}+{}",
    "\\mathrm {2}={}", "\\mathrm {5}"]
  spells "Tide.le_or_gt" #["\\forall \\mathit {a},{}", "\\mathit {b}:\\mathbb {N},",
    "\\mathit {a}\\leq {}", "\\mathit {b}\\lor {}", "\\mathit {b}<{}", "\\mathit {a}"]
  spells "Tide.swap_and" #["\\forall \\mathit {p},{}", "\\mathit {q}:\\mathrm {Prop},",
    "\\mathit {p}\\land {}", "\\mathit {q}\\leftrightarrow {}", "\\mathit {q}\\land {}",
    "\\mathit {p}"]
  spells "Tide.not_both" #["\\forall \\mathit {p}:\\mathrm {Prop},",
    "\\lnot (\\mathit {p}\\land {}", "\\lnot \\mathit {p})"]
  spells "Tide.neg_neg'" #["\\forall \\mathit {z}:\\mathbb {Z},", "-(-\\mathit {z})={}",
    "\\mathit {z}"]
  spells "Tide.pow_succ'" #["\\forall \\mathit {a},{}", "\\mathit {n}:\\mathbb {N},",
    "\\mathit {a}^{\\mathit {n}+\\mathrm {1}}={}", "\\mathit {a}^{\\mathit {n}}\\cdot {}",
    "\\mathit {a}"]
  spells "Tide.div_mod" #["\\forall \\mathit {a},{}", "\\mathit {b}:\\mathbb {N},",
    "\\mathit {b}\\cdot {}", "(\\mathit {a}/\\mathit {b})+{}", "\\mathit {a}\\bmod {}",
    "\\mathit {b}={}", "\\mathit {a}"]
  spells "Tide.total" #["\\mathrm {total}:", "\\mathrm {Add}\\  \\mathit {α}\\to {}",
    "\\mathit {α}\\to {}", "\\mathrm {List}\\  \\mathit {α}\\to {}", "\\mathit {α}"]
  spells "Tide.strict_hyp" #["(\\forall \\mathit {n}:\\mathbb {N},{}", "\\mathit {n}={}",
    "\\mathrm {0})\\to {}", "\\mathrm {False}"]
  spells "Tide.imp_iff" #["\\forall \\mathit {p},{}", "\\mathit {q}:\\mathrm {Prop},",
    "\\mathit {p}\\to {}", "(\\mathit {q}\\leftrightarrow {}", "\\mathit {q})"]
  spells "Tide.depth_val" #["\\mathrm {depth}={}", "\\mathrm {7}"]
  spells "Tide.holds_ex" #["\\mathrm {holds}",
    "(\\exists \\mathit {n}:\\mathbb {N},\\mathit {n}=\\mathrm {0})"]
  spells "Tide.fixes" #["\\forall \\mathit {f}:(\\mathbb {N}\\to \\mathbb {N}),",
    "\\mathit {f}\\  \\mathrm {0}={}", "\\mathrm {0}\\to {}",
    "\\mathit {f}\\  (\\mathit {f}\\  \\mathrm {0})={}", "\\mathrm {0}"]
  spells "Tide.iff_nest" #["\\forall \\mathit {p}:\\mathrm {Prop},",
    "\\mathit {p}\\leftrightarrow {}", "(\\mathit {p}\\leftrightarrow {}", "\\mathrm {True})"]
  spells "Tide.same" #["\\mathrm {same}:", "\\forall \\mathit {α}:\\mathrm {Type}\\  \\mathit {u},",
    "\\mathit {α}\\to {}", "\\mathit {α}"]
  spells "Tide.pos_ne" #["\\mathit {n}>{}", "\\mathrm {0}\\to {}", "\\mathit {n}\\neq {}",
    "\\mathrm {0}"]
  spells "Tide.nz" #["\\forall \\mathit {n}:\\mathbb {N},",
    "\\mathrm {NeZero}\\  \\mathit {n}\\to {}", "\\mathit {n}\\neq {}", "\\mathrm {0}"]
  spells "Tide.dep_hyp" #["\\forall \\mathit {n}:\\mathbb {N},",
    "(\\mathit {h}:\\mathrm {0}<{}", "\\mathit {n})\\to {}",
    "(\\mathrm {Fin.mk}\\  \\mathrm {0}\\  \\mathit {h}).\\mathrm {val}={}", "\\mathrm {0}"]
  spells "Tide.nested_dep" #["\\forall \\mathit {f}:(\\forall \\mathit {n}:\\mathbb {N},\\mathit {n}>\\mathrm {0}\\to \\mathbb {N}),",
    "(\\forall \\mathit {n}:\\mathbb {N},{}", "(\\mathit {h}:\\mathit {n}>{}", "\\mathrm {0})\\to {}",
    "\\mathit {f}\\  \\mathit {n}\\  \\mathit {h}={}", "\\mathit {n})\\to {}",
    "\\mathit {f}\\  \\mathrm {1}\\  \\mathrm {Nat.one\\_pos}={}", "\\mathrm {1}"]
  spells "Tide.chars_len" #["\\text {\"a\\textasciitilde b\\textasciicircum c\\textbackslash \\textbackslash d\\textbackslash n\\textbackslash t\\textbackslash \"\\textbraceleft \\textbraceright \\textunderscore \\#\\textdollar \\%\\&\"}.\\mathrm {length}={}",
    "\\mathrm {17}"]
  let exImplicit := app "Exists" [app "Nat" [], .lam "n" .explicit (app "Nat" [])
    (.pi "m" .implicit false (app "Nat" []) (app "LE.le" [app "Nat" [], app "instLENat" [], var 0, var 1]))]
  let exDecl : LeanFacts.Decl :=
    { name := "ex_implicit", kind := .theorem, start := (1, 0), stop := (1, 0), type := some exImplicit
      prop := true }
  t "statements: an implicit binder inside an existential's body is a quantifier there, not hidden"
    (((LeanStatement.statementMath facts exDecl exImplicit).map fun (m, _) =>
        Parse.rawSrc (LeanStatement.Math.listRaws {} #[] m.toList)) ==
      #["\\exists \\mathit {n}:\\mathbb {N},", "\\forall \\mathit {m}:\\mathbb {N},",
          "\\mathit {m}\\leq {}", "\\mathit {n}"])
  let mathOf (ty : LeanFacts.Term) : Array String :=
    (LeanStatement.statementMath facts { exDecl with type := some ty } ty).map fun (m, _) =>
      Parse.rawSrc (LeanStatement.Math.listRaws {} #[] m.toList)
  let typeSort : LeanFacts.Term := .apps (.sort "1") []
  t "statements: an instance binder at the top is a hypothesis, never hidden"
    (mathOf (.pi "α" .explicit false typeSort (.pi "inst" .inst false (app "Inhabited" [var 0])
        (app "Nonempty" [var 1]))) ==
      #["\\forall \\mathit {α}:\\mathrm {Type},", "\\mathrm {Inhabited}\\  \\mathit {α}\\to {}",
          "\\mathrm {Nonempty}", "\\mathit {α}"])
  t "statements: an implicit binder the rest of the statement never names is shown, not hidden"
    (mathOf (.pi "α" .implicit false typeSort (.pi "a" .implicit false (var 0)
        (app "Nonempty" [var 1]))) == #["\\mathit {α}\\to {}", "\\mathrm {Nonempty}", "\\mathit {α}"] &&
      mathOf (.pi "x" .implicit false (app "Empty" []) (app "False" [])) ==
        #["\\mathrm {Empty}\\to {}", "\\mathrm {False}"])
  t "statements: membership sets its element first, a list's cons as Lean writes it"
    ((formulasOf facts "Tide.mem_cons").toList.drop 2 ==
      ["\\mathit {x}\\in {}", "\\mathit {x}::{}", "\\mathit {xs}"])
  let relSpaces (cs : List (Math.MathClass × Char)) : Array (Array (String × String)) :=
    let body := cs.foldr (fun (k, c) acc => Math.MList.cons (.atom k (.sym c) .nil .nil false) acc) .nil
    (MathMl.formulaKids false body).filterMap fun
      | .elem "mo" attrs _ => some (attrs.filter fun a => a.1 == "lspace" || a.1 == "rspace")
      | _ => none
  let thick := MathMl.measuredEm 5 18
  let nil := MathMl.measuredEm 0 18
  t "statements: a relation spaces on the web as TeX does beside its neighbours, none between two relations or at a formula's edge"
    (relSpaces [(.ord, 'x'), (.rel, ':'), (.rel, ':'), (.ord, 'y')] ==
        #[#[("lspace", thick), ("rspace", nil)], #[("lspace", nil), ("rspace", thick)]] &&
      relSpaces [(.ord, 'x'), (.rel, '='), (.ord, 'y')] == #[#[]] &&
      relSpaces [(.ord, 'x'), (.rel, '=')] == #[#[("lspace", thick), ("rspace", nil)]] &&
      relSpaces [(.ord, 'x'), (.rel, '='), (.bin, '-'), (.ord, 'y')] == #[#[], #[]] &&
      relSpaces [(.rel, '='), (.ord, 'y')] == #[#[("lspace", nil), ("rspace", thick)]] &&
      relSpaces [(.rel, '=')] == #[#[("lspace", nil), ("rspace", nil)]] &&
      relSpaces [(.ord, 'x'), (.rel, '='), (.opening, '(')] == #[#[], #[]] &&
      relSpaces [(.ord, 'x'), (.rel, '='), (.punct, ',')] == #[#[("lspace", thick), ("rspace", nil)], #[]])
  t "statements: a word space follows a quantifier's head and a definition's name alone"
    (facts.decls.all fun d => (spacedFormulasOf facts d.name).all fun (f, spaced) =>
      (f.endsWith "," || f.endsWith ":") → spaced)
  t "statements: an application beside an operator stands whole, its word spaces only where it stands alone"
    (facts.decls.all fun d =>
      let fs := (spacedFormulasOf facts d.name).toList
      (fs.zip fs.tail).all fun ((f, spaced), (g, _)) =>
        spaced && !(f.endsWith "," || f.endsWith ":") → !g.endsWith "{}")
  -- The table, where no core file reaches.
  t "statements: the number sets are blackboard letters"
    (["Nat", "Int", "Rat", "Real", "Complex"].map (fun c => texOf (app c []) []) ==
      ["\\mathbb {N}", "\\mathbb {Z}", "\\mathbb {Q}", "\\mathbb {R}", "\\mathbb {C}"])
  t "statements: a sum inside a product is parenthesized, a product inside a sum is not"
    (texOf (app "HMul.hMul" [app "HAdd.hAdd" [var 0, var 1], var 2]) ["c", "b", "a"] ==
        "(\\mathit {c}+\\mathit {b})\\cdot \\mathit {a}" &&
      texOf (app "HAdd.hAdd" [app "HMul.hMul" [var 0, var 1], var 2]) ["c", "b", "a"] ==
        "\\mathit {c}\\cdot \\mathit {b}+\\mathit {a}")
  t "statements: either side of an equivalence that is one is parenthesized"
    (texOf (app "Iff" [app "Iff" [var 3, var 2], app "Iff" [var 1, var 0]]) ["d", "c", "b", "a"] ==
      "(\\mathit {a}\\leftrightarrow \\mathit {b})\\leftrightarrow (\\mathit {c}\\leftrightarrow \\mathit {d})")
  t "statements: an argument a constant's binders mark implicit is hidden"
    (texOf (app "f" [app "Nat" [], var 0]) ["x"] [("f", #[.implicit, .explicit])] ==
      "\\mathrm {f}\\  \\mathit {x}")
  t "statements: a function among several arguments is parenthesized"
    (texOf (app "g" [.lam "x" .explicit (app "Nat" []) (var 0), var 0]) ["y"] ==
      "\\mathrm {g}\\  (\\mathit {x}\\mapsto \\mathit {x})\\  \\mathit {y}")
  t "statements: a name mathematics cannot spell sets as text, subscript digits lower, TeX's own characters escaped"
    (texOf (var 0) ["x₁"] == "\\mathit {x}_{1}" && texOf (var 0) ["«odd name»"] == "\\text {«odd name»}" &&
      texOf (.apps (.str "a%b$c") []) [] == "\\text {\"a\\%b\\textdollar c\"}")
  let listBinders := [("List.cons", #[LeanFacts.Binder.implicit, .explicit, .explicit]),
    ("List.nil", #[LeanFacts.Binder.implicit])]
  let nat := app "Nat" []
  t "statements: a list down to its end sets as a literal, a list with an open tail by its cons"
    (texOf (app "List.cons" [nat, var 0, app "List.cons" [nat, var 1, app "List.nil" [nat]]])
        ["a", "b"] listBinders == "[\\mathit {a},\\mathit {b}]" &&
      texOf (app "List.nil" [nat]) [] listBinders == "[]" &&
      texOf (app "List.cons" [nat, var 1, var 0]) ["xs", "x"] listBinders ==
        "\\mathit {x}::\\mathit {xs}")
  t "statements: a list literal standing alone breaks after each comma, the comma spaced as punctuation"
    (piecesOf (app "List.cons" [nat, var 0, app "List.cons" [nat, var 1, app "List.nil" [nat]]])
        ["a", "b"] listBinders == ["[\\mathit {a},{}", "\\mathit {b}]"] &&
      piecesOf (app "List.nil" [nat]) [] listBinders == ["[]"])
  let p (i : Nat) := app "P" [var i]
  t "statements: a negation, a quantifier and a named hypothesis inside an operator break inside their parentheses after a connective or a binder's head, a relation or an application whole"
    (piecesOf (app "Not" [app "And" [var 0, app "And" [var 1, var 2]]]) ["c", "b", "a"] ==
        ["\\lnot (\\mathit {c}\\land {}", "\\mathit {b}\\land {}", "\\mathit {a})"] &&
      piecesOf (.pi "h" .explicit false (.pi "n" .explicit false nat (p 0)) (app "Q" [])) [] ==
        ["(\\forall \\mathit {n}:\\mathbb {N},{}", "\\mathrm {P}\\  \\mathit {n})\\to {}",
          "\\mathrm {Q}"] &&
      piecesOf (.pi "h" .explicit true (app "And" [var 0, var 1]) (app "Q" [var 0])) ["b", "a"] ==
        ["(\\mathit {h}:\\mathit {b}\\land {}", "\\mathit {a})\\to {}",
          "\\mathrm {Q}\\  \\mathit {h}"])
  let sum : LeanFacts.Term := (List.range 6).foldl (fun acc i => app "HAdd.hAdd" [acc, var (i % 2)]) (var 0)
  t "statements: a long relation inside parentheses breaks after its symbol, its sums whole"
    ((piecesOf (.pi "h" .explicit false (.pi "g" .explicit false (app "Eq" [sum, sum]) (app "P" []))
      (app "Q" [])) ["a", "b"]).length == 4)
  let opensAt (f : String) : Bool :=
    let f := ((f.trimAsciiEnd.toString.dropSuffix "{}").toString.dropSuffix "\\").toString.trimAsciiEnd.toString
    f.endsWith "(" || f.endsWith "["
  let probes : List LeanFacts.Term :=
    [app "Not" [app "Or" [p 0, app "Not" [app "And" [p 0, p 0]]]],
     .pi "h" .explicit false (app "Exists" [nat, .lam "n" .explicit nat (app "And" [p 0, p 0])])
       (app "Not" [app "Iff" [p 0, app "Not" [p 0]]]),
     app "g" [.lam "x" .explicit nat (app "Or" [p 0, p 0]), var 0]]
  t "statements: no formula of a statement or a term ends on an opening bracket or opens on a closing one"
    (((facts.decls.toList.map fun d => (formulasOf facts d.name).toList) ++
        probes.map (piecesOf · ["x"])).all fun fs =>
      fs.all fun f => !opensAt f && !f.startsWith ")" && !f.startsWith "]" && !f.isEmpty)
  t "statements: a function's name its body never reads sets as an underscore"
    (texOf (app "g" [.lam "x" .explicit nat (app "Nat.zero" [])]) [] ==
      "\\mathrm {g}\\  (\\_\\mapsto \\mathrm {Nat.zero})")
  t "statements: a string sets as Lean writes it, its quotes and control characters escaped"
    (texOf (.apps (.str "q\"\n\x01") []) [] ==
      "\\text {\"q\\textbackslash \"\\textbackslash n\\textbackslash x01\"}")
  t "statements: a sort one level up sets as a type of that level, as Lean shows it"
    ((["0", "1", "2", "u + 1", "u + 2", "(max u v) + 1", "u", "max u v"].map fun l =>
        texOf (.apps (.sort l) []) []) ==
      ["\\mathrm {Prop}", "\\mathrm {Type}", "\\mathrm {Type}\\  \\mathrm {1}",
       "\\mathrm {Type}\\  \\mathit {u}", "\\mathrm {Type}\\  (\\text {u + 1})",
       "\\mathrm {Type}\\  \\text {(max u v)}", "\\mathrm {Sort}\\  \\mathit {u}",
       "\\mathrm {Sort}\\  (\\text {max u v})"])
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
    Elab.runKept "statements.lean" raws ds
  let readAs (views : String) : Ir.Doc × Array Diag := readWith views (some facts)
  let (doc, ds) := readAs "show = math, code"
  let codeOnly := Code.codeOf (Code.segmentsOf .lean src)
  t "statements: the listings hold the file's code exactly, statements between them"
    (String.join ((listings doc).toList.map fun (_, c) => (c.drop 1).toString) ==
      String.ofList codeOnly)
  t s!"statements: each statement Lean did not give is named once, in source order ({ds.map (·.subject)})"
    ((ds.filter (·.kind == .W0414)).map (·.subject) == #[some "lean:Tide.placeholder", some "lean:refused"])
  let out := layoutOf fonts doc
  let lines := (bodyLines out).map fun l => (monoLine l, lineInk l)
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
    (!(codePageLines fonts codeDoc).any (fun (_, ink) => ink.startsWith "Theorem (") &&
      !codeDs.any (·.kind == .W0414))
  let (mathDoc, mathDs) := readAs "show = math"
  let mathLines := codePageLines fonts mathDoc
  let fallback := (listings mathDoc).map (·.2.trimAscii.toString)
  t s!"statements: a page that shows math alone sets statements, its title, each declaration's documentation just above its statement, and the code of each declaration its facts give no statement for in its place ({fallback})"
    (mathLines.any (fun (_, ink) => ink.startsWith "Theorem (Tide.height_double).") &&
      mathDoc.info.title == some "Tide arithmetic" &&
      (match mathLines.findIdx? (fun (_, ink) => ink.startsWith "Rising twice"),
          mathLines.findIdx? (fun (_, ink) => ink.startsWith "Theorem (Tide.height_double).") with
        | some i, some j => i + 1 == j
        | _, _ => false) &&
      fallback == #["theorem placeholder (n : Nat) : n = Nat.notAThing n := rfl",
        "theorem refused (n : Nat) : n + (1 : String) = n := rfl"] &&
      (mathDs.filter (·.kind == .W0414)).all fun d => d.subject.any (·.startsWith "lean:"))
  let (unansweredDoc, unansweredDs) := readWith "show = math" none
  t "statements: a page that shows math alone shows the file's code when it has no facts"
    ((listings unansweredDoc).size == (listings codeDoc).size &&
      !(codePageLines fonts unansweredDoc).any (fun (_, ink) => ink.startsWith "Theorem (") &&
      !unansweredDs.any (·.kind == .W0414))
  let afterLines := codePageLines fonts (readAs "show = code, math").1
  t "statements: code before math sets each statement after its declaration's last line"
    ((afterLines.findIdx? fun (mono, ink) => !mono && ink.startsWith "Theorem (Tide.height_double).").any
      fun i => (afterLines[i - 1]?.map fun (mono, ink) =>
        mono && ink.trimAscii.toString.startsWith "unfold height; exact").getD false)
  let (chosenDoc, chosenDs) := readAs "show = math, code, decls = Tide.height, swap_and, nothere"
  let chosen := (codePageLines fonts chosenDoc).filter fun (mono, ink) => !mono && ink.startsWith "Theorem ("
  t s!"statements: decls selects the statements set, and names one Lean does not hold ({chosen.size})"
    ((codePageLines fonts chosenDoc).any (fun (_, ink) => ink.startsWith "Definition (Tide.height).") &&
      chosen.size == 1 && chosenDs.any (·.subject == some "code:decls:nothere"))
  let (unknownDoc, unknownDs) := readAs "show = summary"
  t "statements: a view the engine does not set is named, and the page shows code"
    (unknownDs.any (fun d => d.kind == .W0110 && d.subject == some "code:show:summary") &&
      (codePageLines fonts unknownDoc).any (·.1))
  -- The facts, read whole or refused whole.
  let refused (body : String) : Bool := (LeanFacts.decode body).toOption.isNone
  let header := "{\"leantex-lean-export\":3,\"lean\":\"4.34.1\",\"errors\":0}\n"
  let tail (n : Nat) : String := s!"\{\"leantex-lean-export-end\":{n}}\n"
  let ended0 := tail 0
  let ended1 := tail 1
  t "statements: facts with no declarations read as none"
    ((LeanFacts.decode (header ++ ended0)).toOption.map (·.decls.size) == some 0)
  let record (type : String) : String :=
    header ++ "{\"name\":\"a\",\"module\":\"\",\"kind\":\"theorem\",\"range\":[1,0,1,1],\"head\":[1,0]," ++
      "\"signature\":null,\"proof\":null,\"proved\":true,\"prop\":true," ++
      "\"type\":" ++ type ++ "}\n" ++ ended1
  t "statements: facts cut short, miscounted, of another schema, with a node read twice or a binder marked neither way are refused"
    (refused header && refused (header ++ ended1) &&
      refused ("{\"leantex-lean-export\":2,\"lean\":\"x\",\"errors\":0}\n" ++ ended0) &&
      refused (header ++ "{\"leantex-lean-export-end\":\"0\"}\n") &&
      refused (record "[[\"const\",\"True\"],[\"app\",0,0]]") &&
      refused (record "[[\"const\",\"True\"],[\"const\",\"True\"],[\"pi\",\"x\",\"d\",0,1,2]]") &&
      !refused (record "[[\"const\",\"True\"],[\"const\",\"True\"],[\"pi\",\"x\",\"d\",0,1,1]]"))
  -- The facts file, where the exporter writes it or the document declares it.
  let facts3 := answer.toUTF8
  let lakefile := ("/work/lakefile.toml", "name = \"t\"".toUTF8)
  let standard := ("/work/.lake/build/leantex/statements.facts", facts3)
  let program := LeanFactsFile.factsFor "statements.lean" src none
  let found := factsWorld [lakefile, ("/work/statements.lean", src.toUTF8), standard]
  t "facts: a file's facts are read from beneath its project's .lake/build/leantex, the path read named, and nothing runs"
    ((program.run found).1 == some facts && (program.run found).2.1.isEmpty &&
      (program.run found).2.2 == some "/work/.lake/build/leantex/statements.facts" &&
      !runs (program.asks found))
  let declared := LeanFactsFile.factsFor "proj/statements.lean" src (some "out/tide.facts")
  let elsewhere := factsWorld [("/work/proj/lakefile.toml", "name = \"t\"".toUTF8),
    ("/work/proj/.lake/build/leantex/statements.facts", "{}".toUTF8), ("/work/out/tide.facts", facts3)]
  t "facts: a declared facts file is read in place of the exporter's, where its document places it"
    ((declared.run elsewhere).1 == some facts && (declared.run elsewhere).2.1.isEmpty &&
      (declared.run elsewhere).2.2 == some "/work/out/tide.facts" && !runs (declared.asks elsewhere))
  let none0 := factsWorld [lakefile]
  let absent := (program.run none0).2.1
  t s!"facts: with no facts file the page sets its code, and one note names the exporter to run on the file ({absent.map (·.help)})"
    ((program.run none0).1.isNone && absent.map (·.kind) == #[.N0032] &&
      absent.all (fun d => d.help.any (hasStr · "lake exe leantex-export /work/statements.lean")) &&
      (program.run none0).2.2.isNone && !runs (program.asks none0))
  let declaredAbsent := (declared.run (factsWorld [("/work/proj/lakefile.toml", "".toUTF8)])).2.1
  t "facts: a declared facts file absent names the exporter and the copy that puts its facts there"
    (declaredAbsent.map (·.kind) == #[.N0032] && declaredAbsent.all fun d => d.help.any fun h =>
      hasStr h "lake exe leantex-export /work/proj/statements.lean" &&
        hasStr h "copy '/work/proj/.lake/build/leantex/statements.facts' to the declared path")
  -- What lines up: each command the exporter read, as it read it, and where the source ends.
  let stale (text : String) : Bool :=
    !LeanFacts.alignedWith facts text &&
      ((LeanFactsFile.factsFor "statements.lean" text none).run found).2.1.map (·.kind) == #[.W0433]
  t "facts: facts that line up with the file are read, and every declaration lies in a command they quote"
    (LeanFacts.alignedWith facts src && !facts.commands.isEmpty)
  t "facts: a line added since the export no longer lines up, named once, and its code stands"
    (stale ("-- a line added after the export\n" ++ src))
  let inPlace := [("theorem height_double", "theorem height_dpuble"),
    ("(hr : 0 < rise) (hn : 0 < n) : 0 < height rise n", "(hr : 1 < rise) (hn : 0 < n) : 0 < height rise n"),
    ("exact Nat.mul_pos hr hn", "exact Nat.mul_pos hr  hn"), ("universe u", "universe v"),
    ("open Nat in\ntheorem succ_pos'", "open Int in\ntheorem succ_pos'")]
  t "facts: a name, a statement or a proof edited in place, or a command a statement reads, no longer lines up"
    (inPlace.all fun (a, b) => src.replace a b != src && stale (src.replace a b))
  let untouched := [("Invented facts about tides", "Invented notes on tides!"),
    ("-- leantex: show = math, code", "-- leantex: show = prose, code"),
    ("rise * n\n\n/-- Rising", "rise * n\n-- a note on a blank line\n/-- Rising"),
    ("end Tide\n", "end Tide\n-- a closing note\n/- and a block one -/\n")]
  t "facts: a module's documentation or a comment edited or added within its lines still lines up"
    (untouched.all fun (a, b) => src.replace a b != src && LeanFacts.alignedWith facts (src.replace a b))
  let between := [("rise * n\n\n/-- Rising", "rise * n\nvariable (k : Nat)\n/-- Rising"),
    ("\n\ntheorem exists_step : ∃ n : Nat, n + 2 = 5 := ⟨3, rfl⟩\n\n",
      "\n/-\ntheorem exists_step : ∃ n : Nat, n + 2 = 5 := ⟨3, rfl⟩\n-/\n"),
    ("end Tide\n", "end Tide\ntheorem extra : True := trivial\n")]
  t "facts: a command written between the quoted ones, after them, or a quoted one commented out no longer lines up"
    (between.all fun (a, b) => src.replace a b != src && stale (src.replace a b))
  let exitOnly : LeanFacts.Facts :=
    { lean := "4.34.1", errors := 0, decls := #[], binders := #[]
      commands := #[{ start := (1, 0), stop := (1, 5), text := "#exit" }] }
  t "facts: nothing after a quoted #exit is read, and the commands before it are"
    (LeanFacts.alignedWith exitOnly "#exit\nanything at all := after it\n" &&
      !LeanFacts.alignedWith exitOnly "x\n#exit\n")
  let gap (s : String) : Bool := LeanFacts.trivia s.toList.toArray 0 s.length
  t "facts: white space and comments, nested block comments read, are all that stands between commands"
    (gap " \n-- a\n/- b /- c -/ d -/\t\n" && gap "" && !gap "/- open" && !gap "/- a -/ x" &&
      !gap "- -" && gap "/-! a module's words -/ /-- a doc -/")
  let renamed := src.replace "theorem height_double" "theorem height_dpuble"
  t "facts: a declaration renamed in place no longer lines up, though every span keeps its length"
    (renamed.length == src.length && !LeanFacts.alignedWith facts renamed)
  let shifted : LeanFacts.Facts := { facts with
    commands := facts.commands.map fun c => { c with start := (c.start.1, c.start.2 + 400) } }
  t "facts: a command placed past its line's end does not line up"
    (!LeanFacts.alignedWith shifted src)
  let uncovered : LeanFacts.Facts :=
    { facts with commands := facts.commands.filter fun c => !hasStr c.text "def height" }
  t "facts: a declaration no quoted command holds does not line up"
    (uncovered.commands.size + 1 == facts.commands.size && !LeanFacts.alignedWith uncovered src)
  let old := factsWorld [lakefile, ("/work/.lake/build/leantex/statements.facts",
    ("{\"leantex-lean-export\":2,\"lean\":\"4.34.1\",\"errors\":0}\n" ++ ended0).toUTF8)]
  let oldDs := (program.run old).2.1
  t s!"facts: facts of an older schema are named, the exporter's update named, and the code stands ({oldDs.map (·.message)})"
    ((program.run old).1.isNone && oldDs.map (·.kind) == #[.W0433] &&
      oldDs.all fun d => d.help.any (hasStr · "lake update leantex-export"))
  let newer := factsWorld [lakefile, ("/work/.lake/build/leantex/statements.facts",
    ("{\"leantex-lean-export\":4,\"lean\":\"4.34.1\",\"errors\":0}\n" ++ ended0).toUTF8)]
  let newerDs := (program.run newer).2.1
  t "facts: facts of a newer schema name leantex's update or the exporter's pin, never the exporter's update"
    ((program.run newer).1.isNone && newerDs.map (·.kind) == #[.W0433] &&
      newerDs.all fun d => d.help.any fun h => hasStr h "update leantex" && !hasStr h "lake update")
  let torn := factsWorld [lakefile, ("/work/.lake/build/leantex/statements.facts",
    (facts3.extract 0 (facts3.size / 2)))]
  t "facts: facts cut short are named as not reading, the exporter to run again named, and the code stands"
    ((program.run torn).1.isNone && (program.run torn).2.1.map (·.kind) == #[.W0433] &&
      (program.run torn).2.1.all fun d => d.help.any (hasStr · "again in a project that requires"))

end Tests.LeanStatements
