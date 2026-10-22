module

public import Tests.Support
public import Tests.Diag
public import LeanTex.Core.LeanProseContract

public section

open LeanTex.Core LeanTex.Core.LeanProse Prose

/-! Lean statements in words, on invented words: each sentence of the committed answer and of
random statements over the core table reads back as its statement, each placement a directive
declares holds on the page and on the web page, and a declared phrase is taken or refused by name. -/

namespace Tests.LeanProse

/-- The table of an invented file declaring a phrase and a relation of its own. -/
def phrasedTable (_ : Unit) : Table :=
  (tableFor (factsWith #[("Tide.height", #[.explicit, .explicit]), ("Tide.Calm", #[.explicit])])
    [("Tide.height", "the height after #2 steps of #1"), ("Calm", "#1 is calm")]).table

/-- The words a statement's sentence sets, in order, as the page sets them: the one it opens on,
past the blocks it opens in, capitalized. -/
def sentenceWords (s : Stmt Leaf) : List String :=
  let toks := (render s).filter fun
    | .indent | .dedent | .item => false
    | .w _ | .leaf _ | .bind _ => true
  let capital := match toks with
    | .w _ :: _ => true
    | _ => false
  match toks.filterMap (fun | .w w => some w | .leaf _ | .bind _ | .indent | .dedent | .item => none) with
  | w :: rest => (if capital then w.capitalize else w) :: rest
  | [] => []

/-- Equality's leading binders, as a facts file gives them. -/
def eqBinders : Array (String × Array LeanFacts.Binder) := #[("Eq", #[.implicit, .explicit, .explicit])]

/-- Whether `words` occur in `text` in order. -/
def inOrder (text : String) : List String → Bool
  | [] => true
  | w :: rest => match text.splitOn w with
    | _ :: after :: more => inOrder (w.intercalate (after :: more)) rest
    | _ => false

/-- A page's paragraph for a declaration: its shipped lines from the head through the line before
the next listing or paragraph head, joined. -/
def paragraphOf (lines : Array (Bool × String)) (label : String) : Option String :=
  (lines.findIdx? fun (mono, ink) => !mono && ink.startsWith label).map fun i =>
    let rest := (lines.extract (i + 1) lines.size).toList.takeWhile fun (mono, ink) =>
      !mono && !ink.startsWith "Theorem (" && !ink.startsWith "Definition ("
    " ".intercalate ((lines[i]?.map (·.2)).getD "" :: rest.map (·.2))

def leanProseChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let src ← fixtureText leanFixture
  let facts ← match LeanFacts.decode (← IO.FS.readFile leanFacts) with
    | .ok f => pure f
    | .error why => do t s!"prose: the committed answer reads ({why})" false; return
  -- The round trip, over the committed answer and over random statements.
  let core := coreTable facts.collectionFirst
  let said := facts.decls.filterMap fun d => match d.type with
    | some ty => if ty.elaborated then some (d, proseOf facts core d ty) else none
    | none => none
  t "prose: every statement of the committed answer said in words reads back as itself"
    (said.all fun (_, r) => match r with
      | .ok s => parse core.lexicon (render s) == some s
      | .error _ => true)
  let unsaid := said.filterMap fun (d, r) => match r with
    | .ok _ => none
    | .error u => some (d.name, u)
  let expected : List (String × Unsaid) := [("Tide.depth", .notProp), ("Tide.dep_hyp", .named "h"),
    ("Tide.height", .notProp), ("Tide.nested_dep", .named "h"),
    ("Tide.same", .notProp), ("Tide.total", .notProp)]
  t s!"prose: the statements words cannot say are the definitions' and those naming a hypothesis ({unsaid.map (·.1)})"
    (unsaid.size == expected.length && expected.all unsaid.contains)
  t "evidence: the core table's lexicon and a page's with declared phrases are well formed"
    (core.lexicon.wf && (phrasedTable ()).lexicon.wf && (phrasedTable ()).phrases.length == 1 &&
      (phrasedTable ()).rels.length == (coreRels true).length + 1)
  let mut seed : UInt64 := 0x9E3779B97F4A7C15
  let mut failed : Array String := #[]
  for _ in [0:600] do
    let (s, next) := randStmt (phrasedTable ()) 4 seed
    seed := next
    unless s.ok (phrasedTable ()).lexicon && parse (phrasedTable ()).lexicon (render s) == some s &&
        !opensOnBlock (render s) do
      failed := failed.push (showToks leafWord (render s))
  t s!"evidence: 600 random statements over the core table and declared phrases read back, no list item opening on a block but a nested list ({failed.toList.take 2})"
    failed.isEmpty
  let mut listed : Array String := #[]
  let mut okLists := 0
  for _ in [0:200] do
    let (a, s1) := randStmt (phrasedTable ()) 3 seed
    let (b, s2) := randStmt (phrasedTable ()) 3 s1
    let (c, s3) := randStmt (phrasedTable ()) 3 s2
    seed := s3
    let l : Stmt Leaf := .tfae (.conj a (.conj b c))
    for s in [l, .imp l a, .conj a l, .all (randBinder s3).1 l, .iff a l] do
      if s.ok (phrasedTable ()).lexicon then
        okLists := okLists + 1
        unless parse (phrasedTable ()).lexicon (render s) == some s do
          listed := listed.push (showToks leafWord (render s))
  t s!"evidence: {okLists} of 1000 random statements holding a list of three or more equivalent ones read back from their tokens wherever the list stands ({listed.toList.take 2})"
    (listed.isEmpty && okLists ≥ 900)
  let prop : LeanFacts.Term := .apps (.sort "0") []
  let tfaeOver (xs : List LeanFacts.Term) : LeanFacts.Term := .apps (.const "List.TFAE")
    [xs.foldr (fun x acc => .apps (.const "List.cons") [prop, x, acc]) (.apps (.const "List.nil") [prop])]
  let sayTy (ty : LeanFacts.Term) := proseOf (factsWith #[]) (coreTable true) (theoremAt "tt" 2 ty) ty
  let truth : LeanFacts.Term := .apps (.const "True") []
  t "prose: a list of three equivalent statements says them as a list, of two as an equivalence, and one it cannot say or a last conjunction leaves the list a formula"
    ((match sayTy (tfaeOver [truth, truth, truth]) with
        | .ok (.tfae _) => true
        | _ => false) &&
      (match sayTy (tfaeOver [truth, truth]) with
        | .ok (.iff _ _) => true
        | _ => false) &&
      (match sayTy (tfaeOver [truth, .lam "x" .explicit prop (.apps (.bvar 0) []), truth]) with
        | .ok (.atom _) => true
        | _ => false) &&
      (match sayTy (tfaeOver [truth, truth, .apps (.const "And") [truth, truth]]) with
        | .ok (.atom _) => true
        | _ => false))
  let nat : LeanFacts.Term := .apps (.const "Nat") []
  let calmOf (k : Nat) : LeanFacts.Term := .apps (.const "Tide.Calm") [.apps (.bvar k) []]
  let calmFacts := factsWith #[("Tide.height", #[.explicit, .explicit]), ("Tide.Calm", #[.explicit])]
  let sayCalm (ty : LeanFacts.Term) := proseOf calmFacts (phrasedTable ()) (theoremAt "tt" 2 ty) ty
  let calmT := ((phrasedTable ()).rels.lookup "Tide.Calm").getD ⟨[]⟩
  t "prose: a hypothesis about the bound name alone, through a relation of words, reads as a relative clause, under a quantifier and an existential, and one about another term, a symbolic one or one whose name joins the binder before as a conditional"
    ((match sayCalm (.pi "x" .explicit false nat (.pi "h" .explicit true (calmOf 0) truth)) with
        | .ok (.allThat g r [] (.atom _)) => r == calmT && g.names.length == 1
        | _ => false) &&
      (match sayCalm (.apps (.const "Exists") [nat,
          .lam "x" .explicit nat (.apps (.const "And") [calmOf 0, truth])]) with
        | .ok (.exThat g r [] (.atom _)) => r == calmT && g.names.length == 1
        | _ => false) &&
      (match sayCalm (.pi "y" .explicit false nat (.pi "x" .explicit false nat
          (.pi "h" .explicit true (calmOf 0) truth))) with
        | .ok (.all b (.imp (.rel r _) _)) => r == calmT && b.first.names.length == 2
        | _ => false) &&
      (match sayCalm (.pi "x" .explicit false nat (.pi "h" .explicit true
          (.apps (.const "Eq") [nat, .apps (.bvar 0) [], .apps (.bvar 0) []]) truth)) with
        | .ok (.all _ (.imp _ _)) => true
        | _ => false) &&
      (match sayCalm (.pi "x" .explicit false nat (.pi "h" .explicit true
          (.apps (.const "Tide.Calm") [.apps (.const "Nat.zero") []]) truth)) with
        | .ok (.all ..) => true
        | _ => false))
  let calmTy : LeanFacts.Term := .pi "x" .explicit false nat prop
  let calmDef : LeanFacts.Decl := { theoremAt "Tide.Calm" 2 calmTy with
    kind := .definition, prop := false, value := some (.lam "x" .explicit nat truth) }
  t "prose: a predicate's definition whose value the facts give says its defining equivalence, one without is not said"
    ((match proseOf calmFacts (phrasedTable ()) calmDef calmTy with
        | .ok (.all _ (.iff (.rel r _) (.atom _))) => r == calmT
        | _ => false) &&
      (match proseOf calmFacts (phrasedTable ()) { calmDef with value := none } calmTy with
        | .error .notProp => true
        | _ => false) &&
      (match proseOf calmFacts (phrasedTable ()) { calmDef with value := some (.lam "x" .explicit nat
          (.apps (.const "Tide.Calm.match_1") [.apps (.bvar 0) []])) } calmTy with
        | .error .notProp => true
        | _ => false))
  let proofTy : LeanFacts.Term := .pi "x" .explicit false nat (.pi "h" .explicit true (calmOf 0) prop)
  let implicitTy : LeanFacts.Term := .pi "x" .implicit false nat prop
  t "prose: a predicate's definition taking a proof is not said, one taking an implicit argument is"
    ((match proseOf calmFacts (phrasedTable ()) { calmDef with value := some (.lam "x" .explicit nat
          (.lam "h" .explicit (calmOf 0) truth)) } proofTy with
        | .error .notProp => true
        | _ => false) &&
      (match proseOf calmFacts (phrasedTable ()) { calmDef with value := some (.lam "x" .implicit nat
          truth) } implicitTy with
        | .ok _ => true
        | _ => false))
  let glossFacts := { calmFacts with decls := #[calmDef] }
  let xLeaf := LeanProse.nameLeaf "x"
  let calmOn (n : Leaf) : Stmt Leaf := .rel calmT [.leaf n]
  let glossText (s : Stmt Leaf) : String :=
    Parse.rawSrc (Code.glossaryRaws glossFacts (phrasedTable ()) s {})
  let glossBoth := LeanProse.glossaryToks [([], (.atom "p" : Stmt String),
    .conj (.all ⟨⟨["n"], "N", false⟩, []⟩ (.atom "q")) (.ex ⟨⟨["m"], "N", false⟩, []⟩ (.atom "r"))),
    ([], .atom "s", .atom "u")]
  t "prose: a glossary says what a predicate a statement's words use means, keeping its quantifier where the statement binds its name, entries apart by semicolons, a meaning never a list"
    (hasStr (glossText (calmOn (LeanProse.nameLeaf "y"))) "means" &&
      !hasStr (glossText (calmOn (LeanProse.nameLeaf "y"))) "every" &&
      hasStr (glossText (.all ⟨⟨[xLeaf], [LeanStatement.opMath "N"], false⟩, []⟩ (calmOn xLeaf))) "for every" &&
      !hasStr (glossText (.all ⟨⟨[xLeaf], [LeanStatement.opMath "N"], false⟩, []⟩ (calmOn xLeaf))) "For" &&
      (glossText (.atom xLeaf)).isEmpty &&
      (LeanProse.glossaryToks [([], (.atom "p" : Stmt String), .atom "q"), ([], .atom "r", .atom "s")]).contains (.w ";") &&
      glossBoth.contains (.w ";") && !glossBoth.contains .item)
  t "prose: the glossary key reads where or none, any other value unread"
    ((Code.showingOfValues .lean [("glossary", "where")]).glossary &&
      !(Code.showingOfValues .lean [("glossary", "none")]).glossary &&
      !(Code.showingOfValues .lean []).glossary &&
      (Code.showingOfValues .lean [("glossary", "sometimes")]).unread.contains ("glossary", "sometimes"))
  -- Declared phrases, taken or refused by name.
  let declare (binders : Array (String × Array LeanFacts.Binder)) (declared : List (String × String)) :=
    (tableFor (factsWith binders) declared).refused.map (·.2)
  let two := #[("Tide.height", #[LeanFacts.Binder.explicit, .explicit])]
  t "prose: a phrase is refused when it names no constant, more than one, or one a phrase has"
    (declare two [("depth", "the depth of #1")] == #[.unknown] &&
      declare #[("A.f", #[.explicit]), ("B.f", #[.explicit])] [("f", "the f of #1")] == #[.ambiguous] &&
      declare two [("height", "the height of #1 and #2"), ("Tide.height", "the rise of #1 and #2")] ==
        #[.twice])
  t "prose: a phrase is refused when its slots are no template's, it holds a word that joins the one before, its slots are not its constant's explicit arguments, or it opens as another template's"
    (declare two [("height", "the height after #3 steps of #1")] == #[.shape] &&
      declare two [("height", "#1 #2")] == #[.shape] &&
      declare two [("height", "if #1 then #2")] == #[.shape] &&
      declare two [("height", "the following are equivalent for #1 and #2")] == #[.shape] &&
      declare two [("height", "the height after #2 steps, of #1")] == #[.shape] &&
      declare two [("height", "the height after #2 steps . of #1")] == #[.shape] &&
      declare two [("height", "the height of #1")] == #[.arity 1 2] &&
      declare two [("height", "#1 = #2")] == #[.clash])
  let below := (tableFor (factsWith #[("LE.le", #[.implicit, .implicit, .explicit, .explicit])])
    [("LE.le", "#1 is below #2")]).table
  t "prose: a declared phrase replaces the core table's for its constant, after the rest"
    (below.rels.getLast?.map (·.1) == some "LE.le" && (below.rels.filter (·.1 == "LE.le")).length == 1)
  let equality := (tableFor (factsWith eqBinders) [("Eq", "the equality of #1 and #2")]).table
  t "prose: a phrase of the other kind keeps the core table's relation for its constant"
    (equality.rels.lookup "Eq" == (coreRels true).lookup "Eq" && (equality.phrases.lookup "Eq").isSome)
  t "prose: a phrase is refused for a connective or a quantifier"
    (declare #[("And", #[.explicit, .explicit])] [("And", "#1 as well as #2")] == #[.connective] &&
      declare #[("Exists", #[.implicit, .explicit])] [("Exists", "some #1 exists")] == #[.connective])
  -- Only a proposition is said in words.
  let leafTex (l : Leaf) : String :=
    " ".intercalate (l.map fun m => Parse.rawSrc (LeanStatement.Math.listRaws {} #[] m.toList))
  let axiomDecl : LeanFacts.Decl := { theoremAt "Tide.cap" 1 (.pi "a" .explicit false
    (.apps (.const "Nat") []) (.apps (.const "Nat") [])) with kind := .axiom, prop := false }
  let propDef : LeanFacts.Decl := { theoremAt "Tide.zero_self" 1 (selfEq 0) with kind := .definition }
  let eqFacts := factsWith eqBinders
  t "prose: a declaration whose type is no proposition is not said in words, whatever its kind, and one whose type is one is"
    (proseOf eqFacts core axiomDecl (axiomDecl.type.getD (selfEq 0)) == .error .notProp &&
      ((proseOf eqFacts core propDef (selfEq 0)).toOption.map (showToks leafTex ∘ render) ==
        some "\\mathrm {0}={} \\mathrm {0}."))
  t "prose: an answer whose declaration does not say whether its type is a proposition is refused"
    ((LeanFacts.decode ("{\"leantex-lean-export\":2,\"lean\":\"4.34.1\",\"errors\":0}\n" ++
      "{\"name\":\"a\",\"module\":\"\",\"kind\":\"theorem\",\"range\":[1,0,1,1],\"head\":[1,0]," ++
      "\"signature\":null,\"proof\":null,\"proved\":true,\"type\":[[\"const\",\"True\"]]}\n" ++
      "{\"leantex-lean-export-end\":1}\n")).toOption.isNone)
  let shadowed : LeanFacts.Term := .pi "a" .explicit false (.apps (.const "Nat") [])
    (.pi "a" .explicit false (.apps (.const "Nat") []) (.apps (.const "Eq")
      [.apps (.const "Nat") [], .apps (.bvar 0) [], .apps (.bvar 0) []]))
  t "prose: a quantifier over a name another binds again stays apart"
    ((proseOf eqFacts core (theoremAt "Tide.again" 1 shadowed) shadowed).toOption.map
      (showToks leafTex ∘ render) ==
      some "for every \\mathit {a} : \\mathbb {N}, for every \\mathit {a} : \\mathbb {N}, \\mathit {a}={} \\mathit {a}.")
  let relFacts := factsWith (eqBinders.push ("LE.le", #[.implicit, .implicit, .explicit, .explicit]))
  let sayTex (ty : LeanFacts.Term) : Option String :=
    (proseOf relFacts core (theoremAt "Tide.t" 1 ty) ty).toOption.map (showToks leafTex ∘ render)
  let typeSort : LeanFacts.Term := .apps (.sort "1") []
  let app (c : String) (args : List LeanFacts.Term) : LeanFacts.Term := .apps (.const c) args
  let var (i : Nat) : LeanFacts.Term := .apps (.bvar i) []
  let natT := app "Nat" []
  t "prose: an instance binder at the top is a hypothesis, as below it"
    (sayTex (.pi "α" .explicit false typeSort (.pi "inst" .inst false (app "Inhabited" [var 0])
        (app "Nonempty" [var 1]))) ==
      some "for every \\mathit {α} : \\mathrm {Type}, if \\mathrm {Inhabited}\\ \\mathit {α}, then \\mathrm {Nonempty}\\ \\mathit {α}.")
  t "prose: an implicit binder the rest of the statement never names is said, not hidden"
    (sayTex (.pi "α" .implicit false typeSort (.pi "a" .implicit false (var 0)
        (app "Nonempty" [var 1]))) == some "for every \\mathit {a} : \\mathit {α}, \\mathrm {Nonempty}\\ \\mathit {α}." &&
      sayTex (.pi "x" .implicit false (app "Empty" []) (app "False" [])) ==
        some "for every \\mathit {x} : \\mathrm {Empty}, \\mathrm {False}.")
  t "prose: inside an existential an implicit binder is a quantifier and an instance one a hypothesis"
    (sayTex (app "Exists" [natT, .lam "n" .explicit natT (.pi "m" .implicit false natT
        (app "LE.le" [natT, app "instLENat" [], var 0, var 1]))]) ==
        some "there is \\mathit {n} : \\mathbb {N} such that for every \\mathit {m} : \\mathbb {N}, \\mathit {m}\\leq {} \\mathit {n}." &&
      sayTex (app "Exists" [typeSort, .lam "α" .explicit typeSort (.pi "inst" .inst false
        (app "Inhabited" [var 0]) (app "Nonempty" [var 1]))]) ==
        some "there is \\mathit {α} : \\mathrm {Type} such that if \\mathrm {Inhabited}\\ \\mathit {α}, then \\mathrm {Nonempty}\\ \\mathit {α}.")
  -- Every note's words, under a long name, as the voice lint holds a witness's.
  let long : LeanFacts.Decl := theoremAt "Tide.inhabited_nonempty" 1 (selfEq 0)
  let notes := ([.unknown, .ambiguous, .twice, .shape, .arity 1 2, .clash, .connective, .unused,
    .unshown true, .unshown false] : List Refusal).map
      (Code.refusalNote "t.lean" {} "Tide.inhabited_nonempty") ++
    ([.named "h", .local "n", .function, .notProp] : List Unsaid).map (Code.unsaidNote "t.lean" long)
  for d in notes do
    dvLint (fun m => t s!"prose voice: {m}" false) d
  -- The page, under each placement the directive declares.
  let some text ← loadTestFont "OpenSans-Regular.ttf" | t "prose: the text face loads" false
  let some mono ← loadTestFont "SourceCodePro-Regular.otf" | t "prose: the mono face loads" false
  let fonts ← mathSetOf (slotPairOf 2 text mono)
  let withShow (views : String) : String :=
    "-- leantex: " ++ views ++ "\n" ++ "\n".intercalate ((src.splitOn "\n").drop 1)
  let readWith (views : String) (given : Option LeanFacts.Facts) : Ir.Doc × Array Diag :=
    let (raws, ds) := Surface.readCode .lean "statements.lean" (withShow views) given
    Elab.runKept "statements.lean" raws ds
  let readAs (views : String) : Ir.Doc × Array Diag := readWith views (some facts)
  t "prose: a page that shows prose reads its facts, alone or beside the other views"
    (["show = prose", "show = prose, code", "show = code, prose", "show = math, prose"].all fun v =>
      (Code.showingOf .lean (withShow v).toList.toArray).statements)
  let (doc, ds) := readAs "show = prose, code"
  let out := layoutOf fonts doc
  let lines := (bodyLines out).map fun l => (monoLine l, lineInk l)
  t "prose: the listings hold the file's code exactly, sentences between them"
    (String.join ((listings doc).toList.map fun (_, c) => (c.drop 1).toString) ==
      String.ofList (Code.codeOf (Code.segmentsOf .lean src)))
  t s!"prose: each statement words cannot say is named once, in source order, and Lean's own losses as before ({ds.map (·.subject)})"
    ((ds.filter (·.kind == .W0415)).map (·.subject) == #[some "prose:Tide.height",
      some "prose:Tide.total", some "prose:Tide.depth", some "prose:Tide.same",
      some "prose:Tide.dep_hyp", some "prose:Tide.nested_dep"] &&
      (ds.filter (·.kind == .W0414)).map (·.subject) == #[some "lean:Tide.placeholder", some "lean:refused"])
  let opening (ink : String) : List String := (ink.trimAscii.toString.splitOn " ").take 2
  let mathLines := codePageLines fonts (readAs "show = math, code").1
  for (d, r) in said do
    let label := s!"{d.kind.label} ({d.name}"
    match paragraphOf lines label, r with
    | none, _ => t s!"prose: {d.name}'s paragraph ships" false
    | some para, .ok s =>
      t s!"prose: {d.name}'s sentence ships its words in order, then a full stop ({para})"
        (inOrder para (sentenceWords s) && para.endsWith ".")
      let i := (lines.findIdx? fun (mono, ink) => !mono && ink.startsWith label).getD 0
      let next := (lines.extract (i + 1) lines.size).find? (·.1)
      t s!"prose: {d.name}'s sentence stands just before its code ({next})"
        (next.any fun (_, ink) => opening ink == opening (headLine src d.head.1))
    | some para, .error _ =>
      t s!"prose: {d.name}'s statement words cannot say sets as the math view sets it ({para})"
        (paragraphOf mathLines label == some para)
  let words (name : String) (ws : String) : Bool :=
    (paragraphOf lines s!"Theorem ({name})").any (inOrder · (ws.splitOn " "))
  t "prose: a plural existential, typed groups, order and equality symbols and an instance hypothesis below the top read in order"
    (words "Tide.ordered_pair" "There are such that <" &&
      words "Tide.ge_zero" "For every ≥" &&
      words "Tide.refl_any" "For all Type and =" &&
      words "Tide.inhabited_nonempty" "If for every Type, if Inhabited then Nonempty then True.")
  t "prose: no sentence leaves a line past the measure"
    (!out.diags.any (·.kind == .W0005))
  t "prose: a theorem Lean holds unproved is marked so in words too"
    (lines.any fun (_, ink) => ink.startsWith "Theorem (Tide.unfinished, unproved). For every")
  t "prose: a quantifier over names of one type is one group, plural, its names with commas between"
    ((paragraphOf lines "Theorem (Tide.long_sum)").any fun p =>
      p.startsWith "Theorem (Tide.long_sum). For all" && (p.splitOn ",").length ≥ 18)
  -- The web page: words as text, every formula as MathML.
  let (oneDoc, _) := readAs "show = prose, decls = le_or_gt"
  let oneSentence := ((said.find? (·.1.name == "Tide.le_or_gt")).bind fun (_, r) => r.toOption)
  let pieces := (oneSentence.map fun s => ((render s).filterMap fun
    | .leaf l => some l.length
    | .bind _ => some 1
    | .w _ | .indent | .dedent | .item => none).sum).getD 0
  let nodes := (docNodesOf oneDoc).toList
  let maths := (elemNodesList (· == "math") #[] nodes).size
  let textOf := nodeTextList "" nodes
  t s!"prose: the web page sets each formula of a sentence as MathML and its words as text ({maths} of {pieces})"
    (pieces > 0 && maths == pieces && inOrder textOf ["For all", "either", "or"])
  -- Placements.
  let after := codePageLines fonts (readAs "show = code, prose").1
  t "prose: code before prose sets each sentence after its declaration's last line"
    ((after.findIdx? fun (mono, ink) => !mono && ink.startsWith "Theorem (Tide.height_double). For").any
      fun i => (after[i - 1]?.map fun (mono, ink) =>
        mono && ink.trimAscii.toString.startsWith "unfold height; exact").getD false)
  let both := codePageLines fonts (readAs "show = math, code, prose").1
  t "prose: math before code and prose after it set each in its place"
    ((both.findIdx? fun (_, ink) => ink.startsWith "Theorem (Tide.le_or_gt). ∀").any fun i =>
      (both.findIdx? fun (_, ink) => ink.startsWith "Theorem (Tide.le_or_gt). For").any fun j =>
        i < j && ((both.extract i j).any (·.1)))
  let stacked := codePageLines fonts (readAs "show = prose, math, code").1
  t "prose: two statement views before the code stand in the order the directive gives"
    ((stacked.findIdx? fun (_, ink) => ink.startsWith "Theorem (Tide.le_or_gt). For").any fun i =>
      (stacked.findIdx? fun (_, ink) => ink.startsWith "Theorem (Tide.le_or_gt). ∀").any fun j =>
        i < j && !(stacked.extract i j).any (·.1))
  let (aloneDoc, aloneDs) := readAs "show = prose"
  let alone := codePageLines fonts aloneDoc
  let lineAt (ls : Array (Bool × String)) (opening : String) : Option Nat :=
    ls.findIdx? fun (_, ink) => ink.startsWith opening
  let docAt (ls : Array (Bool × String)) : Option Nat := lineAt ls "Rising twice"
  let stmtAt (ls : Array (Bool × String)) : Option Nat := lineAt ls "Theorem (Tide.height_double)."
  t s!"prose: a page that shows prose alone sets sentences, its title, each declaration's documentation just above its statement, and in place of each statement its facts give none for its code ({(listings aloneDoc).map (·.2.trimAscii.toString)})"
    (alone.any (fun (_, ink) => ink.startsWith "Theorem (Tide.le_or_gt). For all") &&
      aloneDoc.info.title == some "Tide arithmetic" &&
      (match docAt alone, stmtAt alone with
        | some i, some j => i + 1 == j
        | _, _ => false) &&
      (match lineAt alone "Read under an open namespace", lineAt alone "Theorem (Tide.succ_eq)" with
        | some i, some j => i + 1 == j
        | _, _ => false) &&
      (listings aloneDoc).map (·.2.trimAscii.toString) ==
        #["theorem placeholder (n : Nat) : n = Nat.notAThing n := rfl",
          "theorem refused (n : Nat) : n + (1 : String) = n := rfl"] &&
      (aloneDs.filter (·.kind == .W0415)).size == 6)
  let below := codePageLines fonts (readAs "show = prose, doc = below").1
  let hidden := codePageLines fonts (readAs "show = prose, doc = none").1
  t "prose: doc = below sets a declaration's documentation just after its statement, doc = none nowhere"
    ((match docAt below, stmtAt below with
        | some i, some j => j < i && (below.extract (j + 1) i).all (!·.2.startsWith "Theorem (")
        | _, _ => false) && (docAt hidden).isNone &&
      (stmtAt hidden).isSome)
  let (_, oddDocDs) := readAs "show = prose, doc = sideways"
  let (_, codeDocDs) := readAs "show = prose, code, doc = below"
  let (_, sizeDs) := readAs "show = prose, size = small"
  t s!"prose: a doc no place names, a doc beside the code, which holds the documentation, and a page's size are named ({(oddDocDs ++ codeDocDs ++ sizeDs).map (·.subject)})"
    (oddDocDs.any (·.subject == some "code:doc:sideways") && codeDocDs.any (·.subject == some "code:doc") &&
      sizeDs.any (·.subject == some "code:size"))
  let (_, badSizeDs) := readAs "show = prose, size = huger"
  let (_, badDocDs) := readAs "show = prose, code, doc = sideways"
  t s!"prose: a key a page cannot honour is named once, whatever its value ({(badSizeDs ++ badDocDs).map (·.subject)})"
    ((badSizeDs.filter (·.subject.any (·.startsWith "code:size"))).size == 1 &&
      (badDocDs.filter (·.subject.any (·.startsWith "code:doc"))).size == 1)
  let (noneDoc, noneDs) := readWith "show = prose" none
  t "prose: a page that shows prose alone shows the file's code when it has no facts"
    ((listings noneDoc).size == (listings (readAs "show = code").1).size &&
      !(codePageLines fonts noneDoc).any (fun (_, ink) => ink.startsWith "Theorem (") &&
      !noneDs.any (fun d => d.kind == .W0415 || d.kind == .W0416))
  let chosen := codePageLines fonts (readAs "show = prose, code, decls = le_or_gt, height").1
  t "prose: decls selects the sentences set"
    ((chosen.filter fun (mono, ink) => !mono && (ink.startsWith "Theorem (" || ink.startsWith "Definition (")).size == 2)
  -- Adjacent declarations: what stands after one's code stands before the next one's statement.
  let adjFacts : LeanFacts.Facts := { factsWith eqBinders with
    decls := #[theoremAt "aa" 2 (selfEq 0), theoremAt "bb" 3 (selfEq 1), theoremAt "cc" 4 (selfEq 2)] }
  let adjacentLines (views : String) : Array String :=
    let src := s!"-- leantex: show = {views}\ntheorem aa : 0 = 0 := rfl\ntheorem bb : 1 = 1 := rfl\n" ++
      "theorem cc : 2 = 2 := rfl\n"
    let (raws, ds) := Surface.readCode .lean "adjacent.lean" src (some adjFacts)
    (codePageLines fonts (Elab.runKept "adjacent.lean" raws ds).1).map fun (mono, ink) =>
      let one := " ".intercalate ((ink.splitOn " ").filter (!·.isEmpty))
      if mono then s!"code {one}" else one
  let rising (lines : Array String) (want : List String) : Bool :=
    let found := want.map fun w => lines.findIdx? (· == w)
    found.all Option.isSome && decide ((found.filterMap id).Pairwise (· < ·))
  t s!"prose: on adjacent declarations a view after the code stands before the next declaration's views ({adjacentLines "math, code, prose"})"
    (rising (adjacentLines "math, code, prose") ["Theorem (aa). 0 = 0", "code theorem aa : 0 = 0 := rfl",
        "Theorem (aa). 0 = 0.", "Theorem (bb). 1 = 1", "code theorem bb : 1 = 1 := rfl",
        "Theorem (bb). 1 = 1.", "Theorem (cc). 2 = 2"] &&
      rising (adjacentLines "prose, code, math") ["Theorem (aa). 0 = 0.",
        "code theorem aa : 0 = 0 := rfl", "Theorem (aa). 0 = 0", "Theorem (bb). 1 = 1.",
        "code theorem bb : 1 = 1 := rfl", "Theorem (bb). 1 = 1"])
  -- A statement words cannot say sets once, as the math view sets it, wherever that view stands.
  t "prose: on a page that shows the math view too, a statement words cannot say sets once"
    (["show = math, prose", "show = math, code, prose", "show = prose, code, math"].all fun v =>
      let ls := codePageLines fonts (readAs v).1
      ["Definition (Tide.height).", "Theorem (Tide.dep_hyp)."].all fun l =>
        (ls.filter (·.2.startsWith l)).size == 1)
  let swapType : LeanFacts.Term := .pi "p" .implicit false (.apps (.sort "0") [])
    (.pi "q" .implicit false (.apps (.sort "0") []) (.apps (.const "Iff")
      [.apps (.const "And") [.apps (.bvar 1) [], .apps (.bvar 0) []],
       .apps (.const "And") [.apps (.bvar 0) [], .apps (.bvar 1) []]]))
  let swapFacts : LeanFacts.Facts := { factsWith #[] with decls := #[theoremAt "tt" 2 swapType] }
  let (swapRaws, swapDs) := Surface.readCode .lean "swap.lean"
    "-- leantex: show = prose\ntheorem tt {p q : Prop} : p ∧ q ↔ q ∧ p := And.comm\n" (some swapFacts)
  let swapLines := codePageLines fonts (Elab.runKept "swap.lean" swapRaws swapDs).1
  let swapInk := swapLines.map (·.2.trimAscii.toString)
  t s!"prose: a sentence opening on an equivalence of conjunctions sets it bare on the head's line, its first word capitalized ({swapInk})"
    (swapInk.any (·.startsWith "Theorem (tt). Both p and q if and only if") &&
      ((proseOf swapFacts (coreTable true) (theoremAt "tt" 2 swapType) swapType).toOption.map
        fun s => (sentenceWords s).take 1) == some ["Both"])
  -- Phrases on the page.
  let phrased := codePageLines fonts (readAs ("show = prose, code, phrase.height = \"the height after #2 steps of #1\", " ++
    "phrase.Tide.holds = \"#1 holds\"")).1
  t "prose: a declared phrase says its constant's terms, and a declared relation its propositions"
    ((paragraphOf phrased "Theorem (Tide.height_double)").any (fun p =>
        inOrder p ["For all", "the height after", "steps of", "="]) &&
      (paragraphOf phrased "Theorem (Tide.holds_ex)").any (fun p => inOrder p ["holds."]))
  let (_, unusedDs) := readAs ("show = prose, code, phrase.Nat.succ = \"#1 plus one\", " ++
    "phrase.Tide.height = \"#1 rises over #2 steps\", phrase.Tide.holds = \"#1 holds\"")
  t s!"prose: each taken phrase no sentence on the page uses is named at the directive ({unusedDs.filter (·.kind == .W0416) |>.map (·.subject)})"
    ((unusedDs.filter (·.kind == .W0416)).map (·.subject) == #[some "code:phrase:Nat.succ",
      some "code:phrase:Tide.height"])
  let (refusedDoc, refusedDs) := readAs ("show = prose, code, phrase.nothing = \"#1 is void\", " ++
    "phrase.height = \"the height of #1\"")
  t s!"prose: each refused phrase is named once at the directive, its constant set as mathematics ({refusedDs.filter (·.kind == .W0416) |>.map (·.subject)})"
    ((refusedDs.filter (·.kind == .W0416)).map (·.subject) == #[some "code:phrase:nothing",
        some "code:phrase:height"] &&
      (refusedDs.filter (·.kind == .W0416)).all (fun d => d.span.any (·.pos.line == 1)) &&
      (paragraphOf (codePageLines fonts refusedDoc) "Theorem (Tide.height_double)").any fun p =>
        inOrder p ["For all", "height", "="])
  let (_, unshownDs) := readAs "show = math, code, phrase.height = \"the height of #1 and #2\""
  let (_, pyDs) := Surface.readCode .python "t.py" "# leantex: phrase.x = \"the x of #1\"\nx = 1\n" none
  t "prose: a phrase on a page that says nothing in words is named and not used"
    ((unshownDs.filter (·.kind == .W0416)).map (·.subject) == #[some "code:phrase:height"] &&
      (pyDs.filter (·.kind == .W0416)).map (·.subject) == #[some "code:phrase:x"])
  t "prose: a directive's phrases reach no output declaration"
    (Parse.rawSrc (Code.directiveRaws "show = prose, phrase.height = \"the height of #1\", formats = pdf" {}) ==
      "\\output {formats = pdf}")

end Tests.LeanProse
