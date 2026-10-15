module

public import Tests.Support
public import Tests.Diag
public import LeanTex.Core.LeanProseContract

public section

open LeanTex.Core LeanTex.Core.LeanProse

/-! Lean statements in words, on invented words: each sentence of the committed answer and of
random statements over the core table reads back as its statement, each placement a directive
declares holds on the page and on the web page, and a declared phrase is taken or refused by name. -/

namespace Tests.LeanProse

/-- A one-word formula, the leaf of an invented statement. -/
def wordLeaf (s : String) : Leaf := [#[.word s]]

/-- The word a one-word formula holds. -/
def leafWord : Leaf → String
  | [#[.word w]] => w
  | _ => "?"

/-- An invented answer whose constants have the given leading binders. -/
def factsWith (binders : Array (String × Array LeanFacts.Binder)) : LeanFacts.Facts :=
  { lean := "4.34.1", errors := 0, decls := #[], binders }

/-- The table of an invented file declaring a phrase and a relation of its own. -/
def phrasedTable (_ : Unit) : Table :=
  (tableFor (factsWith #[("Tide.height", #[.explicit, .explicit]), ("Tide.Calm", #[.explicit])])
    [("Tide.height", "the height after #2 steps of #1"), ("Calm", "#1 is calm")]).table

/-- A random term for a slot: a leaf, or a phrase of the table over leaves. -/
def randTerm (tb : Table) (s : UInt64) : Term Leaf × UInt64 :=
  let (k, s) := rand s (tb.phrases.length + 2)
  match tb.phrases[k]? with
  | some (_, p) => (.phrase p ((List.range p.arity).map fun i => wordLeaf s!"t{i}"), s)
  | none => (.leaf (wordLeaf s!"u{k}"), s)

/-- A random binder: a number set's noun, a proposition's, or an element of a type, over one to
three names. -/
def randBinder (s : UInt64) : Binder Leaf × UInt64 :=
  let (k, s) := rand s (numberNouns.length + 2)
  let (more, s) := rand s 3
  let names := (List.range more).map fun i => wordLeaf s!"y{i}"
  let pick (one many : List String) : List String := if more == 0 then one else many
  match numberNouns[k]? with
  | some (_, one, many) => (⟨pick one many, wordLeaf "x", names, none⟩, s)
  | none =>
    if k == numberNouns.length then (⟨pick ["proposition"] ["propositions"], wordLeaf "p", names,
      none⟩, s)
    else (⟨pick ["element"] ["elements"], wordLeaf "x", names, some (wordLeaf "T")⟩, s)

/-- A random statement of depth at most `d` over a table's relations and phrases. -/
def randStmt (tb : Table) : Nat → UInt64 → Stmt Leaf × UInt64
  | 0, s =>
    let (k, s) := rand s (tb.rels.length + 1)
    match tb.rels[k]? with
    | some (_, r) =>
      let (args, s) := (List.range r.arity).foldl (fun (acc : List (Term Leaf) × UInt64) _ =>
        let (x, s) := randTerm tb acc.2
        (acc.1 ++ [x], s)) ([], s)
      (.rel r args, s)
    | none => (.atom (wordLeaf "P"), s)
  | d + 1, s =>
    let (k, s) := rand s 9
    let (a, s) := randStmt tb d s
    let (b, s) := randStmt tb d s
    let (q, s) := randBinder s
    match k with
    | 0 => (.all q a, s)
    | 1 => (.ex q a, s)
    | 2 => (.imp a b, s)
    | 3 => (.conj a b, s)
    | 4 => (.disj a b, s)
    | 5 => (.iff a b, s)
    | 6 => (.neg a, s)
    | _ => (a, s)

/-- The words a statement's sentence sets, in order, as the page sets them: the one it opens on,
past any opening parenthesis, capitalized. -/
def sentenceWords (s : Stmt Leaf) : List String :=
  let opening := (render s).dropWhile fun | .w "(" => true | _ => false
  let capital := match opening with
    | .w _ :: _ => true
    | _ => false
  let ws := (render s).filterMap fun | .w w => some w | .leaf _ => none
  let parens := ws.takeWhile (· == "(")
  match ws.drop parens.length with
  | w :: rest => parens ++ (if capital then w.capitalize else w) :: rest
  | [] => parens

/-- A theorem of an invented file: its name, the line it stands on, and its type. -/
def theoremAt (name : String) (line : Nat) (type : LeanFacts.Term) : LeanFacts.Decl :=
  { name, kind := .theorem, prop := true, start := (line, 0), stop := (line, 25), type }

/-- `n = n` for a numeral `n`, as Lean's answer gives it. -/
def selfEq (n : Nat) : LeanFacts.Term :=
  .apps (.const "Eq") [.apps (.const "Nat") [], .apps (.nat n) [], .apps (.nat n) []]

/-- Equality's leading binders, as Lean's answer gives them. -/
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
    ("Tide.height", .notProp), ("Tide.holds", .notProp), ("Tide.nested_dep", .named "h"),
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
    unless s.ok (phrasedTable ()).lexicon && parse (phrasedTable ()).lexicon (render s) == some s do
      failed := failed.push (showToks leafWord (render s))
  t s!"evidence: 600 random statements over the core table and declared phrases read back ({failed.toList.take 2})"
    failed.isEmpty
  -- Declared phrases, taken or refused by name.
  let declare (binders : Array (String × Array LeanFacts.Binder)) (declared : List (String × String)) :=
    (tableFor (factsWith binders) declared).refused.map (·.2)
  let two := #[("Tide.height", #[LeanFacts.Binder.explicit, .explicit])]
  t "prose: a phrase is refused when it names no constant, more than one, or one a phrase has"
    (declare two [("depth", "the depth of #1")] == #[.unknown] &&
      declare #[("A.f", #[.explicit]), ("B.f", #[.explicit])] [("f", "the f of #1")] == #[.ambiguous] &&
      declare two [("height", "the height of #1 and #2"), ("Tide.height", "the rise of #1 and #2")] ==
        #[.twice])
  t "prose: a phrase is refused when its slots are no template's, are not its constant's explicit arguments, or open as another template's"
    (declare two [("height", "the height after #3 steps of #1")] == #[.shape] &&
      declare two [("height", "#1 #2")] == #[.shape] &&
      declare two [("height", "if #1 then #2")] == #[.shape] &&
      declare two [("height", "the height after #2 steps, of #1")] == #[.shape] &&
      declare two [("height", "the height of #1")] == #[.arity 1 2] &&
      declare two [("height", "#1 is at most #2")] == #[.clash])
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
  let axiomDecl : LeanFacts.Decl := { theoremAt "Tide.cap" 1 (.pi "a" .explicit false
    (.apps (.const "Nat") []) (.apps (.const "Nat") [])) with kind := .axiom, prop := false }
  let propDef : LeanFacts.Decl := { theoremAt "Tide.zero_self" 1 (selfEq 0) with kind := .definition }
  let eqFacts := factsWith eqBinders
  t "prose: a declaration whose type is no proposition is not said in words, whatever its kind, and one whose type is one is"
    (proseOf eqFacts core axiomDecl (axiomDecl.type.getD (selfEq 0)) == .error .notProp &&
      ((proseOf eqFacts core propDef (selfEq 0)).toOption.map (showToks leafWord ∘ render) ==
        some "0 is equal to 0"))
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
      (showToks leafWord ∘ render) ==
      some "for every natural number a, for every natural number a, a is equal to a")
  let leafTex (l : Leaf) : String :=
    " ".intercalate (l.map fun m => Parse.rawSrc (LeanStatement.Math.listRaws {} #[] m.toList))
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
      some "for every type α, if \\operatorname {Inhabited}(α), then \\operatorname {Nonempty}(α)")
  t "prose: an implicit binder the rest of the statement never names is said, not hidden"
    (sayTex (.pi "α" .implicit false typeSort (.pi "a" .implicit false (var 0)
        (app "Nonempty" [var 1]))) == some "for every element a of α, \\operatorname {Nonempty}(α)" &&
      sayTex (.pi "x" .implicit false (app "Empty" []) (app "False" [])) ==
        some "for every element x of \\operatorname {Empty}, \\operatorname {False}")
  t "prose: inside an existential an implicit binder is a quantifier and an instance one a hypothesis"
    (sayTex (app "Exists" [natT, .lam "n" .explicit natT (.pi "m" .implicit false natT
        (app "LE.le" [natT, app "instLENat" [], var 0, var 1]))]) ==
        some "there is a natural number n such that for every natural number m, m is at most n" &&
      sayTex (app "Exists" [typeSort, .lam "α" .explicit typeSort (.pi "inst" .inst false
        (app "Inhabited" [var 0]) (app "Nonempty" [var 1]))]) ==
        some "there is a type α such that if \\operatorname {Inhabited}(α), then \\operatorname {Nonempty}(α)")
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
    Elab.runRaws "statements.lean" raws ds
  let readAs (views : String) : Ir.Doc × Array Diag := readWith views (some facts)
  t "prose: a page that shows prose asks Lean, alone or beside the other views"
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
      some "prose:Tide.total", some "prose:Tide.depth", some "prose:Tide.holds", some "prose:Tide.same",
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
  t "prose: a plural existential, a type's noun, an order relation and an instance hypothesis below the top read as words"
    (words "Tide.ordered_pair" "There are natural numbers and such that is less than" &&
      words "Tide.ge_zero" "For every natural number is at least" &&
      words "Tide.refl_any" "For every type for every element of is equal to" &&
      words "Tide.inhabited_nonempty" "If (for every type if Inhabited then Nonempty ), then True.")
  t "prose: no sentence leaves a line past the measure"
    (!out.diags.any (·.kind == .W0005))
  t "prose: a theorem Lean holds unproved is marked so in words too"
    (lines.any fun (_, ink) => ink.startsWith "Theorem (Tide.unfinished, unproved). For every")
  t "prose: a quantifier over names of one type is one, plural, its last name after 'and'"
    ((paragraphOf lines "Theorem (Tide.long_sum)").any fun p =>
      p.startsWith "Theorem (Tide.long_sum). For all natural numbers" && (p.splitOn " and ").length ≥ 2)
  -- The web page: words as text, every formula as MathML.
  let (oneDoc, _) := readAs "show = prose, decls = le_or_gt"
  let oneSentence := ((said.find? (·.1.name == "Tide.le_or_gt")).bind fun (_, r) => r.toOption)
  let pieces := (oneSentence.map fun s => ((render s).filterMap fun
    | .leaf l => some l.length
    | .w _ => none).sum).getD 0
  let nodes := (docNodesOf oneDoc).toList
  let maths := (elemNodesList (· == "math") #[] nodes).size
  let textOf := nodeTextList "" nodes
  t s!"prose: the web page sets each formula of a sentence as MathML and its words as text ({maths} of {pieces})"
    (pieces > 0 && maths == pieces && inOrder textOf ["For all natural numbers", "and", "either",
      "is at most", "or", "is less than"])
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
  t s!"prose: a page that shows prose alone sets sentences, its title, no documentation, and in place of each statement Lean gave none for its code ({(listings aloneDoc).map (·.2.trimAscii.toString)})"
    (alone.any (fun (_, ink) => ink.startsWith "Theorem (Tide.le_or_gt). For all") &&
      aloneDoc.info.title == some "Tide arithmetic" &&
      !alone.any (fun (_, ink) => ink.startsWith "Rising twice") &&
      (listings aloneDoc).map (·.2.trimAscii.toString) ==
        #["theorem placeholder (n : Nat) : n = Nat.notAThing n := rfl",
          "theorem refused (n : Nat) : n + (1 : String) = n := rfl"] &&
      (aloneDs.filter (·.kind == .W0415)).size == 7)
  let (noneDoc, noneDs) := readWith "show = prose" none
  t "prose: a page that shows prose alone shows the file's code when Lean gave no answer"
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
    (codePageLines fonts (Elab.runRaws "adjacent.lean" raws ds).1).map fun (mono, ink) =>
      let one := " ".intercalate ((ink.splitOn " ").filter (!·.isEmpty))
      if mono then s!"code {one}" else one
  let rising (lines : Array String) (want : List String) : Bool :=
    let found := want.map fun w => lines.findIdx? (· == w)
    found.all Option.isSome && decide ((found.filterMap id).Pairwise (· < ·))
  t s!"prose: on adjacent declarations a view after the code stands before the next declaration's views ({adjacentLines "math, code, prose"})"
    (rising (adjacentLines "math, code, prose") ["Theorem (aa). 0 = 0", "code theorem aa : 0 = 0 := rfl",
        "Theorem (aa). 0 is equal to 0.", "Theorem (bb). 1 = 1", "code theorem bb : 1 = 1 := rfl",
        "Theorem (bb). 1 is equal to 1.", "Theorem (cc). 2 = 2"] &&
      rising (adjacentLines "prose, code, math") ["Theorem (aa). 0 is equal to 0.",
        "code theorem aa : 0 = 0 := rfl", "Theorem (aa). 0 = 0", "Theorem (bb). 1 is equal to 1.",
        "code theorem bb : 1 = 1 := rfl", "Theorem (bb). 1 = 1"])
  -- A statement words cannot say sets once, as the math view sets it, wherever that view stands.
  t "prose: on a page that shows the math view too, a statement words cannot say sets once"
    (["show = math, prose", "show = math, code, prose", "show = prose, code, math"].all fun v =>
      let ls := codePageLines fonts (readAs v).1
      ["Definition (Tide.height).", "Theorem (Tide.dep_hyp)."].all fun l =>
        (ls.filter (·.2.startsWith l)).size == 1)
  -- A sentence that opens on a parenthesis capitalizes the word after it.
  let swapType : LeanFacts.Term := .pi "p" .implicit false (.apps (.sort "0") [])
    (.pi "q" .implicit false (.apps (.sort "0") []) (.apps (.const "Iff")
      [.apps (.const "And") [.apps (.bvar 1) [], .apps (.bvar 0) []],
       .apps (.const "And") [.apps (.bvar 0) [], .apps (.bvar 1) []]]))
  let swapFacts : LeanFacts.Facts := { factsWith #[] with decls := #[theoremAt "tt" 2 swapType] }
  let (swapRaws, swapDs) := Surface.readCode .lean "swap.lean"
    "-- leantex: show = prose\ntheorem tt {p q : Prop} : p ∧ q ↔ q ∧ p := And.comm\n" (some swapFacts)
  let swapLines := codePageLines fonts (Elab.runRaws "swap.lean" swapRaws swapDs).1
  t s!"prose: a sentence opening on a parenthesis capitalizes the word after it ({swapLines.map (·.2)})"
    (swapLines.any (·.2.startsWith "Theorem (tt). (Both") &&
      ((proseOf swapFacts (coreTable true) (theoremAt "tt" 2 swapType) swapType).toOption.map
        fun s => (sentenceWords s).take 2) == some ["(", "Both"])
  -- Phrases on the page.
  let phrased := codePageLines fonts (readAs ("show = prose, code, phrase.height = \"the height after #2 steps of #1\", " ++
    "phrase.Tide.holds = \"#1 holds\"")).1
  t "prose: a declared phrase says its constant's terms, and a declared relation its propositions"
    ((paragraphOf phrased "Theorem (Tide.height_double)").any (fun p =>
        inOrder p ["For all natural numbers", "the height after", "steps of", "is equal to"]) &&
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
        inOrder p ["For all natural numbers", "height(", "is equal to"])
  let (_, unshownDs) := readAs "show = math, code, phrase.height = \"the height of #1 and #2\""
  let (_, pyDs) := Surface.readCode .python "t.py" "# leantex: phrase.x = \"the x of #1\"\nx = 1\n" none
  t "prose: a phrase on a page that says nothing in words is named and not used"
    ((unshownDs.filter (·.kind == .W0416)).map (·.subject) == #[some "code:phrase:height"] &&
      (pyDs.filter (·.kind == .W0416)).map (·.subject) == #[some "code:phrase:x"])
  t "prose: a directive's phrases reach no output declaration"
    (Parse.rawSrc (Code.directiveRaws "show = prose, phrase.height = \"the height of #1\", formats = pdf" {}) ==
      "\\output {formats = pdf}")

end Tests.LeanProse
