module

public import Tests.Support
public import Tests.CodeDoc
public import Tests.LeanStatements

public section

open LeanTex.Core LeanTex.Cli LeanTex.Cli.World

/-! A Lean file's views on invented words: the options every entry point reads, proofs folded into
disclosures or removed, a file included in a document, links to the declarations, and the fenced
division markdown includes a file by. -/

namespace Tests.LeanViews

/-- Every listing's text in a document's blocks, in order, those inside disclosures included. -/
def listingTexts (doc : Ir.Doc) : Array String := Id.run do
  let mut out : Array String := #[]
  for b in doc.body do
    match b with
    | .verbatim _ c _ => out := out.push c
    | .disclosure _ _ body =>
      for inner in body do
        if let .verbatim _ c _ := inner then out := out.push c
    | _ => pure ()
  return out

/-- The disclosures a document's blocks hold: each one's summary text and whether it opens. -/
def disclosures (doc : Ir.Doc) : Array (String × Bool) :=
  doc.body.filterMap fun b => match b with
    | .disclosure summary expanded _ => some (Ir.plainText summary, expanded)
    | _ => none

/-- A string's characters but white space. -/
def ink (s : String) : String := String.ofList (s.toList.filter (!Code.isWhite ·))

/-- A world for the export and for git: files by path, lake and git on PATH, Lean's version, one
reply to every export run, and git's replies by the question asked. -/
def gitWorld (files : List (String × ByteArray)) (commit path status : Option String) :
    (q : Ask) → Reply q
  | .env name => if name == "PATH" then some "/bin" else if name == "HOME" then some "/h" else none
  | .cwd => .ok "/work"
  | .stat p =>
    if p == "/bin/git" || files.any (·.1 == p) then
      .ok { kind := .file, size := 0, mtimeSec := 0, mtimeNsec := 0, real := p }
    else .error .absent
  | .metadata _ => .error .absent
  | .readFile p => match files.lookup p with
    | some b => .ok b
    | none => .error .absent
  | .listDir _ => .error .absent
  | .run call =>
    let said (o : Option String) : Ended := match o with
      | some s => Tests.LeanStatements.ended 0 (s ++ "\n") none
      | none => Tests.LeanStatements.ended 128 "" none
    if call.args.contains "rev-parse" then said commit
    else if call.args.contains "ls-tree" then
      Tests.LeanStatements.ended 0 ((path.map (· ++ "\x00")).getD "") none
    else if call.args.contains "status" then said status
    else Tests.LeanStatements.ended 1 "" none
  | .writeAtomic _ _ => .ok ()
  | .createDirAll _ => .ok ()

def leanViewChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let src ← fixtureText leanFixture
  let answer ← IO.FS.readFile leanAnswer
  let facts ← match LeanFacts.decode answer with
    | .ok f => pure f
    | .error why => do t s!"views: the committed answer reads ({why})" false; return
  -- The options, as every entry point reads them.
  let sh := Code.showingOfEntries .lean (Decl.splitEntries
    "show = {math, code}, decls = {a, b}, proofs = collapse, link = \"https://e.org/{name}\"") true
  t "views: options read their views, declarations, proofs and link through braces and quotes"
    (sh.views == [.math, .code] && sh.decls == some ["a", "b"] && sh.proofs == .collapse &&
      sh.link == some "https://e.org/{name}" && sh.strange.isEmpty && sh.unread.isEmpty)
  let bare := Code.showingOfEntries .lean (Decl.splitEntries "show = math, code, decls = a, b")
  t "views: a directive's bare entries continue the key before them"
    (bare.views == [.math, .code] && bare.decls == some ["a", "b"])
  let odd := Code.showingOfEntries .lean (Decl.splitEntries "proofs = folded, caption = x") true
  t "views: a proofs value no mode names and a key no option names are kept to be named"
    (odd.proofs == .show && odd.unread == [("proofs", "folded")] && odd.strange == ["caption"])
  t "views: a key written twice takes its last value, as keyval reads it"
    ((Code.showingOfEntries .lean (Decl.splitEntries "proofs = collapse, proofs = remove")).proofs ==
      .remove)
  t "views: an empty decls chooses nothing, so every declaration is set"
    ((Code.showingOfEntries .lean (Decl.splitEntries "show = math, decls = {}")).decls == none)
  t "views: an inclusion keeps a key written without a value to be named by the key"
    ((Code.showingOfEntries .lean (Decl.splitEntries "link") true).strange == ["link"])
  t "views: an inclusion that chose declarations and has no answer says it is included whole"
    ((Code.showingOfEntries .lean (Decl.splitEntries "decls = {a}, proofs = remove")).lostIncluded ==
        "it is included whole in place of the declarations `decls` names, its proofs as written" &&
      (Code.showingOfEntries .lean (Decl.splitEntries "decls = {a}")).lostIncluded ==
        "it is included whole in place of the declarations `decls` names" &&
      (Code.showingOfEntries .lean (Decl.splitEntries "proofs = remove")).lostIncluded ==
        "its proofs are set as written")
  t "views: a directive's other keys belong to its other declarations and are never strange"
    ((Code.showingOfEntries .lean (Decl.splitEntries "theme = gemini, show = math")).strange.isEmpty)
  t "views: only statements and folded or removed proofs ask Lean"
    (!(Code.showingOfEntries .lean ["link = https://e.org"]).asks &&
      (Code.showingOfEntries .lean ["proofs = remove"]).asks &&
      (Code.showingOfEntries .lean ["show = math"]).asks)
  -- Links.
  let github := "https://github.com/acme/tides/blob/{commit}/{path}#L{line}-L{endline}"
  t "views: a GitHub repository's root links each declaration's lines at the file's commit"
    (Code.linkTemplate "https://github.com/acme/tides" == github &&
      Code.linkTemplate "https://github.com/acme/tides/" == github &&
      Code.linkTemplate "https://github.com/acme/tides.git" == github &&
      Code.linkTemplate "http://github.com/acme/tides" == github &&
      ["https://github.com/acme/tides/tree/main", "https://github.com/acme/tides?x=1",
        "https://github.com/acme/tides#readme",
        "https://acme.example.org/docs/{module}.html#{name}"].all fun l => Code.linkTemplate l == l)
  t "views: a link's value keeps an unbraced comma as written"
    ((Code.showingOfEntries .lean (Decl.splitEntries "link = https://e.org/{name},{line}")).link ==
      some "https://e.org/{name},{line}")
  let some dbl := facts.decls.find? (·.name == "Tide.height_double")
    | t "views: the fixture holds Tide.height_double" false
  t "views: a template takes each part from the declaration and the file's place"
    (Code.expandLink "https://e.org/{module}/{name}#L{line}-L{endline}/{commit}/{path}" dbl
        { commit := some "c0ffee", path := some "lean/statements.lean" } ==
      some "https://e.org/testdata.codedoc.lean.statements/Tide.height_double#L11-L13/c0ffee/lean/statements.lean")
  t "views: a template's filled parts are percent-encoded, a path keeping its slashes"
    (Code.expandLink "https://e.org/{path}#{name}" { dbl with name := "höhe pos'" }
        { path := some "lean/Größe x.lean" } ==
      some "https://e.org/lean/Gr%C3%B6%C3%9Fe%20x.lean#h%C3%B6he%20pos%27")
  t "views: a template naming a part the place lacks gives no link"
    (Code.expandLink "https://e.org/{commit}" dbl {} == none &&
      Code.expandLink "https://e.org/{name}" dbl {} == some "https://e.org/Tide.height_double")
  let notesFor (place : Code.LinkPlace) : Array String :=
    (Code.linkNotes ⟨"host.tex", {}⟩ { link := some "https://github.com/acme/tides" } place).map
      (·.code)
  let held : Code.LinkPlace :=
    { commit := some "c", path := some "t.lean", dirty := some false, tracked := true }
  t "views: a link without its commit, its path, the file's state or the commit's copy is named, and so is one whose file changed since"
    (notesFor {} == #["W0432"] && notesFor held == #[] &&
      notesFor { held with dirty := none } == #["W0432"] &&
      notesFor { held with tracked := false } == #["W0432"] &&
      notesFor { held with dirty := some true } == #["W0431"])
  let placeOf (commit path status : Option String) : Code.LinkPlace :=
    (LeanExport.placeOf "lean/t.lean" github).run (gitWorld [] commit path status)
  let asked := (LeanExport.placeOf "lean/t.lean" "https://e.org/{name}").asks
    (gitWorld [] (some "c") (some "t") (some ""))
  let calls := ((LeanExport.placeOf "lean/t.lean" github).asks
    (gitWorld [] (some "c") (some "t") (some ""))).filterMap fun q => match q with
      | .run call => some call
      | _ => none
  t "views: git says where a file stands, asked only for the parts its template names, with no repository the environment names"
    (placeOf (some "c0ffee") (some "lean/t.lean") (some "") ==
        { commit := some "c0ffee", path := some "lean/t.lean", dirty := some false, tracked := true } &&
      (placeOf (some "c0ffee") (some "lean/t.lean") (some " M lean/t.lean")).dirty == some true &&
      (placeOf (some "c0ffee") (some "lean/t.lean") none).dirty == none &&
      (placeOf (some "c0ffee") none (some "")).tracked == false &&
      (placeOf (some "c0ffee") (some "lean/Größe.lean") (some "")).path == some "lean/Größe.lean" &&
      notesFor (placeOf (some "c0ffee") none (some "")) == #["W0432"] &&
      !asked.any (fun q => match q with
        | .run _ => true
        | _ => false) &&
      calls.length == 3 && calls.all fun c => LeanExport.gitRepoVars.all fun v => c.env.contains (v, none))
  -- Folds on invented proofs of every shape, against the spans Lean gives them.
  let edge := "theorem one_line : 1 + 1 = 2 := rfl\n\ntheorem eqn_style : (n : Nat) → n + 0 = n\n" ++
    "  | 0 => rfl\n  | k + 1 => rfl\n\ntheorem commented : 2 + 2 = 4 := by\n" ++
    "  decide -- by computation\n\ntheorem with_calc (a b c : Nat) (h1 : a = b) (h2 : b = c) : " ++
    "a = c := by\n  calc a = b := h1\n    _ = c := h2\n"
  let mk (name : String) (start stop : Nat × Nat) (proof : (Nat × Nat) × (Nat × Nat)) :
      LeanFacts.Decl :=
    { name, kind := .theorem, start, stop, type := none, proof := some proof, prop := true }
  let edgeDecls : Array LeanFacts.Decl := #[mk "one_line" (1, 0) (1, 35) ((1, 29), (1, 35)),
    mk "eqn_style" (3, 0) (5, 16) ((4, 2), (5, 16)),
    mk "commented" (7, 0) (8, 8) ((7, 30), (8, 8)),
    mk "with_calc" (10, 0) (12, 15) ((10, 66), (12, 15))]
  let edgeFacts : LeanFacts.Facts :=
    { lean := "4.34.1", errors := 0, binders := #[], decls := edgeDecls }
  let es := Code.lineStarts edge.toList.toArray
  let edgeFolds (p : Code.Proofs) := Code.foldsOf es edge.toList.toArray p edgeFacts 0
  let edgePieces (p : Code.Proofs) : List (Nat × String) :=
    (Code.assemble (Code.withFolds (edgeFolds p) (Code.segmentsOf .lean edge))).toList.filterMap
      fun pc => match pc with
        | .code start t => some ((Code.lineCol es start).1, String.ofList t)
        | _ => none
  let foldText (f : Code.ProofFold) : String :=
    String.ofList (edge.toList.toArray.extract f.start f.stop).toList
  t s!"views: a fold takes whole lines, its indentation and a closing comment kept, a one-line proof left in place ({(edgeFolds .collapse).map foldText})"
    ((edgeFolds .collapse).map foldText ==
      ["  | 0 => rfl\n  | k + 1 => rfl", "  decide -- by computation",
        "  calc a = b := h1\n    _ = c := h2"] &&
      (edgePieces .collapse).map (·.2) ==
        ["theorem one_line : 1 + 1 = 2 := rfl\n\ntheorem eqn_style : (n : Nat) → n + 0 = n",
          "theorem commented : 2 + 2 = 4 := by",
          "theorem with_calc (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by"])
  t s!"views: a removal leaves ⋯ where the proof stood, its line's comment kept, and after a proof of more than one line the next listing starts at its own source line ({edgePieces .remove})"
    (edgePieces .remove == [
      (1, "theorem one_line : 1 + 1 = 2 := ⋯\n\ntheorem eqn_style : (n : Nat) → n + 0 = n\n  ⋯"),
      (7, "theorem commented : 2 + 2 = 4 := ⋯ -- by computation"),
      (10, "theorem with_calc (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := ⋯")])
  -- Proofs that open on their signature's line, close on a block comment, or hold a docstring.
  let edge2 := "-- leantex: show = code, proofs = collapse\n" ++
    "theorem mid_by (n : Nat) : n + 0 = n := by induction n with\n  | zero => rfl\n" ++
    "  | succ k _ => rfl\n\ntheorem mid_fun (p : Prop) : p → p := fun hp =>\n  hp\n\n" ++
    "theorem block_after (a : Nat) : a + 0 = a := by\n  simp /- closes it -/\n\n" ++
    "theorem a1 : True := trivial\ntheorem a2 : True := trivial /- also -/\ndef d : Nat := 1\n" ++
    "theorem blank_first : 6 = 6 := by\n\n  rfl\n\n" ++
    "theorem uses_helper (n : Nat) : n + 0 = n := by\n  exact helper n\nwhere\n" ++
    "/-- A helper the proof uses. -/\nhelper (k : Nat) : k + 0 = k := by\n  simp\n\n" ++
    "theorem after : True := trivial\n"
  let lines2 := (edge2.splitOn "\n").toArray
  let col2 (line : Nat) (needle : String) : Nat :=
    (((lines2.getD (line - 1) "").splitOn needle).headD "").length
  let span2 (name : String) (l1 l2 : Nat) (last : Option String := none) : LeanFacts.Decl :=
    let stopCol := match last with
      | some n => col2 l2 n + n.length
      | none => (lines2.getD (l2 - 1) "").length
    mk name (l1, 0) (l2, stopCol) ((l1, col2 l1 ":="), (l2, stopCol))
  let facts2 : LeanFacts.Facts := { lean := "4.34.1", errors := 0, binders := #[], decls := #[
    span2 "mid_by" 2 4, span2 "mid_fun" 6 7, span2 "block_after" 9 10 (some "simp"),
    span2 "a1" 12 12, span2 "a2" 13 13 (some "trivial"), span2 "blank_first" 15 17,
    span2 "uses_helper" 19 24, span2 "after" 26 26] }
  let src2 := edge2.toList.toArray
  let es2 := Code.lineStarts src2
  let folds2 (p : Code.Proofs) := Code.foldsOf es2 src2 p facts2 0
  let pieces2 (p : Code.Proofs) : List (Nat × String) :=
    (Code.assemble (Code.withFolds (folds2 p) (Code.segmentsOf .lean edge2))).toList.filterMap
      fun pc => match pc with
        | .code start t => some ((Code.lineCol es2 start).1, String.ofList t)
        | _ => none
  let foldText2 (f : Code.ProofFold) : String := String.ofList (src2.extract f.start f.stop).toList
  t s!"views: a proof opening on its signature's line folds from its first character, after a bare `by` from the next line, through its block comment, a docstring inside it kept as its code ({(folds2 .collapse).map foldText2})"
    ((folds2 .collapse).map foldText2 == ["by induction n with\n  | zero => rfl\n  | succ k _ => rfl",
        "fun hp =>\n  hp", "  simp /- closes it -/", "\n  rfl",
        "  exact helper n\nwhere\n/-- A helper the proof uses. -/\nhelper (k : Nat) : k + 0 = k := by\n  simp"] &&
      (pieces2 .collapse).map (·.2) == ["theorem mid_by (n : Nat) : n + 0 = n :=",
        "theorem mid_fun (p : Prop) : p → p :=",
        "theorem block_after (a : Nat) : a + 0 = a := by",
        "theorem a1 : True := trivial\ntheorem a2 : True := trivial /- also -/\ndef d : Nat := 1\n" ++
          "theorem blank_first : 6 = 6 := by",
        "theorem uses_helper (n : Nat) : n + 0 = n := by", "theorem after : True := trivial\n"])
  t s!"views: a removal of one line keeps its listing, one of more lines ends it, and no docstring inside a removed proof ships ({pieces2 .remove})"
    (pieces2 .remove == [(2, "theorem mid_by (n : Nat) : n + 0 = n := ⋯"),
      (6, "theorem mid_fun (p : Prop) : p → p := ⋯"),
      (9, "theorem block_after (a : Nat) : a + 0 = a := ⋯ /- closes it -/"),
      (12, "theorem a1 : True := ⋯\ntheorem a2 : True := ⋯ /- also -/\ndef d : Nat := 1\n" ++
        "theorem blank_first : 6 = 6 := ⋯"),
      (19, "theorem uses_helper (n : Nat) : n + 0 = n := ⋯"), (26, "theorem after : True := ⋯\n")])
  let twinOf (body : String) : String := MarkdownDoc.emit (elabStr
    s!"\\documentclass\{article}\n\\begin\{document}\n{body}\n\\end\{document}").1
  t "views: the twin spaces zero glue only between two formulas"
    (((twinOf "$a$\\hspace{0pt}$b$").splitOn "$a$ $b$").length == 2 &&
      ((twinOf "$a$\\hspace{0pt}.").splitOn "$a$.").length == 2)
  -- A page that folds its proofs.
  let some text ← loadTestFont "OpenSans-Regular.ttf" | t "views: the text face loads" false
  let some mono ← loadTestFont "SourceCodePro-Regular.otf" | t "views: the mono face loads" false
  let fonts ← mathSetOf (slotPairOf 2 text mono)
  let (edgeDoc, _) := (fun (r : Array Parse.Raw × Array Diag) => Elab.runRaws "edge2.lean" r.1 r.2)
    (Surface.readCode .lean "edge2.lean" edge2 (some facts2))
  let edgeLines := codePageLines fonts edgeDoc
  let afterProof := (edgeLines.zipIdx.filter fun ((mono, ink), _) =>
    !mono && ink.trimAscii.toString == "Proof").map fun (_, i) =>
      ((edgeLines[i + 1]?.map (ink ·.2)).getD "")
  t s!"views: each disclosure's code opens on its proof's first line of code, never a blank one ({afterProof})"
    (afterProof == #["byinductionnwith", "funhp=>", "simp/-closesit-/", "rfl", "exacthelpern"])
  let withDirective (dir : String) : String :=
    "-- leantex: " ++ dir ++ "\n" ++ "\n".intercalate ((src.splitOn "\n").drop 1)
  let readWith (dir : String) (place : Code.LinkPlace := {}) : Ir.Doc × Array Diag :=
    let (raws, ds) := Surface.readCode .lean "statements.lean" (withDirective dir) (some facts) place
    Elab.runRaws "statements.lean" raws ds
  let starts := Code.lineStarts src.toList.toArray
  let folds := Code.foldsOf starts src.toList.toArray .collapse facts 0
  let removals := Code.foldsOf starts src.toList.toArray .remove facts 0
  let (folded, foldedDs) := readWith "show = code, proofs = collapse"
  t s!"views: each top-level theorem's proof of more than one line folds into one closed disclosure whose summary is Proof ({(disclosures folded).size} of {folds.length})"
    (folds.length ≥ 3 && removals.length > 20 && (disclosures folded).size == folds.length &&
      (disclosures folded).all (· == ("Proof", false)) && !foldedDs.any (·.kind == .W0110))
  t "views: the listings and the disclosures hold the file's code, every character but white space at a fold, in order"
    (ink (String.join (listingTexts folded).toList) ==
      ink (String.ofList (Code.codeOf (Code.segmentsOf .lean src))))
  let summaries := Tests.CodeDoc.elemTexts "summary" folded
  t s!"views: the web page folds each proof in a details element it opens on request ({summaries.size})"
    (summaries.size == folds.length && summaries.all (· == "Proof") &&
      (elemAttrsList (· == "details") #[] (docNodesOf folded).toList).all fun (_, attrs) =>
        (HtmlDoc.attrOf? attrs "open").isNone)
  let lines := codePageLines fonts folded
  let proofAt := lines.findIdx? fun (mono, ink) => !mono && ink.trimAscii.toString == "Proof"
  t "views: the printed page sets a folded proof open, its summary then its code"
    (proofAt.any fun i => (lines[i - 1]?.any (·.1)) && (lines[i + 1]?.any (·.1)))
  -- A page that removes its proofs.
  let (removed, _) := readWith "show = code, proofs = remove"
  let removedText := String.join (listingTexts removed).toList
  t "views: each removed proof leaves Lean's ⋯ after its signature and no character of its own"
    ((removedText.splitOn "⋯").length == removals.length + 1 &&
      (removedText.splitOn "height rise (2 * n) = 2 * height rise n := ⋯").length == 2 &&
      (removedText.splitOn "Nat.mul_left_comm").length == 1 && (disclosures removed).isEmpty)
  let removedCode := Code.codeOf (Code.withFolds (Code.foldsOf starts src.toList.toArray .remove
    facts 0) (Code.segmentsOf .lean src))
  t "views: the listings hold the file's code exactly, each removed proof's characters as ⋯"
    (String.join ((listingTexts removed).toList.map fun c => (c.drop 1).toString) ==
      String.ofList removedCode)
  -- Statements whose names link to their declarations.
  let (linked, linkedDs) := readWith "show = math, code, link = https://github.com/acme/tides"
    { commit := some "c0ffee", path := some "testdata/codedoc/lean/statements.lean"
      dirty := some false, tracked := true }
  let hrefs := Tests.CodeDoc.hrefs linked
  t s!"views: each statement's name links to its declaration's lines at the file's commit ({hrefs.size})"
    (hrefs.contains "https://github.com/acme/tides/blob/c0ffee/testdata/codedoc/lean/statements.lean#L11-L13" &&
      !linkedDs.any fun d => d.kind == .W0431 || d.kind == .W0432)
  let (worded, wordedDs) := readWith "show = prose, code, link = https://github.com/acme/tides"
    { commit := some "c0ffee", path := some "testdata/codedoc/lean/statements.lean"
      dirty := some false, tracked := true }
  t "views: a statement said in words links its name as its mathematics does"
    (Tests.CodeDoc.hrefs worded == hrefs && !wordedDs.any fun d => d.kind == .W0431 || d.kind == .W0432)
  let (foldedMath, _) := readWith "show = math, prose, code, proofs = collapse"
  let foldedMathLines := codePageLines fonts foldedMath
  t s!"views: a page that sets statements folds each proof into a disclosure of its own code ({(disclosures foldedMath).size})"
    ((disclosures foldedMath).size == folds.length &&
      (disclosures foldedMath).all (· == ("Proof", false)) &&
      ink (String.join (listingTexts foldedMath).toList) ==
        ink (String.ofList (Code.codeOf (Code.segmentsOf .lean src))) &&
      foldedMathLines.any (fun (_, l) => l.startsWith "Theorem (Tide.le_or_gt). For"))
  let twin := MarkdownDoc.emit linked
  t "views: the markdown twin keeps a broken statement's formulas apart, so none reads as a display"
    ((twin.splitOn "$$").length == 1 && (twin.splitOn "**Theorem** (").length > 20)
  let (unlinked, unlinkedDs) := readWith "show = math, code, link = https://github.com/acme/tides"
  t "views: with no commit to name, the names set without links and the loss is named once"
    ((Tests.CodeDoc.hrefs unlinked).isEmpty && (unlinkedDs.filter (·.kind == .W0432)).size == 1)
  let emptyRead := Surface.readCode .lean "statements.lean"
    (withDirective "show = math, link = https://github.com/acme/tides")
    (some { facts with decls := #[], failed := #[] })
  let emptyDs : Array Diag := (Elab.runRaws "statements.lean" emptyRead.1 emptyRead.2).2
  t "views: a link with no statement to carry it raises no link loss"
    (!emptyDs.any fun d => d.kind == .W0431 || d.kind == .W0432)
  let idle (dir : String) (lang : Ir.CodeLang := .lean) : Array (Option String) :=
    ((Code.showingOfEntries lang (Decl.splitEntries dir)).idle lang ⟨"t", {}⟩).map
      fun (d : Diag) => d.subject
  t "views: an option the page cannot honour is named: a link with no statement, a key only a Lean page reads, a decls naming nothing"
    (idle "link = https://e.org" == #[some "code:link"] &&
      idle "show = math, decls = {}" == #[some "code:decls"] &&
      idle "proofs = remove, link = https://e.org" .python == #[some "code:proofs", some "code:link"] &&
      idle "show = math, link = https://e.org" == #[] &&
      idle "decls = {a}" == #[some "code:decls"] && idle "show = math, decls = {a}" == #[] &&
      ((Code.showingOfEntries .lean (Decl.splitEntries "decls = {a}")).idle .lean ⟨"t", {}⟩
        (page := false)).isEmpty)
  let theorems (dir : String) : Nat := ((MarkdownDoc.emit (readWith dir).1).splitOn "**Theorem** (").length
  t "views: a page whose decls names nothing sets every statement, as the note says"
    (theorems "show = math, code, decls = {}" == theorems "show = math, code" &&
      theorems "show = math, code" > 20)
  -- A file included in a document.
  let request : Span := ⟨"host.tex", { line := 3, col := 1 }⟩
  let incl (opts : String) (given : Option LeanFacts.Facts) (place : Code.LinkPlace := {}) :
      Array Parse.Raw × Array Diag :=
    Code.includeLean "statements.lean" src
      (Code.showingOfEntries .lean (Decl.splitEntries opts) true) given place request "`\\inputlean`"
  let docOf (rs : Array Parse.Raw × Array Diag) : Ir.Doc × Array Diag :=
    Elab.runRaws "host.tex" (#[.env "document" rs.1 {}]) rs.2
  let (whole, wholeDs) := docOf (incl "" none)
  t "views: a file included with nothing that asks Lean is one listing of the whole file"
    (listingTexts whole == #["\n" ++ (String.ofList ((src.toList.reverse.dropWhile Code.isWhite).reverse))] &&
      !wholeDs.any fun d => d.kind == .W0110 || d.kind == .W0414)
  let (chosen, chosenDs) := docOf (incl "show = {math, code}, decls = {height_double, nothere}, proofs = remove" (some facts))
  let chosenLines := codePageLines fonts chosen
  let codeAfter (i : Nat) : String :=
    String.join (((chosenLines.extract (i + 1) chosenLines.size).filter (·.1)).map (·.2)).toList
  let statementAt := chosenLines.findIdx? fun (mono, ink) =>
    !mono && ink.startsWith "Theorem (Tide.height_double)."
  t s!"views: an included declaration sets its views in order, its proof removed, and a name Lean does not hold is named ({chosenDs.map (·.subject)})"
    (statementAt.any (fun i => ((codeAfter i).splitOn "theorem height_double").length == 2) &&
      (listingTexts chosen).size == 1 &&
      ((listingTexts chosen).all fun c => (c.splitOn "2 * height rise n := ⋯").length == 2) &&
      chosenDs.any (·.subject == some "code:decls:nothere"))
  let (spoken, _) := docOf (incl "show = {prose, code}, decls = {le_or_gt}" (some facts))
  let spokenLines := codePageLines fonts spoken
  t "views: an included declaration says its statement in words, then sets its code"
    ((spokenLines.findIdx? fun (_, l) => l.startsWith "Theorem (Tide.le_or_gt). For").any fun i =>
      ((spokenLines.extract (i + 1) spokenLines.size).filter (·.1)).any fun (_, l) =>
        (l.splitOn "theorem le_or_gt").length == 2)
  let (_, phrasedDs) := docOf (incl "show = prose, phrase.zz = \"#1 is void\"" (some facts))
  t s!"views: an inclusion's phrase is refused at the request that declares it ({phrasedDs.map (·.subject)})"
    (phrasedDs.any fun d => d.kind == .W0416 && d.span == some request)
  let (strange, strangeDs) := docOf (incl "caption = x, proofs = folded" none)
  let strangeNotes := strangeDs.filter fun (d : Diag) => d.kind == .W0110
  t "views: an inclusion names, at its request, a key no option has and a value no mode has, and includes the file whole"
    ((listingTexts strange).size == 1 &&
      strangeNotes.map (·.subject) == #[some "code:proofs:folded", some "code:option:caption"] &&
      strangeNotes.all fun d => d.span == some request)
  let (_, barelyDs) := docOf (incl "link" none)
  t "views: an inclusion names a key written without a value by the key"
    (barelyDs.any fun d => d.subject == some "code:option:link" &&
      (d.message.splitOn "`link` is written without a value").length == 2)
  let (all, allDs) := docOf (incl "show = {math, code}, proofs = collapse" (some facts))
  let allText := String.join (listingTexts all).toList
  t s!"views: an inclusion with no decls sets the whole file, each statement at its declaration, every line not folded ({(listingTexts all).size} listings)"
    (["namespace Tide", "end Tide", "/-! # Tide arithmetic", "open Nat in", "universe u"].all
        (fun w => (allText.splitOn w).length > 1) &&
      (disclosures all).size == folds.length &&
      ink allText == ink src &&
      (codePageLines fonts all).any (fun (_, ink) =>
        ink.startsWith "Theorem (Tide.height_double).") &&
      !allDs.any (·.kind == .W0110))
  -- The fenced division markdown includes a Lean file by.
  let (blks, _) := Md.blocks "d.md" "Before.\n\n::: {.lean file=\"F.lean\" show=\"math, code\"}\n:::\n\nAfter.\n"
  t s!"views: a fenced division of class lean reads as one inclusion between its neighbours ({repr blks})"
    (match blks.toList with
      | [.para _ _, .lean attrs _, .para _ _] => attrs == #[("file", "F.lean"), ("show", "math, code")]
      | _ => false)
  let (others, _) := Md.blocks "d.md" "::: {.note}\nText.\n:::\n"
  t "views: a fenced division of another class stays text, as CommonMark reads it"
    (others.all fun b => match b with
      | .para _ _ => true
      | _ => false)
  let (raws, _) := Md.desugar "d.md" "::: {.lean file=\"F.lean\" show=\"math, code\"}\n:::\n"
  t s!"views: the division lowers onto the inclusion command, its keys as the command's options ({Parse.rawSrc raws})"
    (Parse.rawSrc raws == "\\inputlean [show = {math, code}]{F.lean}")
  let mdSrc := "Before.\n\n::: {.lean file=\"fixtures/example.lean\"}\n:::\n"
  let (mdRaws, mdDs) := Surface.read .markdown "testdata/compat-index/probe.md" mdSrc
  let (executed, inputDs, _) ← Input.expandInputs "testdata/compat-index/probe.md" mdRaws
  let (mdDoc, _) := Elab.runExecuted "testdata/compat-index/probe.md" executed (mdDs ++ inputDs)
  t "views: a markdown page includes the file the division names, read beside the page"
    ((listingTexts mdDoc).any fun c => (c.splitOn "theorem steps_zero").length == 2)
  let (goneRaws, _) := Surface.read .markdown "testdata/compat-index/probe.md"
    "::: {.lean file=\"fixtures/gone.lean\"}\n:::\n"
  let (_, goneDs, _) ← Input.expandInputs "testdata/compat-index/probe.md" goneRaws
  t "views: a division whose file is not there names the division, not the command it lowers onto"
    (goneDs.any fun d => d.kind == .E0502 &&
      (d.message.splitOn "the Lean division's file 'fixtures/gone.lean' is not there").length == 2)

end Tests.LeanViews
