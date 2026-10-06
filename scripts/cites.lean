/-
Does every theorem name a docstring cites resolve to a declaration?

  lake build LeanTex TestsModules Obligations ScriptsModules leantex Tests cites
  .lake/build/bin/cites --check

AGENTS.md asks that a guarantee stated in prose name the theorem holding it.
A cited name that resolves to nothing is that rule's failure mode: the
docstring reads as a guarantee held, and nothing holds it.

This is the gate the pre-commit hook and CI both run, and it is a separate
binary from precommit for one reason: it needs a compiled `Environment`. The
docstrings come from `Lean.findDocString?` over the imported modules and the
names are resolved by `Lean.ResolveName.resolveGlobalName` -- the resolver
the elaborator itself uses. Its predecessor scanned source text for a
declaration keyword, and text-scanning cost it three recorded blind spots: a
declaration whose name sat on a continuation line was invisible, a name that
existed only inside a test's check-label string resolved, and a name matched
by the `n ++ "_"` prefix rule resolved on a relative's spelling. None of the
three survives a resolver that reads what the compiler built.

The limit that remains, which no gate closes: this proves a cited name
RESOLVES, not that the declaration it resolves to states the fact the prose
claims. `foo_exact` may resolve to a theorem about something else entirely,
and the docstring would still read as a guarantee held. Judging a statement
against the sentence citing it stays review's job.

--selftest compiles synthetic modules and exercises inventory and resolution;
--census prints the numbers; --check is the quiet gate mode.
-/

import Lean
import scripts.Gate
import scripts.ProofSources
import scripts.CiteEnv

open Lean CiteEnv

/-- A backticked token that reads as a theorem name in this tree: it opens
with a lowercase ASCII letter, is spelled only in ASCII letters, digits and
underscores, and carries an interior underscore -- the snake_case joint every
theorem name here is built from (`html_fonts_cover_pdf`,
`footBand_projects`). The tree's other backticked things are each a
different shape, and none of them matches: a camelCase def or field
(`foldInlines`), a dotted or spaced type (`Ir.dump`, `Array Block`), a flag
(`--wfail`), a path (`testdata/compat-index`), a SCREAMING_SNAKE environment or
format key (`LEANTEX_FONT`, `ICC_PROFILE`), prose. -/
def citeBare (tk : String) : Bool :=
  let cs := tk.toList
  !cs.isEmpty
    && cs.all isWordChar
    && ((cs.head?.map Char.isLower).getD false)
    && ((cs.getLast?.map (· != '_')).getD false)
    && containsSub tk "_"

/-- The namespace-qualified spelling of the same thing: `Elab.x`,
`Obligations.y`, `Diag.tallySites_exact`. A citation reaching out of its own
file writes the qualifier, and this tree's house style does so routinely, so
the bare form alone left a hole -- three dangling citations to a theorem that
never existed passed the gate under the dotted spelling, in the very change
that recorded the hole. The qualifier must look like one (capitalised
segments, word characters only) and the last component must be the bare
shape, which is what keeps `Ir.dump` and `Font.FontSet` out. -/
def citeQualified (tk : String) : Bool :=
  match tk.splitOn "." with
  | [] | [_] => false
  | segs =>
    let last := segs.getLast!
    let quals := segs.dropLast
    citeBare last
      && quals.all fun q =>
        let cs := q.toList
        !cs.isEmpty && cs.all isWordChar && ((cs.head?.map Char.isUpper).getD false)

/-- Either spelling. -/
def citeCandidate (tk : String) : Bool := citeBare tk || citeQualified tk

/-- The closed backticked spans of a line, in order. An unclosed span -- a
citation wrapped across two lines -- is dropped rather than guessed at. -/
def backtickSpans (l : String) : List String := Id.run do
  let parts := (l.splitOn "`").toArray
  let n := if parts.size % 2 == 0 then parts.size - 1 else parts.size
  let mut out : Array String := #[]
  for i in [0:n] do
    if i % 2 == 1 then out := out.push (parts[i]?.getD "")
  return out.toList

/-- Names that are legitimately not declarations of this tree: foreign
vocabulary that happens to be spelled snake_case, each named where it comes
from. A new entry is a deliberate decision -- the question it answers is
"whose name is this?", and only an answer outside this repository earns a
row.

The resolver shrinks the gate's other allowlist and leaves this one exactly
where it was, and that is the honest outcome rather than a shortfall: every
row names a thing outside this repository, so no resolver over this
environment can ever resolve it. TeX's `mlist_to_hlist` is not a declaration
here and will not become one. What the resolver removed is the class these
rows were once confused with -- a name that IS this tree's and that a text
scan could not see. -/
def citeForeign : List String :=
  ["default_rule_thickness",   -- TeX's math fontdimen (TeXbook, Appendix G)
   "good_length",              -- zlib's deflate configuration field
   "headless_shell",           -- Chrome's own binary name
   "mlist_to_hlist",           -- TeX's math-list conversion pass
   "x_y",                      -- an example label key, quoted as prose
   "xn_over_d"]                -- TeX's scaled-integer routine (TeX §107)

/-- The phantom citations standing when this resolver landed: a backticked
theorem name in a docstring that resolves to no declaration. Each is a
guarantee that reads as held and is not, so the list may only shrink -- a new
phantom fails the commit. A name leaves this list when its citation is
corrected (the theorem is written, the claim is restated in prose, or the
dead name is deleted).

Sixteen stood when the text-scanning gate landed; eleven were resolved over
two sweeps, and the five that remained were all cited from
`LeanTex/Core/Ir.lean`. Those five are now gone too, and not one of them
needed a proof it did not have: four were mislabels, where the fact was
held by something other than the name written down -- an oracle called "the
statement" twice (the boundary request's byte-identity, `boundaryChecks`;
a pure function's determinism is definitional, so no theorem was ever owed
there), an equation a deleted one-line renderer carried and its own
declaration now states, and two live holders one sentence away that did
not say their names (`langWrap_text`, three lines below its own label, and
`pages_partition_frames`, the record Obligations.lean actually states over
`Ir.frameSteps`). The fifth, `algorithm_lines_agree`, was the one that did
owe a proof: the HTML nesting builder was factored out of its match arm so
a statement had something to range over, and the theorem was written.
PLAN 2026-09-23 carries the accounts. A row names the anchor declaration
rather than a line: every line number the first sweep recorded had moved
by the second.

Two rows arrived with the resolver, and neither is new debt -- both were
standing phantoms the text scan could not see, and each is one word to
repair:

  frames_sections   cited from the docstrings of `Ir.frameSteps` and of
                    `deckStepChecks`. It is the name of a check LABEL, not
                    of a declaration: Tests/Themes.lean spells it inside the
                    string a test is titled with. The predecessor resolved a
                    citation against test-label strings, which is how a
                    label came to read as a theorem. The claim is genuinely
                    held -- by `deckStepChecks`, which resolves -- so the
                    repair is to cite the checks by their declaration, or to
                    drop the backticks and let the sentence name the census
                    in prose.
  sty_is_defaults   cited from the docstrings of both halves,
                    `sty_is_defaults_tokens` and `sty_is_defaults_palette`.
                    Nothing carries the shared prefix: it names the pair,
                    which is a pair and not a theorem. The predecessor's
                    resolver accepted a name whenever some declaration
                    started with it and an underscore, so the two halves
                    vouched for a name neither of them is. The repair is to
                    name both halves, or to write the sentence without the
                    shared stem.

Keyed by name and site: a row is one citation's anchor, so the ratchet reads
in both directions, as `subjectDebt` and `siteAccounting` do. A second
citation of a parked name is a new phantom, since a parked name is not a
licence to cite it again, and a row whose citation was fixed is dead and
fails `--check` until it is deleted, so the list cannot hold a name after
its debt is paid. The site is the file and the compiled declaration whose docstring
carries the citation, or `the module docstring` for a module's own. Line numbers are not keys, because every line number the
first sweep recorded had moved by the second.

The list stays when it empties. `citeCandidate` recognises a citation by its
spelling, so the gate can fire on prose that makes no claim -- a docstring
may name a deleted theorem as history -- and a false positive needs a
parking place that names the real holder, or the next reader silences it by
deleting the sentence. That is the one repair this gate must not buy, and an
empty list with no row to imitate invites it. A row added here carries the
same three things every row above did: the anchor declaration, what actually
holds the fact, and the one-line fix. -/
structure PhantomRow where
  name : String
  file : String
  anchor : String
  deriving BEq, Repr, Inhabited

def citePhantomKnown : List PhantomRow :=
  [⟨"frames_sections", "LeanTex/Core/Ir.lean", "LeanTex.Core.Ir.frameSteps"⟩,
   ⟨"frames_sections", "Tests/Themes.lean", "deckStepChecks"⟩,
   -- Five the qualified-spelling hole hid: the resolver read only the bare
   -- snake_case form, so a citation written `Namespace.theorem_name` was not
   -- a candidate at all, and the gate never asked. They are pre-existing,
   -- each in a file this branch does not own, and each is routed with its
   -- owner rather than silenced by deleting the sentence.
   --
   -- The claim is that a frame's overflow is named rather than dropped.
   -- `Layout` states nothing of the kind. Fix: state it over `Layout.Out`
   -- beside the spill emission, or drop the name and let `censusChecks`
   -- carry it.
   ⟨"Layout.spill_accounts", "LeanTex/Core/Ir.lean", "LeanTex.Core.Ir.Block.frame"⟩,
   -- The attachment point is claimed covered for every base. Fix: state it
   -- over `Font.topAccentX` itself, where the fallback arm lives.
   ⟨"Math.accentAttach_covers", "LeanTex/Core/Font.lean", "LeanTex.Core.Font.Font.topAccentX"⟩,
   -- A picture label's face is claimed to agree across backends.
   -- `pictureLabelFaceChecks` is the artifact witness; the IR theorem it
   -- projects from is unwritten. Fix: state the `_agree` over the one IR
   -- value both backends read.
   ⟨"Picture.labelFace_agree", "Tests/Support.lean", "CensusLine.runFonts"⟩,
   ⟨"Picture.labelFace_agree", "Tests/Surface.lean", "pictureLabelFaceChecks"⟩,
   -- Relative node placement claimed exact, at two sites. Nothing states
   -- it; the rows of `pictureNodePlaceChecks` read it off shipped pages.
   -- Fix: state it where the placement is computed.
   ⟨"Picture.placeRel_exact", "Tests/Support.lean", "CensusPage.pathBoxes"⟩,
   ⟨"Picture.placeRel_exact", "Tests/Surface.lean", "pictureNodePlaceChecks"⟩,
   -- Whole-picture permutation remains an executable placement check.
   -- Picture.NodePlan.place_order_agree proves the actual resolving
   -- operations commute under independent reads and writes; it does not
   -- prove the former arbitrary-source claim, refuted by duplicate names.
   -- Fix: cite that local contract with its scope and keep the global
   -- claim attributed to pictureNodePlaceChecks.
   ⟨"Picture.place_order_agree", "Tests/Support.lean", "CensusPage.pathBoxes"⟩]

/-- The phantom judgement, pure so the selftest drives it in both
directions: the hits no row parks (a new phantom, or a new site of a parked
name), and the rows no hit met (dead, because the citation was fixed). -/
def judgePhantoms (rows : List PhantomRow) (hits : Array PhantomRow) :
    Array PhantomRow × List PhantomRow :=
  (hits.filter (!rows.contains ·), rows.filter (!hits.contains ·))

/-- The anchor a site is keyed by: the declaration its docstring is
attached to, as `Site.subject` spells it without the backticks. -/
def anchorOf (subject : String) : String :=
  (subject.replace "`" "").trimAscii.toString

/-- The continuation-line declaration is a regression witness for compiled
lookup: a source scanner looking beside the keyword missed it. -/
theorem
    cite_continuation_witness : True := trivial

def readCiteJson [FromJson α] (path : System.FilePath) : IO α := do
  match Json.parse (← IO.FS.readFile path) >>= fromJson? with
  | .ok value => return value
  | .error why => throw <| IO.userError s!"cites: invalid worker data in {path}: {why}"

def runBatch (modules : Array String) (collect : Bool)
    (queries : Array Query := #[]) : IO Response :=
  IO.FS.withTempDir fun dir => do
    let request := dir / "request.json"
    let response := dir / "response.json"
    let paths := (← searchPathRef.get).toArray.map (·.toString)
    IO.FS.writeFile request (toJson ({ modules, paths, collect, queries } : Request)).compress
    let bin ← IO.appPath
    let workerArgs ← if bin.fileName == some "lean" then do
      pure #["--run", (← IO.FS.realPath "scripts/cites.lean").toString]
      else pure #[]
    let out ← IO.Process.output {
      cmd := bin.toString
      args := workerArgs ++ #["--batch", request.toString, response.toString] }
    unless out.exitCode == 0 do
      throw <| IO.userError s!"cites: compiled batch {modules} failed ({out.exitCode}):\n\
        {out.stdout}{out.stderr}"
    let result : Response ← readCiteJson response
    unless result.modules == modules && result.verdicts.size == queries.size do
      throw <| IO.userError s!"cites: incomplete worker response for {modules}"
    return result

structure CompiledTree where
  batches : Array (Array String)
  sites : Array Site

/-- Use the proof gate's complete inventory and executable grouping. Every source
must have a compiled module; source text never substitutes for compiler metadata.
Workers run sequentially because dropping an Environment does not release its
imported memory regions. -/
def loadTree (root : System.FilePath := ".") : IO CompiledTree := do
  let files ← ProofSources.sources root
  if files.isEmpty then throw <| IO.userError "cites: no maintained source modules found"
  requireCompiled (files.map ProofSources.moduleName)
  let batches := ProofSources.groups files
  let mut docs := #[]
  for modules in batches do
    docs := docs ++ (← runBatch modules true).sites
  return ⟨batches, docs⟩

def bestVerdict : Verdict → Verdict → Verdict
  | .scope, _ | _, .scope => .scope
  | .tree, _ | _, .tree => .tree
  | .phantom, .phantom => .phantom

/-- Scope resolution uses the citing module and namespace, plus Obligations.
The tree tier permits the existing house style of citing another namespace's
short name. Both tiers require Lean to resolve a complete compiled declaration. -/
def resolveTree (tree : CompiledTree) (queries : Array Query) : IO (Array Verdict) := do
  let mut answers := Array.replicate queries.size Verdict.phantom
  for modules in tree.batches do
    let result ← runBatch modules false queries
    answers := answers.zipWith bestVerdict result.verdicts
  return answers

def citationQueries (sites : Array Site) : Array Query := Id.run do
  let mut seen : Std.HashSet Query := {}
  let mut out := #[]
  for site in sites do
    for line in site.text.splitOn "\n" do
      for token in backtickSpans line do
        if citeCandidate token && !citeForeign.contains token then
          let q : Query := ⟨site.moduleName, site.ns, token⟩
          unless seen.contains q do
            seen := seen.insert q
            out := out.push q
  return out

structure Census where
  sites : Nat := 0
  candidates : Nat := 0
  scope : Nat := 0
  tree : Nat := 0
  foreign : Nat := 0
  frozen : Nat := 0
  names : Std.HashSet String := {}
  foreignSeen : Std.HashSet String := {}
  phantoms : Array PhantomRow := #[]
  deriving Inhabited

/-- Every phantom citation no row parks, the rows no citation met, and the
census of what was judged. -/
def scan (tree : CompiledTree) (rows : List PhantomRow := citePhantomKnown) :
    IO (Array (String × String × Nat × String) × List PhantomRow × Census) := do
  let queries := citationQueries tree.sites
  let answers ← resolveTree tree queries
  let verdicts : Std.HashMap Query Verdict := .ofArray (queries.zip answers)
  let mut bad : Array (String × String × Nat × String) := #[]
  let mut c : Census := { sites := tree.sites.size }
  for s in tree.sites do
    for l in s.text.splitOn "\n" do
      for tk in backtickSpans l do
        unless citeCandidate tk do continue
        c := { c with candidates := c.candidates + 1 }
        c := { c with names := c.names.insert tk }
        if citeForeign.contains tk then
          c := { c with foreign := c.foreign + 1 }
          c := { c with foreignSeen := c.foreignSeen.insert tk }
        else match verdicts[(⟨s.moduleName, s.ns, tk⟩ : Query)]?.getD Verdict.phantom with
          | .scope => c := { c with scope := c.scope + 1 }
          | .tree => c := { c with tree := c.tree + 1 }
          | .phantom =>
            let hit : PhantomRow := ⟨tk, s.file, anchorOf s.subject⟩
            c := { c with phantoms := c.phantoms.push hit }
            if rows.contains hit then
              c := { c with frozen := c.frozen + 1 }
            else bad := bad.push (tk, s.file, s.line, s.subject)
  let (_, dead) := judgePhantoms rows c.phantoms
  return (bad, dead, c)

/-- Compile an isolated tree whose extra library, unused private declarations,
aliases and independent executable roots all owe the same citation check. -/
def compiledSelftest : IO (List String) := IO.FS.withTempDir fun dir => do
  let failures ← IO.mkRef ([] : List String)
  let expect (label : String) (ok : Bool) : IO Unit :=
    unless ok do failures.modify (label :: ·)
  let before ← searchPathRef.get
  let paths := dir :: before
  let sysroot ← findSysroot
  try
    searchPathRef.set paths
    let fixtures : Array (String × String) := #[
      ("Extra.Origin", "module\nnamespace Extra.Origin\n\
        public theorem alias_invariant : True := trivial\n\
        end Extra.Origin\n"),
      ("Extra.Unimported", "module\npublic import Extra.Origin\n\
        /-! The module claim `missing_module_invariant` must fail. -/\n\
        namespace Extra\n\
        /-- The private claim `private_invariant` is checked. -/\n\
        private theorem private_invariant (n : Nat) : n = n := rfl\n\
        /-- The private claim `missing_private_invariant` must fail. -/\n\
        private def hiddenAnchor : Nat := 0\n\
        /-- The public claim `missing_public_invariant` must fail. -/\n\
        public def anchor : Nat := 0\n\
        export Origin (alias_invariant)\n\
        /-- The exported claim `Extra.alias_invariant` is checked. -/\n\
        public def aliasAnchor : Nat := 1\n\
        public structure Box where\n  value : Nat\n\
        public def label := \"label_only_invariant\"\n\
        public theorem split_invariant_left : True := trivial\n\
        public theorem split_invariant_right : True := trivial\n\
        end Extra\n\
        public theorem\n  fixture_continuation_witness : True := trivial\n"),
      ("LeanTex.CiteProbe", "module\nnamespace Local\n\
        /-- The private contract `Local.local_invariant` is checked. -/\n\
        private theorem local_invariant (n : Nat) : n = n := rfl\n\
        end Local\n"),
      ("Obligations", "module\nnamespace Obligations\n\
        public theorem staged_invariant : True := trivial\nend Obligations\n"),
      ("Tools.One", "/-- The executable claim `missing_one_invariant` must fail. -/\n\
        def main : IO Unit := pure ()\n"),
      ("Tools.Two", "/-- The other executable claim `missing_two_invariant` must fail. -/\n\
        def main : IO Unit := pure ()\n")]
    for (name, body) in fixtures do
      let file := dir / moduleFile name
      IO.FS.createDirAll file.parent.get!
      IO.FS.writeFile file body
      let out ← IO.Process.output {
        cmd := (sysroot / "bin" / "lean").toString
        args := #["-E", "hasSorry", "-R", dir.toString,
          "-o", (file.withExtension "olean").toString, file.toString]
        env := #[("LEAN_PATH", some (System.SearchPath.toString paths))] }
      unless out.exitCode == 0 do
        throw <| IO.userError s!"cites selftest: cannot compile {name}:\n{out.stdout}{out.stderr}"
    let tree ← loadTree dir
    expect "inventory omitted an unimported library or executable"
      ((tree.batches.flatMap id).size == fixtures.size)
    for subject in ["`Extra.hiddenAnchor`", "`Extra.anchor`", "`Local.local_invariant`"] do
      expect s!"compiled private/public docstring absent or mangled: {subject}"
        (tree.sites.any fun site => site.subject == subject && site.line > 0)
    expect "modern module docstring absent"
      (tree.sites.any fun site =>
        site.file == "Extra/Unimported.lean" && site.subject == "the module docstring")
    let q (token : String) (ns : Name := .anonymous)
        (moduleName : String := "Extra.Unimported") : Query := ⟨moduleName, ns, token⟩
    let cases : Array (String × Query × Verdict) := #[
      ("absent name", q "no_such_theorem_anywhere", .phantom),
      ("check-label string", q "label_only_invariant" `Extra, .phantom),
      ("shared prefix", q "split_invariant" `Extra, .phantom),
      ("continuation-line declaration", q "fixture_continuation_witness" `Extra, .scope),
      ("staging namespace", q "staged_invariant" `Extra, .scope),
      ("private bare name", q "private_invariant" `Extra, .scope),
      ("private qualified name", q "Extra.private_invariant", .scope),
      ("modern private doc namespace", q "Local.local_invariant" `Local "LeanTex.CiteProbe", .scope),
      ("exported alias", q "Extra.alias_invariant", .scope),
      ("short exported alias", q "alias_invariant" `Extra, .scope),
      ("alias across namespaces", q "alias_invariant" `Elsewhere "Tools.One", .tree),
      ("private across namespaces", q "local_invariant" `Elsewhere "Tools.One", .tree),
      ("invented field projection", q "Extra.Box.missing_invariant", .phantom)]
    let verdicts ← resolveTree tree (cases.map fun (_, query, _) => query)
    for ((label, _, want), got) in cases.zip verdicts do
      expect s!"{label}: got {repr got}, want {repr want}" (got == want)
    let (bad, dead, census) ← scan tree []
    let names := bad.map fun (name, _, _, _) => name
    let missing := #["missing_module_invariant", "missing_private_invariant",
      "missing_public_invariant", "missing_one_invariant", "missing_two_invariant"]
    expect "full compiled scan missed a phantom or rejected a valid private/alias citation"
      (names.size == missing.size && missing.all names.contains && dead.isEmpty)
    expect "private phantom lost its actionable source location"
      (census.phantoms.contains ⟨"missing_private_invariant",
        "Extra/Unimported.lean", "Extra.hiddenAnchor"⟩ &&
        bad.any fun (name, _, line, _) => name == "missing_private_invariant" && line > 0)
    IO.FS.writeFile (dir / "Unbuilt.lean")
      "/-- The uncompiled claim `missing_unbuilt_invariant` cannot be read as compiled. -/\ndef x := 0\n"
    let missingRejected ← try
      let _ ← loadTree dir
      pure false
    catch e =>
      pure (containsSub e.toString "no compiled Unbuilt.lean" &&
        containsSub e.toString "lake build")
    expect "missing compiled source did not fail with a build instruction" missingRejected
    return (← failures.get).reverse
  finally
    searchPathRef.set before

/-- Every case the gate must catch and every legal spelling it must pass.
Positive cases are the shapes whose escape prompted a gate change; negative
cases are spellings of this tree. A gate that does not catch the shape it
commemorates grants false confidence, so a gate change lands with both. -/
def selftest : IO UInt32 := do
  let fails ← IO.mkRef ([] : List String)
  let expect (name : String) (p : String → Bool) (cases : List (String × Bool)) : IO Unit := do
    for (line, want) in cases do
      if p line != want then
        fails.modify (s!"{name} {if want then "missed" else "fired on"}: {line}" :: ·)

  expect "citeCandidate" citeCandidate [
    -- theorem names, the shape the gate must judge
    ("footBand_projects", true),
    ("html_fonts_cover_pdf", true),
    ("leafOwners_mem", true),
    ("labMix_L", true),
    ("x_y", true),
    -- the qualified spelling, which is how a citation reaches another file
    ("Elab.warnUnknownCmd_pushes_one", true),
    ("Ir.floorMask_id", true),
    ("Diag.tallySites_exact", true),
    ("LeanTex.Core.Elab.runShape_fold_exact", true),
    -- everything else the tree backticks
    ("foldInlines", false),
    ("Ir.dump", false),
    ("Font.FontSet", false),
    ("Layout.Out", false),
    ("elab.x_y", false),
    (".x_y", false),
    ("x_y.", false),
    ("Array Block", false),
    ("Conserves", false),
    ("--wfail", false),
    ("testdata/compat-index", false),
    ("LEANTEX_FONT", false),
    ("ICC_PROFILE", false),
    ("White_Space", false),
    ("_leading", false),
    ("trailing_", false),
    ("lake env lean --run scripts/owed.lean", false),
    ("", false)]

  let spanCases : List (String × List String) := [
    ("the `features_agree` claim and `steps_agree`", ["features_agree", "steps_agree"]),
    ("no citation here", []),
    ("an unclosed `span is dropped", []),
    ("`opens the line` and closes", ["opens the line"])]
  for (line, want) in spanCases do
    if backtickSpans line != want then
      fails.modify (s!"backtickSpans: {line} gave {backtickSpans line}" :: ·)

  -- The two lists are disjoint and each name on them is a candidate: a row
  -- that the rule would never fire on is dead weight that reads as debt.
  for n in citeForeign do
    unless citeCandidate n do
      fails.modify (s!"allowlisted name is not a candidate: {n}" :: ·)
    if citePhantomKnown.any (·.name == n) then
      fails.modify (s!"name on both citation lists: {n}" :: ·)
  for r in citePhantomKnown do
    unless citeCandidate r.name do
      fails.modify (s!"allowlisted name is not a candidate: {r.name}" :: ·)
  unless citePhantomKnown.eraseDups.length == citePhantomKnown.length do
    fails.modify ("a parked phantom row is listed twice" :: ·)

  -- The parked list reads in both directions. A second site of a parked
  -- name is a new phantom, a row no citation meets is dead, and the rows a
  -- scan meets exactly pass.
  let row : PhantomRow := ⟨"zz_parked_name", "x.lean", "Zz.anchor"⟩
  let elsewhere : PhantomRow := { row with anchor := "Zz.other" }
  let (fresh, dead) := judgePhantoms [row] #[row, elsewhere]
  unless fresh == #[elsewhere] && dead.isEmpty do
    fails.modify ("judgePhantoms: a new site of a parked name passed" :: ·)
  let (fresh, dead) := judgePhantoms [row, elsewhere] #[row]
  unless fresh.isEmpty && dead == [elsewhere] do
    fails.modify ("judgePhantoms: a row no citation meets passed" :: ·)
  let (fresh, dead) := judgePhantoms [row] #[row, row]
  unless fresh.isEmpty && dead.isEmpty do
    fails.modify ("judgePhantoms: two citations at one parked site failed" :: ·)
  unless anchorOf "`LeanTex.Core.Ir.frameSteps`" == "LeanTex.Core.Ir.frameSteps" do
    fails.modify ("anchorOf: the backticked subject did not read as its declaration" :: ·)

  for failure in ← compiledSelftest do
    fails.modify (failure :: ·)

  let failed := (← fails.get).reverse
  if failed.isEmpty then
    IO.println "cites selftest: all passed"
    return 0
  for f in failed do
    IO.eprintln s!"FAIL {f}"
  return 1

def main (args : List String) : IO UInt32 := do
  if let ["--batch", request, response] := args then
    let result ← CiteEnv.run (← readCiteJson request)
    IO.FS.writeFile response (toJson result).compress
    return 0
  initSearchPath (← findSysroot) [".lake/build/lib/lean"]
  if args.contains "--selftest" then
    return (← selftest)
  let envs ← loadTree
  let (bad, dead, c) ← scan envs
  unless args.contains "--check" do
    IO.println s!"cites: {c.sites} docstrings, {c.candidates} citations \
      ({c.names.size} distinct names), {c.scope} resolving in scope, \
      {c.tree} resolving elsewhere in the tree, \
      {c.foreign} foreign ({c.foreignSeen.size} of {citeForeign.length} rows), \
      {c.frozen} frozen ({citePhantomKnown.length - dead.length} of \
      {citePhantomKnown.length} rows), {bad.size} phantom"
  if bad.isEmpty && dead.isEmpty then
    return 0
  unless dead.isEmpty do
    let rows := String.intercalate "\n"
      (dead.map fun r => s!"  `{r.name}` at {r.file} ({r.anchor})")
    IO.eprintln s!"cites: a parked phantom row meets no citation:
{rows}
  The citation it parked was fixed or moved, so the row is dead. Fix: delete
  the row, or, if the citation moved, key the row to where it stands now."
  if bad.isEmpty then
    return 1
  let hits := String.intercalate "\n"
    (bad.toList.map fun (n, f, i, subj) => s!"  {f}:{i} ({subj}): `{n}`")
  IO.eprintln s!"cites: a docstring cites a theorem name that resolves to nothing:
{hits}
  A guarantee stated in prose names the theorem holding it (AGENTS.md,
  Conventions); a name that resolves to nothing reads as held and is not.
  Fix: write the theorem, or cite the one that does hold the claim, or state
  the claim without a name. A name that is not this tree's -- foreign
  vocabulary spelled snake_case -- goes in citeForeign with its source. A
  parked name is parked at its own sites only, so citing it again is new."
  return 1
