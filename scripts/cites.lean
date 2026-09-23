/-
Does every theorem name a docstring cites resolve to a declaration?

  lake build leantex Tests Obligations precommit owed cites
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

--selftest exercises the predicates and the resolver against this tree;
--census prints the numbers; --check is the quiet gate mode.
-/

import Lean
import scripts.Gate

open Lean

/-- A backticked token that reads as a theorem name in this tree: it opens
with a lowercase ASCII letter, is spelled only in ASCII letters, digits and
underscores, and carries an interior underscore -- the snake_case joint every
theorem name here is built from (`html_fonts_cover_pdf`,
`footBand_projects`). The tree's other backticked things are each a
different shape, and none of them matches: a camelCase def or field
(`foldInlines`), a dotted or spaced type (`Ir.dump`, `Array Block`), a flag
(`--wfail`), a path (`tests/compat-index`), a SCREAMING_SNAKE environment or
format key (`LEANTEX_FONT`, `ICC_PROFILE`), prose. -/
def citeCandidate (tk : String) : Bool :=
  let cs := tk.toList
  !cs.isEmpty
    && cs.all isWordChar
    && ((cs.head?.map Char.isLower).getD false)
    && ((cs.getLast?.map (· != '_')).getD false)
    && containsSub tk "_"

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
two sweeps, and the five that remained are all cited from
`LeanTex/Core/Ir.lean`. PLAN 2026-09-23 carries the accounts. A row names the
anchor declaration rather than a line: every line number the first sweep
recorded had moved by the second.

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

Keyed by name, not by site: a second citation of a listed name passes, and
an entry left behind after its citation is fixed is dead weight rather than
a failure. Both are deliberate -- the ratchet's job is to stop new phantoms,
and neither looseness lets one through.

The list stays when it empties. `citeCandidate` recognises a citation by its
spelling, so the gate can fire on prose that makes no claim -- a docstring
may name a deleted theorem as history -- and a false positive needs a
parking place that names the real holder, or the next reader silences it by
deleting the sentence. That is the one repair this gate must not buy, and an
empty list with no row to imitate invites it. -/
def citePhantomKnown : List String :=
  ["algorithm_lines_agree", "boundary_request_deterministic",
   "footLine_eq_slots", "frames_sections", "language_attribute_text_free",
   "pages_count_frame_steps", "sty_is_defaults"]

/-- The modules this tree compiles, each with the lake target that builds
it. The gate imports all of them: a citation may be written anywhere, and a
name may be declared anywhere -- `Obligations` included, since a docstring
citing an owed statement names one that lives only there. A missing olean is
an error rather than a skip, so the gate's coverage never depends on which
targets happen to be warm.

Six import roots, not one: `Main`, `Tests`, and each gate script are
executables, and each declares `main`, so no single environment can hold two
of them. A name resolves when it resolves in any of the six, and a module's
docstrings are read from the first root that carries it. -/
def treeRoots : List (List (Name × String)) :=
  [[(`LeanTex, "leantex"), (`Obligations, "Obligations")],
   [(`Main, "leantex")],
   [(`Tests, "Tests")],
   [(`scripts.precommit, "precommit")],
   [(`scripts.owed, "owed")],
   [(`scripts.cites, "cites")]]

/-- The staging namespace every owed statement is declared in. A docstring
cites an owed theorem by its bare name, which is what the convention asks
for (the statement is staged away from the module that will own it), so the
scope a citation resolves in includes this namespace. -/
def stagingNamespace : Name := `Obligations

/-- The resolver's live witness, and the reason it is spelled across two
lines: its name does not sit on its keyword's line, which is the shape a
declaration scanner cannot see. A citation of `cite_continuation_witness`
read as a phantom under the predecessor and resolves here, and the selftest
asserts exactly that. Not an engine property, so the theorem-shape registry
does not reach it -- it is a fixture whose content is its layout. -/
theorem
    cite_continuation_witness : True := trivial

def ourModule (m : Name) : Bool :=
  [`LeanTex, `Main, `Tests, `Obligations, `scripts].contains m.getRoot

/-- The source file a module name came from. -/
def moduleFile (m : Name) : String :=
  String.intercalate "/" (m.components.map toString) ++ ".lean"

/-- The module name a source path would carry. -/
def fileModule (f : String) : Name :=
  let base := (f.splitOn ".lean").headD f
  (base.splitOn "/").foldl (fun n s => Name.mkStr n s) Name.anonymous

/-- Where a citation is written: the file and line for the report, the
namespace and open declarations that form its scope, and what the docstring
is attached to. -/
structure Site where
  file : String
  line : Nat
  ns : Name
  opens : List OpenDecl
  subject : String
  text : String

def mkSite (file : String) (line : Nat) (ns : Name) (opens : List OpenDecl)
    (subject text : String) : Site :=
  { file, line, ns, opens, subject, text }

/-- `open X` as the line spells it, for a file the build does not compile:
a script's scope is what its own open lines declare, and nothing persists
them into an environment. Only the `open A B` form is read -- `open X in`
and renaming forms are scoped to one declaration, and a script's file-level
opens are the ones a docstring is written under. -/
def openedIn (lines : Array String) : List OpenDecl := Id.run do
  let mut out : List OpenDecl := []
  for l in lines do
    let t := (stripLineComment l).trimAscii.toString
    if t.startsWith "open " && !containsSub t " in" && !containsSub t "(" then
      for w in ((t.drop 5).toString.split (· == ' ')) do
        let w := w.trimAscii.toString
        unless w.isEmpty do out := .simple w.toName [] :: out
  return out

/-- The docstring regions of a file, as text. Used only for a file the build
does not compile into a module -- a `lake env lean --run` script. A line
comment or a PLAN entry may legitimately name a theorem that was deleted, so
only a doc-comment opener starts a region. -/
def docRegions (lines : Array String) : Array (Nat × String) := Id.run do
  let mut out : Array (Nat × String) := #[]
  let mut inDoc := false
  for i in [0:lines.size] do
    let l := lines[i]?.getD ""
    if containsSub l "/--" || containsSub l "/-!" then inDoc := true
    if inDoc then
      out := out.push (i + 1, l)
      if containsSub l "-/" then inDoc := false
  return out

/-- Does `tok` resolve in `ns` under `opens`, the way the elaborator would
resolve an identifier written there? `resolveGlobalName` is the elaborator's
own primitive: it climbs the enclosing namespaces, honours aliases, private
and protected names, and the open declarations it is given. Any environment
answering yes is an answer: the roots partition one tree. -/
def resolvesIn (envs : Array Environment) (ns : Name) (opens : List OpenDecl)
    (tok : String) : Bool :=
  envs.any fun env =>
    !(ResolveName.resolveGlobalName env {} ns opens tok.toName).isEmpty

/-- The modules of this tree an environment carries, with their index in it. -/
def ourModules (env : Environment) : Array (Nat × Name) := Id.run do
  let mut out : Array (Nat × Name) := #[]
  for i in [0:env.header.moduleNames.size] do
    let m := (env.header.moduleNames[i]?).getD .anonymous
    if ourModule m then out := out.push (i, m)
  return out

/-- The namespaces a short name could resolve in, keyed by the name: for
every declaration this tree compiled, its last component maps to the
namespace holding it. The second resolution tier reads this to know which
namespaces are worth asking about -- the resolver still decides, this only
spares it the thousand that cannot answer. Complete for this tree because
this tree declares no aliases (no `export`, no `alias`); a tree that did
would want their names here too. -/
def shortIndex (envs : Array Environment) : Std.HashMap String (Array Name) := Id.run do
  let mut out : Std.HashMap String (Array Name) := {}
  for env in envs do
    for (i, _) in ourModules env do
      for n in (env.header.moduleData[i]?.map (·.constNames)).getD #[] do
        if let .str p s := n then
          out := out.insert s (((out[s]?).getD #[]).push p)
  return out

/-- The citation's resolution verdict.

`scope` is strict: the token resolves in the namespace the docstring is
written in, climbing the enclosing namespaces, plus the staging namespace.
That is what an identifier written at that point would mean.

`tree` is the looseness this tree's own house style needs: a docstring cites
a short name across namespaces (`footBand_projects` from a file where
`Chrome` is a sibling namespace), and AGENTS.md cites them that way too. So
a token also resolves when it resolves in SOME namespace this tree
declares. It is the real resolver either way -- aliases and private names
included -- and the tier is reported separately so the cost of the looseness
stays visible. -/
inductive Verdict where
  | scope
  | tree
  | phantom
  deriving BEq, Inhabited

def verdict (envs : Array Environment) (idx : Std.HashMap String (Array Name))
    (s : Site) (tok : String) : Verdict :=
  if resolvesIn envs s.ns (.simple stagingNamespace [] :: s.opens) tok then .scope
  else if ((idx[tok]?).getD #[]).any (fun ns => resolvesIn envs ns [] tok) then .tree
  else .phantom

def loadTree : IO (Array Environment) := do
  initSearchPath (← findSysroot) [".lake/build/lib/lean"]
  let mut out : Array Environment := #[]
  for root in treeRoots do
    for (m, target) in root do
      try
        let _ ← findOLean m
      catch _ =>
        throw (IO.userError s!"cites: no compiled {moduleFile m}. \
          Fix: lake build {target}")
    out := out.push (← importModules (root.toArray.map fun (m, _) =>
      { module := m }) {})
  return out

/-- Every docstring in the tree, with its scope. A compiled module's
docstrings come from the environment, which is what makes a continuation-line
declaration visible and gives each citation the namespace it was written in.
A file the build does not compile -- a `lake env lean --run` script -- has no
environment entry, so its docstrings are read as text and resolved under the
opens the file declares. -/
def sites (envs : Array Environment) : IO (Array Site) := do
  let mut out : Array Site := #[]
  let mut known : Std.HashSet Name := {}
  for env in envs do
    for (i, m) in ourModules env do
      if known.contains m then continue
      known := known.insert m
      let file := moduleFile m
      for d in (getModuleDoc? env m).getD #[] do
        let ln := d.declarationRange.pos.line
        out := out.push (mkSite file ln .anonymous [] "the module docstring" d.doc)
      for n in (env.header.moduleData[i]?.map (·.constNames)).getD #[] do
        if let some doc ← findDocString? env n then
          let rng := declRangeExt.find? (level := .exported) env n
            <|> declRangeExt.find? (level := .server) env n
          let ln := (rng.map (·.range.pos.line)).getD 0
          out := out.push (mkSite file ln n.getPrefix [] s!"`{n}`" doc)
  let mut files : Array String := #[]
  for root in ["LeanTex", "Tests", "scripts", "Obligations"] do
    if ← System.FilePath.pathExists root then
      for f in ← System.FilePath.walkDir root do
        if f.toString.endsWith ".lean" then files := files.push f.toString
  for e in ← System.FilePath.readDir "." do
    if e.fileName.endsWith ".lean" then files := files.push e.fileName
  for f in files do
    if known.contains (fileModule f) then continue
    let lines := ((← IO.FS.readFile f).splitOn "\n").toArray
    let opens := openedIn lines
    for (i, l) in docRegions lines do
      out := out.push (mkSite f i .anonymous opens "a docstring" l)
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
  frozenSeen : Std.HashSet String := {}
  deriving Inhabited

/-- Every phantom citation, with the census of what was judged. -/
def scan (envs : Array Environment) :
    IO (Array (String × String × Nat × String) × Census) := do
  let ss ← sites envs
  let idx := shortIndex envs
  let mut bad : Array (String × String × Nat × String) := #[]
  let mut c : Census := { sites := ss.size }
  for s in ss do
    for l in s.text.splitOn "\n" do
      for tk in backtickSpans l do
        unless citeCandidate tk do continue
        c := { c with candidates := c.candidates + 1 }
        c := { c with names := c.names.insert tk }
        if citeForeign.contains tk then
          c := { c with foreign := c.foreign + 1 }
          c := { c with foreignSeen := c.foreignSeen.insert tk }
        else match verdict envs idx s tk with
          | .scope => c := { c with scope := c.scope + 1 }
          | .tree => c := { c with tree := c.tree + 1 }
          | .phantom =>
            if citePhantomKnown.contains tk then
              c := { c with frozen := c.frozen + 1 }
              c := { c with frozenSeen := c.frozenSeen.insert tk }
            else bad := bad.push (tk, s.file, s.line, s.subject)
  return (bad, c)

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
    -- everything else the tree backticks
    ("foldInlines", false),
    ("Ir.dump", false),
    ("Array Block", false),
    ("Conserves", false),
    ("--wfail", false),
    ("tests/compat-index", false),
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
    if citePhantomKnown.contains n then
      fails.modify (s!"name on both citation lists: {n}" :: ·)
  for n in citePhantomKnown do
    unless citeCandidate n do
      fails.modify (s!"allowlisted name is not a candidate: {n}" :: ·)

  let docCases : List (Array String × Array (Nat × String)) := [
    (#["/-- a `foo_bar` claim -/", "def x := 1"], #[(1, "/-- a `foo_bar` claim -/")]),
    (#["-- a `foo_bar` comment", "def x := 1"], #[]),
    (#["/-! module `foo_bar`", "continues -/", "def x := 1"],
      #[(1, "/-! module `foo_bar`"), (2, "continues -/")])]
  for (ls, want) in docCases do
    if docRegions ls != want then
      fails.modify (s!"docRegions: got {docRegions ls}" :: ·)

  unless (openedIn #["open LeanTex.Core Lean"]).length == 2 do
    fails.modify ("openedIn: open A B is two opens" :: ·)
  unless (openedIn #["open X in"]).isEmpty do
    fails.modify ("openedIn: a scoped open is not a file-level one" :: ·)

  -- The resolver, against this tree. Every case below is a failure mode the
  -- text-scanning predecessor got wrong, or a legal spelling it got right
  -- and this one must keep.
  let envs ← loadTree
  let idx := shortIndex envs
  let root : Site := mkSite "x.lean" 0 .anonymous [] "a docstring" ""
  let at_ (ns : Name) : Site := { root with ns }
  let vcases : List (String × Site × Verdict × String) := [
    -- a name declared nowhere is a phantom, which is the whole point
    ("no_such_theorem_anywhere", root, .phantom, "an absent name"),
    -- the three shapes the text-scanning predecessor got wrong. The first
    -- two are its false accepts, both live in this tree: a name only a
    -- test's check-label string holds, and a name two declarations merely
    -- share a prefix with. The third is its false reject: a declaration
    -- whose name does not sit on its keyword's line.
    ("frames_sections", root, .phantom, "a name only a check label holds"),
    ("sty_is_defaults", at_ `LeanTex.Core.Elab, .phantom, "a shared prefix"),
    ("cite_continuation_witness", at_ `LeanTex.Core.Ir, .scope,
      "a continuation-line name"),
    -- an owed statement lives in the staging namespace and is cited bare
    ("inflate_deflate_id", at_ `LeanTex.Core.Flate, .scope, "an owed statement"),
    -- a theorem resolves in its own namespace, and across namespaces by the
    -- tree tier -- which is the site Diag.lean actually writes: the
    -- docstring sits in `LeanTex.Core` and the theorem in a namespace below
    ("all_complete", at_ `LeanTex.Core.DiagCode, .scope, "a theorem in scope"),
    ("all_complete", at_ `LeanTex.Core, .tree, "a theorem cited across namespaces")]
  for (tok, s, want, what) in vcases do
    let got := verdict envs idx s tok
    if got != want then
      let show_ := fun (v : Verdict) => match v with
        | .scope => "scope" | .tree => "tree" | .phantom => "phantom"
      fails.modify (s!"verdict {tok} ({what}): got {show_ got}, want {show_ want}" :: ·)

  let failed := (← fails.get).reverse
  if failed.isEmpty then
    IO.println "cites selftest: all passed"
    return 0
  for f in failed do
    IO.eprintln s!"FAIL {f}"
  return 1

def main (args : List String) : IO UInt32 := do
  if args.contains "--selftest" then
    return (← selftest)
  let envs ← loadTree
  let (bad, c) ← scan envs
  unless args.contains "--check" do
    IO.println s!"cites: {c.sites} docstrings, {c.candidates} citations \
      ({c.names.size} distinct names), {c.scope} resolving in scope, \
      {c.tree} resolving elsewhere in the tree, \
      {c.foreign} foreign ({c.foreignSeen.size} of {citeForeign.length} rows), \
      {c.frozen} frozen ({c.frozenSeen.size} of {citePhantomKnown.length} rows), \
      {bad.size} phantom"
  if bad.isEmpty then
    return 0
  let hits := String.intercalate "\n"
    (bad.toList.map fun (n, f, i, subj) => s!"  {f}:{i} ({subj}): `{n}`")
  IO.eprintln s!"cites: a docstring cites a theorem name that resolves to nothing:
{hits}
  A guarantee stated in prose names the theorem holding it (AGENTS.md,
  Conventions); a name that resolves to nothing reads as held and is not.
  Fix: write the theorem, or cite the one that does hold the claim, or state
  the claim without a name. A name that is not this tree's -- foreign
  vocabulary spelled snake_case -- goes in citeForeign with its source."
  return 1
