/-
Does every theorem name a docstring cites resolve to a declaration?

  lake build LeanTex TestsModules ScriptsModules leantex Tests cites
  .lake/build/bin/cites --check

A guarantee stated in prose names the theorem holding it
(AGENTS.md § Lean rules).
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
`Layout.run_paras_body_exact`, `Diag.tallySites_exact`. A citation reaching out of its own
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
  ["add_xdata_ref",            -- biber's xdata-reference reader (Biber::Entry)
   "collate_options",          -- biber's collation settings (Biber::Config)
   "default_rule_thickness",   -- TeX's math fontdimen (TeXbook, Appendix G)
   "format_unencoded",         -- Pygments' LaTeX formatter pass (formatters/latex.py)
   "good_length",              -- zlib's deflate configuration field
   "headless_shell",           -- Chrome's own binary name
   "min_crossrefs",            -- BibTeX's cross-reference threshold (btxdoc, bibtex.web)
   "mlist_to_hlist",           -- TeX's math-list conversion pass
   "normalise_string_sort",    -- biber's sort-string normaliser (Biber::Utils)
   "np_length",                -- biber's name-part widths (Biber::Section)
   "parse_date",               -- biber's one-sided date reader (Biber::Utils)
   "parse_date_range",         -- biber's date-range reader (Biber::Utils)
   "parse_date_unspecified",   -- biber's unspecified-digit reader (Biber::Utils)
   "process_visible_names",    -- biber's name-visibility pass (Biber.pm)
   "resolve_xdata",            -- biber's xdata resolution (Biber::Entry)
   "sort_list",                -- biber's list sort (Biber.pm)
   "style_for_token",          -- Pygments' resolved style lookup (pygments/style.py)
   "von_name_ends_and_last_name_starts_stuff", -- bibtex.web's name-splitting module
   "von_token_found",          -- bibtex.web's von-token test
   "x_y",                      -- an example label key, quoted as prose
   "xn_over_d"]                -- TeX's scaled-integer routine (TeX §107)

/-- A known unresolved citation, keyed by name, file, and declaration.
The ratchet rejects both new sites and rows whose citation now resolves.
Correct the reference or prove its claim; do not remove a supported claim
merely to silence its citation. -/
structure PhantomRow where
  name : String
  file : String
  anchor : String
  deriving BEq, Repr, Inhabited

def citePhantomKnown : List PhantomRow :=
  [⟨"frames_sections", "Tests/Themes.lean", "deckStepChecks"⟩,
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
    (queries : Array Query := #[]) (named : Array Query := #[]) : IO Response :=
  IO.FS.withTempDir fun dir => do
    let request := dir / "request.json"
    let response := dir / "response.json"
    let paths := (← searchPathRef.get).toArray.map (·.toString)
    IO.FS.writeFile request (toJson ({ modules, paths, collect, queries, named } : Request)).compress
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
    unless result.modules == modules && result.verdicts.size == queries.size &&
        result.named.size == named.size do
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

/-- Scope resolution uses the citing module and namespace.
The tree tier permits the existing house style of citing another namespace's
short name. Both tiers require Lean to resolve a complete compiled declaration.
A `named` query is answered with the declarations it resolves to, gathered
across the batches: a declaration every batch imports is one name, not one
per batch. -/
def resolveAll (tree : CompiledTree) (queries : Array Query) (named : Array Query := #[]) :
    IO (Array Verdict × Array (Array Resolved)) := do
  let mut answers := Array.replicate queries.size Verdict.phantom
  let mut names : Array (Array Resolved) := Array.replicate named.size #[]
  for modules in tree.batches do
    let result ← runBatch modules false queries named
    answers := answers.zipWith bestVerdict result.verdicts
    names := names.zipWith (fun acc more =>
      more.foldl (fun a r => if a.any (·.name == r.name) then a else a.push r) acc) result.named
  return (answers, names)

def resolveTree (tree : CompiledTree) (queries : Array Query) : IO (Array Verdict) :=
  return (← resolveAll tree queries).1

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
census of what was judged. `named` queries ride the same compiled batches,
and the declarations each names come back in order: the rule documents' pins
are resolved by the one resolver docstrings are. -/
def scan (tree : CompiledTree) (rows : List PhantomRow := citePhantomKnown)
    (named : Array Query := #[]) :
    IO (Array (String × String × Nat × String) × List PhantomRow × Census ×
      Array (Array Resolved)) := do
  let queries := citationQueries tree.sites
  let (answers, names) ← resolveAll tree queries named
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
  return (bad, dead, c, names)

-- ## Rule documents

/-- The rule documents. `AGENTS.md` and `PRINCIPLES.md` name the check that
holds each rule and `THEOREMS.md` the theorems that state each guarantee, so
a backticked name in any of them is a pin, held to the compiled tree by the
resolver docstrings are held to. A pin a later unit delivers is written owed
— `owed (U37):` or `owed (<branch>):` before it — and must resolve to
nothing until it lands; then it fails until the document promotes it, the
way an owed report row does, so neither kind of pin can rot. A held pin
names exactly one declaration, and never a type: a short name two theorems
share holds whichever one its reader guesses, so it is qualified until one
remains, and a type is vocabulary, which holds nothing. The flag says
whether the document's prose — its list items and paragraphs — states
rules: the first two documents' does, while `THEOREMS.md`'s prose defines
terms and only its table rows index guarantees. -/
def ruleDocs : List (String × Bool) :=
  [("AGENTS.md", true), ("PRINCIPLES.md", true), ("THEOREMS.md", false)]

/-- A unit of a rule document: a list item with its continuation lines, a
table row, or a paragraph, joined into one line, with the line it opens on
and the `## ` section it stands in. `rule` marks the units that must name a
check: every body row of a table, and every list item and paragraph where
`prose` says the document's prose states rules. Fenced code is no unit: a
command in it is an example, not a pin. -/
structure DocBlock where
  line : Nat
  sec : String
  rule : Bool
  text : String
  deriving Inhabited, Repr, BEq

/-- Does the line open a list item: a `-` or `*` bullet, or a numeral and a
period, after any indentation? -/
def opensItem (l : String) : Bool :=
  let cs := l.toList.dropWhile (· == ' ')
  match cs with
  | '-' :: ' ' :: _ | '*' :: ' ' :: _ => true
  | _ =>
    let ds := cs.takeWhile Char.isDigit
    !ds.isEmpty && (cs.drop ds.length).take 2 == ['.', ' ']

/-- The units of a rule document, in order. -/
def docBlocks (text : String) (prose : Bool := true) : Array DocBlock := Id.run do
  let mut out : Array DocBlock := #[]
  let mut cur : Option DocBlock := none
  let mut sec := ""
  let mut fence := false
  let mut tableBody := false
  for (raw, i) in (text.splitOn "\n").zipIdx do
    let l := raw.trimAscii.toString
    if l.startsWith "```" then
      if let some b := cur then out := out.push b
      cur := none
      fence := !fence
      continue
    if fence then continue
    if l.isEmpty || l.startsWith "#" then
      if let some b := cur then out := out.push b
      cur := none
      tableBody := false
      if l.startsWith "## " then sec := (l.drop 3).toString.trimAscii.toString
      else if l.startsWith "# " then sec := ""
      continue
    if l.startsWith "|" then
      if let some b := cur then out := out.push b
      cur := none
      let separator := l.all fun c => c == '|' || c == '-' || c == ':' || c == ' '
      out := out.push { line := i + 1, sec, rule := tableBody && !separator, text := l }
      tableBody := tableBody || separator
      continue
    tableBody := false
    if opensItem raw then
      if let some b := cur then out := out.push b
      cur := some { line := i + 1, sec, rule := prose, text := l }
    else
      cur := match cur with
        | some b => some { b with text := b.text ++ " " ++ l }
        | none => some { line := i + 1, sec, rule := prose, text := l }
  if let some b := cur then out := out.push b
  return out

/-- What a backticked span names: a declaration of the compiled tree, or a
path relative to the repository root. -/
inductive PinKind where
  | ident
  | path
  deriving BEq, Repr, Inhabited

/-- The extensions a bare file name is recognised by, so `AGENTS.md` reads
as the file at the root rather than as a dotted declaration name. -/
def pathExts : List String :=
  [".md", ".lean", ".tsv", ".txt", ".toml", ".tex", ".json", ".yml", ".py", ".sh"]

/-- One segment of a dotted Lean name: an ASCII letter, then the letters,
digits, underscores, primes, `?` and `!` Lean's identifiers allow anywhere
after the first character (`getElem?_eq`, `record?_some_exact`). -/
def identSegment (s : String) : Bool :=
  match s.toList with
  | c :: rest => c.isAlpha && rest.all fun d =>
      d.isAlphanum || d == '_' || d == '\'' || d == '?' || d == '!'
  | [] => false

/-- How a backticked span is judged, if at all. A span with white space is a
command or a phrase; a span holding `/`, a bare name with a known extension,
or a bare name with a dash no identifier can hold (`lean-toolchain`) is a
path; a dotted Lean name is a declaration; anything else — a flag, a TeX
command, a pattern with `<…>` or `*` — is prose. -/
def pinKind (t : String) : Option PinKind :=
  let pathChar := fun (c : Char) => c.isAlphanum || c == '_' || c == '-' || c == '.' || c == '/'
  let bare := t.all pathChar && ((t.toList.head?.map Char.isAlpha).getD false)
  if t.isEmpty || t.any Char.isWhitespace then none
  else if t.any (· == '/') then
    if t.all pathChar && !t.startsWith "-" then some .path else none
  else if bare && (pathExts.any (fun e => t.endsWith e) || t.any (· == '-')) then
    some .path
  else if (t.splitOn ".").all identSegment then some .ident
  else none

/-- A pin as a rule document writes it: the span, what it names, and the unit
or branch that owes it when it is written owed. -/
structure Pin where
  token : String
  kind : PinKind
  owner : Option String
  deriving BEq, Repr, Inhabited

/-- An owner as `owed (…)` spells one: a roadmap unit (`U37`) or a branch
(`build-speed-1008`). -/
def ownerShaped (s : String) : Bool :=
  match s.toList with
  | 'U' :: ds => !ds.isEmpty && ds.all Char.isDigit
  | c :: rest => c.isLower && rest.all fun d => d.isLower || d.isDigit || d == '-'
  | [] => false

/-- Does `lit` occur in `cs` at `i`? -/
def litAtArr (cs : Array Char) (i : Nat) (lit : String) : Bool := Id.run do
  let mut k := i
  for c in lit.toList do
    if cs[k]? != some c then return false
    k := k + 1
  return true

/-- What one unit says about its checks: its pins; whether it carries a check
marker of its own — an owed group, which names the unit that delivers the
check, or `(review)`, which says review holds the rule; and the owners of
the owed groups that name no pin, which nothing can promote when their unit
lands, so they are counted against a baseline instead. -/
structure BlockScan where
  pins : Array Pin := #[]
  marked : Bool := false
  bareOwed : Array String := #[]
  deriving Inhabited

/-- An owed group closing: its owner joins the bare ones unless it named a pin. -/
def closeOwed (owner : Option (String × Nat)) (pinned : Bool) (bare : Array String) :
    Array String :=
  match owner with
  | some (o, _) => if pinned then bare else bare.push o
  | none => bare

/-- Scan one unit. Outside the backticks, `owed (<owner>)` opens a group; `;`,
`|`, a sentence's period, the next group, or the parenthesis closing the one
the group opened inside ends it. A span left unclosed is dropped. -/
def blockPins (text : String) : BlockScan := Id.run do
  let parts := (text.splitOn "`").toArray
  let closed := if parts.size % 2 == 0 then parts.size - 1 else parts.size
  let mut pins : Array Pin := #[]
  let mut owner : Option (String × Nat) := none
  let mut pinned := false
  let mut bare : Array String := #[]
  let mut depth := 0
  let mut marked := false
  for k in [0:closed] do
    let part := parts[k]?.getD ""
    if k % 2 == 1 then
      if let some kind := pinKind part then
        pins := pins.push { token := part, kind, owner := owner.map (·.1) }
        pinned := pinned || owner.isSome
      continue
    let cs := part.toList.toArray
    let mut skip := 0
    for i in [0:cs.size] do
      if skip > 0 then
        skip := skip - 1
        continue
      let c := cs[i]?.getD ' '
      if litAtArr cs i "(review)" then
        marked := true
        skip := "(review)".length - 1
      else if litAtArr cs i "owed (" then
        let start := i + "owed (".length
        let name := String.ofList ((cs.extract start cs.size).toList.takeWhile (· != ')'))
        if ownerShaped name && cs[start + name.length]? == some ')' then
          bare := closeOwed owner pinned bare
          owner := some (name, depth)
          pinned := false
          marked := true
          skip := "owed (".length + name.length
      else if c == '(' then depth := depth + 1
      else if c == ')' then
        if depth > 0 then depth := depth - 1
        if let some (_, d) := owner then
          if depth < d then
            bare := closeOwed owner pinned bare
            owner := none
      else if c == ';' || c == '|' then
        bare := closeOwed owner pinned bare
        owner := none
      else if c == '.' && (cs[i + 1]?.map Char.isWhitespace).getD (k + 1 == closed) then
        bare := closeOwed owner pinned bare
        owner := none
  return { pins, marked, bareOwed := closeOwed owner pinned bare }

/-- The `## ` headings of a document, in order. -/
def headingsOf (text : String) : List String :=
  (text.splitOn "\n").filterMap fun l =>
    if l.startsWith "## " then some (l.drop 3).toString.trimAscii.toString else none

/-- One finding about a rule document. -/
structure DocFault where
  file : String
  line : Nat
  what : String
  deriving BEq, Repr, Inhabited

/-- Judge a rule document against resolution answers, pure so the selftest
drives every branch: an unheld pin (a declaration that resolves to nothing,
a path that is absent), an ambiguous one (a name several declarations
answer to), a type (vocabulary, which holds nothing), a stale owed pin (one
that now resolves), and a rule that names no check. `names` answers what a
pin resolves to, owed or not, each answer with whether it forms types. -/
def judgeDoc (file text : String) (prose : Bool) (names : Pin → Array (String × Bool)) :
    Array DocFault := Id.run do
  let mut out : Array DocFault := #[]
  for b in docBlocks text prose do
    let scan := blockPins b.text
    for p in scan.pins do
      let what := if p.kind == .path then "path" else "name"
      let found := names p
      match p.owner with
      | none =>
        if found.isEmpty then
          out := out.push ⟨file, b.line, s!"the {what} `{p.token}` resolves to nothing"⟩
        else if found.size > 1 then
          out := out.push ⟨file, b.line, s!"the {what} `{p.token}` names {found.size} \
            declarations ({String.intercalate ", " (found.toList.map (·.1))}): qualify it"⟩
        else if found.all (·.2) then
          out := out.push ⟨file, b.line, s!"`{p.token}` is a type, which holds no rule: \
            pin the check or theorem, and write the type without backticks"⟩
      | some o =>
        unless found.isEmpty do
          out := out.push ⟨file, b.line,
            s!"`{p.token}` is written owed ({o}) and now resolves: promote it"⟩
    if b.rule && scan.pins.isEmpty && !scan.marked then
      let excerpt := (b.text.take 60).toString
      out := out.push ⟨file, b.line, s!"a rule names no check: {excerpt}"⟩
  return out

/-- How many of a document's pins are held today and how many are owed. -/
def docPinCounts (text : String) : Nat × Nat := Id.run do
  let mut held := 0
  let mut owed := 0
  for b in docBlocks text do
    for p in (blockPins b.text).pins do
      if p.owner.isSome then owed := owed + 1 else held := held + 1
  return (held, owed)

/-- The owners of a document's owed groups that name no pin, in order. -/
def docBareOwed (text : String) : Array String :=
  (docBlocks text).foldl (fun acc b => acc ++ (blockPins b.text).bareOwed) #[]

/-- How many owed groups each rule document may carry that name no pin: a
unit whose roadmap names no declaration or file for the check it delivers.
Nothing can tell such a group that its unit landed, so the count is held in
both directions: a new bare group fails, and so does one removed without
lowering its row, as the report and subject-debt baselines are read. -/
def bareOwedBaseline : List (String × Nat) :=
  [("AGENTS.md", 3), ("PRINCIPLES.md", 10), ("THEOREMS.md", 4)]

/-- A document whose bare owed groups differ from its baseline, either way. -/
def bareOwedFault (file text : String) (baseline : List (String × Nat) := bareOwedBaseline) :
    Option DocFault :=
  let bare := docBareOwed text
  let want := ((baseline.find? (·.1 == file)).map (·.2)).getD 0
  if bare.size == want then none
  else some ⟨file, 0, s!"{bare.size} owed groups name no check ({String.intercalate ", "
    bare.toList}), and the baseline is {want}: name the check the unit delivers, or set \
    the baseline to the count"⟩

/-- The pins of a document that name declarations, for the resolver. -/
def docIdents (text : String) : Array String := Id.run do
  let mut out : Array String := #[]
  for b in docBlocks text do
    for p in (blockPins b.text).pins do
      if p.kind == .ident && !out.contains p.token then out := out.push p.token
  return out

/-- The resolver query a document pin is asked as: from no module and no
namespace, so the tree tier — the declaration's own module and namespace —
is where a short name resolves. -/
def docQuery (file token : String) : Query := ⟨file, .anonymous, token⟩

/-- The rule documents that exist under `root`, with their text and whether
their prose states rules. -/
def readRuleDocs (root : System.FilePath := ".") : IO (Array (String × String × Bool)) := do
  let mut out := #[]
  for (f, prose) in ruleDocs do
    if ← (root / f).pathExists then out := out.push (f, ← IO.FS.readFile (root / f), prose)
  return out

/-- Every fault of the rule documents, given the declarations each name pin
resolved to; a path pin is held by the file or directory existing under
`root`. -/
def docFaults (root : System.FilePath) (docs : Array (String × String × Bool))
    (named : Std.HashMap String (Array Resolved)) : IO (Array DocFault) := do
  let mut out := #[]
  for (file, text, prose) in docs do
    let mut present : Std.HashSet String := {}
    for b in docBlocks text do
      for p in (blockPins b.text).pins do
        if p.kind == .path then
          let rel := if p.token.endsWith "/" then (p.token.dropEnd 1).toString else p.token
          if ← (root / rel).pathExists then present := present.insert p.token
    let names := fun (p : Pin) => match p.kind with
      | .path => if present.contains p.token then #[(p.token, false)] else #[]
      | .ident => (named[p.token]?.getD #[]).map fun r => (toString r.name, r.typeFormer)
    out := out ++ judgeDoc file text prose names
    if let some f := bareOwedFault file text then out := out.push f
  return out

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
        public def IsTrivial (n : Nat) : Prop := n = n\n\
        public abbrev Width : Type := Int\n\
        public def label := \"label_only_invariant\"\n\
        public theorem split_invariant_left : True := trivial\n\
        public theorem split_invariant_right : True := trivial\n\
        end Extra\n\
        public theorem\n  fixture_continuation_witness : True := trivial\n"),
      ("LeanTex.CiteProbe", "module\nnamespace Local\n\
        /-- The private contract `Local.local_invariant` is checked. -/\n\
        private theorem local_invariant (n : Nat) : n = n := rfl\n\
        end Local\n"),
      ("Extra-Library.dashed-source", "module\nnamespace Dashed\n\
        /-- The private contract `dashed_invariant` is checked. -/\n\
        private theorem dashed_invariant : True := trivial\n\
        /-- The private claim `missing_dashed_invariant` must fail. -/\n\
        private def anchor : Nat := 0\nend Dashed\n"),
      ("ExtraProofs", "module\nnamespace ExtraProofs\n\
        public theorem root_invariant : True := trivial\nend ExtraProofs\n"),
      ("Extra.Twin", "module\nnamespace Twin.A\n\
        public theorem twin_invariant : True := trivial\nend Twin.A\n\
        namespace Twin.B\n\
        public theorem twin_invariant : True := trivial\nend Twin.B\n"),
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
    for subject in ["`Extra.hiddenAnchor`", "`Extra.anchor`", "`Local.local_invariant`",
        "`Dashed.anchor`"] do
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
      ("qualified root module", q "ExtraProofs.root_invariant" `Extra, .scope),
      ("foreign bare name", q "root_invariant" `Extra, .tree),
      ("root module namespace", q "root_invariant" `ExtraProofs "ExtraProofs", .scope),
      ("private bare name", q "private_invariant" `Extra, .scope),
      ("private qualified name", q "Extra.private_invariant", .scope),
      ("modern private doc namespace", q "Local.local_invariant" `Local "LeanTex.CiteProbe", .scope),
      ("dashed module private context",
        q "dashed_invariant" `Dashed "Extra-Library.dashed-source", .scope),
      ("exported alias", q "Extra.alias_invariant", .scope),
      ("short exported alias", q "alias_invariant" `Extra, .scope),
      ("alias across namespaces", q "alias_invariant" `Elsewhere "Tools.One", .tree),
      ("private across namespaces", q "local_invariant" `Elsewhere "Tools.One", .tree),
      ("invented field projection", q "Extra.Box.missing_invariant", .phantom)]
    let verdicts ← resolveTree tree (cases.map fun (_, query, _) => query)
    for ((label, _, want), got) in cases.zip verdicts do
      expect s!"{label}: got {repr got}, want {repr want}" (got == want)
    -- A rule document's pin is asked from no module and no namespace and
    -- answered with every declaration it names: a short name two theorems
    -- share is two, a qualified spelling one, an alias its target once.
    let named : Array (String × Nat) := #[
      ("twin_invariant", 2), ("Twin.A.twin_invariant", 1), ("A.twin_invariant", 1),
      ("alias_invariant", 1), ("no_such_theorem_anywhere", 0)]
    let (_, answers) ← resolveAll tree #[] (named.map fun (t, _) => docQuery "rule-docs" t)
    for ((token, want), got) in named.zip answers do
      expect s!"named resolution of {token}: got {got.map (·.name)}, want {want} declarations"
        (got.size == want)
    -- Each answer says whether it forms types: a structure, its constructor,
    -- a predicate and a type alias do; a value and a theorem do not.
    let formers : Array (String × Bool) := #[
      ("Extra.Box", true), ("Extra.Box.mk", true), ("Extra.IsTrivial", true),
      ("Extra.Width", true), ("Extra.anchor", false), ("Extra.alias_invariant", false)]
    let (_, kinds) ← resolveAll tree #[] (formers.map fun (t, _) => docQuery "rule-docs" t)
    for ((token, want), got) in formers.zip kinds do
      expect s!"type-former reading of {token}: got {got.map (·.typeFormer)}, want {want}"
        (got.map (·.typeFormer) == #[want])
    let (bad, dead, census, _) ← scan tree []
    let names := bad.map fun (name, _, _, _) => name
    let missing := #["missing_module_invariant", "missing_private_invariant",
      "missing_public_invariant", "missing_one_invariant", "missing_two_invariant",
      "missing_dashed_invariant"]
    expect "full compiled scan missed a phantom or rejected a valid private/alias citation"
      (names.size == missing.size && missing.all names.contains && dead.isEmpty)
    expect "private phantom lost its actionable source location"
      (census.phantoms.contains ⟨"missing_private_invariant",
        "Extra/Unimported.lean", "Extra.hiddenAnchor"⟩ &&
        bad.any fun (name, _, line, _) => name == "missing_private_invariant" && line > 0)
    for name in ["Unbuilt", "Extra.Unbuilt"] do
      let file := dir / moduleFile name
      IO.FS.writeFile file
        "/-- The uncompiled claim `missing_unbuilt_invariant` cannot be read as compiled. -/\ndef x := 0\n"
      let missingRejected ← try
        let _ ← loadTree dir
        pure false
      catch e =>
        pure (containsSub e.toString s!"no compiled {moduleFile name}" &&
          containsSub e.toString "lake build")
      expect s!"missing compiled {name} did not fail with a build instruction" missingRejected
      IO.FS.removeFile file
    return (← failures.get).reverse
  finally
    searchPathRef.set before

/-- Every case the gate must catch and every legal spelling it must pass.
Positive cases are the shapes whose escape prompted a gate change; negative
cases are spellings of this tree. A gate that does not catch the shape it
commemorates grants false confidence, so a gate change lands with both. -/
def selftest : IO UInt32 := do
  let fails ← IO.mkRef ([] : List String)
  -- Worker messages must preserve kernel namespaces, including hygienic and
  -- numeric components which are not source-level identifiers.
  let namespaces : Array Name := #[
    .anonymous, `Ordinary.Namespace,
    .str (.str (.num
      (.str (.str (.str (.str .anonymous "initFn") "_@") "scripts") "ProofAudit")
      3794864908) "_hygCtx") "_hyg",
    .str .anonymous "", .str .anonymous "part.with spaces",
    .str .anonymous "quote\"\\\n", .str .anonymous "»", .str .anonymous "#0",
    .num .anonymous 0,
    .str (.num (.str .anonymous "same") 12) "tail",
    .str (.str (.str .anonymous "same") "12") "tail"]
  for ns in namespaces do
    let request : Request := {
      modules := #["Synthetic"], paths := #[], collect := true
      queries := #[⟨"Synthetic", ns, "some_invariant"⟩] }
    let response : Response := {
      modules := #["Synthetic"]
      sites := #[⟨"Synthetic", "Synthetic.lean", 7, ns, "anchor", "text"⟩] }
    let decodedRequest : Except String Request :=
      Json.parse (toJson request).compress >>= fromJson?
    let decodedResponse : Except String Response :=
      Json.parse (toJson response).compress >>= fromJson?
    unless (decodedRequest.toOption.map (·.queries)) == some request.queries do
      fails.modify (s!"request namespace roundtrip failed: {repr ns}" :: ·)
    unless (decodedResponse.toOption.map (·.sites.map (·.ns))) == some #[ns] do
      fails.modify (s!"response namespace roundtrip failed: {repr ns}" :: ·)
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
    ("lake env lean --run scripts/proofcheck.lean", false),
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

  -- The rule documents' grammar: what a pin is, what owes it, where an owed
  -- group ends, and which units must name a check. Each fault is planted
  -- once and each legal spelling passes.
  let kinds : List (String × Option PinKind) := [
    ("censusChecks", some .ident), ("Ir.floorMask_id", some .ident),
    ("find?", some .ident), ("record?_some_exact", some .ident),
    ("Ir.get!_x", some .ident), ("scripts/kp-fuzz.lean", some .path),
    ("testdata/corpus/fonts/", some .path), ("AGENTS.md", some .path),
    ("lean-toolchain", some .path), ("-x", none),
    ("lake build", none), ("--wfail", none), ("\\theme", none),
    ("testdata/scoreboard/<t>.tsv", none), ("foo.lean:12", none),
    ("_text", none), ("Ir.", none), ("x→y", none), ("", none)]
  for (t, want) in kinds do
    unless pinKind t == want do
      fails.modify (s!"pinKind {t}: got {repr (pinKind t)}" :: ·)
  let pinsOf (text : String) := (blockPins text).pins.toList.map fun p => (p.token, p.owner)
  let pinCases : List (String × List (String × Option String)) := [
    ("held by `aChecks` and `b_exact`", [("aChecks", none), ("b_exact", none)]),
    ("`a_x`; owed (U37): `b_y`, `c_z`; then `d_w`",
      [("a_x", none), ("b_y", some "U37"), ("c_z", some "U37"), ("d_w", none)]),
    ("(`a_x`; owed (U9): `b_y`) and `c_z`",
      [("a_x", none), ("b_y", some "U9"), ("c_z", none)]),
    ("owed (build-speed-1008): `Ir.x_y` holds. Then `z_w`.",
      [("Ir.x_y", some "build-speed-1008"), ("z_w", none)]),
    ("| a | owed (U4): `p_q` | `r_s` |", [("p_q", some "U4"), ("r_s", none)]),
    ("owed (Not An Owner): `p_q`", [("p_q", none)]),
    ("an unclosed `span_x is dropped", [])]
  for (text, want) in pinCases do
    unless pinsOf text == want do
      fails.modify (s!"blockPins {text}: got {pinsOf text}" :: ·)
  unless (blockPins "a rule (review)").marked && (blockPins "owed (U3) to come").marked &&
      !(blockPins "a rule with no check").marked do
    fails.modify ("blockPins: a check marker was misread" :: ·)
  -- An owed group that names no pin is bare, wherever it closes: at a `;`,
  -- at the next group, at its parenthesis, at a period, or at the unit's end.
  let bareCases : List (String × List String) := [
    ("`a_x`; owed (U37): `b_y`", []),
    ("owed (U14) removes it", ["U14"]),
    ("(`a_b`, owed (U3)) and owed (U4): `c_d`", ["U3"]),
    ("owed (U1); owed (U2): `x_y`. owed (U3)", ["U1", "U3"]),
    ("owed (U5) owed (U6): `p_q`", ["U5"]),
    ("a rule (review)", [])]
  for (text, want) in bareCases do
    unless (blockPins text).bareOwed.toList == want do
      fails.modify (s!"blockPins bareOwed {text}: got {(blockPins text).bareOwed}" :: ·)
  let doc := "# T\n\nIntro `held_x`.\n\n## Rules\n\n- one `held_x`\n  continues\n\
    - two (review)\n- three names nothing\n\n```\n`absent_in_fence`\n```\n\n\
    | Area | Proofs |\n|---|---|\n| a | `absent_x`; owed (U5): `held_x` |\n| b | none |\n\
    | c | `twin_x`, `type_x` |\n\nA closing paragraph naming nothing.\n"
  let blocks := docBlocks doc
  unless (blocks.map (·.line)).toList == [3, 7, 9, 10, 16, 17, 18, 19, 20, 22] &&
      (blocks.map (·.rule)).toList ==
        [true, true, true, true, false, false, true, true, true, true] &&
      (blocks[1]?.map (·.text)) == some "- one `held_x` continues" &&
      (blocks[1]?.map (·.sec)) == some "Rules" do
    fails.modify (s!"docBlocks: {repr blocks}" :: ·)
  -- `twin_x` stands for a short name two theorems share: it resolves, and
  -- still names no one check; `type_x` resolves to one type, which holds
  -- nothing.
  let answer := fun (p : Pin) =>
    if p.token == "held_x" then #[("held_x", false)]
    else if p.token == "twin_x" then #[("A.twin_x", false), ("B.twin_x", false)]
    else if p.token == "type_x" then #[("T.type_x", true)] else #[]
  let judged := judgeDoc "D.md" doc true answer
  let faults := judged.toList.map (·.line)
  unless faults == [10, 18, 18, 19, 20, 20, 22] do
    fails.modify (s!"judgeDoc: faults at {faults}, want 10, 18, 18, 19, 20, 20, 22" :: ·)
  unless judged.any fun f => f.line == 20 && containsSub f.what "names 2 declarations" do
    fails.modify ("judgeDoc: an ambiguous pin was not named as one" :: ·)
  unless judged.any fun f => f.line == 20 && containsSub f.what "is a type" do
    fails.modify ("judgeDoc: a pin naming a type was not named as one" :: ·)
  -- A document whose prose defines terms rather than states rules owes a
  -- check only on its table rows.
  let termFaults := (judgeDoc "D.md" doc false answer).toList.map (·.line)
  unless termFaults == [18, 18, 19, 20, 20] do
    fails.modify (s!"judgeDoc: a term list owed checks, faults at {termFaults}" :: ·)
  unless docIdents doc == #["held_x", "absent_x", "twin_x", "type_x"] do
    fails.modify (s!"docIdents: {docIdents doc}" :: ·)
  unless headingsOf doc == ["Rules"] do
    fails.modify (s!"headingsOf: {headingsOf doc}" :: ·)
  unless docPinCounts doc == (5, 1) do
    fails.modify (s!"docPinCounts: {docPinCounts doc}, want 5 held and 1 owed" :: ·)
  -- The bare owed count is held both ways: equal passes, and a rise or a
  -- fall from the baseline is a fault.
  let bareDoc := "## R\n\n- one owed (U9) to come\n- two `held_x`\n"
  unless docBareOwed bareDoc == #["U9"] &&
      (bareOwedFault "D.md" bareDoc [("D.md", 1)]).isNone &&
      (bareOwedFault "D.md" bareDoc [("D.md", 0)]).isSome &&
      (bareOwedFault "D.md" bareDoc [("D.md", 2)]).isSome &&
      (bareOwedFault "D.md" bareDoc []).isSome do
    fails.modify (s!"bareOwedFault: the baseline was misread for {docBareOwed bareDoc}" :: ·)

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
  let docs ← readRuleDocs
  let docNames := docs.foldl (fun acc (_, text, _) =>
    (docIdents text).foldl (fun a t => if a.contains t then a else a.push t) acc) #[]
  let (bad, dead, c, docAnswers) ← scan envs citePhantomKnown (docNames.map (docQuery "rule-docs"))
  let docNamed : Std.HashMap String (Array Resolved) := .ofArray (docNames.zip docAnswers)
  let docBad ← docFaults "." docs docNamed
  let (held, owed) := docs.foldl (fun (h, o) (_, text, _) =>
    let (h', o') := docPinCounts text
    (h + h', o + o')) (0, 0)
  let bare := docs.foldl (fun n (_, text, _) => n + (docBareOwed text).size) 0
  unless args.contains "--check" do
    IO.println s!"cites: {c.sites} docstrings, {c.candidates} citations \
      ({c.names.size} distinct names), {c.scope} resolving in scope, \
      {c.tree} resolving elsewhere in the tree, \
      {c.foreign} foreign ({c.foreignSeen.size} of {citeForeign.length} rows), \
      {c.frozen} frozen ({citePhantomKnown.length - dead.length} of \
      {citePhantomKnown.length} rows), {bad.size} phantom; \
      {docs.size} rule documents, {docNames.size} names pinned ({held} pins held, \
      {owed} owed, {bare} owed groups naming none), {docBad.size} faults"
  unless docBad.isEmpty do
    let hits := String.intercalate "\n"
      (docBad.toList.map fun f =>
        if f.line == 0 then s!"  {f.file}: {f.what}" else s!"  {f.file}:{f.line}: {f.what}")
    IO.eprintln s!"cites: a rule document names a check that does not hold:
{hits}
  A rule names the check that holds it, and a pin names one declaration that
  is not a type, or a path the tree has (PRINCIPLES.md § Rules are checks).
  Fix: cite the check that holds the rule; qualify a name several
  declarations share; write a check a later unit delivers as
  `owed (<unit>):` before its name, and drop the mark once it lands; mark a
  rule only review holds `(review)`; write a type, or a word that names no
  declaration, without backticks."
  if bad.isEmpty && dead.isEmpty && docBad.isEmpty then
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
  A guarantee stated in prose names the theorem holding it
  (AGENTS.md § Lean rules); a name that resolves to nothing reads as held
  and is not.
  Fix: write the theorem, or cite the one that does hold the claim, or state
  the claim without a name. A name that is not this tree's -- foreign
  vocabulary spelled snake_case -- goes in citeForeign with its source. A
  parked name is parked at its own sites only, so citing it again is new."
  return 1
