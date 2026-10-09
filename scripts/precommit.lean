/-
Pre-commit gate: lake build --wfail, lake test, lake lint, and
convention checks over the staged diff.
Silent on success. Git executes the FILE
scripts/hooks/pre-commit, a 3-line sh trampoline that runs this after a cheap
staged-file filter; install with: git config core.hooksPath scripts/hooks

Three sources, one gate. The hook reads the index (no flag). CI has no
index and reads a revision range instead (`--range origin/main...HEAD`), or
nothing at all (`--tree`); both run every whole-tree check unconditionally,
so the structural guarantees do not depend on a per-clone core.hooksPath.

The lint driver owns the compiled proof and citation audits. It invokes
this script with --conventions to run source checks without recursively
building or testing. As with a commit-time build, these checks read the
working tree; CI checks the committed tree.
-/

import scripts.Gate
import scripts.Privacy

open Privacy (addedLines addedRuns splitFirst)

/-- A command's exit code and its two output streams as bytes, both read
by tasks of their own so neither pipe can fill and stall the other.
Output is never read as UTF-8 here: a staged Latin-1 file reaches a diff
as its own bytes, and a reader that insists on UTF-8 throws on it. -/
def runBytes (cmd : String) (args : Array String)
    (env : Array (String × Option String) := #[]) : IO (UInt32 × ByteArray × ByteArray) := do
  let child ← IO.Process.spawn
    { cmd, args, env, stdin := .null, stdout := .piped, stderr := .piped }
  let out ← IO.asTask child.stdout.readBinToEnd Task.Priority.dedicated
  let err ← IO.asTask child.stderr.readBinToEnd Task.Priority.dedicated
  let o ← IO.ofExcept out.get
  let e ← IO.ofExcept err.get
  let code ← child.wait
  return (code, o, e)

/-- A git query's output as bytes; a failure stops the run. The privacy
gate reads these bytes in more than one encoding
(`Privacy.segmentReadings`), the other gates as their UTF-8 text (`git`). -/
def gitBytes (args : Array String) : IO ByteArray := do
  let (code, out, err) ← runBytes "git" args
  if code != 0 then
    IO.eprintln s!"pre-commit: git {String.intercalate " " args.toList} failed:\n{Privacy.textOfBytes err}"
    IO.Process.exit 1
  return out

def git (args : Array String) : IO String := do
  return Privacy.textOfBytes (← gitBytes args)

/-- A git query whose failure is an answer rather than an abort. The
merge-base lookups read it: in a CI checkout the trunk exists only as
`origin/main` (actions/checkout creates the one local branch it checked
out), and a shallow clone may hold neither ref. -/
def gitOpt (args : Array String) : IO (Option String) := do
  let (code, out, _) ← runBytes "git" args
  return if code == 0 then some (Privacy.textOfBytes out) else none

/-- The options every patch the gate reads is asked for with, whatever this
clone's configuration says: no colour, external driver or text conversion,
the `a/`/`b/` prefixes the header reader expects (`diff.noprefix` and
`diff.mnemonicPrefix` otherwise rename them, and a header without `b/` drops
its file's lines), the whole tree rather than the current directory,
renames read as renames, no context, and paths unquoted where git allows. -/
def pinnedPatch : Array String :=
  #["--no-color", "--no-ext-diff", "--no-textconv", "--no-relative", "--src-prefix=a/",
    "--dst-prefix=b/", "-M", "--unified=0"]

/-- `git diff` over `sel` as the gate reads one: `pinnedPatch`. -/
def pinnedDiff (sel : Array String) : IO ByteArray :=
  gitBytes (#["-c", "core.quotePath=false", "diff"] ++ pinnedPatch ++ sel)

/-- The merge base with the trunk, under either spelling — a local `main`
first, then `origin/main`. `none` when neither ref resolves. -/
def mergeBaseMain : IO (Option String) := do
  for ref in ["main", "origin/main"] do
    if let some out ← gitOpt #["merge-base", "HEAD", ref] then
      let b := ((out.splitOn "\n").headD "").trimAscii.toString
      if !b.isEmpty then return some b
  return none

/-- Where a run reads its diff. The hook reads the index: the content the
commit will carry, which is the only thing a commit-time gate can judge. CI
has no index, so it reads a revision range — the pushed commits, or a pull
request against its base — and the whole-tree gates run either way. `tree`
is the range-free mode: the whole-tree gates alone, for a CI run whose
range cannot be computed (a first push, a shallow clone). -/
inductive Source where
  | index
  | range (rev : String)
  | tree
  deriving BEq

/-- The `git diff` selector for a source, or `none` when the run reads no
diff at all. -/
def Source.diffSel : Source → Option (Array String)
  | .index => some #["--cached"]
  | .range r => some #[r]
  | .tree => none

/-- `--range <rev>` (or `--range=<rev>`), `--tree`, else the hook's index.
A `--range` with no revision is an error, not a silent whole-tree pass: a
CI step that meant to read the pushed commits must fail loudly rather than
go quiet about them. -/
def parseSource : List String → Except String Source
  | [] => .ok .index
  | a :: rest =>
    if a == "--tree" then .ok .tree
    else if a == "--range" then
      match rest with
      | r :: _ =>
        if (r.trimAscii.toString).isEmpty then
          .error "--range needs a revision range, e.g. --range origin/main...HEAD"
        else .ok (.range r)
      | [] => .error "--range needs a revision range, e.g. --range origin/main...HEAD"
    else if a.startsWith "--range=" then
      let r := (a.drop "--range=".length).toString
      if (r.trimAscii.toString).isEmpty then
        .error "--range needs a revision range, e.g. --range=origin/main...HEAD"
      else .ok (.range r)
    else parseSource rest

def relevant (f : String) : Bool :=
  f.endsWith ".lean" || f == "lakefile.toml" || f == "lakefile.lean"
    || f == "lean-toolchain" || f.startsWith "testdata/golden/"

/-- The banned words, composed so this file's own staged diff never contains
them as word-delimited tokens — the gate scans every .lean file, itself
included. -/
def kwUnsafe : String := "uns" ++ "afe"

/-- Composed for the same reason: prepending to a recursive call's result
copies that result at every element. -/
def patAppend : String := "+" ++ "+"

/-- Composed like the banned keywords: the selftest must hold lines that
ARE markers, and this file's own staged diff may not carry one. (The rule
below fires only at line start, so an indented literal could not trip it
anyway — the composition keeps that true under any reformat.) -/
def mkOurs : String := "<<<" ++ "<<<<"
def mkTheirs : String := ">>>" ++ ">>>>"
def mkBase : String := "|||" ++ "||||"

/-- A merge-conflict marker line: exactly seven `<`, `>`, or `|` opening
the line, then end-of-line or whitespace — the shape git writes
(`<<<<<<< HEAD`, `||||||| base`, `>>>>>>> theirs`). Two deliberate
non-matches, each avoiding a false positive: `=======` alone is a markdown
setext rule and a Lean comment banner, and a wrongly resolved merge always
carries a `<<<<<<<`/`>>>>>>>` sibling this rule does catch; an eighth
marker char (`<<<<<<<<`, a decorative banner) also passes, since git
writes exactly seven. -/
def conflictMarker (l : String) : Bool :=
  [mkOurs, mkTheirs, mkBase].any fun m =>
    l.startsWith m &&
      match ((l.drop 7).toString).toList.head? with
      | none => true
      | some c => c.isWhitespace

/-- Added lines carrying a conflict marker, with file, new-file line
number, and the line itself, from a unified=0 cached diff over every
staged file — staged content, which is what the commit will contain, not
the working tree. Binary files produce no `+` content lines and are
skipped by construction. -/
def conflictMarkers (diff : String) : Array (String × Nat × String) := Id.run do
  let mut out : Array (String × Nat × String) := #[]
  let mut file := ""
  let mut line := 0
  for l in diff.splitOn "\n" do
    if l.startsWith "+++ " then
      file := if l.startsWith "+++ b/" then (l.drop "+++ b/".length).toString else ""
    else if l.startsWith "@@" then
      -- @@ -a,b +c,d @@ — the next added line is new-file line c
      let plus := ((l.splitOn "+").getD 1 "").takeWhile Char.isDigit
      line := (plus.toString.toNat?).getD 0
    else if l.startsWith "+" then
      if !file.isEmpty && conflictMarker ((l.drop 1).toString) then
        out := out.push (file, line, (l.drop 1).toString)
      line := line + 1
  return out

/-- A path spelled only in ASCII letters, digits, `.`, `_`, `/` and `-` —
the alphabet every shell,
git, and `lake` pass through unquoted. A file a mangled command produces
is named by that command's own text (`sed -n "…",+12p` once created a
zero-byte `arnings name the native spelling",+12p` at the root, and a
blanket `git add -A` staged it): spaces, quotes, commas, `+`, `=`, and
non-ASCII are exactly the debris alphabet. -/
def plainPath (p : String) : Bool :=
  !p.isEmpty && p.toList.all fun c =>
    c.isAlphanum || c == '.' || c == '_' || c == '/' || c == '-'

/-- Faults among the staged added files, each with the rule it breaks,
from `git diff --cached --numstat --diff-filter=A -z`: one NUL-terminated
`added<TAB>deleted<TAB>path` record per file, the path raw (no quoting).
Zero lines both ways is an empty file, and no convention in this tree
wants one (no `.gitkeep`) — it is debris too. A binary counts `-`, so a
zero-byte file is the only `0 0` record. -/
def addedPathFaults (numstat : String) : Array (String × String) := Id.run do
  let mut out : Array (String × String) := #[]
  for rec in numstat.splitOn "\x00" do
    match rec.splitOn "\t" with
    | [add, del, path] =>
      if !plainPath path then
        out := out.push (path, "characters outside [A-Za-z0-9._/-]")
      if add == "0" && del == "0" then
        out := out.push (path, "empty file")
    | _ => pure ()
  return out

/-- Case collisions among tracked files and their directories. Distinct
children do not make `Tests/` and `tests/` portable: the directory names
already collide. Include every prefix, then group by folded spelling. -/
def caseCollisions (paths : Array String) : Array (String × String) := Id.run do
  let prefixes := paths.flatMap fun path =>
    ((path.splitOn "/").foldl (fun (state : String × Array String) part =>
      let pathPrefix := if state.1.isEmpty then part else state.1 ++ "/" ++ part
      (pathPrefix, state.2.push pathPrefix)) ("", #[])).2
  let keyed := (prefixes.map fun p => (p.toLower, p)).qsort fun a b =>
    a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)
  let mut out : Array (String × String) := #[]
  let mut previous := none
  for current in keyed do
    if let some prior := previous then
      if current.1 == prior.1 && current.2 != prior.2 then
        out := out.push (prior.2, current.2)
    previous := some current
  return out

/-- The three spellings a home directory takes, composed so this file's own
text never carries one: the gate below scans every tracked text file, this
one included. -/
def dirHome : String := "/ho" ++ "me/"
def dirLocalHome : String := "/lo" ++ "cal" ++ dirHome
def dirUsers : String := "/Us" ++ "ers/"

/-- The one home directory the tree may name: the toolchain prefix the setup
instructions export (`LEAN_CC`), which belongs to no person. -/
def homeAllowed : List String := ["linuxbrew"]

/-- A character that can continue a path or host segment. -/
def segChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '.' || c == '-'

/-- Does `lit` occur in `cs` at index `i`? -/
def litAt (cs : Array Char) (i : Nat) (lit : String) : Bool := Id.run do
  let mut k := i
  for c in lit.toList do
    if cs[k]? != some c then return false
    k := k + 1
  return true

/-- The segment starting at index `j`: the run of segment characters. -/
def segAt (cs : Array Char) (j : Nat) : String := Id.run do
  let mut out := ""
  for k in [j:cs.size] do
    match cs[k]? with
    | some c => if segChar c then out := out.push c else return out
    | none => return out
  return out

/-- The home-directory paths one line names: a local home, a home other than
the toolchain's, or a macOS home, each followed by a segment that could be a
login. A path must *start* there — preceded by nothing, or by a character that
cannot continue a segment — so a URL whose path has a `home` segment is not a
person's directory, while the `file://` and `host:` forms still are. A PLAN
entry once carried a specialist's own home path through every gate; this is
that spelling, refused. -/
def homePaths (l : String) : Array String := Id.run do
  let cs := l.toList.toArray
  let mut out : Array String := #[]
  for i in [0:cs.size] do
    if cs[i]? == some '/' then
      let atStart := i == 0 || !segChar (cs[i - 1]?.getD ' ')
      if atStart then
        let hit (pre : String) (allowed : List String) : Option String :=
          if litAt cs i pre then
            let x := segAt cs (i + pre.length)
            match x.toList.head? with
            | some c => if (c.isAlphanum || c == '_') && !allowed.contains x
                then some (pre ++ x) else none
            | none => none
          else none
        match hit dirLocalHome [] with
        | some h => out := out.push h
        | none =>
          match hit dirHome homeAllowed with
          | some h => out := out.push h
          | none =>
            if let some h := hit dirUsers [] then out := out.push h
  return out

/-- Records of `git grep -n -z`: `path NUL line NUL content`, one per line. -/
def grepRecords (out : String) : Array (String × Nat × String) := Id.run do
  let mut recs : Array (String × Nat × String) := #[]
  for r in out.splitOn "\n" do
    match r.splitOn "\x00" with
    | p :: n :: rest => recs := recs.push (p, n.toNat?.getD 0, String.intercalate "\x00" rest)
    | _ => pure ()
  return recs

/-- Every home-directory path among the given lines, located. -/
def homePathHits (lines : Array (String × Nat × String)) : Array (String × Nat × String) :=
  lines.foldl (init := #[]) fun acc (f, n, l) =>
    (homePaths l).foldl (init := acc) fun acc h => acc.push (f, n, h)

/-- The kind of home a hit names, its login dropped: what the gate prints,
since a login names a person. -/
def homeKind (h : String) : String :=
  if h.startsWith dirLocalHome then dirLocalHome
  else if h.startsWith dirUsers then dirUsers
  else dirHome

/-- The objects `git cat-file --batch` answered, one per request in order:
a found object's content, empty content for a name git could not resolve. -/
def parseBatch (out : ByteArray) (n : Nat) : Array ByteArray := Id.run do
  let mut res : Array ByteArray := #[]
  let mut p := 0
  for _ in [0:n] do
    let mut q := p
    for _ in [p:out.size] do
      if out[q]? == some 10 then break
      q := q + 1
    let header := (String.fromUTF8? (out.extract p q)).getD ""
    match ((header.splitOn " ")[2]?).bind String.toNat? with
    | some size =>
      res := res.push (out.extract (q + 1) (q + 1 + size))
      p := q + 2 + size
    | none =>
      res := res.push ByteArray.empty
      p := q + 1
  return res

/-- The content of each named object, through one `git cat-file --batch`.
A dedicated task reads the answers while the requests are written, so
neither pipe can fill and stall the other. -/
def catBlobs (names : Array String) : IO (Array ByteArray) := do
  if names.isEmpty then return #[]
  let child ← IO.Process.spawn
    { cmd := "git", args := #["cat-file", "--batch"],
      stdin := .piped, stdout := .piped, stderr := .null }
  let (stdin, child) ← child.takeStdin
  let reader ← IO.asTask child.stdout.readBinToEnd Task.Priority.dedicated
  stdin.putStr (String.join (names.toList.map (· ++ "\n")))
  stdin.flush
  let out ← IO.ofExcept reader.get
  let code ← child.wait
  if code != 0 then
    IO.eprintln s!"pre-commit: git cat-file --batch exited {code}"
    IO.Process.exit 1
  return parseBatch out names.size

/-- This clone's denylist, compiled: `info/private-terms` in the git common
directory, which every worktree shares and no commit carries. `none` when
the file is absent: another machine, or CI. -/
def denylist : IO (Option Privacy.Matcher) := do
  let some dir ← gitOpt #["rev-parse", "--path-format=absolute", "--git-common-dir"]
    | return none
  let path := System.FilePath.mk dir.trimAscii.toString / "info" / "private-terms"
  unless ← path.pathExists do return none
  let text := Privacy.textOfBytes (← IO.FS.readBinFile path)
  return some (Privacy.Matcher.ofTerms (Privacy.parseTerms text))

/-- The paths of a `-z` numstat answer whose content the privacy gate reads
as a blob (`Privacy.blobRow`): those git counted no lines in — the content
it reads as binary, an attribute's `-diff` included — and those whose name
says their text is stored compressed. -/
def binaryPaths (numstat : String) : Array String :=
  Privacy.uniq ((numstat.splitOn "\x00").toArray.filterMap Privacy.blobRow)

/-- The paths of a `-z` name list given as bytes, from each of its readings
(`Privacy.segmentReadings`). -/
def zPaths (names : ByteArray) : Array String :=
  Privacy.uniq ((Privacy.segmentReadings names).foldl
    (fun acc r => acc.append ((r.splitOn "\x00").filter (!·.isEmpty)).toArray) #[])

/-- Where the staged changes add a denylisted term: an added line of
`diff` (the staged patch, `pinnedDiff`, in each of its readings), an added,
copied or renamed path, or the staged content of an added or modified file
git reads as binary or whose name says its text is compressed — its lines
when it is text all the same, its bytes and what they decompress to
otherwise. Each finding is a location, a path masked where it holds the
term, never the term. -/
def privacyStaged (m : Privacy.Matcher) (diff : ByteArray) : IO (Array String) := do
  let mut out := m.diffFindings diff ""
  let names ← gitBytes #["diff", "--cached", "--name-only", "-z", "--no-relative",
    "--diff-filter=ACR", "-M"]
  out := out.append (m.pathFindings (zPaths names) "" "its path")
  let binaries := binaryPaths (← git #["diff", "--cached", "--numstat", "-z", "--no-relative",
    "--no-renames", "--diff-filter=AM"])
  let blobs ← catBlobs (binaries.map (":" ++ ·))
  for (p, bs) in binaries.zip blobs do
    out := out.append (m.blobFindings p bs "")
  return Privacy.uniq out

/-- Set by the commit hook for the stages it runs, `lake lint` among them. -/
def hookVar : String := "LEANTEX_PRECOMMIT_HOOK"

/-- The revisions a landing would publish: reachable from HEAD and not from
`refs/remotes/origin/main`. -/
def unpushedRange : Array String := #["HEAD", "--not", "refs/remotes/origin/main"]

/-- Where an unpushed commit adds a denylisted term — an added line, an
added, copied or renamed path, an added or changed binary blob — or its
message names one. Every commit is read, not only the tip's tree: a term one
commit adds and a later one removes is gone from the tree and still in the
history a push publishes. Merges are read against their first parent. -/
def privacyCommits (m : Privacy.Matcher) : IO (Array String) := do
  let mergesFirst := "--diff-merges=first-parent"
  let patches ← gitBytes (#["-c", "core.quotePath=false", "log"] ++ pinnedPatch ++
    #[mergesFirst, "-p", "--format=%x00%H"] ++ unpushedRange)
  let paths ← gitBytes (#["log", "--format=%x00%H", "--name-only", "-z", "--diff-filter=ACR",
    "-M", mergesFirst] ++ unpushedRange)
  let numstat ← git (#["log", "--format=%x00%H", "--numstat", "-z", "--no-renames",
    "--diff-filter=AM", mergesFirst] ++ unpushedRange)
  let binaries := (Privacy.logRecords numstat).filterMap fun (sha, row) =>
    (Privacy.blobRow row).bind fun p => if p.contains '\n' then none else some (sha, p)
  let blobs ← catBlobs (binaries.map fun (sha, p) => s!"{sha}:{p}")
  let found := m.commitFindings (Privacy.logPatchesOf patches) (Privacy.logRecordsOf paths)
    (binaries.zip blobs)
  let log ← gitBytes (#["log", "-z", "--format=%H%n%B"] ++ unpushedRange)
  return Privacy.uniq (found.append (m.messageFindingsOf log))

/-- Where the tree the next commit carries names a denylisted term, and,
outside the commit hook, where an unpushed commit does (`privacyCommits`).
The tree is the index: every staged path and blob, which in a clean checkout
such as the landing's gate tree is HEAD's tree, and which a commit scrubbing
a term already carries scrubbed, so the fix is never refused by its own
gate. The commits are left to a run outside the hook, the landing's lint
above all: every way of rewriting one (an amend, a rebase's reword or
squash) runs the hook while the old commit is still HEAD's, and the hook
already reads what the commit being made adds. Each finding is a location,
never the term. With the list present and no `refs/remotes/origin/main` to
bound the unpushed commits, the run is refused (the second component says
why): skipping the commits there would pass a landing nothing had read. -/
def privacyTree (m : Privacy.Matcher) : IO (Array String × Option String) := do
  let staged ← gitBytes #["ls-files", "--stage", "-z"]
  let entriesOf (r : String) : Array (String × String) :=
    (r.splitOn "\x00").toArray.filterMap fun rec =>
      match splitFirst rec "\t" with
      | some (info, path) =>
        match info.splitOn " " with
        | [mode, oid, _] => if mode == "160000" then none else some (oid, path)
        | _ => none
      | none => none
  let readings := Privacy.segmentReadings staged
  let entries := entriesOf (readings[0]?.getD "")
  let paths := Privacy.uniq (readings.foldl (fun acc r => acc.append ((entriesOf r).map (·.2))) #[])
  let mut out := m.pathFindings paths "" "its path"
  let blobs ← catBlobs (entries.map (·.1))
  for ((_, p), bs) in entries.zip blobs do
    out := out.append (m.blobFindings p bs "")
  if (← IO.getEnv hookVar).isSome then return (out, none)
  if (← gitOpt #["rev-parse", "--verify", "--quiet", "refs/remotes/origin/main"]).isNone then
    return (out, some "this clone keeps a denylist but no refs/remotes/origin/main, so \
which commits are unpushed is unknown and none was checked against it.
  Fix: git fetch origin, so refs/remotes/origin/main names what the remote holds, then re-run.")
  return (out.append (← privacyCommits m), none)

def tokens (s : String) : List String :=
  (s.split Char.isWhitespace).toList.map (·.toString) |>.filter (!·.isEmpty)

/-- One applied name, dotted qualification included (`Ir.dumpInlineList`). -/
def isAtom (w : String) : Bool :=
  !w.isEmpty && w.toList.all (fun c => isWordChar c || c == '.')

/-- Is the append writing back onto the very name it extends
(`s := s ++ one x`)? That appends in place under unique ownership — the
blessed `mut` accumulator pattern — it does not copy a recursive result. -/
def selfAppend (lhs : String) : Bool :=
  match (lhs.splitOn ":=").reverse with
  | after :: before :: _ =>
    match tokens after, (tokens before).reverse with
    | [n], target :: _ => n == target
    | _, _ => false
  | _ => false

/-- Does the text after the line's last append read as a plain application
of two or more names ending in a bare variable (`… ++ walk cfg rest`)? That
is the spelling of every quadratic walk this tree has produced — with or
without a `#[` literal, qualified head (`Mod.f rest`) included: prepending
to the recursive call's result copies it at every element. Still legal: a
bare name after the append (the one-off prepend escape — bind the call to a
name first), a parenthesised append (`walk cfg (acc ++ node x) rest` extends
an accumulator), an RHS with non-name structure (literals, brackets), a
self-append (`s := s ++ one x`), and an RHS ending in a projection
(`out.extract i out.size` splices, it does not walk a tail). Line-local: an
application split across lines is not seen. -/
def quadraticPrepend (l : String) : Bool :=
  match (l.splitOn patAppend).reverse with
  | rhs :: lhs :: _ =>
    let ws := tokens rhs
    ws.length ≥ 2 && ws.all isAtom
      && (ws.getLastD "").toList.all isWordChar
      && !selfAppend lhs
  | _ => false

/-- The text of the innermost paren group still open at the end of `pre`,
with closed inner groups dropped: for `(f : (A → B) ` that is `f : `. -/
def lastOpenGroup (pre : String) : Option String :=
  let step : List String → Char → List String := fun st c =>
    match c, st with
    | '(', _ => "" :: st
    | ')', _ :: rest => rest
    | c, cur :: rest => (cur.push c) :: rest
    | _, [] => []
  (pre.toList.foldl step []).head?

/-- Does the group read `name :` — a binder with a type ascription, the only
opening a constructor field default can live in? A named argument `(n := 3)`
has no ascription colon and stays legal. -/
def binderish (g : String) : Bool :=
  let g := g.trimAscii.toString
  let name := (g.takeWhile isWordChar).toString
  !name.isEmpty && ((g.drop name.length).toString.trimAscii.toString).startsWith ":"

/-- Is some `:=` on the line inside a paren group that opens `(name :`? -/
def hasBinderDefault (t : String) : Bool := Id.run do
  let mut pre := ""
  for p in (t.splitOn ":=").dropLast do
    pre := pre ++ p
    if (lastOpenGroup pre).any binderish then return true
    pre := pre ++ ":="
  return false

/-- An inductive constructor field with a default value: patterns then
under-specify silently (`.run a b c` once matched only the default — PLAN
2026-09-15). Structure fields keep their defaults; their lines do not start
with `|`. The default lives in a binder, `(name : … := …)`, so the `:=`
must sit inside a paren group that opens like one: a `:=` elsewhere on a
`|` line — a Markdown table row in a docstring, a named argument — is not a
field default, and requiring the binder (rather than the absence of `=>`)
keeps a lambda default like `(f : α → β := fun _ => c)` caught. Takes the
raw diff line, `+` prefix included. -/
def ctorDefault (l : String) : Bool :=
  let t := (l.drop 1).toString.trimAscii.toString
  t.startsWith "|" && hasBinderDefault t

/-- Added lines of one unified diff, attributed to their file. -/
def addedByFile (diff : String) : Array (String × Array String) := Id.run do
  let mut out : Array (String × Array String) := #[]
  let mut cur : Option String := none
  let mut lines : Array String := #[]
  for l in diff.splitOn "\n" do
    if l.startsWith "+++ b/" then
      if let some f := cur then out := out.push (f, lines)
      cur := some (l.drop "+++ b/".length).toString
      lines := #[]
    else if l.startsWith "+" && !l.startsWith "+++" then
      lines := lines.push (l.drop 1).toString
  if let some f := cur then out := out.push (f, lines)
  return out

/-- Modules that consume the IR and must never reach back into the surface:
re-parsing is how md→PDF and tex→HTML would decay into N×M special cases. -/
def backendFiles : List String :=
  ["LeanTex/Core/Layout.lean", "LeanTex/Core/Pdf.lean", "LeanTex/Core/PdfContent.lean",
   "LeanTex/Core/PdfStruct.lean", "LeanTex/Core/Html.lean", "LeanTex/Core/HtmlDoc.lean",
   "LeanTex/Core/MathMl.lean"]

/-- `IO`, or a name that runs effects without it (`BaseIO`, `EIO`, and the
escapes that run either from pure code), as a code token, using the same
string and line-comment boundary as the banned-keyword gate. A block
comment's continuation still looks like code; the shared string scanner's
stated limitations apply here too. -/
def ioInCore (l : String) : Bool :=
  ["IO", "BaseIO", "EIO", "unsafeBaseIO", "unsafeIO", "unsafeEIO"].any (bannedWord · l)

def surfaceMods : List String := ["Lex", "Parse", "Elab", "Compat"]

/-- Composed like the banned keywords: the gate scans this file's own staged
diff, and the pattern must not read as a violation where it is defined. -/
def kwDemotedAssign : String := "demo" ++ "ted :="

/-- A literal demotion: severity and code derive from a `Diag`'s stored
kind (`Diag.of`), and `demoted` — the one policy bit left — is written in
Diag.lean alone (`\allow`'s demote). A call site that writes it delivers a
content loss as a note, the free-severity defect in its new spelling.
String and comment content aside. -/
def demotedAssign (l : String) : Bool :=
  containsSub (stripLineComment (stripStrings l)) kwDemotedAssign

def surfaceImports : List String := surfaceMods.map ("import LeanTex.Core." ++ ·)

/-- A qualified use `Mod.…` with nothing word-like before the name: catches
`Parse.scanOpt` and `LeanTex.Core.Parse.scanOpt`, not `myParse.foo`. -/
def usesQualified (l mod : String) : Bool :=
  (l.splitOn (mod ++ ".")).dropLast.any fun p =>
    match p.toList.getLast? with
    | none => true
    | some c => !isWordChar c

/-- A bare dimension literal (`pt 14`, `mm 5`, `inch 1`, `mm100 140`): a
design value spelled at a use site with no same-line `--` comment to carry
its source. The comment is taken as the source whatever it says — the gate
checks that a why was written, not that it is right — and same-line is a
stated limit of the diff scanner: it cannot see a comment on the line
above. -/
def dimLiteral (l : String) : Bool :=
  if containsSub l "--" then false
  else
    ["pt", "mm", "mm100", "inch"].any fun u =>
      let parts := l.splitOn (u ++ " ")
      (parts.zip parts.tail).any fun (before, after) =>
        (match before.toList.getLast? with
         | none => true
         | some c => !isWordChar c)
        && (after.toList.head?.map Char.isDigit).getD false


def isVarToken (w : String) : Bool :=
  !w.isEmpty && w.toList.all isWordChar
    && (w.toList.head?.map Char.isLower).getD false

/-- The pattern and RHS of a line-leading match arm, when the line is one
(`| pat => rhs` with exactly one `=>`). An arm split across lines, or an
arm not opening the line, is not seen — a stated line-scanner blind spot. -/
def armParts (l : String) : Option (List String × List String) :=
  let t := (stripLineComment l).trimAscii.toString
  if !t.startsWith "|" then none
  else match (t.drop 1).toString.splitOn "=>" with
    | [pat, rhs] => some (tokens pat, tokens rhs)
    | _ => none

/-- The identity catch-all of a rewrite walk: a match arm whose pattern is
one bare variable and whose RHS is that same variable (`| other => other`).
It is how a new IR constructor ships through a walk untouched — the walks
in Ir.lean and Layout.lean spell every constructor now, and the compiler
turns the next constructor into a build error at each. -/
def identityArm (l : String) : Bool :=
  match armParts l with
  | some ([p], [r]) => p == r && isVarToken p
  | _ => false

/-- A catch-all arm answering a bare numeral (`| _ => 1`): the measure-walk
default that once kept a step inside a section title off the handout.
Checked only in Ir.lean, where every walk over the IR lives. -/
def wildcardNumeral (l : String) : Bool :=
  match armParts l with
  | some ([p], [r]) =>
    (p == "_" || isVarToken p) && !r.isEmpty && r.toList.all Char.isDigit
  | _ => false

/-- The registered conservation-shape suffixes: a public IR-to-IR walk's
census statement is the walk's name plus one of these — census equality
(`dimBlocks_text`), leaf coverage (`keepFor_covers`), or conditional
identity (`substPage_id`). AGENTS.md § Conventions carries the
reviewer-facing suffix registry; this list is its mechanical half. -/
def conservesSuffixes : List String := ["_text", "_covers", "_id"]

/-- A public IR-to-IR walk entry: a non-private `def`, signature on one
line, taking and returning `Array Block` or `Array Inline` — the shape
whose census fact the obligation table's walk row owes. Returns the def's
name. A signature split across lines is not seen — the same line-scanner
limitation as `ioInCore`, stated, not claimed away. -/
def walkEntry (l : String) : Option String := Id.run do
  let (hidden, t) := declarationHead l
  if hidden then return none
  unless t.startsWith "def " do return none
  let name := String.ofList (((t.drop 4).toString).toList.takeWhile isWordChar)
  if name.isEmpty then return none
  let parts := t.splitOn ") : "
  if parts.length < 2 then return none
  let ret0 := ((parts.getLast?.getD "").splitOn ":=").headD ""
  let ret := (ret0.trimAscii).toString
  unless ret == "Array Block" || ret == "Array Inline" do return none
  -- an IR-to-IR walk consumes what it returns: a parameter carries the type
  let params := String.intercalate ") : " parts.dropLast
  unless containsSub params s!": {ret}" do return none
  return some name

/-- The escape a walk that genuinely conserves nothing writes beside its
def: a comment line carrying `conserves: none` and the reason. -/
def conservesNone (l : String) : Bool :=
  containsSub l "conserves: none"

/-- A backend reaching into the surface: an import, an `open`, or a
qualified use of a surface module, comments aside. An alias
(`abbrev P := LeanTex.Core.Parse` elsewhere) would not be seen — the same
line-scanner limitation as `ioInCore`, stated, not claimed away. -/
def surfaceReach (l : String) : Bool :=
  let l := stripLineComment l
  let t := l.trimAscii.toString
  surfaceImports.any (t == ·)
    || (t.startsWith "open " && surfaceMods.any (hasWord t ·))
    || surfaceMods.any (usesQualified l ·)

/-- The modules that judge a PDF's bytes and must never see the writer:
the census, and the conformance contract that reads it. -/
def judgeFiles : List String :=
  ["LeanTex/Core/PdfCensus.lean", "LeanTex/Core/PdfContract.lean"]

/-- A judge reaching into the writer: an import, an `open`, or a
qualified use of `Pdf` in PdfCensus.lean or PdfContract.lean. The census
judges a file's bytes through the reader alone — a census that could read
the writer's spellings would report what the writer meant, not what the
file carries, which is the defect (an unembedded copied face passing
`fonts.all_embedded`) it replaced; a contract that could see them would be
a contract on intent, and its violations would judge the plan, not the
file. `PdfRead.` is a different module and does not match. -/
def writerReach (l : String) : Bool :=
  let l := stripLineComment l
  let t := l.trimAscii.toString
  t == "import LeanTex.Core.Pdf"
    || (t.startsWith "open " && hasWord t "Pdf")
    || usesQualified l "Pdf"

/-- HTML built by concatenating tag strings: the exact shape AGENTS.md bans
(`"<" ++ …`) everywhere but the typed tree's own renderer (Html.lean, which
the caller exempts by file). A multi-character tag literal (`"<div>" ++`)
is a stated blind spot — Pdf.lean's CMap and XMP writers legitimately build
non-HTML angle-bracket text that way. -/
def tagStringEmit (l : String) : Bool :=
  ((stripLineComment l).splitOn "\"<\"").drop 1 |>.any fun rest =>
    rest.trimAscii.toString.startsWith patAppend

/-- `pat` with no identifier character following — so `FontDiscovery.scan` does not
match `FontDiscovery.scanRoots`. `hasWord` cannot carry a dotted name: the dot is
a word delimiter. -/
def hasCall (line pat : String) : Bool :=
  ((line.splitOn pat).drop 1).any fun rest =>
    match rest.toList with
    | [] => true
    | c :: _ => !isWordChar c

/-- A host font scan in a test: `FontDiscovery.scan` where only the shipped-corpus
`FontDiscovery.scanRoots [testFonts]` is hermetic (AGENTS.md, Conventions). -/
def fontScanInTest (l : String) : Bool :=
  hasCall (stripLineComment (stripStrings l)) "FontDiscovery.scan"

/-- The marker stating why an `Ir.dump` read in a test is not a page claim;
its presence on the line is the escape the gate honours. -/
def irTierMark : String := "-- ir tier:"

/-- An IR dump in a test without its stated tier. `Ir.dump` and its walk
companions all match: each reads the IR, and a page claim judged there is
the six-visual-defects shape (AGENTS.md, Conventions). -/
def irDumpUnmarked (l : String) : Bool :=
  containsSub (stripLineComment (stripStrings l)) "Ir.dump" && !containsSub l irTierMark

/-- Handed by impl-proofs: a heartbeat raise is a proof smell, not a budget
knob — the tree holds zero. Composed self-diff-safe, like the keywords. -/
def kwMaxHeartbeats : String := "maxHeart" ++ "beats"

/-- Lean's own heartbeat budget. A literal bound under it is no raise: it
holds a proof's cost below the default, and the kernel honours it too. -/
def defaultHeartbeats : Nat := 200000

/-- Any heartbeat setting but one: the bare option, alone on its line, set to
a literal bound under the default. A larger value, zero (no limit at all), a
value not spelled as a literal, and every other heartbeat option are raises:
`synthInstance`'s budget defaults to 20000, so a value under the bare
option's default can still raise it fivefold. -/
def heartbeatRaise (l : String) : Bool :=
  match (stripLineComment (stripStrings l)).splitOn kwMaxHeartbeats with
  | [_] => false
  | [before, after] =>
    !(before.endsWith "set_option " &&
      match after.trimAscii.toString.splitOn " " with
      | n :: _ => n.toNat?.any fun v => v != 0 && v ≤ defaultHeartbeats
      | [] => false)
  | _ => true

/-- Handed by impl-shapes: a catch-all arm that ships its scrutinee or an
accumulator through unchanged (`| _ => out`, `| other => other`) — in an IR
walk that is the next constructor silently falling through. A `none`/`nil`
pattern is a constructor match, not a catch-all; an answer (`false`,
`none`) or a control keyword (`break`) as RHS is a decision, not a
pass-through. -/
def wildcardThrough (l : String) : Bool :=
  let answers := ["false", "true", "none", "nil", "break", "continue", "return"]
  match armParts l with
  | some ([p], [r]) =>
    (p == "_" || (isVarToken p && p != "none" && p != "nil")) &&
      isVarToken r && !answers.contains r
  | _ => false

/-- `]!` sites in a file, strings and comments aside — the panic-on-miss
index COMMON bans adding to reach green. -/
def bangCount (ls : Array String) : Nat := Id.run do
  let mut n := 0
  for l in ls do
    n := n + ((stripLineComment (stripStrings l)).splitOn "]!").length - 1
  return n

/-- The frozen `]!` counts per file (whole LeanTex/ tree, 2026-09-18). A
commit may lower a file's count — and then lowers its row — never raise
it. Regenerate after removing sites: `bangCount` over the file. -/
def bangBaseline : List (String × Nat) := [
  ("LeanTex/Cli/Render.lean", 2),
  ("LeanTex/Core/Compat.lean", 2),
  ("LeanTex/Core/Elab.lean", 3),
  ("LeanTex/Core/Flate.lean", 2),
  ("LeanTex/Core/Font.lean", 3),
  ("LeanTex/Core/HtmlDoc.lean", 4),
  ("LeanTex/Core/Hyphen.lean", 4),
  ("LeanTex/Core/Ir.lean", 2),
  ("LeanTex/Core/Layout.lean", 41),
  ("LeanTex/Core/Lex.lean", 2),
  ("LeanTex/Core/MathParse.lean", 1),
  ("LeanTex/Core/Pdf.lean", 8),
  ("LeanTex/Core/Utf8.lean", 4)]

/-- The line's string-literal contents, concatenated — `stripStrings`'
complement, with its stated line-scanner limitations. What the engine says
to a user lives in string literals; this is the text the self-containment
gate reads. -/
def stringsOnly (l : String) : String := Id.run do
  let mut out := ""
  let mut inStr := false
  let mut esc := false
  for c in l.toList do
    if inStr then
      if esc then
        esc := false
        out := out.push c
      else if c == '\\' then esc := true
      else if c == '"' then inStr := false
      else out := out.push c
    else if c == '"' then
      inStr := true
      out := out.push ' '
  return out

/-- A milestone token (`M6`, `M8`, …): an internal name that means nothing
outside this repository. -/
def milestoneTok (s : String) : Bool := Id.run do
  let cs := s.toList.toArray
  for i in [0:cs.size] do
    if cs[i]! == 'M' && ((cs[i+1]?.map Char.isDigit).getD false)
        && !(i > 0 && (isWordChar (cs[i-1]!)))
        && !((cs[i+2]?.map isWordChar).getD false) then
      return true
  return false

/-- A repo-internal reference inside a string literal: `PLAN.md`,
`AGENTS.md`, a `LeanTex/` path, or a milestone token. A diagnostic must be
actionable by someone holding only their own document — `see PLAN.md`
points at a file the user does not have (the diag-voice defect). Lines that
are themselves comments stay legal: prose for developers may name the plan. -/
def repoRefInString (l : String) : Bool :=
  let s := stringsOnly (stripLineComment l)
  containsSub s "PLAN.md" || containsSub s "AGENTS.md" ||
    containsSub s "LeanTex/" || milestoneTok s

/-- The Config fields the driver may read: the command, the diagnostic
channel, the where/when of a run, the run's acceptance policy, the font
environment — and `mathBoundary`, the one recorded artifact-shaping
remainder (see `artifact_flag_free` in Args.lean). `effectiveEmit` is the
planning function the theorem covers. A new entry lands here only after
the question "can it change a byte of the artifact?" is answered no — a
field that does shape the artifact is the theorem's counterexample, not a
new list entry. -/
def driverConfigReads : List String :=
  ["cmd", "verbosity", "quiet", "porcelain", "color", "output", "watch",
   "bestEffort", "werror", "fontDirs", "mathBoundary", "effectiveEmit"]

/-- A change a golden's regeneration may travel with: Lean source, or a
golden fixture under `testdata/corpus`, in either surface the golden set
reads (`.tex`, `.md`). -/
def goldenSource (f : String) : Bool :=
  f.endsWith ".lean" ||
    (f.startsWith "testdata/corpus/" && (f.endsWith ".tex" || f.endsWith ".md"))

/-- A `cfg.<name>` read whose name is not on `driverConfigReads`, comments
and strings aside. This is how a new flag would reach a backend from the
driver — the thread starts as exactly this token in `Main.build` — so the
common leak is caught where it starts. Stated misses, line-scanner shaped:
a read that never spells the dot (destructuring, a helper handed the whole
`Config`), an alias (`let c := ui.cfg` then `c.newFlag`), and an
allowlisted field newly routed into a backend call. -/
def undeclaredConfigRead (l : String) : Bool := Id.run do
  let t := stripLineComment (stripStrings l)
  let parts := t.splitOn "cfg."
  let mut pre := parts.headD ""
  for p in parts.tail do
    let boundary := match pre.toList.getLast? with
      | none => true
      | some c => !isWordChar c
    if boundary then
      let field := (p.takeWhile isWordChar).toString
      if !field.isEmpty && !driverConfigReads.contains field then
        return true
    pre := pre ++ "cfg." ++ p
  return false

/-- The string-comparison spelling that compiles against the `DocClass`
inductive and bypasses exhaustiveness: `docClass.name == "…"` re-creates
the stringly class checks the inductive replaced, one flag at a time. The
plain `docClass == "article"` does not build, so the compiler owns that
spelling; this is the variant it cannot see. -/
def classNameCompare (l : String) : Bool :=
  containsSub (stripLineComment (stripStrings l)) "docClass.name =="

/-- The quoted names of the `nativePackages` list block in a Compat
source: from its `def nativePackages` line to the block's closing
bracket. Package names never contain a quote or a bracket, so the scan is
a line walk. -/
def nativePackagesOf (src : String) : Array String := Id.run do
  let mut out : Array String := #[]
  let mut inside := false
  for l in src.splitOn "\n" do
    if (stripLineComment l).startsWith "def nativePackages" then
      inside := true
    else if inside then
      let mut parts := (l.splitOn "\"")
      let mut quoted := false
      for p in parts do
        if quoted then out := out.push p
        quoted := !quoted
      if containsSub (stripLineComment (stripStrings l)) "]" then
        inside := false
  return out

/-- A local reimplementation of Support's `hasStr`: a function-shaped `let`
whose body splits on a needle and compares the piece count against one —
`> 1` and `≥ 2` are the two spellings of "it appears". Eight copies of
this idiom grew across the test tree before the shared helper was reached
for; the Support-rule gate below could not see them because they are
`let`s, not top-level defs. Checked in test files only: the hook's own
scanners split on markers legitimately. -/
def splitOnIdiom (l : String) : Bool :=
  let t := ((stripLineComment l).trimAscii).toString
  t.startsWith "let " && containsSub t ".splitOn " &&
    (containsSub t ".length > 1" || containsSub t ".length ≥ 2")

/-- The `seal`/`unseal` names of one source, in occurrence order: `seal`
keeps a knot's elaboration budget, and every sealed name must be unsealed
right after the knot — the lists are hand-kept in pairs, and a
mis-mirrored unseal is silent until a later proof slows or fails strangely
(asked by q-elab). Comments are stripped; a docstring's continuation line
opening with `seal ` is a stated line-scanner blind spot, like
`ioInCore`'s. -/
def sealNames (lines : Array String) : List String × List String := Id.run do
  let mut sl : List String := []
  let mut ul : List String := []
  for l in lines do
    let t := (((stripLineComment l).trimAscii).toString)
    if t.startsWith "unseal " then
      for w in tokens ((t.drop 7).toString) do ul := w :: ul
    else if t.startsWith "seal " then
      for w in tokens ((t.drop 5).toString) do sl := w :: sl
  return (sl, ul)

/-- The mirror's residue as a multiset difference — (sealed but never
unsealed, unsealed but never sealed) — so a name two knots seal must be
unsealed twice. Empty on both sides is the invariant. -/
def sealMismatch (lines : Array String) : List String × List String :=
  let (sl, ul) := sealNames lines
  (ul.foldl (fun acc n => acc.erase n) sl, sl.foldl (fun acc n => acc.erase n) ul)

/-- Deliberately module-final seals, frozen by name: MarkdownDoc seals
`noteDefs` so unification cannot whnf through the collection walk, and
never unseals it — its comment says so where it stands. Shrink the list
when a site closes; a new entry is a deliberate decision, not a mirror
miss. -/
def sealAllow : List String := ["noteDefs"]

/-- The size-step formula re-spelled outside Ir (asked by q-layout, live
once `Ir.scaleStep` landed): `sizeScale.lookup … getD` is `scaleStep`'s
body, and nine copies of it once diverged on the default (`getD 700` vs
`getD 1000` — both dead, still drift). A bare `match` on the lookup is not
the shape: an unknown size name must stay an `Option`. -/
def scaleStepRespell (l : String) : Bool :=
  let t := stripLineComment (stripStrings l)
  containsSub t "sizeScale.lookup" && containsSub t ".getD"

/-- A bare state mutation in Compat: a statement opening with `modify` or
`set`, the two spellings the file uses. Legal only inside the declared
doors (`compatStateDoors`): the rewrite dispatcher's silence guard reads
`diags.size` and the `writes` counter (`rewriteCtrl_accounts`), and a
mutation outside `say`/`write` is invisible to both — the arm would look
silent and draw a false W0387. Statement-initial only: a mutation hidden
mid-line is a stated line-scanner blind spot, like `ioInCore`'s, and
docstring prose using the words stays legal. -/
def bareStateMutation (l : String) : Bool :=
  let t := (((stripLineComment (stripStrings l)).trimAscii).toString.takeWhile isWordChar).toString
  t == "modify" || t == "set"

/-- The doors a `modify`/`set` may live in, in Compat: `say` pushes the
diagnostic, `write` counts the mutation, `account` is the guard itself. -/
def compatStateDoors : List String := ["say", "write", "account"]

/-- The reads that name the document's declared *setup* rather than the
content under judgement: the elaboration context, the driver's config, the
scanned declaration list, and the monadic state read through `get`. A
condition built from one of these decides something about the configuration;
a condition built from the content decides something about the loss. That is
the whole distinction the stale-premise defects turned on — `picTool` said
which tool was configured, and the fact the gate needed was whether anything
had drawn the picture. -/
def premiseSources : List String := ["ctx.", "cfg.", "decls", "(← get)."]

/-- The diagnostic doors: the calls that name a loss to the reader. `say` and
`sayOnce` are separate tokens to `hasWord`, so both are listed. -/
def premiseEmitters : List String := ["say", "sayOnce", "warnOnce", "noteOnce", "diag"]

/-- Does the text call a diagnostic door? -/
def emitsDiag (t : String) : Bool := premiseEmitters.any (hasWord t ·)

/-- Does the text read the declared setup? -/
def readsSetup (t : String) : Bool := premiseSources.any (containsSub t ·)

/-- The indentation of a line, in leading spaces. -/
def indentOf (l : String) : Nat := (l.toList.takeWhile (· == ' ')).length

/-- The condition text of a conditional opening at line `i`, continuation
lines included up to the `then`/`do` that closes it, with the line the
condition ends on. `none` when the line opens no conditional. Four lines is
the bound: the longest condition in this tree spans two, and the gate whose
`ctx.` read sat on the continuation line is why this is not line-local. -/
def condSpan (lines : Array String) (i : Nat) : Option (String × Nat) := Id.run do
  let l := stripLineComment (lines[i]?.getD "")
  unless hasWord l "if" || hasWord l "unless" do return none
  let mut cond := l
  let mut j := i
  for _ in [0:4] do
    if hasWord cond "then" || hasWord cond "do" then break
    j := j + 1
    cond := cond ++ " " ++ stripLineComment (lines[j]?.getD "")
  return some (cond, j)

/-- The block a conditional opens (the following more-indented lines) and the
forty lines after it: the two texts the site judgement reads. -/
def premiseBlock (lines : Array String) (i j : Nat) : String × String := Id.run do
  let ind := indentOf (lines[i]?.getD "")
  let mut body := ""
  let mut k := j + 1
  for _ in [0:400] do
    if k ≥ lines.size then break
    let lk := lines[k]?.getD ""
    let t := lk.trimAscii.toString
    if !t.isEmpty && indentOf lk ≤ ind then break
    if !t.isEmpty then
      let piece := stripLineComment lk
      body := body ++ "\n" ++ piece
    k := k + 1
  let mut after := ""
  for d in [0:40] do
    let piece := stripLineComment (lines[k + d]?.getD "")
    after := after ++ "\n" ++ piece
  return (body, after)

/-- What a premise site claims, in the two spellings a line scanner can see.
`.gate`: the engine speaks only under this configuration, so the other
configuration is claimed to be covered elsewhere. `.silence`: the engine goes
quiet under this configuration and names the loss below, so the quiet branch
claims another subsystem names it. `.demote`: the loss is delivered at
reduced strength because the reader is claimed to be unable to act — a fact
about who wrote the file, never about the loss. -/
inductive PremiseKind where
  | gate
  | silence
  | demote
  deriving BEq

def PremiseKind.what : PremiseKind → String
  | .gate => "names a loss only under a declared configuration"
  | .silence => "goes quiet under a declared configuration, naming the loss below"
  | .demote => "computes a demotion: the reader is claimed unable to act"

/-- A demotion whose value is computed rather than written. `demote := true`
is a decision about this loss; `demote := f x` is a claim about the reader —
who wrote the file the site sits in — which is a fact about another
subsystem, and the `.sty` proxy defect is what it cost. The door's own
signature (`demote : Bool := false`) spells no `:=` after the name and does
not match. -/
def computedDemote (l : String) : Bool :=
  ((stripLineComment (stripStrings l)).splitOn "demote := ").drop 1 |>.any fun rest =>
    let w := (rest.trimAscii.toString.takeWhile isWordChar).toString
    !w.isEmpty && w != "true" && w != "false"

/-- The premise site a line opens, if any: a computed demotion, or a
conditional on the declared setup that either names a loss in its block or
skips one named below it. A conditional whose block both reads the setup and
emits is a `.gate`; one that returns without emitting while an emission
follows is a `.silence`. -/
def premiseSite (lines : Array String) (i : Nat) : Option PremiseKind := Id.run do
  let l := lines[i]?.getD ""
  if computedDemote l then return some .demote
  match condSpan lines i with
  | none => return none
  | some (cond, j) =>
    unless readsSetup cond do return none
    let (body, after) := premiseBlock lines i j
    if emitsDiag body || emitsDiag cond then return some .gate
    if hasWord body "return" && emitsDiag after then return some .silence
    return none

/-- The marker beside a premise site: `-- premise: <pin> — <why>`, naming the
check that fails when the premise breaks, or `-- premise: none — <why>` as
the reasoned refusal. The `conserves: none` refusal is the precedent; the pin
resolving against the tree is what `scripts/cites.lean` does for a cited
theorem, one step over. -/
def premiseMark : String := "premise:"

/-- The pin and reason a marker line carries: `some (none, why)` for the
refusal spelling, `none` when the line carries the mark with no reason after
the pin — a marker that names nothing is not a marker. -/
def premisePin (l : String) : Option (Option String × String) :=
  if !containsSub l premiseMark then none
  else
    match tokens ((l.splitOn premiseMark).getLastD "") with
    | [] => none
    | pin :: rest =>
      let why := String.intercalate " " (rest.filter (fun w => w != "—" && w != "-"))
      if (why.trimAscii.toString).isEmpty then none
      else some (if pin == "none" then (none, why) else (some pin, why))

/-- Does `pin` name something that fails when the premise breaks: a theorem
the build checks, or a check block the suite runs — defined in a test file and
invoked, so a block the suite never calls cannot pin anything. Text-scanned,
with the blind spots `scripts/cites.lean` records for the technique (a name on
a declaration's continuation line is invisible); a pin is a short registered
name, and the resolver there cannot be reached from here without a compiled
environment. -/
def pinResolves (treeText testText : String) (testDefs : List String)
    (pin : String) : Bool :=
  containsSub treeText s!"theorem {pin}" ||
    (testDefs.contains pin && ((testText.splitOn pin).length ≥ 3))

/-- A premise site that cannot carry its marker in place, with the pin that
holds it. Every row is a migration step, not a parking space: when the
marker lands beside the site, the row goes. `pin := none` is recorded debt —
the premise is not falsified by anything, and the reason says what is
missing. The rows are checked in both directions: the site text must still
occur in the file (an edited condition invalidates the row, which is the
point — a changed gate owes a fresh reading of its premise), and a named pin
must resolve. -/
structure PremiseRow where
  file : String
  site : String
  pin : Option String
  why : String

/-- The premise sites of this tree, 2026-09-24. Each was found by the gate
below and read by hand; none can carry an in-place marker yet, because the
engine files belong to other slices. -/
def premiseRegistry : List PremiseRow := [
  { file := "LeanTex/Core/Elab.lean", site := "Compat.boundaryCtrls.contains name"
    pin := none
    why := "premise false when no picture reached the boundary: the set lines \
ride into a standalone only for a picture that went there whole, so a \
natively drawn document swallows them unnamed -- W0334's fix, unapplied to W0301" },
  { file := "LeanTex/Core/Elab.lean", site := "hnb : ctx.noteBody"
    pin := none
    why := "the premise (a note's frame has no side channel to drain into) is \
carried by an inline have, not a named statement; noteChecks exercises the \
refusal without falsifying the premise" },
  { file := "LeanTex/Core/Elab.lean", site := "(← get).titleDone"
    pin := some "titleChecks"
    why := "the once-only rule the premise cites (classes.dtx) is exercised there" },
  { file := "LeanTex/Core/Elab.lean", site := "(← get).declaredKeys.contains"
    pin := some "layerDiagChecks"
    why := "breaks if declaredKeys stops meaning document-declared" },
  { file := "LeanTex/Core/Compat.lean", site := "(← get).deck && modeSilencesPresentation"
    pin := some "frameSpecChecks"
    why := "pins that a silenced frame ships no page, which is what buys the silence" },
  { file := "LeanTex/Core/Compat.lean", site := "(← get).inDoc"
    pin := some "compatChecks"
    why := "asserts a body \\usepackage draws the placement refusal and never W0103, \
which is the premise (the dispatch below never judges it)" },
  { file := "LeanTex/Core/Elab.lean", site := "ctx.user.any (·.name == element)"
    pin := some "classHookChecks"
    why := "asserts an authored role's class reaches the page, which is the premise \
that makes styling a \\define'd name meaningful rather than silently inert" },
  { file := "LeanTex/Core/Compat.lean", site := "styInternal"
    pin := none
    why := "the proxy defect: the load-bearing fact is whether the author wrote \
the file, and the predicate also asks whether the name is a TeX internal, so a \
vendor .sty's own macro names stay full warnings under --werror" },
  { file := "LeanTex/Core/Elab.lean", site := "Compat.styInternal"
    pin := none
    why := "the same proxy, at the preamble's unknown-command and refused-set sites" }]

/-- One staged-diff check: which files it reads, the line predicate, the
headline naming the file, and the fix paragraph. The stanzas `main` used
to spell one by one differed only in these four fields. -/
structure Gate where
  applies : String → Bool
  flag : String → Bool
  what : String → String
  help : String

def gates : List Gate := [
  { applies := (·.startsWith "LeanTex/")
    flag := classNameCompare
    what := fun f => s!"a class judged by its name string (`docClass.name ==`) in {f}"
    help := "  The DocClass inductive exists so a class check is a match the compiler
  keeps exhaustive; comparing the name string re-creates the stringly
  checks it replaced, invisible to the next constructor.
  Fix: match on the constructor; a genuinely name-shaped need (a
  diagnostic quoting the class) reads .name without comparing it." },
  { applies := fun _ => true
    flag := bannedWord kwPartial
    what := fun f => s!"new '{kwPartial}' in staged changes to {f}"
    help := s!"  The tree holds no '{kwPartial}': every recursion terminates by a
  proved measure (elaboration_total names the elaborator's; AGENTS.md,
  Conventions, holds the technique) — the allowance list emptied on
  2026-09-19 and stays empty.
  Fix: make the recursion structural (see AGENTS.md, Conventions)." },
  { applies := fun _ => true
    flag := bannedWord kwSorry
    what := fun f => s!"'{kwSorry}' in staged changes to {f}"
    help := "  Fix: finish the proof." },
  { applies := fun _ => true
    flag := bannedWord kwUnsafe
    what := fun f => s!"'{kwUnsafe}' in staged changes to {f}"
    help := s!"  Fix: stay in the safe fragment; {kwUnsafe} code voids the certification story." },
  { applies := fun _ => true
    flag := quadraticPrepend
    what := fun f => s!"'{patAppend} walk rest' (prepend to a recursive call's result) in {f}"
    help := "  Prepending to a recursive call's result copies it at every element -- it
  turned a 4 ms pass into 1157 ms, three times in one day (PLAN 2026-09-16).
  Fix: thread an Array accumulator through the walk (see Compat.rewriteList);
  a one-off prepend outside a recursion can bind the call to a name first." },
  { applies := fun _ => true
    flag := ctorDefault
    what := fun f => s!"inductive constructor field with a default value, in {f}"
    help := "  Defaults on constructor fields let patterns under-specify silently: `.run
  a b c` once matched only the default, with the whole suite green (PLAN
  2026-09-15).
  Fix: spell the field at every constructor site; defaults belong on structures." },
  { applies := fun f => f.endsWith ".lean" && f != "LeanTex/Core/Diag.lean"
    flag := demotedAssign
    what := fun f => s!"a demotion written outside Diag.lean, in {f}"
    help := "  Severity and the code letter are projections of a Diag's stored kind
  since the derivation landed — `severity :=` no longer compiles — and
  `demoted` is the one policy bit left: a call site that writes it ships
  a content loss as a note, which is how \"content silently gone\" once
  shipped as a warning fourteen times (PLAN, the severity policy).
  Fix: emit through Diag.of; demotion is `\\allow`'s decision alone
  (Diag.demote, in Diag.lean)." },
  { applies := fun f => f.startsWith "LeanTex/" || f == "Main.lean"
    flag := repoRefInString
    what := fun f => s!"a repo-internal reference in a string the user can see, in {f}"
    help := "  A diagnostic is read by someone holding only their own document: PLAN.md,
  AGENTS.md, a LeanTex/ path, and milestone names (M6, M8) mean nothing
  there — 'see PLAN.md' shipped in real output (the diag-voice defect).
  Fix: say what happens and what to write instead; the voice lint in
  Tests.lean judges the registered text." },
  { applies := fun f => f == "Main.lean" || f == "LeanTex/Cli/Driver.lean"
    flag := undeclaredConfigRead
    what := fun f => s!"a Config read in {f} not on the driver's declared list"
    help := "  The artifact is a function of the document and the font environment;
  flags are not arguments to it (AGENTS.md, Conventions). A new Config
  field the driver reads is one question away from shaping the artifact,
  so it lands on driverConfigReads (scripts/precommit.lean) only after
  that question is answered no — and a flag that does shape the artifact
  breaks the theorem artifact_flag_free instead of growing the list.
  Fix: make it a document declaration (\\output) rather than a flag; a
  flag about where/when/how-loudly goes on the list, deliberately." },
  { applies := fun f => f.startsWith "LeanTex/Core/" || f == "LeanTex/Cli/World.lean"
    flag := ioInCore
    what := fun f => s!"IO in {f}"
    help := "  Modules under LeanTex/Core/ do no IO: files
  and fonts surface as request values the CLI driver fulfills. World.lean
  is the host's vocabulary, and a program over it is a value: Host.lean
  alone answers its questions.
  Fix: return a request value and fulfill it under LeanTex/Cli/, or ask
  World's question and answer it in Host.lean." },
  { applies := (·.startsWith "LeanTex/Core/")
    flag := identityArm
    what := fun f => s!"identity catch-all arm (`| x => x`) in {f}"
    help := "  A rewrite walk with a wildcard ships a new IR constructor through
  untouched -- the shape of the covered-content defect (PLAN 2026-09-17).
  Fix: spell every constructor; the compiler then makes the next
  constructor a build error at every walk (AGENTS.md, obligation table)." },
  { applies := (· == "LeanTex/Core/Ir.lean")
    flag := wildcardNumeral
    what := fun f => s!"wildcard arm answering a numeral (`| _ => 1`) in {f}"
    help := "  A measure walk with a numeric default silently miscounts a new IR
  constructor -- a step inside a section title got no handout page this
  way (PLAN 2026-09-17).
  Fix: spell every constructor and say what each one measures." },
  { applies := (backendFiles.contains ·)
    flag := surfaceReach
    what := fun f => s!"a backend reaches into the surface, in {f}"
    help := "  Backends consume the IR and nothing else; a backend that re-parses is how
  md→PDF and tex→HTML decay into N×M special cases (AGENTS.md, Conventions).
  Fix: put what the backend needs on the IR." },
  { applies := (judgeFiles.contains ·)
    flag := writerReach
    what := fun f => s!"a judge of the PDF's bytes reaches into the writer, in {f}"
    help := "  PdfCensus judges what a PDF's bytes carry, through PdfRead alone, and
  PdfContract judges the census; a judge that can see Pdf.lean's spellings
  reports the writer's intent, which is how an unembedded copied face once
  passed fonts.all_embedded.
  Fix: read the fact off the parsed objects or the census; a spelling a
  judge needs is a fact of ISO 32000-2 or a profile, stated where it
  stands with its section." },
  { applies := (backendFiles.contains ·)
    flag := dimLiteral
    what := fun f => s!"bare dimension literal in {f}"
    help := "  A design value in a backend is a token, or carries its source where it
  stands (AGENTS.md, obligation table): a loose `pt 14` is how a heading
  scale drifts from the type scale, invisibly.
  Fix: read a token/style/palette entry, or put the source in a `--`
  comment on the same line (the diff scanner cannot see the line above)." },
  { applies := fun f => backendFiles.contains f && f != "LeanTex/Core/Html.lean"
    flag := tagStringEmit
    what := fun f => s!"HTML built from tag strings, in {f}"
    help := "  HTML is a typed tree with a certified escaper; a concatenated tag skips
  the escaper by construction (AGENTS.md, Conventions). Html.lean's own
  renderer is the one sanctioned site.
  Fix: build the node with the typed constructors; the renderer emits it." },
  { applies := fun f => f == "Tests.lean" || f.startsWith "Tests/"
    flag := fontScanInTest
    what := fun f => s!"FontDiscovery.scan in {f}"
    help := "  Tests scan only the shipped corpus fonts — FontDiscovery.scanRoots [testFonts]
  (AGENTS.md, Conventions); a host scan makes the suite depend on what
  this machine has installed.
  Fix: ship the font in testdata/corpus/fonts/ and scan through testFonts." },
  { applies := fun f => f == "Tests.lean" || f.startsWith "Tests/"
    flag := irDumpUnmarked
    what := fun f => s!"Ir.dump in {f} without its stated tier"
    help := s!"  A claim about what a page shows never comes from an IR dump — six visual
  defects once passed a fully green suite that way (AGENTS.md, Conventions).
  Fix: assert over Layout.Out or the typed HTML tree; an IR-tier fact that
  is not a page claim says so on the line: `{irTierMark} <why>`." },
  { applies := fun f => f.startsWith "LeanTex/" && f != "LeanTex/Core/Ir.lean"
    flag := scaleStepRespell
    what := fun f => s!"the size-step formula re-spelled (`sizeScale.lookup … getD`) in {f}"
    help := "  Ir.scaleStep is the one resolving site for a named step of the size
  scale; the getD re-spelling is how markBox's default drifted to 700
  while every other site said 1000.
  Fix: read Ir.scaleStep base name; a genuine Option need (an unknown
  name must stay none) matches on the lookup without getD, and a theorem
  naming a raw table value lives beside the table in Ir.lean." },
  { applies := fun f => (f == "Tests.lean" || f.startsWith "Tests/")
      && f != "Tests/Support.lean"
    flag := splitOnIdiom
    what := fun f => s!"a local copy of Support's hasStr (a splitOn-count `let`) in {f}"
    help := "  (hay.splitOn needle).length > 1 is Tests/Support.lean's hasStr; eight
  copies of the idiom grew across the test tree before the shared helper
  was reached for (AGENTS.md, Conventions: the second caller moves it).
  Fix: use hasStr, or bind it over a fixed page: let has := hasStr page." },
  { applies := fun f => f.startsWith "LeanTex/" && f.endsWith ".lean"
    flag := heartbeatRaise
    what := fun f => s!"a {kwMaxHeartbeats} raise in {f}"
    help := s!"  The tree holds zero heartbeat raises; a proof that needs one is telling
  you the definition's shape is wrong (the MarkdownDoc emit_body_title_first
  case), not that the budget is small.
  Fix: reshape the proof or the definition. Report any remaining blocker
  without claiming an unproved guarantee." }]

/-- An import of the scoreboard format module, spelled by concatenation so
this file's own gate does not read it as a site. -/
def boardImport : String := "import scripts" ++ ".Board"

/-- The one script that frames its own selftest. `scripts/scoreboard.lean`
is the aggregate, and its success line counts the cases its own body binds —
the malformations, the well-formed states, the base and CLI cases — so no
caller outside it can supply that line. -/
def selftestFrameAllow : List String := ["scripts/scoreboard.lean"]

/-- Tier producers whose selftest still frames itself, each with what its
migration owes. Read in both directions: a row whose file no longer frames
itself fails, so a migrated file drops its row in the same commit. -/
def selftestFrameDebt : List (String × String) :=
  [("scripts/commonmark.lean", "its assertions push to a local array; each becomes a `no` call"),
   ("scripts/parity.lean", "its assertions push to a local array; each becomes a `no` call")]

/-- The top-level `def` name a line binds, dots included, for the
gates that need to know which definition a line stands inside. Visibility,
attributes and declaration modifiers do not change ownership; a nested helper
or a prose mention never counts. The name is the whole declared one — truncating it at the first dot
made every `Foo.bar` in the tree read as `Foo`, so two files declaring
different members of one namespace read as one helper declared twice. -/
def topLevelDefName (l : String) : Option String :=
  let t := (declarationHead l).2
  if t.startsWith "def " then
    let rest := (t.drop 4).toString
    let n := (rest.takeWhile (fun c => isWordChar c || c == '.' || c == '\'')).toString
    if n.isEmpty then none else some n
  else none

/-- Resolve line-leading definition names through namespace and section scopes.
This shares `declarationHead`'s lexical limits; it does not elaborate aliases.
Two modules may both define `checks` in distinct namespaces without defining
the same helper. Sections change scope lifetime, not the namespace. -/
def scopedDefNames (lines : Array String) : Array String := Id.run do
  let qualify (space name : String) :=
    if name.startsWith "_root_." then (name.drop 7).toString
    else if space.isEmpty then name else space ++ "." ++ name
  let mut scopes : List String := []
  let mut out := #[]
  for line in lines do
    let head := (declarationHead line).2
    let space := scopes.headD ""
    if head.startsWith "namespace " then
      let name := ((head.drop 10).toString.splitOn " ").headD ""
      scopes := qualify space name :: scopes
    else if head == "section" || head.startsWith "section " then
      scopes := space :: scopes
    else if head == "end" || head.startsWith "end " then
      scopes := scopes.tail
    else if let some name := topLevelDefName line then
      out := out.push (qualify space name)
  return out

/-- CLI terminal output has a small, audited boundary. Document diagnostics
remain Diag values until Ui.diag calls Render; other writers carry status,
startup failures or a command's result (including the stable IR dump).
This is a source convention check, not interprocedural data-flow analysis.
Mask strings and nested block comments across lines so documentation and
multiline help cannot look like output calls. -/
def diagnosticOutputBypasses (file : String) (lines : Array String) : Array (Nat × String) := Id.run do
  unless file == "Main.lean" || file.startsWith "LeanTex/Cli/" do return #[]
  let writers := ["Ui.diag", "Ui.accepted", "Ui.phase", "Ui.summary", "Ui.done",
    "Ui.werror", "main", "dump", "hyphenate"]
  let names (s : String) := (s.split (fun c => !(isWordChar c || c == '.'))).toList.map
    (·.toString) |>.filter (!·.isEmpty)
  -- Output is also a configuration/path field. Only associate it with
  -- receivers explicitly bound as Diag or built by Diag.of in this def;
  -- a mention of Diag must not taint unrelated status/output values.
  let diagBindings (s : String) :=
    (s.split (fun c => c == '(' || c == ')' || c == '{' || c == '}')).toList.flatMap fun part =>
      match part.toString.splitOn ":" with
      | lhs :: rhs :: _ =>
        let bound := (names lhs).filter fun n => !["def", "private", "let", "mut"].contains n
        let head := (names rhs).headD ""
        if ["Diag", "Core.Diag", "LeanTex.Core.Diag"].contains head then bound
        else if (names lhs).headD "" == "let" &&
            ["Diag.of", "Core.Diag.of", "LeanTex.Core.Diag.of"].contains head then bound
        else []
      | _ => []
  let projects (diags : List String) (s : String) := (names s).any fun n =>
    ([".message", ".code", ".help", ".severity", ".span", ".subject", ".sites",
      ".trigger", ".recovery"].any fun f =>
        (n.endsWith f || containsSub n (f ++ ".")) && n.length > f.length) ||
      diags.any (fun d => n == d ++ ".output" || n.startsWith (d ++ ".output."))
  let mut owner := ""
  let mut diags : List String := []
  let mut depth := 0
  let mut inStr := false
  let mut esc := false
  let mut out := #[]
  for (line, row) in lines.zipIdx do
    let cs := line.toList.toArray
    let mut code := ""
    let mut text := ""
    let mut i := 0
    while i < cs.size do
      let c := cs[i]?.getD ' '
      let next := cs[i + 1]?.getD ' '
      if depth > 0 then
        if c == '/' && next == '-' then
          depth := depth + 1
          i := i + 2
        else if c == '-' && next == '/' then
          depth := depth - 1
          i := i + 2
        else i := i + 1
      else if inStr then
        if esc then
          esc := false
          text := text.push c
        else if c == '\\' then esc := true
        else if c == '"' then inStr := false
        else text := text.push c
        i := i + 1
      else if c == '-' && next == '-' then break
      else if c == '/' && next == '-' then
        depth := 1
        code := code.push ' '
        i := i + 2
      else if c == '"' then
        inStr := true
        code := code.push ' '
        i := i + 1
      -- A quote character literal must not open a multiline string.
      else if c == '\'' && cs[i + 2]? == some '\'' then
        code := code.push ' '
        i := i + 3
      else
        code := code.push c
        i := i + 1
    if code.trimAscii.isEmpty && text.trimAscii.isEmpty then continue
    if let some n := topLevelDefName code then
      owner := n
      diags := []
    diags := diags ++ diagBindings code
    let ns := names code
    let driver := file == "LeanTex/Cli/Driver.lean"
    let writer := driver && writers.contains owner
    let sink := driver && owner == "Ui.diag"
    let terminal := ns.any fun n =>
      ["IO.print", "IO.println", "IO.eprint", "IO.eprintln",
        "print", "println", "eprint", "eprintln", "putStr", "putStrLn"].contains n ||
      n.endsWith ".putStr" || n.endsWith ".putStrLn"
    let rendered := ns.any fun n =>
      n == "Render.human" || n == "Render.porcelainDiag" ||
      n.endsWith ".Render.human" || n.endsWith ".Render.porcelainDiag"
    let stream := ns.any fun n =>
      ["IO.getStdout", "IO.getStderr", "getStdout", "getStderr"].contains n ||
      n.endsWith ".outStream" || n.endsWith ".errStream"
    if (terminal && !writer) || (stream && !writer && !(driver && owner == "Ui.mk'")) then
      out := out.push (row + 1, "terminal write or stream outside a UI/command handler")
    if rendered && !sink && file != "LeanTex/Cli/Render.lean" then
      out := out.push (row + 1, "diagnostic rendered before the typed sink")
    if terminal && sink && !rendered then
      out := out.push (row + 1, "typed sink must print a Render diagnostic directly")
    -- Interpolation fields are inside the masked string, so inspect their
    -- projections separately from literal text such as a documented IO call.
    let interpolated := containsSub code "s!" &&
      ((text.splitOn "{").drop 1).any (fun p => projects diags ((p.splitOn "}").headD ""))
    if ((writer && !sink) || terminal) && (projects diags code || interpolated) then
      out := out.push (row + 1, "diagnostic fields printed outside Render")
    let headline := text.trimAscii.toString.toLower
    let headerAfter (label : String) (marks : List String) :=
      headline.startsWith label &&
        marks.any (fun mark => (headline.drop label.length).trimAsciiStart.toString.startsWith mark)
    -- Diagnostic icons lead into a code bracket; plain ✔/✖ run summaries
    -- remain legal. Word labels also cover the legacy headline spellings.
    if writer && (
        ["warning", "error", "note", "info"].any (fun word => headerAfter word [":", "[", "- "]) ||
        ["⚠", "✖", "ℹ"].any (fun icon => headerAfter icon ["["])) then
      out := out.push (row + 1, "hand-written diagnostic headline")
  return out

/-- The selftests a tier producer frames by hand: the top-level definitions
returning `IO UInt32` that its `--selftest` reaches — named on a line that
calls `tierMain` or dispatches `"--selftest"`, or named `…selftest` — whose
body is not a `tierSelftest` application. A file that calls no `tierMain`
is no producer. The rule reads which definition is the selftest and how it
is built, never how a failure list is spelled: matching one spelling, the
`List` ref, passed an `Array` ref, a mutable array and every frame under
another name. -/
def selfFramed (lines : Array String) : Array String := Id.run do
  let code := lines.map fun l => stripLineComment (stripStrings l)
  unless code.any (containsSub · "tierMain") do return #[]
  let mut reached : Array String := #[]
  for (l, c) in lines.zip code do
    let args := " ".intercalate ((c.splitOn "tierMain").drop 1)
    let target := " ".intercalate (((l.splitOn "\"--selftest\"").drop 1).map
      (stripLineComment ∘ stripStrings))
    for w in (args ++ " " ++ target).split (fun ch => !(isWordChar ch || ch == '.')) do
      reached := reached.push ((w.toString.splitOn ".").getLastD "")
  let mut out : Array String := #[]
  for i in [0:code.size] do
    let c := code[i]?.getD ""
    let some full := topLevelDefName (lines[i]?.getD "") | continue
    let n := (full.splitOn ".").getLastD full
    let parts := c.splitOn ":="
    unless containsSub (parts.headD "") ": IO UInt32" do continue
    unless n.endsWith "selftest" || n.endsWith "Selftest" || reached.contains n do continue
    let rest := (":=".intercalate (parts.drop 1)).trimAscii.toString
    let body := if !rest.isEmpty then rest else
      (((code.extract (i + 1) code.size).find? (!·.trimAscii.isEmpty)).getD "").trimAscii.toString
    unless body.startsWith "tierSelftest " || body.startsWith "Scoreboard.tierSelftest " do
      out := out.push n
  return out

/-- Every case a gate predicate must catch and every legal spelling it must
pass, run by `lean --run scripts/precommit.lean --selftest` from `lake test`.
Positive cases are the shapes whose escape prompted a gate change; negative
cases are lines of this tree. A gate that does not catch the shape it
commemorates grants false confidence, so a gate change lands with both. -/
def selftest : IO UInt32 := do
  let fails ← IO.mkRef ([] : List String)
  let expect (name : String) (p : String → Bool) (cases : List (String × Bool)) : IO Unit := do
    for (line, want) in cases do
      if p line != want then
        fails.modify (s!"{name} {if want then "missed" else "fired on"}: {line}" :: ·)

  expect "goldenSource" goldenSource [
    ("Tests/Census.lean", true),
    ("testdata/corpus/md-table.md", true),
    ("testdata/corpus/tables.tex", true),
    ("testdata/golden/md-table.txt", false),
    ("testdata/typeset/md-report.md", false)]

  expect "computedDemote" computedDemote [
    -- the proxy defect's spelling: a demotion decided by a predicate over
    -- the file and the name, at every site that carries it
    ("        (demote := styInternal (← get).file name)", true),
    ("      (demote := Compat.styInternal ctx.file name)", true),
    ("        let d := { d with x := 1 } -- demote := f x", false),
    -- a written decision about this loss stays legal, as does the door's own
    -- signature default and a mention in a comment or string
    ("  say .W0301 msg pos (demote := true)", false),
    ("  sayOnce key .W0357 msg pos (demote := false)", false),
    ("    (demote : Bool := false) (subject : Option String := none) : M Unit :=", false),
    ("  -- demote := styInternal file name would need a pin", false),
    ("  say s!\"a message naming demote := f x\" pos", false)]

  expect "premisePin" (fun l => (premisePin l).isSome) [
    -- the two legal spellings
    ("  -- premise: pictureKeyGateChecks — the two builds ship the same bytes", true),
    ("  -- premise: none — nothing falsifies this yet; recorded as debt", true),
    -- a marker that names nothing is not a marker
    ("  -- premise: pictureKeyGateChecks", false),
    ("  -- premise: none", false),
    ("  -- premise:", false),
    -- an ordinary comment carries no marker
    ("  -- the boundary tool reads what the subset refused", false)]

  -- the pin and reason a marker yields, refusal spelling included
  if premisePin "  -- premise: fooChecks — because bar" != some (some "fooChecks", "because bar") then
    fails.modify ("premisePin did not read the pin and reason" :: ·)
  if premisePin "  -- premise: none — nothing pins it" != some (none, "nothing pins it") then
    fails.modify ("premisePin did not read the refusal" :: ·)

  -- pinResolves: a theorem the build checks, or a check block the suite
  -- runs — defined AND invoked. A block the suite never calls pins nothing.
  let treeSrc := "theorem footBand_projects : True := trivial"
  let testSrc := "def liveChecks (ref : IO.Ref (List String)) : IO Unit := do\n  liveChecks ref\ndef deadChecks : IO Unit := pure ()"
  let pinCases : List (String × Bool) := [
    ("footBand_projects", true),
    ("liveChecks", true),
    ("deadChecks", false),
    ("neverWrittenChecks", false)]
  for (pin, want) in pinCases do
    if pinResolves treeSrc testSrc ["liveChecks", "deadChecks"] pin != want then
      fails.modify (s!"pinResolves {pin}: want {want}" :: ·)

  -- condSpan: the condition read continues past the line, which is how the
  -- W0301 boundary gate's `ctx.` read (on its continuation line) is seen at
  -- all; a line opening no conditional yields nothing.
  let twoLine : Array String :=
    #["    if Compat.nativeSetCtrls.contains name ||",
      "        (s.ctx.picTool.isSome && Compat.boundaryCtrls.contains name) then",
      "      return s"]
  match condSpan twoLine 0 with
  | some (cond, j) =>
    if !readsSetup cond || j != 1 then
      fails.modify ("condSpan did not reach the continuation line's setup read" :: ·)
  | none => fails.modify ("condSpan missed a two-line condition" :: ·)
  if (condSpan #["  let x := 3"] 0).isSome then
    fails.modify ("condSpan fired on a plain let" :: ·)

  -- premiseSite, the gate's core: the three shapes that rotted must fire,
  -- and the healthy spellings of this tree must not.
  let siteCase (name : String) (src : List String) (want : Option PremiseKind) : IO Unit := do
    if premiseSite src.toArray 0 != want then
      fails.modify (s!"premiseSite {name}" :: ·)
  -- the picture gate as it stands: a diagnostic named only under a
  -- configuration the drawing does not depend on
  siteCase "configuration-gated diagnostic"
    ["  if ctx.picTool.isSome && pic.shapes.isEmpty then",
     "    warnOnce ctx key .N0023 msg pos",
     "    return blocks"] (some .gate)
  -- the silencer: quiet under the configuration, named below it
  siteCase "configuration-gated silence"
    ["    if Compat.nativeSetCtrls.contains name ||",
     "        (s.ctx.picTool.isSome && Compat.boundaryCtrls.contains name) then",
     "      return s",
     "    warnOnce s.ctx (\"ctrl:\" ++ name) .W0301 msg pos"] (some .silence)
  -- the computed demotion, on its own line
  siteCase "computed demotion"
    ["      (demote := Compat.styInternal ctx.file name)"] (some .demote)
  -- the healthy shape, and the one the naive version of this gate fired on
  -- 212 times: the condition IS the loss, so nothing is claimed elsewhere
  siteCase "the condition is the loss"
    ["  unless dropped.isEmpty do",
     "    say .W0104 s!\"dropped {dropped}\" pos"] none
  siteCase "a content condition naming its own loss"
    ["  if b.kind.isNone && refFormNeedsKind form then",
     "    diag ctx .W0380 msg (some rpos)"] none
  -- a configuration read with no diagnostic either way is not a premise
  siteCase "configuration read, no loss named"
    ["  if ctx.slides then",
     "    blocks := blocks.push (.frame title inner)"] none
  -- a quiet configuration branch with nothing named below claims nothing
  siteCase "configuration-gated return, no loss below"
    ["  if ctx.literalText then",
     "    return st",
     "  pure (flatten st)"] none
  -- STATED BLIND SPOT, pinned so closing it is a deliberate change: the
  -- defect's own historical spelling read a local bound from the
  -- declarations two lines above, and a line scanner cannot see through the
  -- binding. Tainting locals was measured at 30% precision (ten sites, three
  -- real), so the vocabulary stays the direct reads; both of that gate's
  -- sites today read `ctx.` and are caught.
  siteCase "a knob hoisted into a local is not seen"
    ["  if picTool0.isNone then",
     "    say .W0334 s!\"picture key '{k}' is not read\" pos"] none

  expect "scaleStepRespell" scaleStepRespell [

    -- the drift shapes the collapse deleted, default divergence included
    ("  let markSize := around * ((Ir.sizeScale.lookup \"scriptsize\").getD 700) / 1000", true),
    ("  milliFactor ((Ir.sizeScale.lookup name).getD 1000) ++ unit", true),
    -- an Option-shaped match, the shared def, comments and strings stay legal
    ("  | .size n => match Ir.sizeScale.lookup n with", false),
    ("  let s := Ir.scaleStep base n", false),
    ("  -- sizeScale.lookup … .getD quoted in a comment", false),
    ("  say s!\"a message naming sizeScale.lookup and .getD\"", false)]

  -- The gate applies to both judges: the contract module never imports the
  -- writer any more than the census does.
  for f in judgeFiles do
    unless gates.any fun g => g.applies f && g.flag "import LeanTex.Core.Pdf" do
      fails.modify (s!"writerReach gate does not cover {f}" :: ·)

  expect "writerReach" writerReach [
    ("import LeanTex.Core.Pdf", true),
    ("open LeanTex.Core.Pdf in", true),
    ("  let s := Pdf.write geom fs pages", true),
    ("  let s := LeanTex.Core.Pdf.keepFaces fs pages", true),
    -- the reader is a different module; comments and prose stay legal
    ("import LeanTex.Core.PdfRead", false),
    ("open LeanTex.Core.PdfRead", false),
    ("  let es ← PdfRead.objects b", false),
    ("  -- Pdf.write spells its dictionaries as strings", false)]

  expect "bareStateMutation" bareStateMutation [
    -- the mutations the door rule routes: statement-initial modify/set
    ("  modify fun st => { st with themed := true }", true),
    ("    modify fun st => { st with file := f }", true),
    ("      set { st with diags := st.diags.push d }", true),
    -- the doors' own calls, comments, strings, docstring prose, and
    -- word-boundary neighbours stay legal
    ("  write fun st => { st with themed := true }", false),
    ("  -- modify in a comment is prose", false),
    ("`palatino` set rm/sf/tt whole, `helvet` one slot,", false),
    ("  say .W0104 s!\"'x' would set the page\" pos", false),
    ("  let offset := 3", false),
    ("  (\"setspace\", 0)", false),
    ("  setlist := true", false)]

  expect "splitOnIdiom" splitOnIdiom [
    -- the copies the audit deleted, both count spellings and the
    -- fixed-page curried variant
    ("  let has (hay needle : String) : Bool := (hay.splitOn needle).length > 1", true),
    ("  let has (page s : String) : Bool := (page.splitOn s).length ≥ 2", true),
    ("  let has (n : String) : Bool := (page.splitOn n).length ≥ 2", true),
    -- an inline assertion is a use, not a helper copy; the shared binding,
    -- a splitOn let without the count compare, an exactly-once count, and
    -- a comment stay legal
    ("    ((mutedPage.splitOn \"u-muted\").length == 2)", false),
    ("  let has := hasStr page", false),
    ("  let parts := (l.splitOn \"+\")", false),
    ("  let once (s : String) : Bool := (page.splitOn s).length == 2", false),
    ("  -- let has (hay needle : String) : Bool := (hay.splitOn needle).length > 1", false)]

  -- the seal/unseal mirror: pairs balance as multisets, order and grouping
  -- free; comments are data; the residue names each side
  let smCase (name : String) (src : List String) (want : List String × List String) : IO Unit := do
    if sealMismatch src.toArray != want then
      fails.modify (s!"sealMismatch {name}" :: ·)
  smCase "mirrored pair" ["seal Foo Bar", "unseal Bar Foo"] ([], [])
  smCase "two knots, one name each" ["seal Foo", "unseal Foo", "seal Foo", "unseal Foo"] ([], [])
  smCase "sealed but never unsealed" ["seal Foo Bar", "unseal Foo"] (["Bar"], [])
  smCase "unsealed but never sealed" ["unseal Foo"] ([], ["Foo"])
  smCase "twice sealed, once unsealed" ["seal Foo", "seal Foo", "unseal Foo"] (["Foo"], [])
  smCase "a comment is data" ["-- seal Foo"] ([], [])

  expect "topLevelDefName" (fun l => (topLevelDefName l).isSome) [
    -- the Support-rule gate: only a top-level def counts
    ("def deckBuilder (body : String) : String := body", true),
    ("private def helper2 : IO Unit := pure ()", true),
    ("public def exposed : IO Unit := pure ()", true),
    ("@[inline] public def exposed : IO Unit := pure ()", true),
    ("@[simp, inline] private def helper := 1", true),
    ("noncomputable public def choice := Classical.choose h", true),
    ("public unsafe def unsafeHelper := 1", true),
    ("  def nested := 1", false),
    ("-- def commented := 1", false),
    ("definition prose speaking of def forms", false),
    ("theorem def_named_thing : True := trivial", false)]

  -- The whole declared name, dots included. Truncated at the dot, two files
  -- declaring different members of one namespace read as one helper declared
  -- twice, and the Support-rule gate names a helper nobody wrote.
  expect "topLevelDefName keeps the namespace"
    (fun l => topLevelDefName l == some "ArtRun.isArtifact") [
    ("def ArtRun.isArtifact (r : ArtRun) : Bool := r.marks.any ArtMark.isArtifact", true),
    ("@[inline] public def ArtRun.isArtifact (r : ArtRun) : Bool := true", true),
    ("def ArtRun (r : ArtRun) : Bool := true", false)]
  expect "topLevelDefName keeps primes" (fun l => topLevelDefName l == some "Ui.mk'") [
    ("public def Ui.mk' := 1", true), ("def Ui.mk := 1", false)]
  let scopedNames := scopedDefNames #[
    "namespace First", "public def checks := 1", "section Local",
    "@[inline] public def checks' := 2", "end Local", "namespace Nested",
    "def checks := 3", "def _root_.Root.checks := 4", "end Nested", "end First",
    "namespace Second", "private def checks := 5", "end Second", "def checks := 6"]
  unless scopedNames == #["First.checks", "First.checks'", "First.Nested.checks",
      "Root.checks", "Second.checks", "checks"] do
    fails.modify ("scopedDefNames: namespace or section ownership was lost" :: ·)
  unless scopedDefNames #["namespace First", "def checks := 1", "end First",
      "namespace First", "public def checks := 2", "end First"] ==
      #["First.checks", "First.checks"] do
    fails.modify ("scopedDefNames: reopening a namespace hid a duplicate" :: ·)

  expect "quadraticPrepend" quadraticPrepend [
    -- the walks this tree has produced, all of which must fire
    ("  | x :: rest => inlineNode cfg x ++ inlineNodes cfg rest", true),
    ("  | x :: rest => plainTextOne x ++ plainTextList rest", true),
    ("  | x :: rest => dumpInline ind x ++ dumpInlineList ind rest", true),
    ("  | b :: rest => dumpBlock ind b ++ dumpBlockList ind rest", true),
    ("    s!\"{ind}item\\n\" ++ dumpBlocks (ind ++ \"  \") item ++ dumpItems ind rest", true),
    ("    | c :: rest => escapeCharText c ++ go rest", true),
    ("    | c :: rest => escapeCharAttr c ++ go rest", true),
    ("  | k :: rest, indent => render k indent ++ renderList rest indent", true),
    ("  | k :: rest => inlineRender k ++ inlineRenderList rest", true),
    ("  | r :: rest => rawSrcOne r ++ rawSrcList rest", true),
    ("  | b :: rest => #[blockNode cfg b] ++ blockNodes cfg rest", true),
    ("  | x :: rest => #[x] ++ Compat.rewriteList rest", true),
    -- legal spellings from this tree that must stay legal
    ("  | x :: rest => inlineNodes cfg (acc ++ inlineNode cfg x) rest", false),
    ("  | b :: rest => blockNodes cfg (acc.push (blockNode cfg b)) rest", false),
    ("  base ++ plus ++ minus", false),
    ("      | other => s := s ++ rawSrcOne other", false),
    ("        | some i => out.extract 0 i ++ running ++ out.extract i out.size", false),
    ("    s!\"{ind}styled {st.label}\\n\" ++ dumpInlines (ind ++ \"  \") body", false),
    ("        chosen := chosen ++ [b]", false),
    ("  | x :: rest => #[x] ++ rest", false)]

  expect "classNameCompare" classNameCompare [
    -- the spelling that compiles past the inductive, wherever it stands
    ("  if doc.docClass.name == \"article\" then", true),
    ("    (d.docClass.name == cls)", true),
    -- legal spellings: a match, a diagnostic quoting the name, prose
    ("  match doc.docClass with", false),
    ("    say s!\"class {doc.docClass.name} has no chapter pages\"", false),
    ("  -- a comment naming docClass.name == article does not count", false),
    ("    (\"docClass.name == inside a string\", true),", false)]

  expect "nativePackages parse" (fun s => (nativePackagesOf s).toList
      == ["geometry", "natbib"]) [
    -- the list block yields exactly its quoted names, quotes elsewhere
    -- ignored, the scan closed at the bracket
    ("def other : List String := [\"nope\"]\n" ++
     "def nativePackages : List String :=\n  [\"geometry\",\n   \"natbib\"]\n" ++
     "def after : String := \"also-not-a-package\"", true)]

  expect "conflictMarker" conflictMarker [
    -- the shapes git writes, all of which must fire
    (mkOurs ++ " HEAD", true),
    (mkTheirs ++ " theirs", true),
    (mkBase ++ " merged common ancestors", true),
    (mkOurs, true),
    (mkBase, true),
    -- near-misses that must pass: the setext rule / comment banner,
    -- an eight-run decorative banner, a six-run, mid-line, indented
    ("=======", false),
    (mkOurs ++ "<", false),
    ("<<<" ++ "<<<", false),
    ("a " ++ mkTheirs, false),
    ("  " ++ mkOurs ++ " HEAD", false),
    (mkOurs ++ "quoted", false)]

  -- the diff walker: staged content only, file and line attributed
  let d := "+++ b/PLAN.md\n@@ -3,0 +4,3 @@\n+prose\n+" ++ mkOurs ++ " HEAD\n+more"
  if conflictMarkers d != #[("PLAN.md", 5, mkOurs ++ " HEAD")] then
    fails.modify ("conflictMarkers missed or misattributed the PLAN.md case" :: ·)
  -- the escape itself: a diff3 base marker in a hand-resolved Markdown log,
  -- beside its two siblings, under a setext underline that must stay legal
  let base := mkBase ++ " parent of 0123abc (Land the slice)"
  let md := "+++ b/docs/log.md\n@@ -0,0 +1,7 @@\n+Title\n+=======\n+" ++ mkOurs ++ " HEAD\n+ours\n+"
    ++ base ++ "\n+theirs\n+" ++ mkTheirs ++ " wt/slice"
  if conflictMarkers md != #[("docs/log.md", 3, mkOurs ++ " HEAD"), ("docs/log.md", 5, base),
      ("docs/log.md", 7, mkTheirs ++ " wt/slice")] then
    fails.modify ("conflictMarkers on the diff3 Markdown case: wrong hits or a setext fire" :: ·)

  expect "plainPath" plainPath [
    -- the tree's own spellings
    ("testdata/corpus/a-b_c.tex", true),
    ("scripts/hooks/pre-commit", true),
    ("LeanTex/Core/Oklab.lean", true),
    -- the debris alphabet: a space, the escape itself (quote, comma, plus),
    -- an `=`, non-ASCII, a newline, the empty name
    ("testdata/corpus/a b.tex", false),
    ("arnings name the native spelling\",+12p", false),
    ("notes=draft.md", false),
    ("testdata/corpus/r\u00e9sum\u00e9.tex", false),
    ("a\nb.tex", false),
    ("", false)]
  -- the numstat walker: an empty file fires, a mangled name fires, a
  -- content-bearing plain path and a binary pass
  let ns := "0\t0\tempty.txt\x00" ++ "12\t0\ttestdata/corpus/a-b_c.tex\x00"
    ++ "0\t0\ta b\x00" ++ "-\t-\ttestdata/corpus/pic.png\x00"
  if addedPathFaults ns != #[("empty.txt", "empty file"),
      ("a b", "characters outside [A-Za-z0-9._/-]"), ("a b", "empty file")] then
    fails.modify ("addedPathFaults: wrong hits on the empty/mangled/plain/binary case" :: ·)
  -- the case walker: the collision that prompted it, a directory's case, and
  -- two paths that merely share a stem. Pairs come out ordered by path.
  if caseCollisions #["scripts/land.lean", "scripts/Gate.lean", "scripts/Land.lean"]
      != #[("scripts/Land.lean", "scripts/land.lean")] then
    fails.modify ("caseCollisions: missed the module-name collision" :: ·)
  if caseCollisions #["a/b.lean", "A/b.lean"] != #[("A", "a"), ("A/b.lean", "a/b.lean")] then
    fails.modify ("caseCollisions: a directory's case does not count" :: ·)
  if caseCollisions #["Tests/Parser.lean", "tests/corpus/probe.tex"]
      != #[("Tests", "tests")] then
    fails.modify ("caseCollisions: different children conceal a directory collision" :: ·)
  if !(caseCollisions #["scripts/land.lean", "scripts/LandCore.lean", "scripts/lands.lean"]).isEmpty then
    fails.modify ("caseCollisions: fired on distinct names" :: ·)

  -- The home-directory rule. Each positive is a spelling a leak takes; each
  -- negative is a line this tree carries or a URL that merely has a `home`
  -- segment. The strings are composed from the same pieces the rule reads.
  expect "homePaths" (fun l => !(homePaths l).isEmpty) [
    (dirLocalHome ++ "alice/notes.md", true),
    ("see `" ++ dirLocalHome ++ "alice`", true),
    ("cp x " ++ dirHome ++ "bob/tmp", true),
    ("file://" ++ dirHome ++ "bob/x.pdf", true),
    ("host:" ++ dirHome ++ "bob", true),
    ("\"" ++ dirUsers ++ "carol/Library\"", true),
    (dirLocalHome ++ "linuxbrew/bin", true),
    (dirHome ++ "linuxbrew2/bin", true),
    ("export LEAN_CC=" ++ dirHome ++ "linuxbrew/.linuxbrew/bin/clang", false),
    ("https://example.org" ++ dirHome ++ "index.html", false),
    ("see https://example.org/docs" ++ dirUsers ++ "guide", false),
    (dirHome ++ "<user>/x and " ++ dirHome ++ "$USER/x", false),
    ("a path relative to the repository: testdata/corpus/fonts", false)]
  if homePaths (dirLocalHome ++ "alice/x " ++ dirHome ++ "linuxbrew " ++ dirUsers ++ "bob")
      != #[dirLocalHome ++ "alice", dirUsers ++ "bob"] then
    fails.modify ("homePaths: wrong hits on a mixed line" :: ·)
  let hd := "diff --git a/PLAN.md b/PLAN.md\n+++ b/PLAN.md\n@@ -9,0 +10,2 @@\n+ok\n+in "
    ++ dirLocalHome ++ "alice/w\n"
  if homePathHits (addedLines hd) != #[("PLAN.md", 11, dirLocalHome ++ "alice")] then
    fails.modify ("homePathHits: wrong hit from a staged diff" :: ·)
  -- An added line whose own text begins `++ ` prints as `+++ …` inside the
  -- hunk; the path after it, and the next file's, must still be read.
  let hp := "diff --git a/x.md b/x.md\n--- a/x.md\n+++ b/x.md\n@@ -0,0 +1,2 @@\n+++ counter\n+see "
    ++ dirLocalHome ++ "bob/x\ndiff --git a/y.md b/y.md\n--- /dev/null\n+++ b/y.md\n@@ -0,0 +1 @@\n+"
    ++ dirHome ++ "carol/z\n"
  if homePathHits (addedLines hp)
      != #[("x.md", 2, dirLocalHome ++ "bob"), ("y.md", 1, dirHome ++ "carol")] then
    fails.modify ("addedLines: an added line beginning ++ read as a file header" :: ·)
  let gr := "notes.md\x003\x00" ++ dirHome ++ "dave/x\n" ++ "AGENTS.md\x0017\x00export LEAN_CC="
    ++ dirHome ++ "linuxbrew/.linuxbrew/bin/clang\n"
  if homePathHits (grepRecords gr) != #[("notes.md", 3, dirHome ++ "dave")] then
    fails.modify ("homePathHits: wrong hit from a tree grep" :: ·)

  expect "bannedWord" (bannedWord kwPartial) [
    -- a declaration must still fire, wherever it stands on the line
    ("+" ++ kwPartial ++ " def foo : Nat := 0", true),
    ("+  " ++ kwPartial ++ " def go (l : List Nat) : Nat := go l", true),
    -- the escape that prompted the stripper: a command-name table entry
    ("+   (\"" ++ kwPartial ++ "\", .ord, '𝜕'),", false),
    ("+    say s!\"a message naming " ++ kwPartial ++ " in prose\"", false),
    -- Both gates share the same treatment of code and comments.
    ("+  -- a comment naming " ++ kwPartial ++ " does not count", false),
    -- word-delimiting still holds
    ("+  let " ++ kwPartial ++ "Sums := 3", false)]

  expect "ctorDefault" ctorDefault [
    -- a field default, with and without the lambda that evaded the old check
    ("+  | run (label : String := \"unnamed\") : Cmd", true),
    ("+  | mk (a : Nat) (f : Nat → Nat := fun _ => 0) : T", true),
    -- `|` lines that carry a `:=` without being a field default
    ("+  | `.run a b c` := what the pattern matched | the whole suite green |", false),
    ("+  | x => go (n := 3) rest", false),
    ("+  | x => { s with field := v }", false),
    ("+  | .text s => s", false)]

  -- `addedByFile` hands these two checks their lines with the `+` already
  -- stripped, unlike the whole-diff checks above.
  expect "ioInCore" ioInCore [
    ("def scan (roots : List String) : IO (Array Face) := do", true),
    ("    let bytes ← IO.FS.readBinFile path", true),
    -- a stated blind spot, pinned so a change to it is a deliberate one:
    -- a block comment's continuation line still looks like code
    ("continuation line of a block comment naming IO", true),
    -- the fix: `--` comments no longer trip the check
    ("  -- files and fonts surface as request values, never IO here", false),
    ("/-- Effects as data: the IO happens in Main.lean. -/", false),
    ("  let names := [\"IO\", \"Char\"]", false),
    ("  let label := \"quoted \\\"IO\\\"\"", false),
    ("  let label := \"--\"; let bytes ← IO.FS.readBinFile path", true),
    ("  let label := \"IO\"; IO.println label", true),
    ("  let priority := ioPriority.toNat", false),
    ("def ask : BaseIO Unit := pure ()", true),
    ("def go : EIO String Unit := pure ()", true),
    ("  let x := unsafeBaseIO (pure 1)", true),
    ("  let tag := baseIOTag", false)]

  expect "surfaceReach" surfaceReach [
    ("import LeanTex.Core.Parse", true),
    ("open LeanTex.Core.Parse in", true),
    ("open Elab", true),
    ("  let opt := Parse.scanOpt args i", true),
    ("    LeanTex.Core.Compat.rewrite doc", true),
    ("import LeanTex.Core.Ir", false),
    ("  -- a backend never calls Parse.scanOpt; the IR carries it", false),
    ("  let reparse := myParse.run s", false),
    ("  openTag := elem tag attrs kids", false)]

  expect "tagStringEmit" tagStringEmit [
    -- the renderer's own shape: outside Html.lean it must fire, spaced or not
    ("    let open' := \"<\" " ++ patAppend ++ " tag " ++ patAppend ++ " attrString attrs", true),
    ("  out := out " ++ patAppend ++ " \"<\"" ++ patAppend ++ "tag", true),
    -- angle-bracket text that is not the banned shape stays legal:
    -- a multi-char literal (stated blind spot), an escaper arm, a CMap
    -- interpolation, and the shape quoted in a comment
    ("  \"<!DOCTYPE html>\\n\" " ++ patAppend, false),
    ("  if c == '<' then out := out " ++ patAppend ++ " \"&lt;\"", false),
    ("  s := s " ++ patAppend ++ " s!\"<{hex4 g}> <{utf16Hex c}>\\n\"", false),
    ("  -- writing \"<\" " ++ patAppend ++ " tag is banned here", false)]

  expect "fontScanInTest" fontScanInTest [
    -- the driver's spelling, which in a test is the hermeticity break
    ("  let faces ← FontDiscovery.scan (cfg.fontDirs.toList ++ (← texFontDirs))", true),
    ("  let faces ← FontDiscovery.scan", true),
    -- the hermetic spelling, a comment, and a string naming the call
    ("  let shipped ← FontDiscovery.scanRoots [testFonts]", false),
    ("  -- FontDiscovery.scan here would break hermeticity", false),
    ("  t \"a message naming FontDiscovery.scan stays data\" true", false)]

  expect "irDumpUnmarked" irDumpUnmarked [
    -- dump and its walk companions, unmarked: all must fire
    ("    let out := Ir.dump doc diags", true),
    ("        ((Ir.dumpBlocks \"\" nbody).splitOn \"never shown\").length == 2", true),
    -- the stated-tier escape, a comment, and a string naming the call
    ("    let out := Ir.dump doc diags " ++ irTierMark ++ " goldens witness elaboration", false),
    ("  -- Ir.dump is rejected in tests without a tier", false),
    ("  t \"a message naming Ir.dump stays data\" true", false)]

  expect "heartbeatRaise" heartbeatRaise [
    -- the raise shapes, standalone and scoped
    ("set_option " ++ kwMaxHeartbeats ++ " 400000", true),
    ("  set_option " ++ kwMaxHeartbeats ++ " 1000000 in", true),
    ("set_option " ++ kwMaxHeartbeats ++ " 0 in", true),
    ("  withOptions (" ++ kwMaxHeartbeats ++ ".set · 2000)", true),
    -- another heartbeat option, under the bare default and over its own
    ("set_option synthInstance." ++ kwMaxHeartbeats ++ " 100000 in", true),
    ("set_option " ++ kwMaxHeartbeats ++ " 2000 in set_option synthInstance." ++
      kwMaxHeartbeats ++ " 100000 in", true),
    -- a literal bound under the default holds a cost: no raise
    ("set_option " ++ kwMaxHeartbeats ++ " 2000 in", false),
    -- a comment, a string, and the other budget option stay legal
    ("-- " ++ kwMaxHeartbeats ++ ": zero sites in the tree", false),
    ("  say s!\"raise " ++ kwMaxHeartbeats ++ "\"", false),
    ("set_option maxRecDepth 8192", false)]

  expect "wildcardThrough" wildcardThrough [
    -- the frozen pass-through shapes, all of which must fire
    ("  | _ => out", true),
    ("  | other => other", true),
    ("  | x => x", true),
    -- constructor matches, predicate answers, and multi-token arms stay legal
    ("  | none => acc", false),
    ("  | nil => simp [textLeavesTableCells]", false),
    ("  | _ => false", false),
    ("  | _ => none", false),
    ("  | _ => break", false),
    ("  | .text s => s", false),
    ("  | other => cur := cur.push other", false),
    ("  | _ => 1", false)]

  -- bangCount: strings and comments are data, code is counted
  if bangCount #["let x := xs[i]!", "-- xs[i]! in a comment",
      "say \"xs[i]! quoted\"", "ys[j]! + zs[k]!"] != 3 then
    fails.modify ("bangCount miscounted the mixed sample" :: ·)

  expect "identityArm" identityArm [
    -- the wildcard drops the walk audit found, all of which must fire
    ("  | other => other", true),
    ("  | x => x", true),
    -- explicit arms and non-arm lines that must stay legal
    ("  | .text s => .text s", false),
    ("  | .verbatim s => .verbatim s", false),
    ("  | .box .. | .pen .. => it", false),
    ("  | some x => x", false),
    ("  | [] => []", false),
    ("  | x :: rest => fillOne content x :: fillList content rest", false),
    ("| a docstring table row | with cells |", false),
    ("  -- | other => other, quoted in a comment", false)]

  expect "wildcardNumeral" wildcardNumeral [
    ("  | _ => 1", true),
    ("  | other => 1", true),
    -- a wildcard answering a non-numeral stays legal (a Nat scrutinee
    -- cannot spell every case), as does an explicit arm answering one
    ("  | _ => \"mono\"", false),
    ("  | _ => geom.fontSize", false),
    ("  | .verbatim _ => 1", false),
    ("  | [] => 1", false)]

  expect "dimLiteral" dimLiteral [
    -- the unsourced design values this tree has carried
    ("  | 1 => pt 14", true),
    ("        fun g => (a.resolve g).width).getD (pt 1)", true),
    ("  vmargin := Dim.mm 9", true),
    ("  if w > inch 1 then", true),
    ("  let floor := Dim.mm100 140", true),
    -- sourced or token-borne spellings that must stay legal
    ("  pageW : Sp := pt 612 -- US letter, the class default", false),
    ("  let w := scaledAt size font (font.advance c)", false),
    ("  let s := v.toPtString", false),
    ("  let g := (a.resolve tok).width", false),
    ("  let mmNames := [\"mm\", \"cm\"]", false)]

  -- The same proof rule applies to every maintained source path.
  expect "unfinished proof in every source path" (fun f =>
    gates.any fun r => r.applies f && r.flag ("theorem unfinished : True := by " ++ kwSorry)) [
    ("LeanTex/Core/Probe.lean", true),
    ("Tests/Probe.lean", true),
    ("scripts/probe.lean", true),
    ("ExtraProofs.lean", true),
    ("ExtraProofs/Probe.lean", true)]

  expect "walkEntry" (fun l => (walkEntry l).isSome) [
    -- the shapes the tree carries today: entries in, companions and
    -- non-walks out
    ("def dimBlocks (cover : Cover) (k : Nat) (xs : Array Block) : Array Block :=", true),
    ("def unwrapItemSteps (xs : Array Block) : Array Block :=", true),
    ("def keepFor (t : String) (xs : Array Block) : Array Block :=", true),
    ("def substPage (n total : Nat) (xs : Array Inline) : Array Inline :=", true),
    ("def fillTemplate (template content : Array Inline) : Array Inline :=", true),
    -- a body on the definition line does not evade the scan
    ("def sneakyWalk (xs : Array Block) : Array Block := xs", true),
    ("public def visibleWalk (xs : Array Block) : Array Block := xs", true),
    ("@[inline] public def visibleWalk (xs : Array Inline) : Array Inline := xs", true),
    ("noncomputable public def visibleWalk (xs : Array Block) : Array Block := xs", true),
    ("@[simp, inline] public def visibleWalk (xs : Array Inline) : Array Inline := xs", true),
    ("private def helperWalk (xs : Array Block) : Array Block := xs", false),
    ("@[inline] private def helperWalk (xs : Array Block) : Array Block := xs", false),
    ("  def nestedWalk (xs : Array Block) : Array Block := xs", false),
    -- a List companion is scaffolding, not the public entry
    ("def unwrapItemStepList (out : Array Block) : List Block → Array Block", false),
    -- a rendering makes its output from another type: not IR-to-IR
    ("def bandInlines (b : Array BandSlot) : Array Inline :=", false),
    -- a census returns a summary, not the IR
    ("def blocksText (xs : Array Block) : String := blockTextList \"\" xs.toList", false),
    ("private def raggedItems (items : Array Item) : Array Item :=", false),
    ("  -- def fake (xs : Array Block) : Array Block, quoted in a comment", false)]

  expect "conservesNone" conservesNone [
    ("-- conserves: none — fills a hole; the output census is a mix", true),
    ("  -- conserves: none — the walk edits only image alt text", true),
    ("-- conserves everything", false),
    ("def keepFor (t : String) (xs : Array Block) : Array Block :=", false)]

  expect "repoRefInString" repoRefInString [
    -- the shapes that shipped in real output (the diag-voice defects)
    ("      (help := \"the rest of M6; see PLAN.md\")", true),
    ("      (help := \"there is no Lua here; see PLAN.md for the native declarations\")", true),
    ("            (help := s!\"planned for {milestone}; see PLAN.md\" ++", true),
    ("  say .W0104 \"planned for M8\" pos", true),
    ("  let msg := \"stated in AGENTS.md\"", true),
    ("  fail s!\"see LeanTex/Core/Diag.lean\"", true),
    -- legal spellings: code tokens, comments, docstrings, honest text
    ("  -- planned for M8, tracked in PLAN.md", false),
    ("/-- the registry row's why lives in PLAN.md -/", false),
    ("  let milestone := reservedCtrl.lookup name", false),
    ("      (help := \"\\\\allow{E0333} accepts the loss\")", false),
    ("    \"'{tikzpicture}' is not implemented yet; its content is not rendered\"", false),
    ("  say .W0104 \"a 10mm margin\" pos", false),
    ("  let m8 := M8.compute x", false)]

  expect "demotedAssign" demotedAssign [
    -- the free-severity channel in its new spelling: a call-site demotion
    ("    ({ d with " ++ kwDemotedAssign ++ " true }, true)", true),
    ("  let d : Diag := { kind := k, " ++ kwDemotedAssign ++ " quiet }", true),
    -- mentions in comments and strings, and reads of the field, stay legal
    ("  -- " ++ kwDemotedAssign ++ " comes only from \\allow, never a call site", false),
    ("  say s!\"a string naming " ++ kwDemotedAssign ++ " x\"", false),
    ("  match d.demoted with", false)]

  expect "undeclaredConfigRead" undeclaredConfigRead [
    -- the leak shape: a new Config field threaded from the driver toward a
    -- backend starts as exactly this token
    ("          mathRenderer := ui.cfg.mathRenderer", true),
    ("        let hcfg := { css := ui.cfg.cssMode, imgs }", true),
    ("  if cfg.newFlag then", true),
    -- the declared reads of today's driver
    ("      let emit := ui.cfg.effectiveEmit doc.output.formats", false),
    ("          mathBoundary := ui.cfg.mathBoundary", false),
    ("  if ui.cfg.porcelain then", false),
    ("    let allowAll := ui.cfg.bestEffort", false),
    ("  let faces ← FontDiscovery.scan (cfg.fontDirs.toList ++ (← texFontDirs))", false),
    -- comments, strings, and non-Config names stay legal
    ("  -- ui.cfg.frobnicate would be rejected here", false),
    ("  say s!\"a message naming cfg.frobnicate\"", false),
    ("  let x := hcfg.mathBoundary", false),
    ("  cfg : Config", false)]

  -- The source parser: the hook's index is the default, CI's range and
  -- tree modes are explicit, and a range with no revision is an error —
  -- a CI step that meant to read the pushed commits must not go quiet.
  let srcShow : Except String Source → String
    | .ok .index => "index"
    | .ok .tree => "tree"
    | .ok (.range r) => s!"range {r}"
    | .error e => s!"error {e}"
  let srcCases : List (List String × String) := [
    ([], "index"),
    (["--tree"], "tree"),
    (["--range", "origin/main...HEAD"], "range origin/main...HEAD"),
    (["--range=abc123..HEAD"], "range abc123..HEAD"),
    (["--range"], "error --range needs a revision range, e.g. --range origin/main...HEAD"),
    (["--range="], "error --range needs a revision range, e.g. --range=origin/main...HEAD"),
    (["-q", "--tree"], "tree")]
  for (argv, want) in srcCases do
    let got := srcShow (parseSource argv)
    if got != want then
      fails.modify (s!"parseSource {argv}: got {got}, want {want}" :: ·)
  -- The index is the only source that reads a diff selector `--cached`;
  -- the tree mode reads no diff at all.
  if (Source.index).diffSel != some #["--cached"] then
    fails.modify ("Source.index.diffSel" :: ·)
  if (Source.tree).diffSel != none then
    fails.modify ("Source.tree.diffSel" :: ·)

  -- The frame rule reads which definition `--selftest` reaches and how it is
  -- built. The first five shapes frame themselves, one construct each: the
  -- rule's first spelling, and the four the spelling rule passed; the rest
  -- are legal, the second one a frame split across two lines.
  let hand (fl : String) : List String :=
    ["def selftest : IO UInt32 := do", fl, "  return 0"]
  let producer := "def main (args : List String) : IO UInt32 := tierMain \"t\" .raw m selftest args"
  let frameCases : List (String × List String × List String) := [
    ("a List failure list", hand "  let fails ← IO.mkRef ([] : List String)" ++ [producer],
      ["selftest"]),
    ("an Array failure list", hand "  let fails ← IO.mkRef (#[] : Array String)" ++ [producer],
      ["selftest"]),
    ("a mutable array", hand "  let mut bad : Array String := #[]" ++ [producer], ["selftest"]),
    ("a frame under another name, handed to tierMain",
      ["def checkAll : IO UInt32 := do", "  return 1",
       "def main (args : List String) : IO UInt32 := tierMain \"t\" .raw m checkAll args"],
      ["checkAll"]),
    ("a frame under another name, dispatched by --selftest",
      ["def checkAll : IO UInt32 := do", "  return 1",
       "def main (args : List String) : IO UInt32 := do",
       "  if args.contains \"--selftest\" then return ← checkAll",
       "  tierMain \"t\" .raw m (pure 1) args"], ["checkAll"]),
    ("the shared frame, a cache inside it",
      ["def selftest : IO UInt32 := tierSelftest \"t\" fun no => do",
       "  let cache ← IO.mkRef #[]", producer], []),
    ("the shared frame on the next line",
      ["def selftest : IO UInt32 :=", "", "  Scoreboard.tierSelftest \"t\" fun no => do",
       producer], []),
    ("a report that exits on its own findings",
      ["def table : IO UInt32 := do", "  return 1",
       "def main (args : List String) : IO UInt32 := do",
       "  if args.contains \"--table\" then return ← table", "  tierMain \"t\" .raw m selftest args",
       "def selftest : IO UInt32 := tierSelftest \"t\" fun no => do"], []),
    ("a script that measures no tier", hand "  let mut bad : Array String := #[]", [])]
  for (what, file, want) in frameCases do
    let got := selfFramed file.toArray
    if got.toList != want then
      fails.modify (s!"selfFramed, {what}: got {got}, want {want}" :: ·)

  -- Break the real output boundary, including aliases and multiline
  -- calls; leave status/help/startup failures and structured builders legal.
  let diagCases : List (String × String × List String × Bool) := [
    ("entry point cannot print diagnostics", "Main.lean",
      ["def main := IO.eprintln msg"], true),
    ("direct stderr", "LeanTex/Cli/Driver.lean",
      ["def report (d : Diag) : IO Unit :=", "  IO.eprintln d.message"], true),
    ("CLI module printing", "LeanTex/Cli/DriverDiag.lean",
      ["def report (d : Diag) : IO Unit :=", "  IO.println d.code"], true),
    ("opened IO namespace", "LeanTex/Cli/Driver.lean",
      ["open IO", "def report (d : Diag) := eprintln d.message"], true),
    ("opened stream namespace", "LeanTex/Cli/DriverDiag.lean",
      ["open IO.FS.Stream", "def report (s : IO.FS.Stream) := putStrLn s msg"], true),
    ("multiline stream write", "LeanTex/Cli/Driver.lean",
      ["def report (ui : Ui) (d : Diag) : IO Unit := do", "  ui.errStream.putStrLn",
       "    d.message"], true),
    ("stream alias", "LeanTex/Cli/Driver.lean",
      ["def report (ui : Ui) := do", "  let s := ui.errStream", "  pure s"], true),
    ("print alias", "LeanTex/Cli/Driver.lean",
      ["def report := do", "  let emit := IO.eprintln", "  emit msg"], true),
    ("early human render", "LeanTex/Cli/Input.lean",
      ["def text (d : Diag) := Render.human false d"], true),
    ("early machine render", "LeanTex/Cli/Driver.lean",
      ["def text := Render.porcelainDiag"], true),
    ("sink bypass", "LeanTex/Cli/Driver.lean",
      ["def Ui.diag (ui : Ui) (d : Diag) := do", "  IO.eprintln d.message"], true),
    ("sink raw suffix", "LeanTex/Cli/Driver.lean",
      ["def Ui.diag (ui : Ui) (d : Diag) := do",
       "  ui.errStream.putStrLn (Render.human ui.color d ++ d.message)"], true),
    ("command field alias", "LeanTex/Cli/Driver.lean",
      ["def main := do", "  let msg := d.message", "  IO.println msg"], true),
    ("status interpolation", "LeanTex/Cli/Driver.lean",
      ["def Ui.phase := do", "  IO.eprintln s!\"{d.code}: {d.message}\""], true),
    ("literal diagnostic", "LeanTex/Cli/Driver.lean",
      ["def main := do", "  IO.eprintln \"warning: lost text\""], true),
    ("warning icon headline", "LeanTex/Cli/Driver.lean",
      ["def Ui.phase := IO.eprintln \"⚠ [W0301] lost text\""], true),
    ("error icon headline", "LeanTex/Cli/Driver.lean",
      ["def Ui.phase := IO.eprintln \"✖ [E0001] lost text\""], true),
    ("info icon headline", "LeanTex/Cli/Driver.lean",
      ["def Ui.phase := IO.eprintln \"ℹ [N0100] translated text\""], true),
    ("icon headline interpolation", "LeanTex/Cli/Driver.lean",
      ["def Ui.phase := IO.eprintln s!\"⚠ [{code}] lost text\""], true),
    ("multiline icon headline", "LeanTex/Cli/Driver.lean",
      ["def Ui.phase := do", "  IO.eprintln", "    \"⚠[W0301] lost text\""], true),
    ("typed sink", "LeanTex/Cli/Driver.lean",
      ["def Ui.diag (ui : Ui) (d : Diag) := do", "  if d.severity != .note then",
       "    ui.errStream.putStrLn (Render.human ui.color d)",
       "    ui.errStream.putStrLn (Render.human ui.color d ui.showOutput)",
       "  ui.outStream.putStrLn (Render.porcelainDiag d)"], false),
    ("literal status summaries", "LeanTex/Cli/Driver.lean",
      ["def Ui.done := IO.println \"✔ demo.tex → demo.pdf — 1 page (1 ms) · 2 notes (-v)\"",
       "def Ui.summary := IO.eprintln \"✖ demo.tex — 1 error (1 ms)\"",
       "def Ui.werror := IO.eprintln \"✖ demo.tex — 1 warning (--werror) (1 ms)\""], false),
    ("headline word boundaries", "LeanTex/Cli/Driver.lean",
      ["def Ui.phase := IO.println \"information: scanning fonts\"",
       "def Ui.summary := IO.println \"warnings: 2\""], false),
    ("commented headlines", "LeanTex/Cli/Driver.lean",
      ["def Ui.phase := do", "  /- IO.eprintln \"⚠ [W0301] lost text\" -/",
       "  -- IO.eprintln \"Info [N0100] translated text\"",
       "  IO.println \"finished\""], false),
    ("status and verdict", "LeanTex/Cli/Driver.lean",
      ["def Ui.phase := IO.println s!\"{name}: {detail}\"", "def Ui.werror := do",
       "  ui.errStream.putStrLn (Render.humanWerror ui.color file warnings ms)"], false),
    ("help and startup failure", "LeanTex/Cli/Driver.lean",
      ["def main := do", "  IO.println helpText", "  let stderr ← IO.getStderr",
       "  stderr.putStrLn s!\"leantex: {msg}\"", "  stderr.putStrLn \"try 'leantex --help'\""], false),
    ("command output", "LeanTex/Cli/Driver.lean",
      ["def dump := IO.print (Ir.dump front.doc front.diags)",
       "def hyphenate := IO.println (showHyphens pats w)"], false),
    ("structured builder and policy", "LeanTex/Cli/DriverDiag.lean",
      ["def make := Diag.of .E0001 msg", "def fatal (d : Diag) := d.severity == .error",
       "def scope (d : Diag) := d.output"], false),
    ("output paths beside a diagnostic", "LeanTex/Cli/Driver.lean",
      ["def Ui.phase (d : Diag) (cfg : Config) := do", "  ui.diag d",
       "  IO.println cfg.output", "  IO.println s!\"{ui.cfg.output}\""], false),
    ("output context ends at the next definition", "LeanTex/Cli/Driver.lean",
      ["def Ui.phase (d : Diag) := ui.diag d",
       "def main (d : Config) := IO.println d.output"], false),
    ("output type names are exact", "LeanTex/Cli/Driver.lean",
      ["def main (cfg : Diag.Config) := IO.println cfg.output"], false),
    ("output status and subprocess", "LeanTex/Cli/Driver.lean",
      ["def main := do", "  let result ← IO.Process.output command",
       "  IO.println result.stdout", "  IO.println s!\"wrote {doc.output.formats}\""], false),
    ("output context ignores documentation", "LeanTex/Cli/Driver.lean",
      ["def main := do", "  /- (cfg : Diag) -/", "  let help := \"(cfg : Diag)\"",
       "  IO.println cfg.output"], false),
    ("documentation", "LeanTex/Cli/Input.lean",
      ["/-- Render.human is the formatter.", "IO.eprintln d.message", "-/",
       "def doc := \"IO.eprintln (Render.human false d)\"",
       "-- IO.eprintln d.message"], false),
    ("multiline help", "LeanTex/Cli/Args.lean",
      ["def helpText :=", "  \"leantex", "print the document; IO.eprintln is just text",
       "Render.human -- /- quotes are not comments here", "end\""], false),
    ("quote character", "LeanTex/Cli/Input.lean",
      ["def isQuote (c : Char) := c == '\"'", "def report := IO.eprintln msg"], true),
    ("inline nested comment", "LeanTex/Cli/Driver.lean",
      ["def report := do", "  /- outer /- inner -/ done -/ IO.eprintln msg"], true),
    ("other tools are out of scope", "scripts/example.lean",
      ["def main := IO.eprintln \"warning: a tool status\""], false)] ++
    (["Warning", "ERROR", "note", "Info"].flatMap fun label =>
      [": lost text", "[W0301] lost text", " [W0301] lost text", " - lost text"].map fun tail =>
        (s!"literal {label}{tail}", "LeanTex/Cli/Driver.lean",
          ["def Ui.phase := IO.eprintln \"" ++ label ++ tail ++ "\""], true)) ++
    ["trigger", "recovery", "output"].flatMap fun field =>
      -- All use permitted writers: the field rule itself must reject them,
      -- not the independent rule against an unaudited terminal writer.
      [(s!"structured {field} direct", "LeanTex/Cli/Driver.lean",
        ["def Ui.phase (d : Diag) := IO.eprintln (reprStr d." ++ field ++ ")"], true),
       (s!"structured {field} accessor", "LeanTex/Cli/Driver.lean",
        ["def Ui.phase (d : Diag) := IO.eprintln (reprStr d." ++ field ++ ".isSome)"], true),
       (s!"structured {field} alias", "LeanTex/Cli/Driver.lean",
        ["def main := do", "  let d : Diag := make",
         "  let text := reprStr d." ++ field, "  IO.println text"], true),
       (s!"structured {field} interpolation", "LeanTex/Cli/Driver.lean",
        ["def Ui.phase", "    (notice : LeanTex.Core.Diag) :=",
         "  IO.eprintln s!\"{reprStr notice." ++ field ++ "}\""], true),
       (s!"structured {field} constructor", "LeanTex/Cli/Driver.lean",
        ["def main := do", "  let d := Diag.of .E0001 msg",
         "  IO.println (reprStr d." ++ field ++ ")"], true),
       (s!"structured {field} sink suffix", "LeanTex/Cli/Driver.lean",
        ["def Ui.diag (d : Diag) :=",
         "  IO.eprintln (Render.human false d ++ reprStr d." ++ field ++ ")"], true)]
  for (what, file, lines, bad) in diagCases do
    for declPrefix in ["", "public ", "private ", "@[inline] public "] do
      let source := lines.map fun line =>
        if line.startsWith "def " then s!"{declPrefix}{line}" else line
      let got := !(diagnosticOutputBypasses file source.toArray).isEmpty
      if got != bad then
        fails.modify (s!"diagnosticOutputBypasses {declPrefix}{what}: got {got}, want {bad}" :: ·)
  let escapedWriter := #["public def Ui.phase := IO.println \"finished\"",
    "public def report := IO.eprintln msg"]
  unless (diagnosticOutputBypasses "LeanTex/Cli/Driver.lean" escapedWriter).map (·.1) == #[2] do
    fails.modify ("diagnosticOutputBypasses: public helper inherited an allowed writer" :: ·)

  -- The privacy gate's plumbing (the matcher's own selftest runs in lake
  -- test): added lines join into runs by file and consecutive line, and a
  -- batch answer splits into its objects, a missing one empty.
  let runs := addedRuns #[("a", 3, "x"), ("a", 4, "y"), ("a", 7, "z"), ("b", 8, "w")]
  unless runs == #[("a", 3, "x\ny"), ("a", 7, "z"), ("b", 8, "w")] && addedRuns #[] == #[] do
    fails.modify ("addedRuns did not join consecutive lines of one file, and only those" :: ·)
  let batch := "0a1b blob 3\nabc\nnope missing\n0c2d blob 0\n\n".toUTF8
  unless (parseBatch batch 3).map (·.toList) == #["abc".toUTF8.toList, [], []] do
    fails.modify ("parseBatch did not split a batch answer into its objects" :: ·)
  unless splitFirst "a\tb\tc" "\t" == some ("a", "b\tc") && splitFirst "abc" "\t" == none do
    fails.modify ("splitFirst did not cut at the first separator alone" :: ·)
  -- A home hit prints its kind, never the login after it.
  unless homeKind (dirLocalHome ++ "dave") == dirLocalHome && homeKind (dirHome ++ "dave") == dirHome &&
      homeKind (dirUsers ++ "dave") == dirUsers do
    fails.modify ("homeKind did not keep the kind of home and drop the login" :: ·)
  unless binaryPaths "-\t-\tfig.bin\x003\t1\tnotes.md\x00-\t-\ta\tb.pdf\x002\t0\tdoc.PDF\x00" ==
      #["fig.bin", "a\tb.pdf", "doc.PDF"] do
    fails.modify ("binaryPaths did not keep exactly the rows git counted no lines in and \
those whose name says their text is compressed" :: ·)
  let legacyNames : ByteArray := ⟨"a.md\x00caf".toUTF8.data ++ #[0xE9] ++ ".md\x00".toUTF8.data⟩
  unless zPaths legacyNames == #["a.md", "caf\uFFFD.md", "caf\u00E9.md"] do
    fails.modify ("zPaths did not read a -z name list in each of its encodings" :: ·)

  let failed := (← fails.get).reverse
  if failed.isEmpty then
    IO.println "precommit selftest: all passed"
    return 0
  for f in failed do
    IO.eprintln s!"FAIL {f}"
  return 1

/-- The compiled part of the hook. Build all prerequisites together, then
run the standard drivers in order. A failing stage stops the run and keeps
its exit code; no later stage may turn an incomplete proof into a pass.
What a failing stage printed passes through `redact` (the denylist's
masking, where this clone keeps one) before it is shown. -/
def checkCompiledTree (env : Array (String × Option String) := #[])
    (redact : String → String := id) : IO UInt32 := do
  let stages := #[
    ("lake", #["build", "--wfail", "LeanTex", "leantex", "Tests",
      "precommit", "proofcheck", "lint", "cites", "land"]),
    ("lake", #["test"]),
    ("lake", #["lint"])]
  for (cmd, args) in stages do
    let (code, out, err) ← runBytes cmd args env
    if code != 0 then
      IO.eprintln s!"pre-commit: {cmd} {String.intercalate " " args.toList} failed:"
      IO.eprint (redact (Privacy.textOfBytes out))
      IO.eprint (redact (Privacy.textOfBytes err))
      return code
  return 0

def main (args : List String) : IO UInt32 := do
  if args.contains "--selftest" then
    return (← selftest)
  let src ← match parseSource args with
    | .ok s => pure s
    | .error e =>
      IO.eprintln s!"pre-commit: {e}"
      return 1
  let sel := src.diffSel
  -- The changed-file list: the index for the hook, the range for CI, empty
  -- for --tree. Only the hook may exit early on an empty list — a CI run
  -- whose range touches nothing still owes the whole-tree checks.
  let staged ← match sel with
    | none => pure ([] : List String)
    | some s => pure (((← git (#["diff", "--name-only"] ++ s)).splitOn "\n").filter (!·.isEmpty))
  if src == .index && staged.isEmpty then
    return 0

  -- The denylist, read first: every message below passes through its
  -- masking, so no gate prints a listed term — a home path's login, a
  -- debris file's name — while it reports something else.
  let privacy ← denylist
  let redact : String → String := fun msg => match privacy with
    | some m => m.redact msg
    | none => msg
  let failed ← IO.mkRef false
  let say (msg : String) : IO Unit := do
    IO.eprintln (redact msg)
    failed.set true

  -- Checked in every staged file whatever its extension — the two markers
  -- that once landed were in PLAN.md prose — and before the relevance
  -- gate, which would otherwise skip a prose-only commit.
  let fullDiffBytes ← match sel with
    | none => pure ByteArray.empty
    | some s => pinnedDiff s
  let fullDiff := Privacy.textOfBytes fullDiffBytes
  let bad := conflictMarkers fullDiff
  if !bad.isEmpty then
    let hits := String.intercalate "\n" (bad.toList.map fun (f, n, l) => s!"  {f}:{n}: {l}")
    say s!"pre-commit: merge-conflict marker in staged content:
{hits}
  Fix: resolve the conflict -- keep the side you mean, delete the marker
  lines -- then re-stage the file."

  -- Also over every staged file, before the relevance gate: the checks
  -- above read content, and the debris that escaped had none — a
  -- zero-byte file named by a mangled shell command's own text.
  let numstat ← match sel with
    | none => pure ""
    | some s => git (#["diff", "--numstat", "--diff-filter=A", "-z"] ++ s)
  let faults := addedPathFaults numstat
  if !faults.isEmpty then
    let hits := String.intercalate "\n" (faults.toList.map fun (p, rule) => s!"  {p}: {rule}")
    say s!"pre-commit: a staged added file is debris:
{hits}
  Fix: git rm --cached -- '<path>' and delete the file; stage files by name,
  never with -A or ."

  -- Two paths that differ only by case. Read from the index, which already
  -- holds a staged addition, so the pair is caught by the commit that
  -- creates it rather than by a checkout on another filesystem.
  let tracked ← git #["ls-files", "-z"]
  let collisions := caseCollisions
    ((tracked.splitOn "\x00").filter (!·.isEmpty)).toArray
  if !collisions.isEmpty then
    let hits := String.intercalate "\n" (collisions.toList.map fun (a, b) => s!"  {a}\n  {b}")
    say s!"pre-commit: two tracked paths differ only by case:
{hits}
  Fix: rename one. A case-insensitive checkout keeps one of the two, and for
  a Lean module the compiled .olean names collide as well."

  -- A home directory names a person and a machine, and the tree may carry
  -- neither (AGENTS.md, opening paragraph). The hook reads the lines this
  -- commit adds to every staged file, whatever its extension; CI and --tree
  -- read every tracked text file, so a path that arrived by a route with no
  -- hook — a machine without core.hooksPath — is still found.
  let homeLines ← if src == .index then pure (addedLines fullDiff) else do
    let r ← IO.Process.output
      { cmd := "git", args := #["grep", "-I", "-n", "-z", "-E", "/(home|Users)/"] }
    if r.exitCode == 0 then pure (grepRecords r.stdout)
    else if r.exitCode == 1 then pure #[]
    else
      IO.eprintln s!"pre-commit: git grep failed:\n{r.stderr}"
      IO.Process.exit 1
  let homeHits := homePathHits homeLines
  if !homeHits.isEmpty then
    -- The location and the kind of home, never the login after it.
    let hits := String.intercalate "\n" (homeHits.toList.map fun (f, n, h) =>
      s!"  {f}:{n}: {homeKind h}…")
    say s!"pre-commit: a home directory path in a tracked text file:
{hits}
  A home directory names a person and a machine; neither belongs in this tree.
  Fix: refer to the private reference corpus abstractly, write a placeholder,
  or give the path relative to the repository."

  -- Personal and private-document terms (AGENTS.md, opening paragraph), by
  -- the denylist this clone keeps outside the tree: the hook reads every line,
  -- path and binary the commit adds, whatever its extension; --tree and
  -- --range read the whole staged tree and, outside the hook, every unpushed
  -- commit and its message, which is what the landing's lint gate runs. With
  -- no list (another machine, CI) the check says so and passes.
  match privacy with
  | none =>
    IO.println "pre-commit: this clone keeps no info/private-terms in its git directory; \
the privacy check is skipped."
  | some m =>
    let (hits, refused) ← if src == .index then pure ((← privacyStaged m fullDiffBytes), none)
      else privacyTree m
    if let some why := refused then say s!"pre-commit: {why}"
    unless hits.isEmpty do
      let scope := if src == .index then "in the staged changes"
        else "in the staged tree or an unpushed commit"
      say s!"pre-commit: a denylisted term {scope}, at:
{String.intercalate "\n" hits.toList}
  The local denylist (info/private-terms in the git common directory) holds
  personal and private-document terms; none may enter the tree, a commit or
  a commit message. The term is never printed, and a path holding it is
  shown with that part as …; git ls-files or git show --stat names it.
  Fix: replace the text with invented words that exercise the same property,
  then re-stage. A term in an unpushed commit stays in what a push publishes
  even after a later commit removes it: rewrite that commit (amend, or
  squash it with the fix) before landing."

  if src == .index && !staged.any relevant then
    return (if ← failed.get then 1 else 0)

  -- One commit, one bump: a range legitimately spans a bump commit and the
  -- commits around it, so this reads the index alone.
  if src == .index && staged.contains "lean-toolchain" && staged.any (· != "lean-toolchain") then
    say "pre-commit: lean-toolchain changed together with other files.
  Toolchain bumps are deliberate and go in their own commit (AGENTS.md, Don't touch).
  Fix: git restore --staged lean-toolchain, commit the rest, then commit the bump alone."

  if staged.any (·.startsWith "testdata/golden/") then
    -- A golden may not be hand-edited, which is why it must travel with the
    -- change that moved it. On a branch that already carries such a change,
    -- a later regeneration is legitimate on its own: two slices landing in
    -- the same fixture only agree after the second one rebases, and the
    -- harness output is what lands either way. So the source change is
    -- looked for across the branch, not only in this commit.
    let branchTouched ← do
      match ← mergeBaseMain with
      | some b =>
        pure (((← git #["diff", "--name-only", b ++ "..HEAD"]).splitOn "\n").filter
          (!·.isEmpty)).toArray
      | none => pure #[]
    if !staged.any goldenSource && !branchTouched.any goldenSource then
      say "pre-commit: testdata/golden/** changed without a .lean or testdata/corpus/*.tex or *.md change.
  Goldens are regenerated through the harness, never hand-edited (AGENTS.md, Don't touch).
  Fix: revert the golden files, or regenerate with: lake exe Tests --update"

  let diff ← match sel with
    | none => pure ""
    | some s => git (#["diff", "--no-color", "--unified=0"] ++ s ++ #["--", "*.lean"])
  for (file, lns) in addedByFile diff do
    for g in gates do
      if g.applies file then
        let bad := lns.filter g.flag
        if !bad.isEmpty then
          say s!"pre-commit: {g.what file}:
{String.intercalate "\n" bad.toList}
{g.help}"


  -- Warn-once keys are namespaced: a flat key space let an environment and a
  -- command of one name silence each other once (W0301/W0302), and a growing
  -- catch-all table re-creates the collision quietly. The check is
  -- structural about the call site, not about one literal spelling: every
  -- warn-once call in core code must spell its namespace where it stands —
  -- a string literal containing ':', alone or opening a concatenation. A
  -- key the line cannot prove namespaced (`sayOnce name`, a variable, an
  -- interpolation, a call split across lines) is rejected outright.
  let addedInCore : List String := Id.run do
    let mut file := ""
    let mut out : List String := []
    for l in diff.splitOn "\n" do
      if l.startsWith "+++ b/" then
        file := (l.drop "+++ b/".length).toString
      else if l.startsWith "+" && !l.startsWith "+++" && file.startsWith "LeanTex/" then
        out := (l.drop 1).toString :: out
    return out.reverse
  let patSay := "say" ++ "Once "
  let patWarn := "warn" ++ "Once "
  let keyNamespaced (rest : String) : Bool :=
    let r := rest.trimAscii.toString
    let r := if r.startsWith "(" then ((r.drop 1).toString.trimAscii.toString) else r
    r.startsWith "\"" && containsSub ((((r.drop 1).toString.splitOn "\"").headD "")) ":"
  let onceCallFlat (l : String) : Bool := Id.run do
    if containsSub l ("def say" ++ "Once") || containsSub l ("def warn" ++ "Once") then
      return false
    for pat in [patSay, patWarn] do
      for rest in (l.splitOn pat).drop 1 do
        -- warnOnce takes the context first; the key follows it
        let rest := if pat == patWarn then
            match rest.splitOn " " with
            | _ :: rs => String.intercalate " " rs
            | [] => rest
          else rest
        if !keyNamespaced rest then
          return true
    return false
  let bad := addedInCore.filter onceCallFlat
  if !bad.isEmpty then
    say s!"pre-commit: warn-once call whose key is not visibly namespaced at the call site:
{String.intercalate "\n" bad}
  Keys share one flat store per module; spell the namespace where the call is —
  a literal (\"ctrl:x\") or a concatenation opening with one ((\"env:\" ++ name)) —
  so two constructs of one name cannot silence each other, and this check can see it."

  -- The claim and its evidence arrive together: a nativePackages entry
  -- without its testdata/compat-index file used to surface an hour later at
  -- lake test (the paper-bib escape); the hook refuses it at commit time.
  -- Whole tree, like the conservation gate: the entry and the file may
  -- land in different hunks.
  if (← System.FilePath.pathExists "LeanTex/Core/Compat.lean") then
    let compatSrc ← IO.FS.readFile "LeanTex/Core/Compat.lean"
    for pkg in nativePackagesOf compatSrc do
      unless (← System.FilePath.pathExists s!"testdata/compat-index/{pkg}.txt") do
        say s!"pre-commit: '{pkg}' is in nativePackages with no testdata/compat-index/{pkg}.txt.
  A nativePackages entry arrives with its index file: the package's
  documented command list, one row per command, the manual section named
  in its header (AGENTS.md, obligation table); lake test probes every row.
  Fix: write testdata/compat-index/{pkg}.txt before adding the entry."

  -- The conservation gate — the obligation table's walk row, mechanical:
  -- every public IR-to-IR walk in core (a def taking and returning
  -- Array Block / Array Inline) ships its census statement, named by a
  -- registered shape suffix (`_text` / `_covers` / `_id`, the Conserves
  -- instances and census equalities), or writes
  -- `-- conserves: none — <why>` beside the def. Whole tree, not the
  -- diff: the walk and its theorem may land in different hunks, and the
  -- next walk must not ship without one.
  let mut coreFiles : Array String := #[]
  for f in (← System.FilePath.walkDir "LeanTex") do
    if f.toString.endsWith ".lean" then coreFiles := coreFiles.push f.toString
  let mut allCore := ""
  let mut coreTexts : Array (String × Array String) := #[]
  let mut walkSites : Array (String × Nat × String × Array String) := #[]
  for f in coreFiles do
    let txt ← IO.FS.readFile f
    allCore := allCore ++ txt
    let lines := (txt.splitOn "\n").toArray
    coreTexts := coreTexts.push (f, lines)
    for i in [0:lines.size] do
      if let some name := walkEntry lines[i]! then
        walkSites := walkSites.push (f, i, name, lines)
  for (f, i, name, lines) in walkSites do
    let hasThm := conservesSuffixes.any fun suf =>
      containsSub allCore s!"theorem {name}{suf}"
    let escaped := (List.range 13).any fun d =>
      i ≥ d && conservesNone (lines[i - d]?.getD "")
    unless hasThm || escaped do
      say s!"pre-commit: the IR walk `{name}` ({f}:{i + 1}) has no conservation statement.
  A public Block/Inline walk owes its census fact (AGENTS.md, obligation
  table): a theorem named `{name}_text` (census equality — state it as a
  `Conserves` instance), `{name}_covers`, or `{name}_id` — or, when the
  walk genuinely conserves nothing, the one-line refusal
  `-- conserves: none — <why>` beside the def."

  -- The premise gate: a decision about whether the engine speaks, or how
  -- loudly, that rests on a fact about ANOTHER subsystem owes the check that
  -- holds the fact. Three defects shared this shape, each a conditional
  -- whose comment asserted a premise that later became false with nothing
  -- watching: a picture gate that read which tool was configured when the
  -- load-bearing fact was whether anything had drawn the picture (and dropped
  -- a deck's arrowheads in silence), a recovery justified by what no other
  -- path could then do, and a demotion asking whether a name is a TeX
  -- internal when the fact it needs is whether the author wrote the file.
  -- AGENTS.md already says a guarantee stated in prose is not a guarantee and
  -- cites.lean enforces it for theorem citations; this is the same rule where
  -- the claim is about a sibling subsystem rather than a proof.
  -- Whole tree, not the diff: a gate and its pin land in different hunks, and
  -- the next gate must not ship without one.
  let mut premiseTexts : Array (String × Array String) := coreTexts
  if (← System.FilePath.pathExists "Main.lean") then
    premiseTexts := premiseTexts.push
      ("Main.lean", ((← IO.FS.readFile "Main.lean").splitOn "\n").toArray)
  for (f, lines) in premiseTexts do
    for (row, why) in diagnosticOutputBypasses f lines do
      say s!"pre-commit: diagnostic output bypass in {f}:{row}: {why}.
  Keep document diagnostics as Diag values through Ui.diag; only Render formats them.
  Status/help and command output belong in the audited UI and command handlers."
  let mut testDefs : List String := []
  let mut testText := ""
  for f in (#["Tests.lean"] : Array String) ++ (← System.FilePath.walkDir "Tests").filterMap
      (fun p => if p.toString.endsWith ".lean" then some p.toString else none) do
    if (← System.FilePath.pathExists f) then
      let txt ← IO.FS.readFile f
      testText := testText ++ txt
      for l in txt.splitOn "\n" do
        if let some n := topLevelDefName l then testDefs := n :: testDefs
  let treeText := allCore
  -- Every marker in the tree resolves, wherever it stands: a pin naming
  -- nothing reads as a premise held and holds nothing, which is the failure
  -- mode this gate exists to close. This half needs no site detection, so it
  -- covers the sites the detector cannot see.
  for (f, lines) in premiseTexts do
    for i in [0:lines.size] do
      let l := lines[i]?.getD ""
      if containsSub (stripLineComment l) premiseMark then
        match premisePin l with
        | none =>
          say s!"pre-commit: a premise marker with no reason, in {f}:{i + 1}:
  {l.trimAscii}
  A marker names the check that fails when the premise breaks, and why:
  `-- {premiseMark} <pin> — <why>`, or `-- {premiseMark} none — <why>` when
  nothing falsifies it."
        | some (some pin, _) =>
          unless pinResolves treeText testText testDefs pin do
            say s!"pre-commit: the premise marker in {f}:{i + 1} names `{pin}`, which resolves to nothing.
  A pin is a theorem the build checks, or a check block the suite runs — one
  that fails when the premise breaks. A block the suite never calls pins
  nothing.
  Fix: name the real check, or write `{premiseMark} none — <why>` and say what is missing."
        | some (none, _) => pure ()
  -- Each registry row is checked in both directions, so it cannot rot either
  -- way: the site text must still occur, and a named pin must resolve.
  for row in premiseRegistry do
    let txt := ((premiseTexts.find? (·.1 == row.file)).map
      (fun e => String.intercalate "\n" e.2.toList)).getD ""
    unless containsSub txt row.site do
      say s!"pre-commit: the premise row for {row.file} no longer matches its site:
  {row.site}
  A premise row records a gate whose honesty rests on another subsystem. The
  site moved or its condition changed, so the premise owes a fresh reading.
  Fix: update the row, or move the marker beside the site and delete the row."
    match row.pin with
    | some pin =>
      unless pinResolves treeText testText testDefs pin do
        say s!"pre-commit: the premise row for {row.file} ({row.site}) names `{pin}`, which resolves to nothing.
  Fix: name the check that falsifies the premise, or record the row with no
  pin and say what is missing."
    | none => pure ()
  for (f, lines) in premiseTexts do
    for i in [0:lines.size] do
      if let some kind := premiseSite lines i then
        let (cond, _) := (condSpan lines i).getD ((lines[i]?.getD ""), i)
        let marked := (List.range 13).any fun d =>
          i ≥ d && (premisePin (lines[i - d]?.getD "")).isSome
        let registered := premiseRegistry.any fun row =>
          row.file == f && (containsSub cond row.site
            || containsSub (lines[i]?.getD "") row.site)
        unless marked || registered do
          say s!"pre-commit: a premise with no pin, in {f}:{i + 1} — it {kind.what}:
  {(lines[i]?.getD "").trimAscii}
  A gate that rests on a fact about another subsystem owes the check that
  holds the fact; a premise recorded in prose alone rots silently — that is
  how a deck lost every arrowhead with a green suite. The decisive shape is
  two builds differing by the gate's own condition: if the artifact is
  byte-identical and only the diagnostics move, nothing else was handling the
  case (`pictureKeyGateChecks` is the worked example).
  Fix: write `-- {premiseMark} <pin> — <why>` beside it, naming that check;
  `-- {premiseMark} none — <why>` records it as debt instead."


  -- a knot's seal list and its unseal list are hand-kept in pairs, and a
  -- name sealed but never unsealed degrades every later elaboration in
  -- the file silently. Multiset equality per file; the deliberately
  -- module-final seals are allowlisted by name in sealAllow.
  for (f, lines) in coreTexts do
    let (sealedOnly, unsealedOnly) := sealMismatch lines
    let sealedOnly := sealedOnly.filter (!sealAllow.contains ·)
    unless sealedOnly.isEmpty && unsealedOnly.isEmpty do
      let side (what : String) (ns : List String) : String :=
        if ns.isEmpty then "" else s!"\n  {what}: {String.intercalate " " ns}"
      say s!"pre-commit: seal/unseal mismatch in {f}:{side "sealed but never unsealed" sealedOnly}{side "unsealed but never sealed" unsealedOnly}
  Every name a knot seals is unsealed right after it (Elab.lean's pairs
  are the shape); a deliberately module-final seal is allowlisted in
  sealAllow (scripts/precommit.lean) with its reason where it stands."

  -- The state-door gate (the accounts slice), whole tree over Compat:
  -- every modify/set lives in a declared door, or the dispatcher's
  -- silence guard cannot see the mutation. Whole tree, not the diff:
  -- the mutation and its door may land in different hunks.
  for (f, lines) in coreTexts do
    if f == "LeanTex/Core/Compat.lean" then
      let mut cur := ""
      for i in [0:lines.size] do
        let l := lines[i]!
        if let some n := topLevelDefName l then cur := n
        if bareStateMutation l && !compatStateDoors.contains cur then
          say s!"pre-commit: bare state mutation outside a door, in `{cur}` ({f}:{i + 1}):
  {l.trimAscii}
  The dispatcher's silence guard reads diags.size and the writes counter
  (rewriteCtrl_accounts), and a modify/set outside the declared doors
  (compatStateDoors, scripts/precommit.lean) is invisible to both: the
  arm would look silent and draw a false W0387.
  Fix: mutate through `write` (it counts); diagnostics go through `say`."

  -- The arm gate (handed by impl-shapes), whole tree over LeanTex/Core:
  -- a pass-through catch-all in a def whose signature takes IR is the
  -- next constructor silently falling through. Two allowlists in one:
  -- the leaf functions of the generic walks (setAltLeaf, resolveRefLeaf,
  -- substPageLeaf, imageSrcPush, floatLabelPush) carry deliberate
  -- catch-alls — the explicit-arm obligation lives at the one walk
  -- (mapInlines/foldInlines), and a leaf answers "not my node" by design —
  -- and the frozen holes (flattenLeadStep, collectTable, collectItem),
  -- which shrink the list as they close.
  let armAllow : List String :=
    ["setAltLeaf", "resolveRefLeaf", "substPageLeaf", "imageSrcPush",
     "floatLabelPush",
     "flattenLeadStep", "collectTable", "collectItem"]
  for (f, lines) in coreTexts do
    if f.startsWith "LeanTex/Core/" then
      -- A leaf projection is not a walk: a def handed to `foldInlines`/
      -- `foldBlocks`/`mapInline`/`mapBlock` reads one node while the shared
      -- fold recurses, so its catch-all is the fold's own totality, not a
      -- hole (AGENTS: a new collector is a fold leaf). Every identifier
      -- following a fold call on its line is exempt.
      let folds := ["foldInlines", "foldBlocks", "mapInline", "mapBlock"]
      let leafNames : Array String := lines.foldl (fun acc l =>
        let t := stripLineComment l
        match folds.find? (fun fd => hasWord t fd) with
        | none => acc
        | some fd =>
          let after := (t.splitOn fd).drop 1 |> String.intercalate fd
          (after.splitOn " ").foldl (fun acc w =>
            let w := (w.takeWhile (fun c => isWordChar c || c == '.')).toString
            if w.isEmpty then acc else acc.push w) acc) #[]
      let mut cur := ""
      let mut curWalk := false
      let mut sigOpen := false
      for i in [0:lines.size] do
        let l := lines[i]!
        let t := stripLineComment l
        if let some n := topLevelDefName l then
          cur := n
          curWalk := hasWord t "Inline" || hasWord t "Block"
          -- a signature split across lines (the leaf-function spelling)
          -- keeps contributing to the walk judgement until its `:=`
          sigOpen := !containsSub t ":="
        else if sigOpen then
          curWalk := curWalk || hasWord t "Inline" || hasWord t "Block"
          if containsSub t ":=" then sigOpen := false
        if curWalk && wildcardThrough l && !armAllow.contains cur
            && !leafNames.contains cur then
          say s!"pre-commit: wildcard arm in the IR walk `{cur}` ({f}:{i + 1}):
  {l.trimAscii}
  Spell every constructor, or the next Ir constructor silently falls
  through (AGENTS.md, obligation table: an Ir constructor owes an explicit
  arm in every walk); the allowlisted frozen sites live in precommit.lean."

  -- The ]! ratchet (handed by impl-shapes), whole tree: per-file counts
  -- against the frozen baseline — a commit may lower a count, never raise
  -- it. ]! aborts the process; COMMON bans adding it to reach green.
  for (f, lines) in coreTexts do
    let n := bangCount lines
    let base := ((bangBaseline.find? (·.1 == f)).map (·.2)).getD 0
    if n > base then
      say s!"pre-commit: new ]! index in {f}: {n} sites, baseline {base}.
  ]! aborts the whole run on a miss — one font in a TeX Live tree once took
  the run down with it.
  Fix: use `for h :` bounds, getD, or a proof-carrying index; the per-file
  count may only fall (lower its bangBaseline row in scripts/precommit.lean
  when you remove sites)."

  -- The Support rule, mechanical (AGENTS.md, Conventions: a test helper
  -- used by two check blocks moves to Tests/Support.lean the moment the
  -- second caller appears): a top-level def name spelled in two test
  -- files is that second caller arriving. Fifteen copies of one deck
  -- builder once grew exactly this way.
  let mut testFiles : Array String := #["Tests.lean"]
  for f in (← System.FilePath.walkDir "Tests") do
    if f.toString.endsWith ".lean" then testFiles := testFiles.push f.toString
  let mut defSites : Array (String × String) := #[]
  for f in testFiles do
    let txt ← IO.FS.readFile f
    for name in scopedDefNames (txt.splitOn "\n").toArray do
      defSites := defSites.push (name, f)
  for (name, f) in defSites do
    for (name2, f2) in defSites do
      if name == name2 && f < f2 then
        say s!"pre-commit: test helper `{name}` is defined in both {f} and {f2}.
  A helper used by two check blocks moves to Tests/Support.lean the moment
  the second caller appears (AGENTS.md, Conventions).
  Fix: keep one `{name}` in Tests/Support.lean and delete the copies."

  -- The same rule one directory over: a tier producer's `--selftest` is its
  -- assertions, and the frame around them — the failure list, the recorder,
  -- the print-and-exit tail — is `Scoreboard.tierSelftest`. Six producers
  -- wrote those nine lines out by hand before it existed, which is what let
  -- them differ: a producer that recorded a failure and still exited 0 read
  -- exactly like the others. `selfFramed` finds a frame by what it is.
  for f in (← System.FilePath.readDir "scripts") do
    let p := ("scripts/" ++ f.fileName)
    unless !p.endsWith ".lean" || selftestFrameAllow.contains p do
      let lines := ((← IO.FS.readFile p).splitOn "\n").toArray
      let framed := if lines.any (fun l => (l.trimAscii.toString).startsWith boardImport)
        then selfFramed lines else #[]
      if selftestFrameDebt.any (·.1 == p) then
        if framed.isEmpty then
          say s!"pre-commit: {p} no longer frames its own selftest.
  Fix: delete its row in selftestFrameDebt (scripts/precommit.lean) in this commit."
      else
        for n in framed do
          say s!"pre-commit: {p}: `{n}` is the tier's selftest, and frames itself.
  A tier producer's selftest is `tierSelftest \"<tier>\" fun no => do` and its
  assertions; the frame around them lives in scripts/Board.lean, so every
  producer reports and exits the same way.
  Fix: build `{n}` with `tierSelftest`, or allowlist this file in selftestFrameAllow
  (scripts/precommit.lean) with the reason it cannot."
  for (p, _) in selftestFrameDebt do
    unless ← System.FilePath.pathExists p do
      say s!"pre-commit: selftestFrameDebt names {p}, which is gone.
  Fix: delete its row (scripts/precommit.lean)."

  -- The standard lint driver invokes these source checks without starting
  -- another build. Compile and proof checks are owned by that driver.
  if args.contains "--conventions" then
    return if ← failed.get then 1 else 0

  if ← failed.get then
    return 1

  let mut env : Array (String × Option String) := #[]
  let clang := "/home/linuxbrew/.linuxbrew/bin/clang"
  if (← IO.getEnv "LEAN_CC").isNone && (← System.FilePath.pathExists clang) then
    let prefixOut ← IO.Process.output { cmd := "lean", args := #["--print-prefix"] }
    let pre := prefixOut.stdout.trimAscii.toString
    env := #[("LEAN_CC", some clang), ("LIBRARY_PATH", some s!"{pre}/lib:{pre}/lib/lean")]
  if src == .index then env := env.push (hookVar, some "1")

  checkCompiledTree env redact
