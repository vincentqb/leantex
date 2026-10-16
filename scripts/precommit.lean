/-
The pre-commit gate: source conventions over the staged diff, the lines and paths a revision range
adds (`--range`) or the tree (`--tree`), then lake build --wfail, lake test and lake lint unless
`--conventions` is given.
-/

import scripts.Gate
import scripts.Layers
import scripts.Privacy
import LeanTex.Core.DesignRole
import LeanTex.Core.SurfaceKind

open Privacy (addedLines addedRuns splitFirst)

/-- A command's exit code and its output streams as bytes, each read by its own task so neither pipe
stalls. -/
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

/-- A git query's output as bytes; a failure stops the run. -/
def gitBytes (args : Array String) : IO ByteArray := do
  let (code, out, err) ← runBytes "git" args
  if code != 0 then
    IO.eprintln s!"pre-commit: git {String.intercalate " " args.toList} failed:\n{Privacy.textOfBytes err}"
    IO.Process.exit 1
  return out

def git (args : Array String) : IO String := do
  return Privacy.textOfBytes (← gitBytes args)

/-- A git query whose failure is an answer, `none`, rather than an abort. -/
def gitOpt (args : Array String) : IO (Option String) := do
  let (code, out, _) ← runBytes "git" args
  return if code == 0 then some (Privacy.textOfBytes out) else none

/-- The patch options every diff the gate reads is asked with, whatever this clone's configuration
says. -/
def pinnedPatch : Array String :=
  #["--no-color", "--no-ext-diff", "--no-textconv", "--no-relative", "--src-prefix=a/",
    "--dst-prefix=b/", "-M", "--unified=0"]

/-- `git diff` over `sel` as the gate reads one: `pinnedPatch`. -/
def pinnedDiff (sel : Array String) : IO ByteArray :=
  gitBytes (#["-c", "core.quotePath=false", "diff"] ++ pinnedPatch ++ sel)

/-- The merge base with `main`, else with `origin/main`. -/
def mergeBaseMain : IO (Option String) := do
  for ref in ["main", "origin/main"] do
    if let some out ← gitOpt #["merge-base", "HEAD", ref] then
      let b := ((out.splitOn "\n").headD "").trimAscii.toString
      if !b.isEmpty then return some b
  return none

/-- Where a run reads its diff: the index (the hook), a revision range (CI and the landing gate),
which judges only what it adds, or no diff (`--tree`). -/
inductive Source where
  | index
  | range (rev : String)
  | tree
  deriving BEq

/-- The `git diff` selector for a source, `none` when it reads no diff. -/
def Source.diffSel : Source → Option (Array String)
  | .index => some #["--cached"]
  | .range r => some #[r]
  | .tree => none

/-- The source the arguments name; a `--range` naming no revision range (`..`) is an error. -/
def parseSource : List String → Except String Source
  | [] => .ok .index
  | a :: rest =>
    if a == "--tree" then .ok .tree
    else if a == "--range" then
      match rest with
      | r :: _ =>
        if !containsSub r ".." then
          .error "--range needs a revision range, e.g. --range origin/main...HEAD"
        else .ok (.range r)
      | [] => .error "--range needs a revision range, e.g. --range origin/main...HEAD"
    else if a.startsWith "--range=" then
      let r := (a.drop "--range=".length).toString
      if !containsSub r ".." then
        .error "--range needs a revision range, e.g. --range=origin/main...HEAD"
      else .ok (.range r)
    else parseSource rest

/-- The revision a range's diff reads new text at, `none` for one revision, whose diff reads the
working tree. -/
def rangeTip (r : String) : Option String :=
  match r.splitOn ".." with
  | [_] => none
  | parts =>
    let t := String.ofList ((parts.getLastD "").toList.dropWhile (· == '.'))
    some (if t.isEmpty then "HEAD" else t)

/-- The prefix that names, with a path, the object a source's diff reads its new side from: `:` the
index, `<tip>:` a range's tip; none for the tree, whose blobs are their own texts. -/
def Source.newSide : Source → Option String
  | .index => some ":"
  | .range r => (rangeTip r).map (· ++ ":")
  | .tree => none

def relevant (f : String) : Bool :=
  f.endsWith ".lean" || f == "lakefile.toml" || f == "lakefile.lean"
    || f == "lean-toolchain" || f.startsWith "testdata/golden/"

/-- The banned keyword, composed so this file's own diff never spells it. -/
def kwUnsafe : String := "uns" ++ "afe"

/-- The append operator, composed so this file's own diff never spells it. -/
def patAppend : String := "+" ++ "+"

/-- Conflict markers, composed so this file's own diff carries none. -/
def mkOurs : String := "<<<" ++ "<<<<"
def mkTheirs : String := ">>>" ++ ">>>>"
def mkBase : String := "|||" ++ "||||"

/-- A merge-conflict marker line: exactly seven `<`, `>` or `|` opening the line, then its end or
white space. -/
def conflictMarker (l : String) : Bool :=
  [mkOurs, mkTheirs, mkBase].any fun m =>
    l.startsWith m &&
      match ((l.drop 7).toString).toList.head? with
      | none => true
      | some c => c.isWhitespace

/-- The added lines of a unified diff that carry a conflict marker, with file and new-file line. -/
def conflictMarkers (diff : String) : Array (String × Nat × String) :=
  (addedLines diff).filter (conflictMarker ·.2.2)

/-- A path spelled only in ASCII letters, digits, `.`, `_`, `/` and `-`, which shells and git pass
unquoted. -/
def plainPath (p : String) : Bool :=
  !p.isEmpty && p.toList.all fun c =>
    c.isAlphanum || c == '.' || c == '_' || c == '/' || c == '-'

/-- Faults among added files in a `--numstat -z` answer: a path outside `plainPath`'s alphabet, or
an empty file. -/
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

/-- Pairs of tracked paths or directories whose spellings differ only by case. -/
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

/-- The collisions an added path takes part in, as one spelling or under one. -/
def collisionsTouching (added : Array String) (pairs : Array (String × String)) :
    Array (String × String) :=
  pairs.filter fun (a, b) => added.any fun p =>
    p == a || p == b || p.startsWith (a ++ "/") || p.startsWith (b ++ "/")

/-- The spellings a home directory takes, composed so this file's own text carries none. -/
def dirHome : String := "/ho" ++ "me/"
def dirLocalHome : String := "/lo" ++ "cal" ++ dirHome
def dirUsers : String := "/Us" ++ "ers/"

/-- The one home directory the tree may name: the toolchain prefix the setup exports. -/
def homeAllowed : List String := ["linuxbrew"]

/-- A character that can continue a path or host segment. -/
def segChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '.' || c == '-'

/-- The segment starting at index `j`: the run of segment characters. -/
def segAt (cs : Array Char) (j : Nat) : String := Id.run do
  let mut out := ""
  for k in [j:cs.size] do
    match cs[k]? with
    | some c => if segChar c then out := out.push c else return out
    | none => return out
  return out

/-- The home-directory paths a line names, each opening a path and followed by a login: a local or
macOS home, or a home other than the toolchain's. -/
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

/-- The kind of home a hit names, its login dropped. -/
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

/-- The content of each named object, through one `git cat-file --batch`. -/
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

/-- This clone's compiled denylist, `info/private-terms` in the git common directory, if present. -/
def denylist : IO (Option Privacy.Matcher) := do
  let some dir ← gitOpt #["rev-parse", "--path-format=absolute", "--git-common-dir"]
    | return none
  let path := System.FilePath.mk dir.trimAscii.toString / "info" / "private-terms"
  unless ← path.pathExists do return none
  let text := Privacy.textOfBytes (← IO.FS.readBinFile path)
  return some (Privacy.Matcher.ofTerms (Privacy.parseTerms text))

/-- The paths of a `-z` numstat answer the privacy gate reads as blobs (`Privacy.blobRow`). -/
def binaryPaths (numstat : String) : Array String :=
  Privacy.uniq ((numstat.splitOn "\x00").toArray.filterMap Privacy.blobRow)

/-- The paths of a `-z` name list given as bytes, from each of its readings
(`Privacy.segmentReadings`). -/
def zPaths (names : ByteArray) : Array String :=
  Privacy.uniq ((Privacy.segmentReadings names).foldl
    (fun acc r => acc.append ((r.splitOn "\x00").filter (!·.isEmpty)).toArray) #[])

/-- The paths a diff over `sel` adds, copies or renames to. -/
def addedNames (sel : Array String) : IO (Array String) := do
  return zPaths (← gitBytes (#["diff", "--name-only", "-z", "--no-relative", "--diff-filter=ACR",
    "-M"] ++ sel))

/-- The citation's places' texts on the new side of a source's diff (`Source.newSide`), which
`Privacy.excused` reads; none where the source has no such side. -/
def citedTexts (src : Source) : IO (Array (String × String)) := do
  let some pre := src.newSide | return #[]
  let cited := Privacy.citationPlaces.map (·.1)
  return cited.zip ((← catBlobs (cited.map (pre ++ ·))).map Privacy.textOfBytes)

/-- Where the staged changes add a denylisted term, in a line the citation's staged text does not
excuse (`Privacy.excused`), a path or a blob, located and never quoted. -/
def privacyStaged (m : Privacy.Matcher) (diff : ByteArray) : IO (Array String) := do
  let mut out := m.diffFindings diff "" (← citedTexts .index)
  out := out.append (m.pathFindings (← addedNames #["--cached"]) "" "its path")
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

/-- Where a commit among `revs`, the unpushed ones unless named, adds a denylisted term in a line
its citation's text does not excuse (`Privacy.excused`), a path or a blob, or names one in its
message. -/
def privacyCommits (m : Privacy.Matcher) (revs : Array String := unpushedRange) :
    IO (Array String) := do
  let mergesFirst := "--diff-merges=first-parent"
  let patches := Privacy.logPatchesOf (← gitBytes (#["-c", "core.quotePath=false", "log"] ++
    pinnedPatch ++ #[mergesFirst, "-p", "--format=%x00%H"] ++ revs))
  let cited := Privacy.citedIn patches
  let texts ← catBlobs (cited.map fun (sha, p) => s!"{sha}:{p}")
  let paths ← gitBytes (#["log", "--format=%x00%H", "--name-only", "-z", "--diff-filter=ACR",
    "-M", mergesFirst] ++ revs)
  let numstat ← git (#["log", "--format=%x00%H", "--numstat", "-z", "--no-renames",
    "--diff-filter=AM", mergesFirst] ++ revs)
  let binaries := (Privacy.logRecords numstat).filterMap fun (sha, row) =>
    (Privacy.blobRow row).bind fun p => if p.contains '\n' then none else some (sha, p)
  let blobs ← catBlobs (binaries.map fun (sha, p) => s!"{sha}:{p}")
  let found := m.commitFindings patches (Privacy.logRecordsOf paths) (binaries.zip blobs)
    (cited.zip (texts.map Privacy.textOfBytes))
  let log ← gitBytes (#["log", "-z", "--format=%H%n%B"] ++ revs)
  return Privacy.uniq (found.append (m.messageFindingsOf log))

/-- Where the staged tree and, outside the hook, each unpushed commit name a denylisted term, with
why a run lacking `refs/remotes/origin/main` is refused. -/
def privacyTree (m : Privacy.Matcher) : IO (Array String × Option String) := do
  let staged ← gitBytes #["ls-files", "--stage", "-z", "--full-name"]
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

/-- The commits a range's diff reads, its tip's and not its base's, as `git log` arguments. -/
def rangeCommits (r : String) : Array String :=
  let ends (sep : String) : Option (String × String) := match r.splitOn sep with
    | [a, b] => some (if a.isEmpty then "HEAD" else a, if b.isEmpty then "HEAD" else b)
    | _ => none
  match ends "..." <|> ends ".." with
  | some (a, b) => #[b, "--not", a]
  | none => #[r]

/-- Where a range adds a denylisted term, in a line the citation's text at its tip does not excuse
(`Privacy.excused`), a path or a blob, or one of its commits adds or names one. -/
def privacyRange (m : Privacy.Matcher) (r : String) (diff : ByteArray) : IO (Array String) := do
  let mut out := m.diffFindings diff "" (← citedTexts (.range r))
  out := out.append (m.pathFindings (← addedNames #[r]) "" "its path")
  let binaries := binaryPaths (← git #["diff", "--numstat", "-z", "--no-relative", "--no-renames",
    "--diff-filter=AM", r])
  if let some tip := rangeTip r then
    let blobs ← catBlobs (binaries.map (tip ++ ":" ++ ·))
    for (p, bs) in binaries.zip blobs do
      out := out.append (m.blobFindings p bs "")
    out := out.append (← privacyCommits m (rangeCommits r))
  return Privacy.uniq out

def tokens (s : String) : List String :=
  (s.split Char.isWhitespace).toList.map (·.toString) |>.filter (!·.isEmpty)

/-- One applied name, dotted qualification included (`Ir.dumpInlineList`). -/
def isAtom (w : String) : Bool :=
  !w.isEmpty && w.toList.all (fun c => isWordChar c || c == '.')

/-- Does the append write back onto the name it extends (`s := s ++ one x`)? -/
def selfAppend (lhs : String) : Bool :=
  match (lhs.splitOn ":=").reverse with
  | after :: before :: _ =>
    match tokens after, (tokens before).reverse with
    | [n], target :: _ => n == target
    | _, _ => false
  | _ => false

/-- Does the text after the line's last append apply two or more names ending in a bare variable
(`… ++ walk cfg rest`)? -/
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

/-- Does the group open a binder with a type ascription, `(name :`? -/
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

/-- An inductive constructor field with a default value, `| c (name : … := …)`, on a raw diff
line. -/
def ctorDefault (l : String) : Bool :=
  let t := (l.drop 1).toString.trimAscii.toString
  t.startsWith "|" && hasBinderDefault t

/-- Added lines of one unified=0 diff, grouped by their file in diff order. -/
def addedByFile (diff : String) : Array (String × Array String) :=
  (addedLines diff).foldl (fun out (f, _, l) =>
    match out.back? with
    | some (g, ls) => if g == f then out.pop.push (g, ls.push l) else out.push (f, #[l])
    | none => out.push (f, #[l])) #[]

/-- The backends' files. -/
def backendFiles : List String := backendModules.map fun m => "/".intercalate (m.splitOn ".") ++ ".lean"

/-- A temporary directory or file made outside Host, as a code token. -/
def tempRootOutsideHost (l : String) : Bool :=
  ["withTempDir", "createTempDir", "withTempFile", "createTempFile"].any (bannedWord · l)

/-- `IO`, or a name that runs effects without it, as a code token. -/
def ioInCore (l : String) : Bool :=
  ["IO", "BaseIO", "EIO", "unsafeBaseIO", "unsafeIO", "unsafeEIO"].any (bannedWord · l)

/-- Composed so this file's own diff never spells the pattern. -/
def kwDemotedAssign : String := "demo" ++ "ted :="

/-- A literal demotion, which only Diag.lean may write, strings and comments aside. -/
def demotedAssign (l : String) : Bool :=
  containsSub (stripComments (stripLiterals l)) kwDemotedAssign

/-- The module an import line names, at any visibility, or `none` for a line that is no import. -/
def importedModule (t : String) : Option String :=
  let ws := ((t.splitOn " ").filter (!·.isEmpty)).dropWhile
    (fun w => w == "public" || w == "private" || w == "meta")
  match ws with
  | "import" :: "all" :: m :: _ => some m
  | "import" :: m :: _ => some m
  | _ => none

/-- A qualified use `Mod.…` with nothing word-like before the name: catches
`Parse.scanOpt` and `LeanTex.Core.Parse.scanOpt`, not `myParse.foo`. -/
def usesQualified (l mod : String) : Bool :=
  (l.splitOn (mod ++ ".")).dropLast.any fun p =>
    match p.toList.getLast? with
    | none => true
    | some c => !isWordChar c

/-- A bare dimension literal (`pt 14`, `mm 5`, `inch 1`, `mm100 140`) with no same-line `--` comment
giving its source. -/
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

/-- The pattern and right-hand side of a line-leading match arm with exactly one `=>`. -/
def armParts (l : String) : Option (List String × List String) :=
  let t := (stripComments l).trimAscii.toString
  if !t.startsWith "|" then none
  else match (t.drop 1).toString.splitOn "=>" with
    | [pat, rhs] => some (tokens pat, tokens rhs)
    | _ => none

/-- An identity catch-all arm: one bare variable mapped to itself (`| other => other`). -/
def identityArm (l : String) : Bool :=
  match armParts l with
  | some ([p], [r]) => p == r && isVarToken p
  | _ => false

/-- A catch-all arm answering a bare numeral (`| _ => 1`). -/
def wildcardNumeral (l : String) : Bool :=
  match armParts l with
  | some ([p], [r]) =>
    (p == "_" || isVarToken p) && !r.isEmpty && r.toList.all Char.isDigit
  | _ => false

/-- The suffixes a public IR walk's census theorem takes (THEOREMS.md § Naming). -/
def conservesSuffixes : List String := ["_text", "_covers", "_id"]

/-- The name of a public IR-to-IR walk entry: a non-private `def` whose one-line signature takes and
returns `Array Block` or `Array Inline`. -/
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

/-- Is `pat` spelled as a whole name, with no identifier character on either side? -/
def spellsName (line pat : String) : Bool :=
  let parts := line.splitOn pat
  (parts.zip parts.tail).any fun (before, after) =>
    (match before.toList.getLast? with
     | none => true
     | some c => !isWordChar c)
    && (match after.toList.head? with
     | none => true
     | some c => !isWordChar c)

/-- The modules that judge a PDF's bytes: the census, the conformance contract and the destination
judge. -/
def judgeFiles : List String :=
  ["LeanTex/Core/PdfCensus.lean", "LeanTex/Core/PdfContract.lean", "LeanTex/Core/PdfDests.lean"]

/-- A judge reaching into the writer: an import, an `open` or a qualified use of `Pdf`. -/
def writerReach (l : String) : Bool :=
  let l := stripComments l
  let t := l.trimAscii.toString
  importedModule t == some "LeanTex.Core.Pdf"
    || (t.startsWith "open " && hasWord t "Pdf")
    || usesQualified l "Pdf"

/-- HTML built by concatenating a tag string, `"<" ++ …`. -/
def tagStringEmit (l : String) : Bool :=
  ((stripComments l).splitOn "\"<\"").drop 1 |>.any fun rest =>
    rest.trimAscii.toString.startsWith patAppend

/-- The backends `tagStringEmit` does not judge: the typed tree's renderer and the markdown twin,
whose `<url>` is a CommonMark autolink. -/
def tagStringExempt : List String := ["LeanTex/Core/Html.lean", "LeanTex/Core/MarkdownDoc.lean"]

/-- Is `pat` present with no identifier character after it? -/
def hasCall (line pat : String) : Bool :=
  ((line.splitOn pat).drop 1).any fun rest =>
    match rest.toList with
    | [] => true
    | c :: _ => !isWordChar c

/-- A host font scan in a test, where only `FontDiscovery.scanRoots [testFonts]` is hermetic. -/
def fontScanInTest (l : String) : Bool :=
  hasCall (stripComments (stripLiterals l)) "FontDiscovery.scan"

/-- A document's file read as text past the decoding door, by `IO.FS.readFile`. -/
def undecodedRead (l : String) : Bool :=
  hasCall (stripComments (stripLiterals l)) "IO.FS.readFile"

/-- A file's text read past the decoding door and handed to a reader on the same line. -/
def undecodedFixture (l : String) : Bool :=
  let code := stripComments (stripLiterals l)
  hasCall code "IO.FS.readFile" &&
    ["Lex.lex", "Md.read", "Surface.read", "Elab.run", "Elab.runRaws", "elabFixture",
      "elabInputSrc"].any (hasCall code ·)

/-- A harness restating the driver's front end instead of calling `Input.readDocument`,
line-local. -/
def frontEndRestated (l : String) : Bool :=
  let code := stripComments (stripLiterals l)
  hasCall code "Input.expandInputs" || hasCall code "Input.resolveData" ||
    hasCall code "Elab.executeInputs" || undecodedFixture l


/-- The marker stating why an `Ir.dump` read in a test is not a page claim. -/
def irTierMark : String := "-- ir tier:"

/-- An IR dump in a test without its stated tier. -/
def irDumpUnmarked (l : String) : Bool :=
  containsSub (stripComments (stripLiterals l)) "Ir.dump" && !containsSub l irTierMark

/-- The heartbeat option, composed so this file's own diff never spells it. -/
def kwMaxHeartbeats : String := "maxHeart" ++ "beats"

/-- Lean's default heartbeat budget. -/
def defaultHeartbeats : Nat := 200000

/-- Any heartbeat setting but the bare option set, alone on its line, to a nonzero literal under the
default. -/
def heartbeatRaise (l : String) : Bool :=
  match (stripComments (stripLiterals l)).splitOn kwMaxHeartbeats with
  | [_] => false
  | [before, after] =>
    !(before.endsWith "set_option " &&
      match after.trimAscii.toString.splitOn " " with
      | n :: _ => n.toNat?.any fun v => v != 0 && v ≤ defaultHeartbeats
      | [] => false)
  | _ => true

/-- A catch-all arm passing its scrutinee or an accumulator through unchanged (`| _ => out`,
`| other => other`). -/
def wildcardThrough (l : String) : Bool :=
  let answers := ["false", "true", "none", "nil", "break", "continue", "return"]
  match armParts l with
  | some ([p], [r]) =>
    (p == "_" || (isVarToken p && p != "none" && p != "nil")) &&
      isVarToken r && !answers.contains r
  | _ => false

/-- The `]!` sites in a file, strings and comments aside. -/
def bangCount (ls : Array String) : Nat := Id.run do
  let mut n := 0
  for l in ls do
    n := n + ((stripComments (stripLiterals l)).splitOn "]!").length - 1
  return n

/-- The frozen per-file `]!` counts of the LeanTex/ tree; a commit may lower a row, never raise
it. -/
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
  ("LeanTex/Core/Pdf.lean", 8)]

/-- The line's string text, one space where each literal opens, lexed alone. -/
def stringsOnly (l : String) : String :=
  (lexView l (· == .strText) (· == .litOpen))[0]?.getD ""

/-- A milestone token (`M6`, `M8`, …). -/
def milestoneTok (s : String) : Bool := Id.run do
  let cs := s.toList.toArray
  for i in [0:cs.size] do
    if cs[i]! == 'M' && ((cs[i+1]?.map Char.isDigit).getD false)
        && !(i > 0 && (isWordChar (cs[i-1]!)))
        && !((cs[i+2]?.map isWordChar).getD false) then
      return true
  return false

/-- The documents a source may point into by section, `<doc> § <heading>`. -/
def sectionDocs : List String := ["AGENTS.md", "PRINCIPLES.md", "THEOREMS.md"]

/-- A repo-internal reference in a string literal: `PLAN.md`, a rule document, a `LeanTex/` path or
a milestone token. -/
def repoRefInString (l : String) : Bool :=
  let s := stringsOnly (stripComments l)
  containsSub s "PLAN.md" || sectionDocs.any (containsSub s ·) ||
    containsSub s "LeanTex/" || milestoneTok s

/-- The caps of a rule document an agent session reads whole: lines, a line's width in characters,
and bytes. -/
structure DocCap where
  doc : String
  lines : Nat
  width : Nat
  bytes : Nat

def ruleDocCaps : List DocCap := [
  { doc := "AGENTS.md", lines := 180, width := 100, bytes := 14000 },
  { doc := "PRINCIPLES.md", lines := 130, width := 100, bytes := 9000 }]

/-- Does the line date a rule: an ISO date, or the retired plan file named as a word? -/
def datedStory (l : String) : Bool := Id.run do
  if hasWord l "PLAN" then return true
  let cs := l.toList.toArray
  let digit (k : Nat) : Bool := (cs[k]?.map Char.isDigit).getD false
  for i in [0:cs.size] do
    if digit i && digit (i + 1) && digit (i + 2) && digit (i + 3) && cs[i + 4]? == some '-'
        && digit (i + 5) && digit (i + 6) && cs[i + 7]? == some '-'
        && digit (i + 8) && digit (i + 9) then
      return true
  return false

/-- A rule document's text, its bytes read leniently, and the finding they owe when they are not
UTF-8. -/
def ruleDocText (doc : String) (bytes : ByteArray) : String × Option String :=
  match String.fromUTF8? bytes with
  | some text => (text, none)
  | none => (Privacy.textOfBytes bytes, some s!"pre-commit: {doc} is not UTF-8.
  A rule document is read whole as text at the start of every session.
  Fix: write it in UTF-8.")

/-- Each cap of `caps` the document exceeds; a document with no row is uncapped. -/
def capFaults (doc text : String) (caps : List DocCap := ruleDocCaps) : Array String := Id.run do
  let some cap := caps.find? (·.doc == doc) | return #[]
  let lines := text.splitOn "\n"
  let lines := if text.endsWith "\n" then lines.dropLast else lines
  let mut out := #[]
  if lines.length > cap.lines then
    out := out.push s!"{doc} is {lines.length} lines, over its cap of {cap.lines}"
  for (l, i) in lines.zipIdx do
    if l.length > cap.width then
      out := out.push s!"{doc}:{i + 1} is {l.length} characters wide, over its cap of {cap.width}"
  if text.utf8ByteSize > cap.bytes then
    out := out.push s!"{doc} is {text.utf8ByteSize} bytes, over its cap of {cap.bytes}"
  return out

/-- The lines of a rule document `datedStory` reads as dated, numbered. -/
def datedLines (text : String) : Array (Nat × String) :=
  ((text.splitOn "\n").zipIdx.filter (datedStory ·.1)).toArray.map fun (l, i) =>
    (i + 1, l.trimAscii.toString)

/-- The section marker, composed so this file's own text makes no pointer. -/
def sectionMark : String := " " ++ "§"

/-- The `<doc> § <heading>` pointers a line makes, backticks aside, each heading running to a
parenthesis, `,`, `;`, `:`, `"`, a backslash or a comment's close, less a closing period. -/
def sectionRefs (l : String) : Array (String × String) := Id.run do
  let t := l.replace "`" ""
  let mut out := #[]
  for doc in sectionDocs do
    for rest in (t.splitOn (doc ++ sectionMark)).drop 1 do
      let rest := (rest.splitOn "-/").headD rest
      let h := String.ofList ((rest.toList.drop 1).takeWhile fun c =>
        c != '(' && c != ')' && c != ',' && c != ';' && c != ':' && c != '"' && c != '\\')
      let h := h.trimAscii.toString
      let h := if h.endsWith "." then (h.dropEnd 1).toString else h
      out := out.push (doc, if rest.startsWith " " then h else "")
  return out

/-- Every section pointer in `files` naming no heading of its document, located. -/
def danglingSectionRefs (heads : List (String × List String))
    (files : Array (String × String)) : Array (String × Nat × String) := Id.run do
  let mut out := #[]
  for (f, text) in files do
    for (l, i) in (text.splitOn "\n").zipIdx do
      for (doc, h) in sectionRefs l do
        unless (((heads.find? (·.1 == doc)).map (·.2)).getD []).contains h do
          out := out.push (f, i + 1, doc ++ sectionMark ++ " " ++ h)
  return out

/-- A tracked source's text for the prose scans, decoded leniently from its bytes. -/
def sourceText (path : System.FilePath) : IO String :=
  return Privacy.textOfBytes (← IO.FS.readBinFile path)

/-- The trampoline git executes. -/
def hookPath : String := "scripts/hooks/pre-commit"

/-- The pattern the trampoline's first test greps the staged names with, if it has one. -/
def hookNamePattern (hook : String) : Option String := do
  let marker := "git diff --cached --name-only | grep -qE '"
  let l ← (hook.splitOn "\n").find? (containsSub · marker)
  let pat := ((((l.splitOn marker).drop 1).headD "").splitOn "'").headD ""
  if pat.isEmpty then none else some pat

/-- Does the trampoline's `grep -qE` accept `name` under `pat`? -/
def hookGreps (pat name : String) : IO Bool := do
  let (code, _, _) ← runBytes "sh"
    #["-c", "printf '%s\\n' \"$1\" | grep -qE \"$2\"", "sh", name, pat]
  return code == 0

/-- The rule documents a commit touching only them could carry past this gate, unmatched by the
trampoline's staged-name pattern. -/
def hookSkippedDocs (hook : String) : IO (List String) := do
  let some pat := hookNamePattern hook | return sectionDocs
  sectionDocs.filterM fun d => return !(← hookGreps pat d)

/-- The prose of a Lean source, one entry per line: its comments and docstrings, code and strings
left out. -/
def leanProse (text : String) : Array String := lexView text (· == .prose)

/-- The prose of a markdown file, one entry per line: fenced code blanked. -/
def mdProse (text : String) : Array String := Id.run do
  let mut out : Array String := #[]
  let mut fence := false
  for l in text.splitOn "\n" do
    if l.trimAscii.toString.startsWith "```" then
      fence := !fence
      out := out.push ""
    else
      out := out.push (if fence then "" else l)
  return out

/-- Text with its backticked spans removed. -/
def unticked (l : String) : String :=
  String.join (((l.splitOn "`").zipIdx.filter fun (_, i) => i % 2 == 0).map (·.1))

/-- A loose pointer into a rule document: `AGENTS.md` or `PRINCIPLES.md` named in prose with no
section after it, or the retired `obligation table`. -/
def looseRuleRef (prose : String) : Bool :=
  let t := unticked prose
  containsSub t ("obligation" ++ " table") ||
    ["AGENTS", "PRINCIPLES"].any fun doc =>
      ((t.splitOn doc).drop 1).any fun rest => !rest.startsWith (".md" ++ sectionMark)

/-- The roots of the vendored corpora: each directory holding a tracked `PROVENANCE.txt`. -/
def vendoredRoots (tracked : Array String) : Array String :=
  tracked.filterMap fun p =>
    if p.endsWith "/PROVENANCE.txt" then some (p.dropEnd "PROVENANCE.txt".length).toString
    else none

/-- Is the path inside a vendored corpus? -/
def vendored (roots : Array String) (p : String) : Bool := roots.any (p.startsWith ·)

/-- Every loose pointer in `files`, located, in Lean comments and unfenced markdown. -/
def looseRuleRefs (files : Array (String × String)) : Array (String × Nat × String) := Id.run do
  let mut out := #[]
  for (f, text) in files do
    let prose := if f.endsWith ".lean" then leanProse text else mdProse text
    for (l, i) in prose.zipIdx do
      if looseRuleRef l then out := out.push (f, i + 1, l.trimAscii.toString)
  return out

/-- The Config fields the driver may read, none of which shapes the artifact but `mathBoundary`
(`artifact_flag_free`). -/
def driverConfigReads : List String :=
  ["cmd", "verbosity", "quiet", "porcelain", "color", "output", "watch",
   "bestEffort", "werror", "fontDirs", "mathBoundary", "effectiveEmit"]

/-- A change a golden's regeneration may travel with: Lean source, or a fixture a surface reads
under `testdata/corpus`. -/
def goldenSource (f : String) : Bool :=
  f.endsWith ".lean" ||
    (f.startsWith "testdata/corpus/" && (LeanTex.Core.Ir.Surface.ofInput? f).isSome)

/-- A `cfg.<name>` read whose field is not on `driverConfigReads`, comments and strings aside. -/
def undeclaredConfigRead (l : String) : Bool := Id.run do
  let t := stripComments (stripLiterals l)
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

/-- A class judged by its name string, `docClass.name == …`, which the compiler cannot keep
exhaustive. -/
def classNameCompare (l : String) : Bool :=
  containsSub (stripComments (stripLiterals l)) "docClass.name =="

/-- The quoted names of the `nativePackages` list block in a Compat source. -/
def nativePackagesOf (src : String) : Array String := Id.run do
  let mut out : Array String := #[]
  let mut inside := false
  for l in src.splitOn "\n" do
    if (stripComments l).startsWith "def nativePackages" then
      inside := true
    else if inside then
      let mut parts := (l.splitOn "\"")
      let mut quoted := false
      for p in parts do
        if quoted then out := out.push p
        quoted := !quoted
      if containsSub (stripComments (stripLiterals l)) "]" then
        inside := false
  return out

/-- A local copy of Support's `hasStr`: a function-shaped `let` comparing a `splitOn` count against
one. -/
def splitOnIdiom (l : String) : Bool :=
  let t := ((stripComments l).trimAscii).toString
  t.startsWith "let " && containsSub t ".splitOn " &&
    (containsSub t ".length > 1" || containsSub t ".length ≥ 2")

/-- The `seal` and `unseal` names of one source, in order, comments aside. -/
def sealNames (lines : Array String) : List String × List String := Id.run do
  let mut sl : List String := []
  let mut ul : List String := []
  for l in lines do
    let t := (((stripComments l).trimAscii).toString)
    if t.startsWith "unseal " then
      for w in tokens ((t.drop 7).toString) do ul := w :: ul
    else if t.startsWith "seal " then
      for w in tokens ((t.drop 5).toString) do sl := w :: sl
  return (sl, ul)

/-- The seal mirror's residue as a multiset difference: (sealed but never unsealed, unsealed but
never sealed). -/
def sealMismatch (lines : Array String) : List String × List String :=
  let (sl, ul) := sealNames lines
  (ul.foldl (fun acc n => acc.erase n) sl, sl.foldl (fun acc n => acc.erase n) ul)

/-- Deliberately module-final seals, by name. -/
def sealAllow : List String := ["noteDefs"]

/-- The size-step formula, `sizeScale.lookup … getD`, spelled outside `Ir.scaleStepIn`. -/
def scaleStepRespell (l : String) : Bool :=
  let t := stripComments (stripLiterals l)
  containsSub t "sizeScale.lookup" && containsSub t ".getD"

/-- A hexadecimal digit table or a digit-letter range, spelled outside `Hex`. -/
def hexRespell (l : String) : Bool :=
  let t := stripComments l
  containsSub t "0123456789abcdef" || containsSub t "0123456789ABCDEF" ||
    containsSub t "≤ 'f'" || containsSub t "≤ 'F'"

/-- A statement-initial `modify` or `set` in Compat, legal only inside `compatStateDoors`. -/
def bareStateMutation (l : String) : Bool :=
  let t := (((stripComments (stripLiterals l)).trimAscii).toString.takeWhile isWordChar).toString
  t == "modify" || t == "set"

/-- The Compat definitions a `modify` or `set` may stand in. -/
def compatStateDoors : List String := ["say", "write", "account"]

/-- The reads that name the document's declared setup rather than the content under judgement. -/
def premiseSources : List String := ["ctx.", "cfg.", "decls", "(← get)."]

/-- The diagnostic doors: the calls that name a loss to the reader. -/
def premiseEmitters : List String := ["say", "sayOnce", "warnOnce", "noteOnce", "diag"]

/-- Does the text call a diagnostic door? -/
def emitsDiag (t : String) : Bool := premiseEmitters.any (hasWord t ·)

/-- Does the text read the declared setup? -/
def readsSetup (t : String) : Bool := premiseSources.any (containsSub t ·)

/-- The indentation of a line, in leading spaces. -/
def indentOf (l : String) : Nat := (l.toList.takeWhile (· == ' ')).length

/-- The condition of a conditional opening at line `i`, through up to four continuation lines to its
`then` or `do`, with the line it ends on. -/
def condSpan (lines : Array String) (i : Nat) : Option (String × Nat) := Id.run do
  let l := stripComments (lines[i]?.getD "")
  unless hasWord l "if" || hasWord l "unless" do return none
  let mut cond := l
  let mut j := i
  for _ in [0:4] do
    if hasWord cond "then" || hasWord cond "do" then break
    j := j + 1
    cond := cond ++ " " ++ stripComments (lines[j]?.getD "")
  return some (cond, j)

/-- The block a conditional opens and the forty lines after it. -/
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
      let piece := stripComments lk
      body := body ++ "\n" ++ piece
    k := k + 1
  let mut after := ""
  for d in [0:40] do
    let piece := stripComments (lines[k + d]?.getD "")
    after := after ++ "\n" ++ piece
  return (body, after)

/-- What a premise site claims: `.gate` speaks only under a configuration, `.silence` goes quiet
under one, `.demote` weakens a loss. -/
inductive PremiseKind where
  | gate
  | silence
  | demote
  deriving BEq

def PremiseKind.what : PremiseKind → String
  | .gate => "names a loss only under a declared configuration"
  | .silence => "goes quiet under a declared configuration, naming the loss below"
  | .demote => "computes a demotion: the reader is claimed unable to act"

/-- A demotion whose value is computed rather than written (`demote := f x`). -/
def computedDemote (l : String) : Bool :=
  ((stripComments (stripLiterals l)).splitOn "demote := ").drop 1 |>.any fun rest =>
    let w := (rest.trimAscii.toString.takeWhile isWordChar).toString
    !w.isEmpty && w != "true" && w != "false"

/-- The premise site a line opens: a computed demotion, or a conditional on the declared setup that
names a loss in its block (`.gate`) or returns before one (`.silence`). -/
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

/-- The marker beside a premise site: `-- premise: <pin> — <why>`, or `-- premise: none — <why>`. -/
def premiseMark : String := "premise:"

/-- A marker's text after its first `mark`, strings aside, cut at a block comment's close. -/
def markerText (mark l : String) : String :=
  let after := mark.intercalate (((stripLiterals l).splitOn mark).drop 1)
  (after.splitOn "-/").headD after

/-- The pin and reason a marker line carries, `some (none, why)` for the refusal, `none` for a
marker with no reason. -/
def premisePin (l : String) : Option (Option String × String) :=
  if !containsSub l premiseMark then none
  else
    match tokens (markerText premiseMark l) with
    | [] => none
    | pin :: rest =>
      let why := String.intercalate " " (rest.filter (fun w => w != "—" && w != "-"))
      if (why.trimAscii.toString).isEmpty then none
      else some (if pin == "none" then (none, why) else (some pin, why))

/-- The names that follow `theorem ` in a text. -/
def theoremNames (text : String) : Std.HashSet String :=
  ((text.splitOn "theorem ").drop 1).foldl (init := {}) fun acc rest =>
    let n := (rest.takeWhile fun (c : Char) => !c.isWhitespace && !"({[:,;".contains c).toString
    let n := String.ofList (n.toList.reverse.dropWhile (· == '.')).reverse
    if n.isEmpty then acc else acc.insert n

/-- How often each identifier occurs in a text, a dotted name counted by its parts. -/
def identCounts (text : String) : Std.HashMap String Nat :=
  let bump (m : Std.HashMap String Nat) (w : String) := m.insert w (m.getD w 0 + 1)
  let (counts, last) := text.foldl (init := (({} : Std.HashMap String Nat), "")) fun (m, cur) c =>
    if isWordChar c || c == '\'' then (m, cur.push c)
    else if cur.isEmpty then (m, cur)
    else (bump m cur, "")
  if last.isEmpty then counts else bump counts last

/-- Does `pin` name a theorem, or a check block the suite defines, under any qualification
`testDefs` holds, and invokes? -/
def pinResolves (theorems : Std.HashSet String) (counts : Std.HashMap String Nat)
    (testDefs : Std.HashSet String) (pin : String) : Bool :=
  theorems.contains pin ||
    (testDefs.contains pin && counts.getD ((pin.splitOn ".").getLastD pin) 0 ≥ 2)

/-- Does the line carry a marker: a comment, or a line of one, opening with `mark`? -/
def markerLine (mark l : String) : Bool :=
  let s := stripLiterals l
  let opens (t : String) : Bool :=
    (t.dropWhile (fun c => c == '-' || c == '!' || c.isWhitespace)).toString.startsWith mark
  s.trimAscii.toString.startsWith mark || ((s.splitOn "--").drop 1).any opens ||
    ((s.splitOn "/-").drop 1).any opens

/-- Does a premise marker stand on line `i` or one of the twelve above it? -/
def premiseMarkedAt (lines : Array String) (i : Nat) : Bool :=
  (List.range 13).any fun d => i ≥ d &&
    let m := lines[i - d]?.getD ""
    markerLine premiseMark m && (premisePin m).isSome

/-- The reason a `conserves: none — <why>` marker gives, if the line is one. -/
def conservesReason (l : String) : Option String :=
  if !markerLine "conserves:" l then none
  else match tokens (markerText "conserves:" l) with
    | "none" :: rest =>
      let why := " ".intercalate (rest.filter (fun w => w != "—" && w != "-"))
      if why.isEmpty then none else some why
    | _ => none

/-- Does a `conserves: none — <why>` marker stand on line `i` or one of the twelve above it? -/
def conservedAt (lines : Array String) (i : Nat) : Bool :=
  (List.range 13).any fun d => i ≥ d && (conservesReason (lines[i - d]?.getD "")).isSome

/-- The premise markers of a source with no reason (`none`) or a pin `resolves` refuses, by line. -/
def premiseFaults (resolves : String → Bool) (lines : Array String) :
    Array (Nat × Option String) := Id.run do
  let mut out := #[]
  for (l, i) in lines.zipIdx do
    if markerLine premiseMark l then
      match premisePin l with
      | none => out := out.push (i + 1, none)
      | some (some pin, _) => unless resolves pin do out := out.push (i + 1, some pin)
      | some (none, _) => pure ()
  return out

/-- The conserves markers of a source that are not `conserves: none — <why>`, by line. -/
def conservesFaults (lines : Array String) : Array Nat :=
  (lines.zipIdx.filter fun (l, _) => markerLine "conserves:" l && (conservesReason l).isNone).map
    (·.2 + 1)

/-- A premise site that cannot carry its marker in place, with the pin that holds it, or `none` and
what is missing. -/
structure PremiseRow where
  file : String
  site : String
  pin : Option String
  why : String

/-- The premise sites that carry no marker in place. -/
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

/-- Does the code hold an elapsed `ms`, `elapsed`, `spent` or `…Ms` to a numeral, with neither
`hangGuardMs` nor `hostMarginMs` named? -/
def clockBound (l : String) : Bool := Id.run do
  let t := stripComments (stripLiterals l)
  if containsSub t "hangGuardMs" || containsSub t "hostMarginMs" then return false
  let cs := t.toList.toArray
  let elapsedName (w : String) : Bool :=
    w == "ms" || w == "elapsed" || w == "spent" ||
      (w.endsWith "Ms" && w.length > 2 && ((w.toList.head?.map Char.isLower).getD false))
  for i in [0:cs.size] do
    let c := cs[i]!
    if c == '<' || c == '>' || c == '≤' || c == '≥' then
      let after := (String.ofList ((cs.toList.drop (i + 1)).dropWhile (· == '='))).trimAsciiStart
      let before := (String.ofList (cs.toList.take i)).trimAsciiEnd.toString
      let word := String.ofList (before.toList.reverse.takeWhile isWordChar).reverse
      if elapsedName word && ((after.toString.toList.head?.map Char.isDigit).getD false) then
        return true
  return false

/-- The suite files that run a child directly: the helper itself and the runtime's own checks. -/
def childRunOwners : List String :=
  ["Tests/Support.lean", "Tests/World.lean", "Tests/ProcessRuntime.lean"]

/-- Does the code run a child through `RunBounded` itself rather than `childRun`? -/
def childRunBypass (l : String) : Bool :=
  let t := stripComments (stripLiterals l)
  hasWord t "runBounded" || containsSub t "RunBounded.output {" || containsSub t "RunBounded.output ("

/-- One staged-diff check: the files it reads, the line predicate, the headline and the fix
paragraph. -/
structure Gate where
  applies : String → Bool
  flag : String → Bool
  what : String → String
  help : String

def gates : List Gate := [
  { applies := fun f => (f == "Tests.lean" || f.startsWith "Tests/") && !childRunOwners.contains f
    flag := childRunBypass
    what := fun f => s!"a child run outside `childRun` in {f}"
    help := "  A test's child is held to a hang guard over its typical time, which `childRun`
  (Tests/Support.lean) takes, so a loaded host stalls it without failing the check.
  Fix: run it with `childRun <typical ms>`, the time a run takes here rounded up." },
  { applies := fun f => f == "Tests.lean" || f.startsWith "Tests/"
    flag := clockBound
    what := fun f => s!"a check decided by a fixed wall-clock bound in {f}"
    help := "  A test's clock measures the host as much as the code, so a bound deciding a
  check is a hang guard: `hangGuardMs` of the run's typical time, or a budget and
  `hostMarginMs`, labelled as one. A claim about growth or speed is a bench row,
  never a lake-test check (AGENTS.md § Build and verify).
  Fix: assert the count the claim rests on where the code exposes it, else time it
  in scripts/bench.lean and keep a labelled `hangGuardMs` guard." },
  { applies := (·.startsWith "LeanTex/")
    flag := classNameCompare
    what := fun f => s!"a class judged by its name string (`docClass.name ==`) in {f}"
    help := "  The DocClass inductive exists so a class check is a match the compiler
  keeps exhaustive; comparing the name string re-creates the stringly
  checks it replaced, invisible to the next constructor (PRINCIPLES.md § Typed boundaries).
  Fix: match on the constructor; a genuinely name-shaped need (a
  diagnostic quoting the class) reads .name without comparing it." },
  { applies := fun _ => true
    flag := bannedWord kwPartial
    what := fun f => s!"new '{kwPartial}' in staged changes to {f}"
    help := s!"  No declaration in the tree is marked '{kwPartial}': every recursion the
  source spells terminates by a proved measure, though do-notation repeat
  loops still compile to a {kwPartial} combinator (AGENTS.md § Lean rules).
  A map or flatMap over children hides the call behind a lambda the checker
  cannot see, and a list matched against a literal pattern with a catch-all
  variable loses its tail; an index loop bounded by [0:xs.size + 1] is total.
  A construct that cannot terminate is a design question, never fuel.
  Fix: make the recursion structural, through a List companion or an index
  measure whose facts stand beside each call." },
  { applies := fun _ => true
    flag := bannedWord kwSorry
    what := fun f => s!"'{kwSorry}' in staged changes to {f}"
    help := "  Every theorem has a complete proof (AGENTS.md § Lean rules).
  Fix: finish the proof." },
  { applies := fun _ => true
    flag := bannedWord kwUnsafe
    what := fun f => s!"'{kwUnsafe}' in staged changes to {f}"
    help := s!"  No code is {kwUnsafe}: it voids the certification story (AGENTS.md § Lean rules).
  Fix: stay in the safe fragment." },
  { applies := fun _ => true
    flag := quadraticPrepend
    what := fun f => s!"'{patAppend} walk rest' (prepend to a recursive call's result) in {f}"
    help := "  Prepending to a recursive call's result copies it at every element
  (AGENTS.md § Lean rules).
  Fix: thread an Array accumulator through the walk (see Compat.rewriteList);
  a one-off prepend outside a recursion can bind the call to a name first." },
  { applies := fun _ => true
    flag := ctorDefault
    what := fun f => s!"inductive constructor field with a default value, in {f}"
    help := "  Constructor fields carry no defaults: a pattern then under-specifies
  silently (AGENTS.md § Lean rules).
  Fix: spell the field at every constructor site; defaults belong on structures." },
  { applies := fun f => f.endsWith ".lean" && f != "LeanTex/Core/Diag.lean"
    flag := demotedAssign
    what := fun f => s!"a demotion written outside Diag.lean, in {f}"
    help := "  Severity and the code letter are projections of a Diag's stored kind, and
  `demoted` is the one policy bit left: a call site that writes it ships a
  content loss as a note (PRINCIPLES.md § One loss in one line).
  Fix: emit through Diag.of; demotion is `\\allow`'s decision alone
  (Diag.demote, in Diag.lean)." },
  { applies := fun f => f.startsWith "LeanTex/" || f == "Main.lean"
    flag := repoRefInString
    what := fun f => s!"a repo-internal reference in a string the user can see, in {f}"
    help := "  A diagnostic is read by someone holding only their own document: PLAN.md,
  AGENTS.md, a LeanTex/ path and milestone names (M6, M8) mean nothing there
  (PRINCIPLES.md § One loss in one line).
  Fix: say what happens and what to write instead; the voice lint in
  Tests.lean judges the registered text." },
  { applies := fun f => f == "Main.lean" || f == "LeanTex/Cli/Driver.lean"
    flag := undeclaredConfigRead
    what := fun f => s!"a Config read in {f} not on the driver's declared list"
    help := "  The artifact is a function of the document and the font environment;
  flags are not arguments to it (AGENTS.md § Layout and design). A new Config
  field the driver reads is one question away from shaping the artifact,
  so it lands on driverConfigReads (scripts/precommit.lean) only after
  that question is answered no — and a flag that does shape the artifact
  breaks the theorem artifact_flag_free instead of growing the list.
  Fix: make it a document declaration (\\output) rather than a flag; a
  flag about where/when/how-loudly goes on the list, deliberately." },
  { applies := fun f => (f.startsWith "LeanTex/" || f == "Main.lean") && f != "LeanTex/Cli/Host.lean"
    flag := tempRootOutsideHost
    what := fun f => s!"a temporary directory or file made outside Host in {f}"
    help := "  On Lean v4.34.1 the toolchain's temporary-directory and temporary-file
  calls end the process with a segmentation fault when the temporary root
  is missing, so the host's one interpreter makes them (AGENTS.md § Layout and design).
  Fix: make the directory with Host.withScratch, whose failure is an
  IO.Error naming the root." },
  { applies := fun f => f.startsWith "LeanTex/Core/" || f == "LeanTex/Cli/World.lean"
    flag := ioInCore
    what := fun f => s!"IO in {f}"
    help := "  Modules under LeanTex/Core/ do no IO: files
  and fonts surface as request values the CLI driver fulfills. World.lean
  is the host's vocabulary, and a program over it is a value: Host.lean
  alone answers its questions (AGENTS.md § Layout and design).
  Fix: return a request value and fulfill it under LeanTex/Cli/, or ask
  World's question and answer it in Host.lean." },
  { applies := (·.startsWith "LeanTex/Core/")
    flag := identityArm
    what := fun f => s!"identity catch-all arm (`| x => x`) in {f}"
    help := "  A rewrite walk with a wildcard ships a new IR constructor through
  untouched (AGENTS.md § When you add).
  Fix: spell every constructor; the compiler then makes the next
  constructor a build error at every walk." },
  { applies := (· == "LeanTex/Core/Ir.lean")
    flag := wildcardNumeral
    what := fun f => s!"wildcard arm answering a numeral (`| _ => 1`) in {f}"
    help := "  A measure walk with a numeric default silently miscounts a new IR
  constructor (AGENTS.md § When you add).
  Fix: spell every constructor and say what each one measures." },
  { applies := (judgeFiles.contains ·)
    flag := writerReach
    what := fun f => s!"a judge of the PDF's bytes reaches into the writer, in {f}"
    help := "  PdfCensus judges what a PDF's bytes carry, through PdfRead alone, PdfDests
  where their navigation leads, and PdfContract judges the census; a judge
  that can see Pdf.lean's spellings reports the writer's intent (AGENTS.md
  § Layout and design).
  Fix: read the fact off the parsed objects or the census; a spelling a
  judge needs is a fact of ISO 32000-2 or a profile, stated where it
  stands with its section." },
  { applies := (backendFiles.contains ·)
    flag := dimLiteral
    what := fun f => s!"bare dimension literal in {f}"
    help := "  A design value in a backend is a token, or carries its source where it
  stands (AGENTS.md § When you add): a loose `pt 14` is how a heading
  scale drifts from the type scale, invisibly.
  Fix: read a token/style/palette entry, or put the source in a `--`
  comment on the same line (the diff scanner cannot see the line above)." },
  { applies := fun f => backendFiles.contains f && !tagStringExempt.contains f
    flag := tagStringEmit
    what := fun f => s!"HTML built from tag strings, in {f}"
    help := "  HTML is a typed tree with a certified escaper; a concatenated tag skips
  the escaper by construction (AGENTS.md § Layout and design). Html.lean's own
  renderer is the one sanctioned site.
  Fix: build the node with the typed constructors; the renderer emits it." },
  { applies := fun f => f == "Tests.lean" || f.startsWith "Tests/"
    flag := fontScanInTest
    what := fun f => s!"FontDiscovery.scan in {f}"
    help := "  Tests scan only the shipped corpus fonts — FontDiscovery.scanRoots [testFonts]
  (AGENTS.md § Privacy); a host scan makes the suite depend on what
  this machine has installed.
  Fix: ship the font in testdata/corpus/fonts/ and scan through testFonts." },
  { applies := fun f => f == "Tests.lean" || f.startsWith "Tests/"
    flag := irDumpUnmarked
    what := fun f => s!"Ir.dump in {f} without its stated tier"
    help := s!"  A claim about what a page shows never comes from an IR dump
  (AGENTS.md § Layout and design).
  Fix: assert over Layout.Out or the typed HTML tree; an IR-tier fact that
  is not a page claim says so on the line: `{irTierMark} <why>`." },
  { applies := fun f => f.startsWith "LeanTex/" && f != "LeanTex/Core/Hex.lean"
    flag := hexRespell
    what := fun f => s!"a hexadecimal digit table or digit-letter range spelled in {f}"
    help := "  LeanTex/Core/Hex.lean reads and spells every hexadecimal digit the
  engine handles.
  Fix: read through Hex.val?, Hex.digit?, Hex.caseDigit or Hex.value?, and
  spell through Hex.spell, Hex.digits, Hex.byte or Hex.scalar." },
  { applies := fun f => f.startsWith "LeanTex/" && f != "LeanTex/Core/Ir.lean"
    flag := scaleStepRespell
    what := fun f => s!"the size-step formula re-spelled (`sizeScale.lookup … getD`) in {f}"
    help := "  Ir.scaleStepIn is the one resolving site for a named step of a size
  ladder (PRINCIPLES.md § One fact in one IR value).
  Fix: read Ir.scaleStepIn over the document's own ladder (Ir.PageSpec.scale,
  Layout's geom.scale); a genuine Option need (an unknown name must stay none) matches on
  the lookup without getD, and a theorem naming a raw table value lives
  beside the table in Ir.lean." },
  { applies := fun f => (f == "Tests.lean" || f.startsWith "Tests/")
      && f != "Tests/Support.lean"
    flag := splitOnIdiom
    what := fun f => s!"a local copy of Support's hasStr (a splitOn-count `let`) in {f}"
    help := "  (hay.splitOn needle).length > 1 is Tests/Support.lean's hasStr, and the
  second caller of a test helper moves it there (AGENTS.md § Repository).
  Fix: use hasStr, or bind it over a fixed page: let has := hasStr page." },
  { applies := (· == "LeanTex/Cli/Input.lean")
    flag := undecodedRead
    what := fun f => s!"a document file read as text past the decoding door, in {f}"
    help := "  A file the document names becomes text through Encoding.readTex or
  Encoding.readMarkdown, which replace bytes that are not text and name
  where; IO.FS.readFile throws instead and ends the run (PRINCIPLES.md § Always ship).
  Fix: read the bytes with readSource and decode them through Encoding." },
  { applies := fun f => f.startsWith "Tests" && f.endsWith ".lean"
    flag := undecodedFixture
    what := fun f => s!"a fixture's text read past the decoding door, in {f}"
    help := "  The suite reads a fixture as the driver reads it: fixtureText decodes
  its bytes through the decoding door (a byte-order mark skipped, bytes
  that are not text replaced, lines ended at CR, a declared encoding
  honoured), where IO.FS.readFile hands a reader bytes the binary never
  sees as they stand (PRINCIPLES.md § One mechanism per concept).
  Fix: read the file with fixtureText." },
  { applies := fun f => f.startsWith "scripts/" && f.endsWith ".lean"
    flag := frontEndRestated
    what := fun f => s!"a document's front end restated in {f}"
    help := "  A harness that reads a document as the driver reads it takes the front
  door, Input.readDocument: the decoding door, the surface reader the
  extension selects, input execution and the declaration's settling. A copy
  of the steps reads a Latin-1, BOM or CR file differently from the binary,
  and the tier then measures a page no build ships
  (PRINCIPLES.md § One mechanism per concept).
  Fix: read the bytes with Input.readSource and pass them to Input.readDocument." },
  { applies := fun f => f.startsWith "LeanTex/" && f.endsWith ".lean"
    flag := heartbeatRaise
    what := fun f => s!"a {kwMaxHeartbeats} raise in {f}"
    help := s!"  The tree holds zero heartbeat raises; a proof that needs one is telling
  you the definition's shape is wrong, not that the budget is small
  (AGENTS.md § Lean rules).
  Fix: reshape the proof or the definition. Report any remaining blocker
  without claiming an unproved guarantee." }]

/-- An import of the scoreboard module, composed so this file's own gate reads no site. -/
def boardImport : String := "import scripts" ++ ".Board"

/-- The one script that frames its own selftest, the aggregate. -/
def selftestFrameAllow : List String := ["scripts/scoreboard.lean"]

/-- Tier producers whose selftest still frames itself, with what each migration owes. -/
def selftestFrameDebt : List (String × String) :=
  [("scripts/commonmark.lean", "its assertions push to a local array; each becomes a `no` call"),
   ("scripts/parity.lean", "its assertions push to a local array; each becomes a `no` call")]

/-- The whole top-level `def` name a line binds, dots included. -/
def topLevelDefName (l : String) : Option String :=
  let t := (declarationHead l).2
  if t.startsWith "def " then
    let rest := (t.drop 4).toString
    let n := (rest.takeWhile (fun c => isWordChar c || c == '.' || c == '\'')).toString
    if n.isEmpty then none else some n
  else none

/-- Each line's code, literals and comments blanked across lines: one space where a literal or a
block comment opens. -/
def codeOnly (lines : Array String) : Array String :=
  lexView ("\n".intercalate lines.toList) (· == .code) fun k => k == .litOpen || k == .blockOpen

/-- A comment of a Lean source: the line it opens on and the prose of each line it spans. -/
structure CommentBlock where
  first : Nat
  lines : Array (Nat × String)
  deriving Inhabited, BEq, Repr

/-- The comments of a Lean source: each block comment, and each run of lines holding only a line
comment; a line comment after code stands alone. -/
def commentBlocks (text : String) : Array CommentBlock := Id.run do
  let mut out : Array CommentBlock := #[]
  let mut run : Option CommentBlock := none
  let mut block : CommentBlock := default
  let mut prose := ""
  let mut line := 1
  let mut inBlock := false
  let mut inLine := false
  let mut trailing := false
  let mut code := false
  for (c, k) in lexClasses text ++ #[('\n', .newline)] do
    match k with
    | .newline =>
      if inLine then
        let one : CommentBlock := { first := line, lines := #[(line, prose)] }
        if trailing then out := out.push one
        else
          match run with
          | some r =>
            if r.lines.back?.any (·.1 + 1 == line) then
              run := some { r with lines := r.lines.push (line, prose) }
            else
              out := out.push r
              run := some one
          | none => run := some one
        inLine := false
      else if inBlock then
        block := { block with lines := block.lines.push (line, prose) }
      prose := ""
      line := line + 1
      code := false
    | .lineOpen =>
      inLine := true
      trailing := code
    | .blockOpen =>
      if let some r := run then out := out.push r
      run := none
      inBlock := true
      block := { first := line, lines := #[] }
    | .blockClose =>
      out := out.push { block with lines := block.lines.push (line, prose) }
      prose := ""
      inBlock := false
      code := true
    | .prose => prose := prose.push c
    | .mark => pure ()
    | .code | .litOpen | .lit | .strText =>
      if !c.isWhitespace && !code then
        if let some r := run then out := out.push r
        run := none
        code := true
  if let some r := run then out := out.push r
  if inBlock then out := out.push block
  return out

/-- The words that mark a licence or generated-file header. -/
def headerMarks : List String :=
  ["generated by", "generated from", "do not edit", "copyright", "spdx-license-identifier",
   "licensed under"]

/-- The first line of a source's code other than `module`, `prelude` and imports. -/
def firstDeclLine (lines : Array String) : Nat := Id.run do
  for (code, i) in (codeOnly lines).zipIdx do
    let t := code.trimAscii.toString
    unless t.isEmpty || t == "module" || t == "prelude" || (importedModule t).isSome do
      return i + 1
  return lines.size + 1

/-- A licence or generated-file header: a comment before the first declaration that says so. -/
def headerComment (declLine : Nat) (b : CommentBlock) : Bool :=
  b.first < declLine &&
    headerMarks.any (containsSub (" ".intercalate (b.lines.toList.map (·.2))).toLower ·)

/-- A word of comment prose: its text, its offset, the text since the word before, and whether a
backtick span holds it. -/
structure ProseWord where
  text : String
  pos : Nat
  sep : String
  ticked : Bool
  deriving Inhabited

/-- The words of a prose text: runs of ASCII letters, digits, `_`, `'` and `-`, trimmed of `'` and
`-`. -/
def proseWords (s : String) : Array ProseWord := Id.run do
  let cs := s.toList.toArray
  let edge (c : Char) : Bool := c == '\'' || c == '-'
  let mut out : Array ProseWord := #[]
  let mut sep := ""
  let mut cur := ""
  let mut start := 0
  let mut ticks := 0
  for i in [0:cs.size + 1] do
    let c := cs[i]?.getD ' '
    if i < cs.size && (c.isAlphanum || c == '_' || edge c) then
      if cur.isEmpty then start := i
      cur := cur.push c
    else
      let w := String.ofList ((cur.toList.dropWhile edge).reverse.dropWhile edge).reverse
      if w.isEmpty then sep := sep ++ cur
      else
        out := out.push { text := w, pos := start, sep, ticked := ticks % 2 == 1 }
        sep := ""
      cur := ""
      if i < cs.size then
        sep := sep.push c
        if c == '`' then ticks := ticks + 1
  return out

/-- Past-tense forms that do not end in `-ed`. -/
def irregularPast : List String :=
  ["ate", "beat", "became", "began", "bent", "bled", "bore", "bought", "bred", "broke", "brought",
   "built", "came", "caught", "chose", "cost", "crept", "cut", "dealt", "did", "drank", "drew",
   "drove", "dug", "fed", "fell", "felt", "fit", "fled", "flew", "flung", "forgot", "fought",
   "found", "froze", "gave", "got", "grew", "had", "held", "hid", "hit", "hung", "kept", "knew",
   "laid", "lay", "led", "left", "lent", "let", "lit", "lost", "made", "meant", "met", "paid",
   "put", "quit", "ran", "rang", "read", "rode", "rose", "said", "sang", "sank", "sat", "saw",
   "sent", "set", "shook", "shot", "shrank", "shut", "slept", "slid", "sought", "spent", "split",
   "spoke", "sprang", "spread", "spun", "stood", "stole", "strove", "struck", "stuck", "swam",
   "swept", "swore", "swung", "taught", "thought", "threw", "told", "took", "tore", "was", "went",
   "wept", "were", "woke", "won", "wore", "wound", "wrote"]

/-- Is the word a past-tense form, an irregular one under a prefix included? -/
def pastWord (w : String) : Bool :=
  (w.length > 3 && w.endsWith "ed") || irregularPast.contains w ||
    ["re", "over", "mis", "un", "out", "with", "under", "up"].any fun p =>
      w.startsWith p && irregularPast.contains (w.drop p.length).toString

/-- Does the word spell an ISO date, `YYYY-MM-DD`, at its start? -/
def isoDateWord (w : String) : Bool :=
  let cs := w.toList.toArray
  let digit (k : Nat) : Bool := (cs[k]?.map Char.isDigit).getD false
  digit 0 && digit 1 && digit 2 && digit 3 && cs[4]? == some '-' && digit 5 && digit 6 &&
    cs[7]? == some '-' && digit 8 && digit 9 && !digit 10

/-- Does the word read as an abbreviated commit hash: 7 to 40 lowercase hex digits, a digit and
a letter among them? -/
def hashWord (w : String) : Bool :=
  w.length ≥ 7 && w.length ≤ 40 && w.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) &&
    w.any Char.isDigit && w.any Char.isAlpha

/-- Does the word spell a report id, `R` and digits? -/
def reportIdWord (w : String) : Bool :=
  w.length ≥ 2 && w.startsWith "R" && (w.drop 1).toString.all Char.isDigit

/-- The inflections of `review`. -/
def reviewForms : List String :=
  ["review", "reviews", "reviewed", "reviewer", "reviewers", "reviewing"]

/-- The narrative markers of comment prose, each with the offset it opens at: a report id, an ISO
date, a commit hash, a `review` naming an event or a round, and `once`, `used to` or `previously`
telling history. -/
def narrativeMarks (prose : String) : Array (Nat × String) := Id.run do
  let ws := proseWords prose
  let raw (k : Nat) : String := (ws[k]?.map (·.text)).getD ""
  let joined (k : Nat) : Bool := k > 0 && (ws[k]?.any (·.sep.all Char.isWhitespace))
  let after (k : Nat) : String := if joined k then (raw k).toLower else ""
  let bare (p : String) : String := if p.endsWith "'s" then (p.dropEnd 2).toString else p
  let digits (n : String) : Bool := !n.isEmpty && n.all Char.isDigit
  let numberWord (n : String) : Bool :=
    ["two", "three", "four", "five", "six", "seven", "eight", "nine", "ten"].contains n
  let ordinal (n : String) : Bool :=
    ["first", "second", "third", "fourth", "fifth", "final", "last", "next"].contains n ||
      (n.length ≥ 3 && n.front.isDigit && ["st", "nd", "rd", "th"].any (n.endsWith ·))
  let listedNoun := ["list", "lists", "tip", "result", "results", "verdict", "verdicts", "row",
    "rows", "merge"]
  let mut out : Array (Nat × String) := #[]
  for (w, k) in ws.zipIdx do
    let t := w.text
    let l := t.toLower
    let rawParts := (t.splitOn "-").map bare
    let parts := rawParts.map (·.toLower)
    let prev := if joined k then (raw (k - 1)).toLower else ""
    let next := after (k + 1)
    let rounds := parts.any (fun p => p == "round" || p == "rounds")
    if (isoDateWord t && !w.ticked) || rawParts.any reportIdWord ||
        (rawParts.any hashWord && !w.sep.endsWith "#") then
      out := out.push (w.pos, t)
    else if w.ticked then continue
    else if parts.length > 1 && ((parts.any reviewForms.contains &&
          !(parts.head? == some "reviewed" && parts.getLast?.any listedNoun.contains)) ||
        l.startsWith "must-fix" || (rounds && parts.any (fun p => ordinal p || digits p))) then
      out := out.push (w.pos, t)
    else if reviewForms.contains (bare l) then
      let id := bare (if joined (k + 1) then raw (k + 1) else "")
      let listed := bare l == "reviewed" && listedNoun.contains next
      if !listed && ((!id.isEmpty && !id.any Char.isLower) || pastWord next ||
          next == "round" || next == "rounds" ||
          ["the", "a", "an", "this", "that", "every", "each", "first", "second", "third", "last",
           "final", "adversarial", "independent", "fresh", "same", "earlier", "prior", "later",
           "code", "peer"].contains prev) then
        out := out.push (w.pos, t)
    else if l == "must" && (next == "fix" || next == "fixes") then
      out := out.push (w.pos, s!"{t} {next}")
    else if (l == "round" || l == "rounds") &&
        ((ordinal prev && !["trip", "trips", "of", "off", "robin"].contains next) ||
        digits next || (numberWord next && ["in", "the", "a", "of", "after", "before", "during",
          "since", "until", "from", "this", "that", "each", "every"].contains prev)) then
      out := out.push (if ordinal prev then ((ws[k - 1]?.map (·.pos)).getD w.pos) else w.pos,
        if ordinal prev then s!"{prev} {t}" else s!"{t} {next}")
    else if l == "once" && !prev.isEmpty &&
        !["at", "and", "or", "but", "nor", "then", "is", "are", "be", "has", "have", "exactly",
          "only", "just", "each", "all"].contains prev then
      let skip := if (after (k + 1)).endsWith "ly" then
        (if (after (k + 2)).endsWith "ly" then 3 else 2) else 1
      let verb := after (k + skip)
      let tail := ((ws[k + skip + 1]?.map (·.sep)).getD "").trimAscii.toString
      let elliptic := [",", ";", "(", ")", "*"].any (tail.startsWith ·)
      if (pastWord verb && !elliptic) || (["was", "were", "had", "been"].contains prev &&
          !["per", "each", "every", "more", "again", "only"].contains next) then
        out := out.push (w.pos, if verb.isEmpty then t else s!"{t} {verb}")
    else if l == "used" && next == "to" && !prev.isEmpty &&
        !["is", "are", "was", "were", "be", "been", "being", "get", "gets", "got"].contains
          prev then
      out := out.push (w.pos, s!"{t} to")
    else if l == "previously" &&
        !["the", "a", "an", "all", "any", "every", "each", "its", "their", "his", "her", "our",
          "your", "own", "no", "some", "those", "these"].contains prev then
      out := out.push (w.pos, t)
  return out

/-- The documentation rule's findings in a Lean source, by line: each comment its added lines take
past three lines, and each narrative marker on an added comment line. -/
def docFindings (text : String) (added : Array Nat) : Array (Nat × String) := Id.run do
  let addedSet : Std.HashSet Nat := added.foldl (·.insert ·) {}
  let declLine := firstDeclLine (text.splitOn "\n").toArray
  let mut out : Array (Nat × String) := #[]
  for b in commentBlocks text do
    unless b.lines.any (addedSet.contains ·.1) do continue
    if headerComment declLine b then continue
    let texts := b.lines.filter (!·.2.trimAscii.isEmpty)
    let n := texts.size
    if n > 3 && n - (texts.filter (addedSet.contains ·.1)).size ≤ 3 then
      out := out.push (b.first, s!"a comment of {n} lines")
    let mut joined := ""
    let mut starts : Array (Nat × Nat) := #[]
    for (ln, p) in b.lines do
      starts := starts.push (joined.length, ln)
      joined := joined ++ p ++ "\n"
    for (pos, mark) in narrativeMarks joined do
      let ln := ((starts.filter (·.1 ≤ pos)).back?.map (·.2)).getD b.first
      if addedSet.contains ln then out := out.push (ln, s!"\"{mark}\"")
  return out.qsort (·.1 < ·.1)

/-- A maintained Lean source, which the documentation rule reads. -/
def docRuleFile (f : String) : Bool := f.endsWith ".lean" && !f.startsWith "testdata/"

/-- Whether a line of code conses onto a list through `.modify`, the shape of a check block writing
its failure list itself. -/
def failureListWrite (code : String) : Bool :=
  containsSub code ".modify (" && containsSub code " :: ·)"

/-- The definition names of a source's code, qualified through its namespace, section and mutual
scopes. -/
def scopedDefNames (lines : Array String) : Array String := Id.run do
  let qualify (space name : String) :=
    if name.startsWith "_root_." then (name.drop 7).toString
    else if space.isEmpty then name else space ++ "." ++ name
  let mut scopes : List String := []
  let mut out := #[]
  for line in codeOnly lines do
    let head := (declarationHead line).2
    let space := scopes.headD ""
    let named (n : Nat) := (((head.drop n).toString.splitOn " ").headD "").splitOn "."
    if head.startsWith "namespace " then
      for part in named 10 do
        scopes := qualify (scopes.headD "") part :: scopes
    else if head == "section" || head.startsWith "section " then
      for _ in named 8 do
        scopes := space :: scopes
    else if head == "mutual" then
      scopes := space :: scopes
    else if head == "end" || head.startsWith "end " then
      scopes := scopes.drop (named 4).length
    else if let some name := topLevelDefName line then
      out := out.push (qualify space name)
  return out

/-- The surface reads the CLI spells only through a surface's door. -/
def surfaceDoorCalls : List String :=
  ["Lex.lex", "Parse.parse", "Md.read", "Md.desugar", "Parse.inputEnv"]

/-- The core's own tex readers around the door, by file and definition, each reading text the engine
holds. -/
def coreTexReaders : List (String × String) :=
  [("LeanTex/Core/Elab.lean", "run"), ("LeanTex/Core/Elab.lean", "applyStyle"),
   ("LeanTex/Core/Data.lean", "valParsed"), ("LeanTex/Core/Compat.lean", "synth"),
   ("LeanTex/Core/Picture.lean", "readMacro"), ("LeanTex/Core/BibText.lean", "formulaOf"),
   ("LeanTex/Core/BibElab.lean", "FieldDoor.readWith")]

/-- The tex door's own stages and the door. -/
def texDoorFiles : List String :=
  ["LeanTex/Core/Lex.lean", "LeanTex/Core/Parse.lean", "LeanTex/Core/Surface.lean"]

/-- The rows of a source that read a surface around its door, with the call each spells. -/
def surfaceDoorBypasses (file : String) (lines : Array String) : Array (Nat × String) := Id.run do
  let mut out := #[]
  if file == "Main.lean" || file.startsWith "LeanTex/Cli/" then
    for (code, row) in (codeOnly lines).zipIdx do
      for call in surfaceDoorCalls do
        if spellsName code call then out := out.push (row + 1, call)
  else if file.startsWith "LeanTex/Core/" && !texDoorFiles.contains file then
    let mut current := ""
    for (code, row) in (codeOnly lines).zipIdx do
      if let some name := topLevelDefName code then current := name
      for call in ["Lex.lex", "Parse.parse"] do
        if spellsName code call && !coreTexReaders.contains (file, current) then
          out := out.push (row + 1, call)
  return out

/-- The rows of a CLI source that print a diagnostic outside Ui.diag and Render, with why. -/
def diagnosticOutputBypasses (file : String) (lines : Array String) : Array (Nat × String) := Id.run do
  unless file == "Main.lean" || file.startsWith "LeanTex/Cli/" do return #[]
  let writers := ["Ui.diag", "Ui.accepted", "Ui.phase", "Ui.fontPhase", "Ui.summary",
    "Ui.done", "Ui.werror", "main", "dump", "hyphenate"]
  let names (s : String) := (s.split (fun c => !(isWordChar c || c == '.'))).toList.map
    (·.toString) |>.filter (!·.isEmpty)
  -- Output and detail fields count only on receivers bound as a Diag in this def.
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
      diags.any (fun d => [".output", ".detail"].any fun f =>
        n == d ++ f || n.startsWith (d ++ f ++ "."))
  let mut owner := ""
  let mut diags : List String := []
  let codes := codeOnly lines
  let texts := lexView ("\n".intercalate lines.toList) (· == .strText)
  let mut out := #[]
  for row in [0:lines.size] do
    let code := codes[row]?.getD ""
    let text := texts[row]?.getD ""
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
    -- Interpolation fields sit inside the masked string, so their projections are read here.
    let interpolated := containsSub code "s!" &&
      ((text.splitOn "{").drop 1).any (fun p => projects diags ((p.splitOn "}").headD ""))
    if ((writer && !sink) || terminal) && (projects diags code || interpolated) then
      out := out.push (row + 1, "diagnostic fields printed outside Render")
    let headline := text.trimAscii.toString.toLower
    let headerAfter (label : String) (marks : List String) :=
      headline.startsWith label &&
        marks.any (fun mark => (headline.drop label.length).trimAsciiStart.toString.startsWith mark)
    -- Diagnostic icons lead into a code bracket; plain ✔/✖ run summaries stay legal.
    if writer && (
        ["warning", "error", "note", "info"].any (fun word => headerAfter word [":", "[", "- "]) ||
        ["⚠", "✖", "ℹ"].any (fun icon => headerAfter icon ["["])) then
      out := out.push (row + 1, "hand-written diagnostic headline")
  return out

/-- The selftests a tier producer frames by hand: those its `--selftest` reaches whose body is no
`tierSelftest` application. -/
def selfFramed (lines : Array String) : Array String := Id.run do
  let code := lines.map fun l => stripComments (stripLiterals l)
  unless code.any (containsSub · "tierMain") do return #[]
  let mut reached : Array String := #[]
  for (l, c) in lines.zip code do
    let args := " ".intercalate ((c.splitOn "tierMain").drop 1)
    let target := " ".intercalate (((l.splitOn "\"--selftest\"").drop 1).map
      (stripComments ∘ stripLiterals))
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

/-- The registry's `\palette` keys. -/
def roleKeyNames : List String := LeanTex.Core.Ir.Role.all.filterMap (·.row.key)

/-- A colour role read by its key string, through the palette's role view, or by a raw role lookup,
comments aside. -/
def roleReadLine (l : String) : Bool :=
  let t := stripComments l
  (roleKeyNames.any fun k =>
    ["find? ", "declareKey ", "ofKey ", "ofKey? ", "contains "].any (fun door =>
      containsSub t (door ++ "\"" ++ k ++ "\"")) ||
    (containsSub t "readColor " && containsSub t ("\"" ++ k ++ "\""))) ||
  (["lookup (.role ", "lookup (ColorRef.role ", "lookup (Ir.ColorRef.role "].any
    (containsSub t ·)) ||
  ((t.splitOn ".declaredRoles").drop 1).any fun rest =>
    rest.isEmpty || !(rest.front.isAlphanum || rest.front == '_')

/-- The role reads one file makes outside the registry and Ir.lean's `DesignResolve` section. -/
def roleReads (f : String) (lines : Array String) : Array (Nat × String) := Id.run do
  if f == "LeanTex/Core/DesignRole.lean" then return #[]
  let mut inRegion := false
  let mut out := #[]
  for i in [0:lines.size] do
    let l := lines[i]!
    let t := l.trimAscii.toString
    if f == "LeanTex/Core/Ir.lean" && t == "section DesignResolve" then inRegion := true
    else if f == "LeanTex/Core/Ir.lean" && t == "end DesignResolve" then inRegion := false
    else if !inRegion && roleReadLine l then out := out.push (i, l)
  return out

/-- A catch-all arm in the registry's `Role.row`. -/
def roleRowWildcards (lines : Array String) : Array Nat := Id.run do
  let mut inRow := false
  let mut out := #[]
  for i in [0:lines.size] do
    let l := lines[i]!
    if let some n := topLevelDefName l then inRow := n == "Role.row"
    if inRow && (stripComments l).trimAscii.toString.startsWith "| _ " then
      out := out.push i
  return out

/-- The hook's compiled stages: every library and the tools built failing on any warning,
then the test and lint drivers. -/
def compiledStages : Array (String × Array String) := #[
  ("lake", #["build", "--wfail", "LeanTex", "TestsModules", "ScriptsModules", "leantex", "Tests",
    "precommit", "proofcheck", "lint", "cites", "land"]),
  ("lake", #["test"]),
  ("lake", #["lint"])]

/-- Every case a gate predicate must catch and every legal spelling it must pass. -/
def selftest : IO UInt32 := do
  let fails ← IO.mkRef ([] : List String)
  match compiledStages[0]? with
  | some ("lake", args) =>
    unless args[0]? == some "build" && args.contains "--wfail" &&
        #["LeanTex", "TestsModules", "ScriptsModules", "leantex", "Tests"].all args.contains do
      fails.modify ("the hook's build does not fail every library on a warning" :: ·)
  | _ => fails.modify ("the hook's first stage is not lake build" :: ·)
  let expect (name : String) (p : String → Bool) (cases : List (String × Bool)) : IO Unit := do
    for (line, want) in cases do
      if p line != want then
        fails.modify (s!"{name} {if want then "missed" else "fired on"}: {line}" :: ·)

  expect "goldenSource" goldenSource [
    ("Tests/Census.lean", true),
    ("testdata/corpus/md-table.md", true),
    ("testdata/corpus/tables.tex", true),
    ("testdata/corpus/code-python.py", true),
    ("testdata/corpus/code-bash.sh", true),
    ("testdata/golden/md-table.txt", false),
    ("testdata/typeset/md-report.md", false)]

  expect "roleReadLine" roleReadLine [
    ("  let g := pal.find? \"bg\"", true),
    ("  let r := p.declaredRoles.find? (·.1 == .page)", true),
    ("  if pal.decorative.contains \"fg\" then", true),
    ("  let p := pal.declareKey \"frametitlebg\" c", true),
    ("  match ← readColor ctx ctx.palette none \"alert\" pos with", true),
    ("  match ctx.palette.lookup (.role .alert) with", true),
    ("  (ctx.basePalette.lookup (ColorRef.role .page))", true),
    ("  let c := (nm.bind ctx.palette.lookup).getD c", false),
    ("  if (key == \"fg\" && fg.isNone) || (key == \"bg\" && bg.isNone) then", false),
    ("  let g := Design.declared? pal .page", false),
    ("  for (name, fg, bg) in BeamerColor.roles do", false),
    ("    { acc with roles := acc.roles.push role }", false),
    ("  let t := doc.styles.find? \"titlepage\"", false),
    ("  let m := s!\"text coloured 'fg' reads low\"", false),
    ("  -- pal.find? \"bg\" in a comment", false)]
  if (roleReads "LeanTex/Core/Layout.lean" #["  let r := a.pal.declaredRoles"]).isEmpty then
    fails.modify ("roleReads missed a planted role view read in Layout.lean" :: ·)
  if (roleReads "LeanTex/Core/Layout.lean" #["  let g := a.pal.lookup (.role .page)"]).isEmpty then
    fails.modify ("roleReads missed a planted raw role lookup in Layout.lean" :: ·)
  if !(roleReads "LeanTex/Core/Ir.lean"
      #["section DesignResolve", "  p.declaredRoles.size", "end DesignResolve"]).isEmpty then
    fails.modify ("roleReads fired inside the resolving region" :: ·)
  if (roleReads "LeanTex/Core/Ir.lean"
      #["section DesignResolve", "end DesignResolve", "  p.declaredRoles.size"]).isEmpty then
    fails.modify ("roleReads missed a read after the resolving region" :: ·)
  if !(roleReads "LeanTex/Core/DesignRole.lean" #["  pal.find? \"bg\""]).isEmpty then
    fails.modify ("roleReads fired in the registry" :: ·)
  if (roleRowWildcards #["@[expose] public def Role.row : Role → Row", "  | .page => x",
      "  | _ => y"]).isEmpty then
    fails.modify ("roleRowWildcards missed a catch-all in Role.row" :: ·)
  if !(roleRowWildcards #["public def Role.depth : Role → Nat", "  | _ => 0"]).isEmpty then
    fails.modify ("roleRowWildcards fired outside Role.row" :: ·)

  expect "computedDemote" computedDemote [
    ("        (demote := styInternal (← get).file name)", true),
    ("      (demote := Compat.styInternal ctx.file name)", true),
    ("        let d := { d with x := 1 } -- demote := f x", false),
    ("  say .W0301 msg pos (demote := true)", false),
    ("  sayOnce key .W0357 msg pos (demote := false)", false),
    ("    (demote : Bool := false) (subject : Option String := none) : M Unit :=", false),
    ("  -- demote := styInternal file name would need a pin", false),
    ("  say s!\"a message naming demote := f x\" pos", false)]

  expect "premisePin" (fun l => (premisePin l).isSome) [
    ("  -- premise: pictureKeyGateChecks — the two builds ship the same bytes", true),
    ("  -- premise: none — nothing falsifies this yet; recorded as debt", true),
    ("  -- premise: pictureKeyGateChecks", false),
    ("  -- premise: none", false),
    ("  -- premise:", false),
    ("  -- the boundary tool reads what the subset refused", false)]

  if premisePin "  -- premise: fooChecks — because bar" != some (some "fooChecks", "because bar") then
    fails.modify ("premisePin did not read the pin and reason" :: ·)
  if premisePin "  -- premise: none — nothing pins it" != some (none, "nothing pins it") then
    fails.modify ("premisePin did not read the refusal" :: ·)

  let treeSrc := "theorem footBand_projects : True := trivial"
  let testSrc := "def liveChecks (ref : IO.Ref (List String)) : IO Unit := do\n  liveChecks ref\ndef deadChecks : IO Unit := pure ()"
  let pinCases : List (String × Bool) := [
    ("footBand_projects", true),
    ("footBand", false),
    ("liveChecks", true),
    ("Tests.liveChecks", true),
    ("deadChecks", false),
    ("neverWrittenChecks", false)]
  let testSet : Std.HashSet String := {"liveChecks", "Tests.liveChecks", "deadChecks"}
  let resolves := pinResolves (theoremNames treeSrc) (identCounts testSrc) testSet
  for (pin, want) in pinCases do
    if resolves pin != want then
      fails.modify (s!"pinResolves {pin}: want {want}" :: ·)
  let markerSrc := #["  if ctx.slides then -- premise: noSuchChecks — a reason",
    "  -- premise: liveChecks — the suite runs it",
    "  -- premise: noSuchChecks — a pin that names nothing",
    "  -- premise: none — nothing falsifies it yet",
    "  -- premise: liveChecks",
    "premise: noSuchChecks — a docstring line carries a marker too",
    "the process-group premise: a descendant that outlives the run",
    "  say \"-- premise: noSuchChecks — a string is no marker\" pos",
    "  -- conserves: none — fills a hole",
    "  -- conserves: none",
    "-- conserves: everything",
    "  /- premise: noSuchChecks — a block comment carries a marker too -/",
    "  -- premise: noSuchChecks — as the premise: liveChecks reads",
    "  -- (premise: noSuchChecks — a parenthesis is prose)",
    "  /- premise: none -/",
    "  /- premise: liveChecks -/",
    "  say \"premise: liveChecks — x\" -- premise: noSuchChecks — a string is no pin"]
  let premiseGot := premiseFaults resolves markerSrc
  unless premiseGot == #[(1, some "noSuchChecks"), (3, some "noSuchChecks"), (5, none),
      (6, some "noSuchChecks"), (12, some "noSuchChecks"), (13, some "noSuchChecks"), (15, none),
      (16, none), (17, some "noSuchChecks")] do
    fails.modify (s!"premiseFaults: {premiseGot}" :: ·)
  unless conservesFaults (markerSrc.push "/- conserves: none -/") == #[10, 11, 18] do
    fails.modify (s!"conservesFaults: {conservesFaults markerSrc}" :: ·)
  let site := "  if ctx.picTool.isSome && pic.shapes.isEmpty then"
  unless premiseMarkedAt #["  -- premise: liveChecks — the suite runs it", site] 1 &&
      premiseMarkedAt #["  /- premise: liveChecks — the suite runs it -/", site] 1 &&
      !premiseMarkedAt #["  -- (premise: liveChecks — a parenthesis is prose)", site] 1 &&
      !premiseMarkedAt #["  -- premise: liveChecks", site] 1 &&
      !premiseMarkedAt #["  /- premise: liveChecks -/", site] 1 do
    fails.modify ("premiseMarkedAt read a marker it should not, or missed one" :: ·)
  let walk := "def keepFor (t : String) (xs : Array Block) : Array Block :="
  unless conservedAt #["-- conserves: none — fills a hole", walk] 1 &&
      !conservedAt #["-- (conserves: none)", walk] 1 do
    fails.modify ("conservedAt read a marker it should not, or missed one" :: ·)

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

  let siteCase (name : String) (src : List String) (want : Option PremiseKind) : IO Unit := do
    if premiseSite src.toArray 0 != want then
      fails.modify (s!"premiseSite {name}" :: ·)
  siteCase "configuration-gated diagnostic"
    ["  if ctx.picTool.isSome && pic.shapes.isEmpty then",
     "    warnOnce ctx key .N0023 msg pos",
     "    return blocks"] (some .gate)
  siteCase "configuration-gated silence"
    ["    if Compat.nativeSetCtrls.contains name ||",
     "        (s.ctx.picTool.isSome && Compat.boundaryCtrls.contains name) then",
     "      return s",
     "    warnOnce s.ctx (\"ctrl:\" ++ name) .W0301 msg pos"] (some .silence)
  siteCase "computed demotion"
    ["      (demote := Compat.styInternal ctx.file name)"] (some .demote)
  siteCase "the condition is the loss"
    ["  unless dropped.isEmpty do",
     "    say .W0104 s!\"dropped {dropped}\" pos"] none
  siteCase "a content condition naming its own loss"
    ["  if b.kind.isNone && refFormNeedsKind form then",
     "    diag ctx .W0380 msg (some rpos)"] none
  siteCase "configuration read, no loss named"
    ["  if ctx.slides then",
     "    blocks := blocks.push (.frame title inner)"] none
  siteCase "configuration-gated return, no loss below"
    ["  if ctx.literalText then",
     "    return st",
     "  pure (flatten st)"] none
  -- A stated blind spot: a setup read through a local is not seen.
  siteCase "a knob hoisted into a local is not seen"
    ["  if picTool0.isNone then",
     "    say .W0334 s!\"picture key '{k}' is not read\" pos"] none

  expect "hexRespell" hexRespell [
    ("  let digits := \"0123456789abcdef\".toList", true),
    ("    c.isDigit || ('a' ≤ c && c ≤ 'f')", true),
    ("    ('A' ≤ c && c ≤ 'F')", true),
    ("  let d := Hex.digit? c", false),
    ("  -- a 0123456789abcdef table in a comment", false)]

  expect "scaleStepRespell" scaleStepRespell [

    ("  let markSize := around * ((Ir.sizeScale.lookup \"scriptsize\").getD 700) / 1000", true),
    ("  milliFactor ((Ir.sizeScale.lookup name).getD 1000) ++ unit", true),
    ("  | .size n => match Ir.sizeScale.lookup n with", false),
    ("  let s := Ir.scaleStepIn ladder base n", false),
    ("  -- sizeScale.lookup … .getD quoted in a comment", false),
    ("  say s!\"a message naming sizeScale.lookup and .getD\"", false)]

  for f in judgeFiles do
    unless gates.any fun g => g.applies f && g.flag "import LeanTex.Core.Pdf" do
      fails.modify (s!"writerReach gate does not cover {f}" :: ·)

  expect "writerReach" writerReach [
    ("import LeanTex.Core.Pdf", true),
    ("public import LeanTex.Core.Pdf", true),
    ("import all LeanTex.Core.Pdf", true),
    ("open LeanTex.Core.Pdf in", true),
    ("  let s := Pdf.write geom fs pages", true),
    ("  let s := LeanTex.Core.Pdf.keepFaces fs pages", true),
    ("import LeanTex.Core.PdfRead", false),
    ("open LeanTex.Core.PdfRead", false),
    ("  let es ← PdfRead.objects b", false),
    ("  -- Pdf.write spells its dictionaries as strings", false)]

  expect "bareStateMutation" bareStateMutation [
    ("  modify fun st => { st with themed := true }", true),
    ("    modify fun st => { st with file := f }", true),
    ("      set { st with diags := st.diags.push d }", true),
    ("  write fun st => { st with themed := true }", false),
    ("  -- modify in a comment is prose", false),
    ("`palatino` set rm/sf/tt whole, `helvet` one slot,", false),
    ("  say .W0104 s!\"'x' would set the page\" pos", false),
    ("  let offset := 3", false),
    ("  (\"setspace\", 0)", false),
    ("  setlist := true", false)]

  expect "splitOnIdiom" splitOnIdiom [
    ("  let has (hay needle : String) : Bool := (hay.splitOn needle).length > 1", true),
    ("  let has (page s : String) : Bool := (page.splitOn s).length ≥ 2", true),
    ("  let has (n : String) : Bool := (page.splitOn n).length ≥ 2", true),
    ("    ((mutedPage.splitOn \"u-muted\").length == 2)", false),
    ("  let has := hasStr page", false),
    ("  let parts := (l.splitOn \"+\")", false),
    ("  let once (s : String) : Bool := (page.splitOn s).length == 2", false),
    ("  -- let has (hay needle : String) : Bool := (hay.splitOn needle).length > 1", false)]

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
  unless scopedDefNames #["namespace Tests", "mutual", "def walk := 1", "end", "def after := 2",
      "end Tests"] == #["Tests.walk", "Tests.after"] do
    fails.modify ("scopedDefNames: a mutual block's end closed the namespace" :: ·)
  unless scopedDefNames #["namespace Tests.Inner", "def inner := 1", "end Inner", "def outer := 2",
      "end Tests", "def top := 3"] == #["Tests.Inner.inner", "Tests.outer", "top"] do
    fails.modify ("scopedDefNames: a dotted namespace did not close one component at a time" :: ·)
  unless scopedDefNames #["namespace Tests", "section A.B", "def inside := 1", "end A.B",
      "/-- end of a sentence", "section page after page -/", "def after := 2", "end Tests"] ==
      #["Tests.inside", "Tests.after"] do
    fails.modify ("scopedDefNames: a dotted section, or prose, moved a scope" :: ·)
  unless scopedDefNames #["namespace Tests", "def a := r\"\\\"", "def b := r#\"x\"y\"#",
      "def c := 3", "end Tests", "def top := 4"] == #["Tests.a", "Tests.b", "Tests.c", "top"] do
    fails.modify ("scopedDefNames: a raw string hid the code after it" :: ·)
  unless failureListWrite "  let t (name : String) (ok : Bool) := unless ok do ref.modify (name :: ·)" &&
      failureListWrite "    unless ok do failures.modify (s!\"PDF: {name}\" :: ·)" &&
      !failureListWrite "      calls.modify (· + 1)" && !failureListWrite "  check ref name ok" do
    fails.modify ("failureListWrite: a failure-list write went unread, or a counter read as one" :: ·)
  unless (theoremNames "theorem foo.{u} : True\ntheorem append_chain₂ : True").toList.all
      (["foo", "append_chain₂"].contains ·) do
    fails.modify ("theoremNames misread a universe suffix or a subscript" :: ·)

  expect "quadraticPrepend" quadraticPrepend [
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
    ("  | x :: rest => inlineNodes cfg (acc ++ inlineNode cfg x) rest", false),
    ("  | b :: rest => blockNodes cfg (acc.push (blockNode cfg b)) rest", false),
    ("  base ++ plus ++ minus", false),
    ("      | other => s := s ++ rawSrcOne other", false),
    ("        | some i => out.extract 0 i ++ running ++ out.extract i out.size", false),
    ("    s!\"{ind}styled {st.label}\\n\" ++ dumpInlines (ind ++ \"  \") body", false),
    ("        chosen := chosen ++ [b]", false),
    ("  | x :: rest => #[x] ++ rest", false)]

  expect "classNameCompare" classNameCompare [
    ("  if doc.docClass.name == \"article\" then", true),
    ("    (d.docClass.name == cls)", true),
    ("  match doc.docClass with", false),
    ("    say s!\"class {doc.docClass.name} has no chapter pages\"", false),
    ("  -- a comment naming docClass.name == article does not count", false),
    ("    (\"docClass.name == inside a string\", true),", false)]

  expect "nativePackages parse" (fun s => (nativePackagesOf s).toList
      == ["geometry", "natbib"]) [
    ("def other : List String := [\"nope\"]\n" ++
     "def nativePackages : List String :=\n  [\"geometry\",\n   \"natbib\"]\n" ++
     "def after : String := \"also-not-a-package\"", true)]

  expect "conflictMarker" conflictMarker [
    (mkOurs ++ " HEAD", true),
    (mkTheirs ++ " theirs", true),
    (mkBase ++ " merged common ancestors", true),
    (mkOurs, true),
    (mkBase, true),
    ("=======", false),
    (mkOurs ++ "<", false),
    ("<<<" ++ "<<<", false),
    ("a " ++ mkTheirs, false),
    ("  " ++ mkOurs ++ " HEAD", false),
    (mkOurs ++ "quoted", false)]

  let d := "+++ b/PLAN.md\n@@ -3,0 +4,3 @@\n+prose\n+" ++ mkOurs ++ " HEAD\n+more"
  if conflictMarkers d != #[("PLAN.md", 5, mkOurs ++ " HEAD")] then
    fails.modify ("conflictMarkers missed or misattributed the PLAN.md case" :: ·)
  let base := mkBase ++ " parent of 0123abc (Land the slice)"
  let md := "+++ b/docs/log.md\n@@ -0,0 +1,7 @@\n+Title\n+=======\n+" ++ mkOurs ++ " HEAD\n+ours\n+"
    ++ base ++ "\n+theirs\n+" ++ mkTheirs ++ " wt/slice"
  if conflictMarkers md != #[("docs/log.md", 3, mkOurs ++ " HEAD"), ("docs/log.md", 5, base),
      ("docs/log.md", 7, mkTheirs ++ " wt/slice")] then
    fails.modify ("conflictMarkers on the diff3 Markdown case: wrong hits or a setext fire" :: ·)

  expect "plainPath" plainPath [
    ("testdata/corpus/a-b_c.tex", true),
    ("scripts/hooks/pre-commit", true),
    ("LeanTex/Core/Oklab.lean", true),
    ("testdata/corpus/a b.tex", false),
    ("arnings name the native spelling\",+12p", false),
    ("notes=draft.md", false),
    ("testdata/corpus/r\u00e9sum\u00e9.tex", false),
    ("a\nb.tex", false),
    ("", false)]
  let ns := "0\t0\tempty.txt\x00" ++ "12\t0\ttestdata/corpus/a-b_c.tex\x00"
    ++ "0\t0\ta b\x00" ++ "-\t-\ttestdata/corpus/pic.png\x00"
  if addedPathFaults ns != #[("empty.txt", "empty file"),
      ("a b", "characters outside [A-Za-z0-9._/-]"), ("a b", "empty file")] then
    fails.modify ("addedPathFaults: wrong hits on the empty/mangled/plain/binary case" :: ·)
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
  unless rangeCommits "main...tip" == #["tip", "--not", "main"] &&
      rangeCommits "a..b" == #["b", "--not", "a"] && rangeCommits "a.." == #["HEAD", "--not", "a"] do
    fails.modify ("rangeCommits: a range's commits are its tip's, not its base's" :: ·)
  unless (ruleDocText "AGENTS.md" ⟨#[0x23, 0xFF]⟩).2.isSome &&
      ruleDocText "AGENTS.md" "## Rules\n".toUTF8 == ("## Rules\n", none) &&
      (docHeadings (ruleDocText "AGENTS.md" ⟨"## Rules\n".toUTF8.data.push 0xFF⟩).1) == ["Rules"] do
    fails.modify ("ruleDocText: a rule document's encoding fault, and its headings kept" :: ·)
  let cased := caseCollisions #["Tests/Parser.lean", "tests/Extra.md", "README.md", "readme.md",
    "A/b.lean", "a/c.lean"]
  let touched := collisionsTouching #["tests/Extra.md", "readme.md"] cased
  unless touched == #[("README.md", "readme.md"), ("Tests", "tests")] do
    fails.modify (s!"collisionsTouching: an added path's own or directory collision: {touched}" :: ·)
  unless (collisionsTouching #["other.md"] cased).isEmpty do
    fails.modify ("collisionsTouching: kept a collision no added path takes part in" :: ·)

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
  -- An added line whose text opens `++ ` reads `+++ …` in the hunk and is no file header.
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

  expect "datedStory" datedStory [
    ("the allowance list emptied on 2026-09-19 and stays empty", true),
    ("see PLAN for the history", true),
    ("v4.34.1, 2^24 inputs, 30 min, U37", false),
    ("a PLANE figure, a plan file", false)]
  let cap : List DocCap := [{ doc := "D.md", lines := 3, width := 10, bytes := 40 }]
  let capCases : List (String × Nat) := [
    ("- a\n- b\n- c\n", 0), ("- a\n- b\n- c\n- d\n", 1),
    ("- a rule too wide\n", 1), (String.join (List.replicate 3 "- abcdefgh\n") ++ "", 0),
    ("- abcdefgh\n- abcdefgh\n- abcdefghi\n" ++ "", 1), ("x".pushn 'y' 50, 2)]
  for (text, want) in capCases do
    unless (capFaults "D.md" text cap).size == want do
      fails.modify (s!"capFaults: {(capFaults "D.md" text cap).size} faults for {repr text}" :: ·)
  unless (capFaults "Other.md" ("x".pushn 'y' 500) cap).isEmpty do
    fails.modify ("capFaults: a document with no cap row was capped" :: ·)
  unless datedLines "a\nemptied on 2026-09-19\nb\n" == #[(2, "emptied on 2026-09-19")] do
    fails.modify (s!"datedLines: {datedLines "a\nemptied on 2026-09-19\nb\n"}" :: ·)
  let vendoredTree := #["testdata/external/x/PROVENANCE.txt", "testdata/external/x/a/README.md",
    "testdata/externalia.md", "README.md"]
  unless vendoredRoots vendoredTree == #["testdata/external/x/"] &&
      vendored (vendoredRoots vendoredTree) "testdata/external/x/a/README.md" &&
      !vendored (vendoredRoots vendoredTree) "testdata/externalia.md" &&
      !vendored (vendoredRoots vendoredTree) "README.md" do
    fails.modify (s!"vendoredRoots: {vendoredRoots vendoredTree}" :: ·)
  -- Pointers are spelled through `sectionMark` so this file's own text holds none.
  let ag := "AGENTS.md" ++ sectionMark
  let refCases : List (String × Array (String × String)) := [
    (s!"  stands ({ag} When you add): a loose", #[("AGENTS.md", "When you add")]),
    (s!"the registry (`{ag} Naming`) and {ag} Lean rules.",
      #[("AGENTS.md", "Naming"), ("AGENTS.md", "Lean rules")]),
    (s!"names follow {ag} Naming (`conservesSuffixes`)", #[("AGENTS.md", "Naming")]),
    (s!"  ({ag} Principles, 14)", #[("AGENTS.md", "Principles")]),
    (s!"(PRINCIPLES.md{sectionMark} Rules are checks)", #[("PRINCIPLES.md", "Rules are checks")]),
    (s!"defers to {ag}", #[("AGENTS.md", "")]),
    ("names AGENTS.md in prose and no section", #[])]
  for (l, want) in refCases do
    unless sectionRefs l == want do
      fails.modify (s!"sectionRefs {l}: got {sectionRefs l}" :: ·)
  let heads := [("AGENTS.md", docHeadings "# T\n\n## Lean rules\n\ntext\n## When you add\n")]
  let srcs := #[("a.lean", s!"-- ({ag} Lean rules)\n-- ({ag} Conventions)\n"),
    ("b.md", s!"see {ag} When you add.\n")]
  unless danglingSectionRefs heads srcs == #[("a.lean", 2, ag ++ " Conventions")] do
    fails.modify (s!"danglingSectionRefs: {danglingSectionRefs heads srcs}" :: ·)
  unless sectionRefs s!"a docstring ending at {ag} Lean rules -/" == #[("AGENTS.md", "Lean rules")] do
    fails.modify ("sectionRefs: a comment close read as part of the heading" :: ·)
  let src := "def a := \"x -- y\" -- one\n/-- two\n  three -/\ndef b := '\"' -- four\n\
    def c := \"five\\\n  six\" /- seven /- eight -/ nine -/\n"
  unless leanProse src == #[" one", " two", "  three ", " four", "", " seven  eight  nine ", ""] do
    fails.modify (s!"leanProse: {leanProse src}" :: ·)
  -- Literals, comments and identifiers as Lean reads them.
  expect "ioInCore through a quote's literal" ioInCore [
    ("  if c == '\"' then IO.println s", true),
    ("  let b := !'\"'.isWhitespace; IO.println b", true),
    ("  let b := !r#\"a\"b\"#.isEmpty; IO.println b", true)]
  expect "identityArm past a block comment" identityArm [("  | other => other /- passes -/", true)]
  expect "repoRefInString past a string's dashes" repoRefInString [
    ("  (help := \"run with --tree; see PLAN.md\")", true),
    -- A stated blind spot: a line closing a string an earlier line opened reads its comment as text.
    ("    the content is dropped\" pos -- see LeanTex/Core/Elab.lean", true)]
  expect "bannedWord in a block comment or raw string" (bannedWord kwPartial) [
    ("def x := 1 /- not " ++ kwPartial ++ " -/", false),
    ("  let s := r#\"a \"" ++ kwPartial ++ "\" b\"#", false)]
  expect "walkEntry after a one-line docstring" (fun l => (walkEntry l).isSome)
    [("/-- d -/ def w (xs : Array Block) : Array Block := xs", true)]
  let quoteLit := #["def q := '\"'", "def r := 1"]
  unless codeOnly quoteLit == #["def q :=  ", "def r := 1"] do
    fails.modify (s!"codeOnly: a quote's literal: {codeOnly quoteLit}" :: ·)
  let indexProof := #["xs[i]'h'"]
  unless codeOnly indexProof == indexProof do
    fails.modify (s!"codeOnly: an index proof's quote: {codeOnly indexProof}" :: ·)
  let rawDashes := "def s := r#\"a\"--b\"#"
  unless leanProse rawDashes == #[""] do
    fails.modify (s!"leanProse: a raw string's dashes: {leanProse rawDashes}" :: ·)
  unless lexView "def s := \"a\\\n   b\"" (· == .strText) == #["a", "b"] do
    fails.modify ("lexView: a gap's indentation read as text" :: ·)
  let trailingGap := "  let s := \"a\\"
  unless stringsOnly trailingGap == " a" do
    fails.modify (s!"stringsOnly: a trailing gap: {stringsOnly trailingGap}" :: ·)
  unless premisePin ("  -- " ++ premiseMark ++ " none — \"why\"") == some (none, "\"why\"") do
    fails.modify ("premisePin: a quoted reason read as a literal" :: ·)
  -- A stated blind spot: an interpolation's nested string reads as closing its string.
  unless stripComments "  let t := s!\"{g \"--\"} x\"" == "  let t := s!\"{g \"" do
    fails.modify ("stripComments: an interpolation's nested string" :: ·)
  let plusPlus := "diff --git a/x.lean b/x.lean\n--- a/x.lean\n+++ b/x.lean\n@@ -0,0 +1,2 @@\n\
    +first\n+++ b/y.lean\n"
  unless addedByFile plusPlus == #[("x.lean", #["first", "++ b/y.lean"])] do
    fails.modify ("addedByFile: an added line beginning ++ b/ read as a file header" :: ·)
  expect "narrativeMarks" (fun l => !(narrativeMarks l).isEmpty) [
    ("fixes the gap (R149)", true),
    ("measured on 2026-09-19", true),
    ("fails at `f66f9381`", true),
    ("the reviewer's shape", true),
    ("a must-fix of the audit", true),
    ("as the review found", true),
    ("found in the second round", true),
    ("the walk once took the lead", true),
    ("the bar once silently dropped", true),
    ("the HTML once\n drew a rule", true),
    ("it was once the other way round", true),
    ("the page used to declare its size", true),
    ("expressions previously collapsed", true),
    ("each warning is named once, with its count", false),
    ("read once per element, at once", false),
    ("ships once the preamble ends", false),
    ("Once parsed, the group stands; the value, once set, stays set", false),
    ("a once-latch per code", false),
    ("the key is used to look up the role; the extent, used to project", false),
    ("keeps all previously emitted fields", false),
    ("W0301 names it; owed (U37) delivers it", false),
    ("the colour #1f77b4ff, Lean v4.34.1, 20261013 and a decade", false),
    ("the `.reviewer` state and the `once` latch", false),
    (" premise: fooChecks — named by the elaborator once, with no placeholder", false),
    (" conserves: none — fills a hole; the output census is a mix", false),
    ("the gap R149's fix and rows R12-R14", true),
    ("at f66f9381's tip", true),
    ("a code-review note", true),
    ("peer-reviewed", true),
    ("the Reviewed-by trailer", true),
    ("in round two", true),
    ("the 2nd round", true),
    ("round-2 notes", true),
    ("a second-round finding", true),
    ("Round 3 found it", true),
    ("review NIT: the label", true),
    ("(review LP-5)", true),
    ("the parity review reproduced it", true),
    ("an adversarial review", true),
    ("the parser once rewrote it", true),
    ("it once forgot the tail", true),
    ("the table once shrank", true),
    ("the reviewed list, the reviewed tip and the reviewed-list check", false),
    ("which review holds; not by review; it stays review's job", false),
    ("the 110 dpi review raster", false),
    (" premise: none — review holds it", false),
    ("the first round of glue and a second round trip", false),
    ("a dashed frame fitted round two nodes, and the round-bottomed 3", false),
    ("a record such as `2026-01-31`", false),
    ("how many names it shows once truncated (`uniquelist`)", false),
    ("judged once shipped), never named", false)]
  let docCase (what text : String) (added want : List Nat) : IO Unit := do
    let got := docFindings text added.toArray
    unless got.toList.map (·.1) == want do
      fails.modify (s!"docFindings, {what}: got {got}, want lines {want}" :: ·)
  docCase "a four-line docstring" "/-- one\ntwo\nthree\nfour -/\ndef x := 1\n" [2] [1]
  docCase "three lines" "/-- one\ntwo\nthree -/\ndef x := 1\n" [1, 2, 3] []
  docCase "blank prose lines" "/--\none\ntwo\nthree\n-/\ndef x := 1\n" [2] []
  docCase "an untouched comment" "/-- one\ntwo\nthree\nfour -/\ndef x := 1\n" [5] []
  docCase "an edit inside a long comment" "/-- one\ntwo\nthree\nfour\nfive -/\ndef x := 1\n" [2] []
  docCase "a comment grown past three lines" "/-- one\ntwo\nthree\nfour -/\ndef x := 1\n" [4] [1]
  docCase "a run of line comments" "def x := 1\n-- a\n-- b\n-- c\n-- d\n" [5] [2]
  docCase "trailing comments" "def x := 1 -- a\ndef y := 2 -- b\ndef z := 3 -- c\ndef w := 4 -- d\n"
    [1, 2, 3, 4] []
  docCase "a marker on an added line" "/-- one\nthe walk once took two -/\ndef x := 1\n" [2] [2]
  docCase "a marker on a line not added" "/-- one\nthe walk once took two -/\ndef x := 1\n" [1] []
  docCase "a marker in code" "def x := \"the walk once took R149 on 2026-09-19\"\n" [1] []
  docCase "a licence header"
    "module\n/-\nCopyright 2020 Example.\nPermission is granted.\na\nb\n-/\ndef x := 1\n" [3] []
  docCase "a generated header" "module\n\n/-\nGenerated by scripts/gen-x.lean; do not edit.\n\
    Source: x 1.0 (2025-07-10)\na\nb\n-/\nnamespace X\n" [4, 5] []
  docCase "a header after a declaration" "def x := 1\n/-\nGenerated by hand\na\nb\nc\n-/\n" [3] [2]
  unless [rangeTip "origin/main...HEAD", rangeTip "abc..def", rangeTip "abc..", rangeTip "HEAD"] ==
      [some "HEAD", some "def", some "HEAD", none] do
    fails.modify ("rangeTip misread a revision range" :: ·)
  unless [Source.index.newSide, (Source.range "origin/main...HEAD").newSide,
      (Source.range "abc..def").newSide, (Source.range "HEAD").newSide, Source.tree.newSide] ==
      [some ":", some "HEAD:", some "def:", none, none] do
    fails.modify ("Source.newSide named the wrong side of a diff for the citation's texts" :: ·)
  expect "looseRuleRef" looseRuleRef [
    ("(AGENTS.md, Conventions)", true),
    ("per AGENTS: a visual bug", true),
    ("the obligation table's walk row", true),
    ("budget (AGENTS.md), so", true),
    ("convention is AGENTS': the artifact", true),
    ("see PRINCIPLES.md for the rule", true),
    (s!"holds it ({ag} Lean rules)", false),
    ("`AGENTS.md`'s length cap", false),
    ("names THEOREMS.md and nothing else", false)]
  let looseSrcs := #[
    ("a.lean", s!"def x := \"AGENTS.md, a string\" -- see AGENTS.md\n/-- fine ({ag} Lean rules) -/\n"),
    ("b.md", "see AGENTS.md\n```\nAGENTS.md, in a fence\n```\n")]
  unless (looseRuleRefs looseSrcs).map (fun (f, n, _) => (f, n)) == #[("a.lean", 1), ("b.md", 1)] do
    fails.modify (s!"looseRuleRefs: {looseRuleRefs looseSrcs}" :: ·)
  let hookWith (alt : String) : String :=
    "#!/bin/sh\n# comment\ngit diff --cached --name-only | grep -qE '\\.lean$|^PLAN\\.md$|^("
      ++ alt ++ ")\\.md$' \\\n  || exit 0\n"
  unless hookNamePattern (hookWith "AGENTS") == some "\\.lean$|^PLAN\\.md$|^(AGENTS)\\.md$" do
    fails.modify (s!"hookNamePattern: {hookNamePattern (hookWith "AGENTS")}" :: ·)
  unless hookNamePattern "#!/bin/sh\nexit 0\n" == none do
    fails.modify ("hookNamePattern: a hook with no name test yielded a pattern" :: ·)
  let wholeSkips ← hookSkippedDocs (hookWith "AGENTS|PRINCIPLES|THEOREMS")
  unless wholeSkips.isEmpty do
    fails.modify (s!"hookSkippedDocs: the whole alternative skipped {wholeSkips}" :: ·)
  let partSkips ← hookSkippedDocs (hookWith "AGENTS|THEOREMS")
  unless partSkips == ["PRINCIPLES.md"] do
    fails.modify (s!"hookSkippedDocs: dropping PRINCIPLES skipped {partSkips}" :: ·)
  unless (← hookSkippedDocs "#!/bin/sh\nexit 0\n") == sectionDocs do
    fails.modify ("hookSkippedDocs: a hook with no name test skipped nothing" :: ·)
  unless !(← hookGreps "^(AGENTS|THEOREMS)\\.md$" "docs/AGENTS.md") do
    fails.modify ("hookGreps: an anchored pattern matched a nested path" :: ·)
  let latin1 ← IO.FS.withTempDir fun dir => do
    let f := dir / "latin1.md"
    IO.FS.writeBinFile f (ByteArray.mk #[0x41, 0xE9, 0x0A])
    try
      let t ← sourceText f
      pure (some t)
    catch _ => pure none
  unless latin1.any (·.startsWith "A") do
    fails.modify ("sourceText: a source holding bytes that are not UTF-8 was not read" :: ·)

  expect "bannedWord" (bannedWord kwPartial) [
    ("+" ++ kwPartial ++ " def foo : Nat := 0", true),
    ("+  " ++ kwPartial ++ " def go (l : List Nat) : Nat := go l", true),
    ("+   (\"" ++ kwPartial ++ "\", .ord, '𝜕'),", false),
    ("+    say s!\"a message naming " ++ kwPartial ++ " in prose\"", false),
    ("+  -- a comment naming " ++ kwPartial ++ " does not count", false),
    ("+  let " ++ kwPartial ++ "Sums := 3", false)]

  expect "ctorDefault" ctorDefault [
    ("+  | run (label : String := \"unnamed\") : Cmd", true),
    ("+  | mk (a : Nat) (f : Nat → Nat := fun _ => 0) : T", true),
    ("+  | `.run a b c` := what the pattern matched | the whole suite green |", false),
    ("+  | x => go (n := 3) rest", false),
    ("+  | x => { s with field := v }", false),
    ("+  | .text s => s", false)]

  -- These predicates read lines with the `+` stripped.
  expect "tempRootOutsideHost" tempRootOutsideHost [
    ("    let result ← try IO.FS.withTempDir fun dir => do", true),
    ("  let dir ← IO.FS.createTempDir", true),
    ("  let (h, path) ← IO.FS.createTempFile", true),
    ("  IO.FS.withTempFile fun h path => do", true),
    ("    Host.withScratch fun work => do", false),
    ("  -- IO.FS.withTempDir crashes here", false),
    ("  let note := \"withTempDir\"", false)]

  expect "clockBound" clockBound [
    ("    (sharedMs < 1500)", true),
    ("  t s!\"families is linear ({ms} ms for {many.size} faces)\" (ms < 200)", true),
    ("    (inkReads == 100000 && inkMs < 500)", true),
    ("    (mergeMs < 800)", true),
    ("    (judgeMs < 1500)", true),
    ("    (paleMs < 400)", true),
    ("      check ref \"bounded\" (elapsed <= 2000)", true),
    ("  t \"answered in time\" (spent ≤ 4000)", true),
    ("    (sharedMs < hangGuardMs 250)", false),
    ("  t \"within the budget\" (ms ≤ budget + grace + hostMarginMs)", false),
    ("  while !finished && (← IO.monoMsNow) < deadline do", false),
    ("  t \"few items\" (items < 3)", false),
    ("  -- the old check read (ms < 200)", false),
    ("  t \"(ms < 200) names the old bound\" true", false)]

  expect "childRunBypass" childRunBypass [
    ("    let r ← RunBounded.runBounded lean.toString #[\"--run\"] dir 30000 100", true),
    ("      let result ← RunBounded.output {", true),
    ("    let r ← childRun 900 lean.toString #[\"--run\", driver.toString] dir", false),
    ("example : IO.Process.SpawnArgs → IO IO.Process.Output := RunBounded.output", false),
    ("  -- RunBounded.runBounded holds each run to its budget", false),
    ("    statement := \"RunBounded.runBounded holds each tool run to a budget\"", false)]

  expect "ioInCore" ioInCore [
    ("def scan (roots : List String) : IO (Array Face) := do", true),
    ("    let bytes ← IO.FS.readBinFile path", true),
    -- A stated blind spot: a block comment's continuation line reads as code.
    ("continuation line of a block comment naming IO", true),
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

  let gated (file line : String) : Bool := gates.any fun g => g.applies file && g.flag line
  let autolink := "  | .link url _ => acc " ++ patAppend ++ " \"<\" " ++ patAppend ++
    " url " ++ patAppend ++ " \">\""
  for (file, line, want) in [
      ("LeanTex/Core/HtmlDoc.lean", autolink, true),
      ("LeanTex/Core/MarkdownDoc.lean", autolink, false),
      ("LeanTex/Core/MarkdownDoc.lean", "public import LeanTex.Core.Ir", false),
      ("LeanTex/Cli/PictureAssets.lean", "  let (h, path) ← IO.FS.createTempFile", true),
      ("Main.lean", "  IO.FS.withTempFile fun h path => pure ()", true),
      ("LeanTex/Cli/Host.lean", "  let dir ← IO.FS.createTempDir", false),
      ("scripts/zz.lean", "  IO.FS.withTempDir fun dir => pure ()", false),
      ("Tests/Zz.lean", "  IO.FS.withTempDir fun dir => pure ()", false)] do
    if gated file line != want then
      fails.modify (s!"gates on {file} {if want then "missed" else "fired on"}: {line}" :: ·)

  expect "tagStringEmit" tagStringEmit [
    ("    let open' := \"<\" " ++ patAppend ++ " tag " ++ patAppend ++ " attrString attrs", true),
    ("  out := out " ++ patAppend ++ " \"<\"" ++ patAppend ++ "tag", true),
    ("  \"<!DOCTYPE html>\\n\" " ++ patAppend, false),
    ("  if c == '<' then out := out " ++ patAppend ++ " \"&lt;\"", false),
    ("  s := s " ++ patAppend ++ " s!\"<{hex4 g}> <{utf16Hex c}>\\n\"", false),
    ("  -- writing \"<\" " ++ patAppend ++ " tag is banned here", false)]

  expect "fontScanInTest" fontScanInTest [
    ("  let faces ← FontDiscovery.scan (cfg.fontDirs.toList ++ (← texFontDirs))", true),
    ("  let faces ← FontDiscovery.scan", true),
    ("  let shipped ← FontDiscovery.scanRoots [testFonts]", false),
    ("  -- FontDiscovery.scan here would break hermeticity", false),
    ("  t \"a message naming FontDiscovery.scan stays data\" true", false)]

  expect "undecodedRead" undecodedRead [
    ("      sources := sources.push (src, ← IO.FS.readFile path)", true),
    ("          let text ← IO.FS.readFile path", true),
    ("    match ← readSource path.toString with", false),
    ("  -- IO.FS.readFile would throw on Latin-1 bytes", false),
    ("  t \"a message naming IO.FS.readFile stays data\" true", false)]

  expect "undecodedFixture" undecodedFixture [
    ("    let (d, _) ← elabFixture n (← IO.FS.readFile s!\"testdata/corpus/{n}.tex\")", true),
    ("  let (raws, _) := Surface.read .tex file (← IO.FS.readFile path)", true),
    ("  let (doc, _) ← elabInputSrc path (← IO.FS.readFile path)", true),
    ("  let (doc, ds) := Elab.runRaws file raws (← IO.FS.readFile path).length", true),
    ("    let (d, _) ← elabFixture n (← fixtureText path)", false),
    ("  let pins ← IO.FS.readFile path", false),
    ("  -- elabFixture n (← IO.FS.readFile path) reads past the door", false)]

  expect "frontEndRestated" frontEndRestated [
    ("  let (executed, inputDiags, _) ← Input.expandInputs file raws", true),
    ("  let (executed, ds, _) ← LeanTex.Cli.Input.expandInputs file raws", true),
    ("  let (raws, dataDiags) ← Input.resolveData file executed.raws", true),
    ("  let (executed, log) ← (Elab.executeInputs (readAt dir file 8) file raws).run {}", true),
    ("  let (doc, _) := Elab.run file (← IO.FS.readFile file)", true),
    ("    let (raws, ds) := Md.read file (← IO.FS.readFile path)", true),
    ("  let (doc, ds) ← elabFixture stem (← IO.FS.readFile path)", true),
    ("  let (doc, ds) := Elab.runExecuted file src.executed src.diags", false),
    ("  let src ← Input.readDocument file bytes", false),
    ("  -- Input.expandInputs runs inside the front door", false),
    ("  t \"a message naming Input.expandInputs stays data\" true", false)]

  expect "irDumpUnmarked" irDumpUnmarked [
    ("    let out := Ir.dump doc diags", true),
    ("        ((Ir.dumpBlocks \"\" nbody).splitOn \"never shown\").length == 2", true),
    ("    let out := Ir.dump doc diags " ++ irTierMark ++ " goldens witness elaboration", false),
    ("  -- Ir.dump is rejected in tests without a tier", false),
    ("  t \"a message naming Ir.dump stays data\" true", false)]

  expect "heartbeatRaise" heartbeatRaise [
    ("set_option " ++ kwMaxHeartbeats ++ " 400000", true),
    ("  set_option " ++ kwMaxHeartbeats ++ " 1000000 in", true),
    ("set_option " ++ kwMaxHeartbeats ++ " 0 in", true),
    ("  withOptions (" ++ kwMaxHeartbeats ++ ".set · 2000)", true),
    ("set_option synthInstance." ++ kwMaxHeartbeats ++ " 100000 in", true),
    ("set_option " ++ kwMaxHeartbeats ++ " 2000 in set_option synthInstance." ++
      kwMaxHeartbeats ++ " 100000 in", true),
    ("set_option " ++ kwMaxHeartbeats ++ " 2000 in", false),
    ("-- " ++ kwMaxHeartbeats ++ ": zero sites in the tree", false),
    ("  say s!\"raise " ++ kwMaxHeartbeats ++ "\"", false),
    ("set_option maxRecDepth 8192", false)]

  expect "wildcardThrough" wildcardThrough [
    ("  | _ => out", true),
    ("  | other => other", true),
    ("  | x => x", true),
    ("  | none => acc", false),
    ("  | nil => simp [textLeavesTableCells]", false),
    ("  | _ => false", false),
    ("  | _ => none", false),
    ("  | _ => break", false),
    ("  | .text s => s", false),
    ("  | other => cur := cur.push other", false),
    ("  | _ => 1", false)]

  if bangCount #["let x := xs[i]!", "-- xs[i]! in a comment",
      "say \"xs[i]! quoted\"", "ys[j]! + zs[k]!"] != 3 then
    fails.modify ("bangCount miscounted the mixed sample" :: ·)

  expect "identityArm" identityArm [
    ("  | other => other", true),
    ("  | x => x", true),
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
    ("  | _ => \"mono\"", false),
    ("  | _ => geom.fontSize", false),
    ("  | .verbatim _ => 1", false),
    ("  | [] => 1", false)]

  expect "dimLiteral" dimLiteral [
    ("  | 1 => pt 14", true),
    ("        fun g => (a.resolve g).width).getD (pt 1)", true),
    ("  vmargin := Dim.mm 9", true),
    ("  if w > inch 1 then", true),
    ("  let floor := Dim.mm100 140", true),
    ("  pageW : Sp := pt 612 -- US letter, the class default", false),
    ("  let w := scaledAt size font (font.advance c)", false),
    ("  let s := v.toPtString", false),
    ("  let g := (a.resolve tok).width", false),
    ("  let mmNames := [\"mm\", \"cm\"]", false)]

  expect "unfinished proof in every source path" (fun f =>
    gates.any fun r => r.applies f && r.flag ("theorem unfinished : True := by " ++ kwSorry)) [
    ("LeanTex/Core/Probe.lean", true),
    ("Tests/Probe.lean", true),
    ("scripts/probe.lean", true),
    ("ExtraProofs.lean", true),
    ("ExtraProofs/Probe.lean", true)]

  expect "walkEntry" (fun l => (walkEntry l).isSome) [
    ("def dimBlocks (cover : Cover) (k : Nat) (xs : Array Block) : Array Block :=", true),
    ("def unwrapItemSteps (xs : Array Block) : Array Block :=", true),
    ("def keepFor (t : String) (xs : Array Block) : Array Block :=", true),
    ("def substPage (n total : Nat) (xs : Array Inline) : Array Inline :=", true),
    ("def fillTemplate (template content : Array Inline) : Array Inline :=", true),
    ("def sneakyWalk (xs : Array Block) : Array Block := xs", true),
    ("public def visibleWalk (xs : Array Block) : Array Block := xs", true),
    ("@[inline] public def visibleWalk (xs : Array Inline) : Array Inline := xs", true),
    ("noncomputable public def visibleWalk (xs : Array Block) : Array Block := xs", true),
    ("@[simp, inline] public def visibleWalk (xs : Array Inline) : Array Inline := xs", true),
    ("private def helperWalk (xs : Array Block) : Array Block := xs", false),
    ("@[inline] private def helperWalk (xs : Array Block) : Array Block := xs", false),
    ("  def nestedWalk (xs : Array Block) : Array Block := xs", false),
    ("def unwrapItemStepList (out : Array Block) : List Block → Array Block", false),
    ("def bandInlines (b : Array BandSlot) : Array Inline :=", false),
    ("def blocksText (xs : Array Block) : String := blockTextList \"\" xs.toList", false),
    ("private def raggedItems (items : Array Item) : Array Item :=", false),
    ("  -- def fake (xs : Array Block) : Array Block, quoted in a comment", false)]

  expect "conservesReason" (fun l => (conservesReason l).isSome) [
    ("-- conserves: none — fills a hole; the output census is a mix", true),
    ("  -- conserves: none — the walk edits only image alt text", true),
    ("-- conserves:none — the space is optional", true),
    ("-- conserves everything", false),
    ("-- conserves: nonesuch — not the refusal", false),
    ("/- conserves: none -/", false),
    ("def keepFor (t : String) (xs : Array Block) : Array Block :=", false)]

  expect "repoRefInString" repoRefInString [
    ("      (help := \"the rest of M6; see PLAN.md\")", true),
    ("      (help := \"there is no Lua here; see PLAN.md for the native declarations\")", true),
    ("            (help := s!\"planned for {milestone}; see PLAN.md\" ++", true),
    ("  say .W0104 \"planned for M8\" pos", true),
    ("  let msg := \"stated in AGENTS.md\"", true),
    ("  let msg := \"see THEOREMS.md for the proof\"", true),
    ("  fail s!\"see LeanTex/Core/Diag.lean\"", true),
    ("  -- planned for M8, tracked in PLAN.md", false),
    ("/-- the registry row's why lives in PLAN.md -/", false),
    ("  let milestone := reservedCtrl.lookup name", false),
    ("      (help := \"\\\\allow{E0333} accepts the loss\")", false),
    ("    \"'{tikzpicture}' is not implemented yet; its content is not rendered\"", false),
    ("  say .W0104 \"a 10mm margin\" pos", false),
    ("  let m8 := M8.compute x", false)]

  expect "demotedAssign" demotedAssign [
    ("    ({ d with " ++ kwDemotedAssign ++ " true }, true)", true),
    ("  let d : Diag := { kind := k, " ++ kwDemotedAssign ++ " quiet }", true),
    ("  -- " ++ kwDemotedAssign ++ " comes only from \\allow, never a call site", false),
    ("  say s!\"a string naming " ++ kwDemotedAssign ++ " x\"", false),
    ("  match d.demoted with", false)]

  expect "undeclaredConfigRead" undeclaredConfigRead [
    ("          mathRenderer := ui.cfg.mathRenderer", true),
    ("        let hcfg := { css := ui.cfg.cssMode, imgs }", true),
    ("  if cfg.newFlag then", true),
    ("      let emit := ui.cfg.effectiveEmit doc.output.formats", false),
    ("          mathBoundary := ui.cfg.mathBoundary", false),
    ("  if ui.cfg.porcelain then", false),
    ("    let allowAll := ui.cfg.bestEffort", false),
    ("  let faces ← FontDiscovery.scan (cfg.fontDirs.toList ++ (← texFontDirs))", false),
    ("  -- ui.cfg.frobnicate would be rejected here", false),
    ("  say s!\"a message naming cfg.frobnicate\"", false),
    ("  let x := hcfg.mathBoundary", false),
    ("  cfg : Config", false)]

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
    (["--range", "origin/main"], "error --range needs a revision range, e.g. --range origin/main...HEAD"),
    (["-q", "--tree"], "tree")]
  for (argv, want) in srcCases do
    let got := srcShow (parseSource argv)
    if got != want then
      fails.modify (s!"parseSource {argv}: got {got}, want {want}" :: ·)
  if (Source.index).diffSel != some #["--cached"] then
    fails.modify ("Source.index.diffSel" :: ·)
  if (Source.tree).diffSel != none then
    fails.modify ("Source.tree.diffSel" :: ·)

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
    ["trigger", "recovery", "detail", "output"].flatMap fun field =>
      -- Each uses a permitted writer, so only the field rule can reject it.
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

  let runs := addedRuns #[("a", 3, "x"), ("a", 4, "y"), ("a", 7, "z"), ("b", 8, "w")]
  unless runs == #[("a", 3, "x\ny"), ("a", 7, "z"), ("b", 8, "w")] && addedRuns #[] == #[] do
    fails.modify ("addedRuns did not join consecutive lines of one file, and only those" :: ·)
  let batch := "0a1b blob 3\nabc\nnope missing\n0c2d blob 0\n\n".toUTF8
  unless (parseBatch batch 3).map (·.toList) == #["abc".toUTF8.toList, [], []] do
    fails.modify ("parseBatch did not split a batch answer into its objects" :: ·)
  unless splitFirst "a\tb\tc" "\t" == some ("a", "b\tc") && splitFirst "abc" "\t" == none do
    fails.modify ("splitFirst did not cut at the first separator alone" :: ·)
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

  for (what, file, source, bad) in [
      ("the markdown reader", "LeanTex/Cli/Input.lean",
        ["  let (sub, ds) := Md.read path text"], true),
      ("the markdown desugaring", "Main.lean", ["  let r := LeanTex.Core.Md.desugar f s"], true),
      ("a hand-built include wrapper", "LeanTex/Cli/Input.lean",
        ["  return (#[.env (Parse.inputEnv path) sub pos], ds)"], true),
      ("the tex lexer", "LeanTex/Cli/Driver.lean", ["  let (toks, ds) := Lex.lex file input"], true),
      ("the tex parser", "LeanTex/Cli/Driver.lean",
        ["  let (raws, ds) := LeanTex.Core.Parse.parse file toks"], true),
      ("a docstring", "LeanTex/Cli/Input.lean", ["/-- `Md.read` is the markdown door -/"], false),
      ("a block comment", "LeanTex/Cli/Input.lean", ["/-- the door", "  Lex.lex then Parse.parse", "-/"],
        false),
      ("a message", "LeanTex/Cli/Input.lean", ["  let name := \"Md.read\""], false),
      ("a longer name", "LeanTex/Cli/Input.lean", ["  if (Parse.inputEnvFile? n).isSome then x"], false),
      ("the door", "LeanTex/Cli/Input.lean", ["  let (raws, ds) := Surface.read .tex file text"], false),
      ("a declared core reader", "LeanTex/Core/Data.lean",
        ["def valParsed (src text : String) : Array Raw × Array Diag :=",
          "  let (toks, lexDiags) := Lex.lex src text"], false),
      ("an undeclared core reader", "LeanTex/Core/Elab.lean",
        ["private def reread (s : String) : Array Raw :=", "  (Parse.parse \"\" (Lex.lex \"\" s).1).1"],
        true),
      ("a declared name in another file", "LeanTex/Core/Ir.lean",
        ["def valParsed (src text : String) : Array Raw :=", "  (Parse.parse src (Lex.lex src text).1).1"],
        true),
      ("the core reading a wrapper's name", "LeanTex/Core/Elab.lean",
        ["private def other (s : String) := Parse.inputEnvFile? s"], false),
      ("the door's own stage", "LeanTex/Core/Surface.lean",
        ["@[expose] public def texLex (file text : String) := Lex.lex file text"], false)] do
    let got := !(surfaceDoorBypasses file source.toArray).isEmpty
    if got != bad then
      fails.modify (s!"surfaceDoorBypasses {what}: got {got}, want {bad}" :: ·)

  let failed := (← fails.get).reverse
  if failed.isEmpty then
    IO.println "precommit selftest: all passed"
    return 0
  for f in failed do
    IO.eprintln s!"FAIL {f}"
  return 1

/-- The compiled stages of the hook in order; a failing stage stops the run with its exit code, its
output redacted. -/
def checkCompiledTree (env : Array (String × Option String) := #[])
    (redact : String → String := id) : IO UInt32 := do
  for (cmd, args) in compiledStages do
    let (code, out, err) ← runBytes cmd args env
    if code != 0 then
      IO.eprintln s!"pre-commit: {cmd} {String.intercalate " " args.toList} failed:"
      IO.eprint (redact (Privacy.textOfBytes out))
      IO.eprint (redact (Privacy.textOfBytes err))
      return code
  return 0

/-- The checks that read the whole tree, which a range leaves to lint. -/
def wholeTreeChecks (say : String → IO Unit) : IO Unit := do
  -- Whole tree: an entry and its index file may land in different hunks.
  if (← System.FilePath.pathExists "LeanTex/Core/Compat.lean") then
    let compatSrc ← IO.FS.readFile "LeanTex/Core/Compat.lean"
    for pkg in nativePackagesOf compatSrc do
      unless (← System.FilePath.pathExists s!"testdata/compat-index/{pkg}.txt") do
        say s!"pre-commit: '{pkg}' is in nativePackages with no testdata/compat-index/{pkg}.txt.
  A nativePackages entry arrives with its index file: the package's
  documented command list, one row per command, the manual section named
  in its header (compatIndexChecks in Tests/Surface.lean states the format);
  lake test probes every row.
  Fix: write testdata/compat-index/{pkg}.txt before adding the entry."

  -- Whole tree: a walk and its census theorem may land in different hunks.
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
    unless hasThm || conservedAt lines i do
      say s!"pre-commit: the IR walk `{name}` ({f}:{i + 1}) has no conservation statement.
  A public Block/Inline walk owes its census fact (AGENTS.md § When you add;
  THEOREMS.md § Naming): a theorem named `{name}_text` (census equality — state it as a
  `Conserves` instance), `{name}_covers`, or `{name}_id` — or, when the
  walk genuinely conserves nothing, the one-line refusal
  `-- conserves: none — <why>` beside the def."

  -- Whole tree: a gate and its pin may land in different hunks.
  let mut premiseTexts : Array (String × Array String) := coreTexts
  if (← System.FilePath.pathExists "Main.lean") then
    premiseTexts := premiseTexts.push
      ("Main.lean", ((← IO.FS.readFile "Main.lean").splitOn "\n").toArray)
  for (f, lines) in premiseTexts do
    for (row, why) in diagnosticOutputBypasses f lines do
      say s!"pre-commit: diagnostic output bypass in {f}:{row}: {why}.
  Keep document diagnostics as Diag values through Ui.diag; only Render formats them
  (PRINCIPLES.md § One loss in one line).
  Status/help and command output belong in the audited UI and command handlers."
    for (row, call) in surfaceDoorBypasses f lines do
      say s!"pre-commit: {f}:{row} reads a surface around its door ({call}).
  Each surface has one door into the surface AST, Surface.read, and an
  included file one wrapper, Surface.fragment (LeanTex/Core/Surface.lean);
  a second spelling of either is where two readings of one file drift apart.
  Fix: read through Surface.read or Surface.fragment — or, for tex text the
  core itself holds, name the reader in coreTexReaders with its reason."
  let mut testDefs : Std.HashSet String := {}
  let mut testCode := ""
  for f in (#["Tests.lean"] : Array String) ++ (← System.FilePath.walkDir "Tests").filterMap
      (fun p => if p.toString.endsWith ".lean" then some p.toString else none) do
    if (← System.FilePath.pathExists f) then
      let txt ← IO.FS.readFile f
      let lines := (txt.splitOn "\n").toArray
      testCode := testCode ++ "\n".intercalate (codeOnly lines).toList ++ "\n"
      for l in lines do
        if let some n := topLevelDefName l then testDefs := testDefs.insert n
      testDefs := (scopedDefNames lines).foldl (·.insert ·) testDefs
  let resolves := pinResolves (theoremNames allCore) (identCounts testCode) testDefs
  -- Every marker resolves wherever it stands, sites the detector misses included.
  for (f, lines) in premiseTexts do
    for (n, pin?) in premiseFaults resolves lines do
      match pin? with
      | none =>
        say s!"pre-commit: a premise marker with no reason, in {f}:{n}:
  {(lines[n - 1]?.getD "").trimAscii}
  A premise marker names the check that falsifies it (AGENTS.md § When you add).
  Fix: write `-- {premiseMark} <pin> — <why>`, or `-- {premiseMark} none — <why>`
  when nothing falsifies it."
      | some pin =>
        say s!"pre-commit: the premise marker in {f}:{n} names `{pin}`, which resolves to nothing.
  A pin is a theorem the build checks or a check block the suite runs
  (AGENTS.md § When you add).
  Fix: name the real check, or write `{premiseMark} none — <why>` and say what is missing."
    for n in conservesFaults lines do
      say s!"pre-commit: a malformed conserves marker, in {f}:{n}:
  {(lines[n - 1]?.getD "").trimAscii}
  A walk that conserves nothing says why beside its def (AGENTS.md § When you add).
  Fix: write `-- conserves: none — <why>`."
  -- Each row in both directions: its site text still occurs, and a named pin resolves.
  for row in premiseRegistry do
    let txt := ((premiseTexts.find? (·.1 == row.file)).map
      (fun e => String.intercalate "\n" e.2.toList)).getD ""
    unless containsSub txt row.site do
      say s!"pre-commit: the premise row for {row.file} no longer matches its site:
  {row.site}
  The site moved or its condition changed, so the premise owes a fresh reading
  (AGENTS.md § When you add).
  Fix: update the row, or move the marker beside the site and delete the row."
    match row.pin with
    | some pin =>
      unless resolves pin do
        say s!"pre-commit: the premise row for {row.file} ({row.site}) names `{pin}`, which resolves to nothing.
  A premise names the check that falsifies it (AGENTS.md § When you add).
  Fix: name that check, or record the row with no pin and say what is missing."
    | none => pure ()
  for (f, lines) in premiseTexts do
    for i in [0:lines.size] do
      if let some kind := premiseSite lines i then
        let (cond, _) := (condSpan lines i).getD ((lines[i]?.getD ""), i)
        let marked := premiseMarkedAt lines i
        let registered := premiseRegistry.any fun row =>
          row.file == f && (containsSub cond row.site
            || containsSub (lines[i]?.getD "") row.site)
        unless marked || registered do
          say s!"pre-commit: a premise with no pin, in {f}:{i + 1} — it {kind.what}:
  {(lines[i]?.getD "").trimAscii}
  A gate that rests on a fact about another subsystem owes the check that
  holds the fact (AGENTS.md § When you add; premiseSite states the shape).
  Fix: write `-- {premiseMark} <pin> — <why>` beside it, naming that check;
  `-- {premiseMark} none — <why>` records it as debt instead."


  -- Multiset equality per file; `sealAllow` lists the module-final seals.
  for (f, lines) in coreTexts do
    let (sealedOnly, unsealedOnly) := sealMismatch lines
    let sealedOnly := sealedOnly.filter (!sealAllow.contains ·)
    unless sealedOnly.isEmpty && unsealedOnly.isEmpty do
      let side (what : String) (ns : List String) : String :=
        if ns.isEmpty then "" else s!"\n  {what}: {String.intercalate " " ns}"
      say s!"pre-commit: seal/unseal mismatch in {f}:{side "sealed but never unsealed" sealedOnly}{side "unsealed but never sealed" unsealedOnly}
  Each name a knot seals is unsealed after it (AGENTS.md § Lean rules).
  Fix: unseal it after the knot, as Elab.lean's pairs do; a deliberately
  module-final seal goes on sealAllow (scripts/precommit.lean) with its reason."

  -- Whole tree over Compat: a mutation and its door may land in different hunks.
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
  (rewriteCtrl_accounts, THEOREMS.md § Surfaces), and a modify/set outside the declared doors
  (compatStateDoors, scripts/precommit.lean) is invisible to both: the
  arm would look silent and draw a false W0387.
  Fix: mutate through `write` (it counts); diagnostics go through `say`."

  -- The generic walks' leaf functions, whose catch-alls are the fold's own, and the frozen holes.
  let armAllow : List String :=
    ["setAltLeaf", "resolveRefLeaf", "substPageLeaf", "imageSrcPush",
     "floatLabelPush",
     "flattenLeadStep", "collectTable", "collectItem"]
  for (f, lines) in coreTexts do
    if f.startsWith "LeanTex/Core/" then
      -- A def handed to a fold reads one node while the fold recurses, so its catch-all is no hole.
      let folds := ["foldInlines", "foldBlocks", "mapInline", "mapBlock"]
      let leafNames : Array String := lines.foldl (fun acc l =>
        let t := stripComments l
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
        let t := stripComments l
        if let some n := topLevelDefName l then
          cur := n
          curWalk := hasWord t "Inline" || hasWord t "Block"
          -- A signature split across lines keeps contributing until its `:=`.
          sigOpen := !containsSub t ":="
        else if sigOpen then
          curWalk := curWalk || hasWord t "Inline" || hasWord t "Block"
          if containsSub t ":=" then sigOpen := false
        if curWalk && wildcardThrough l && !armAllow.contains cur
            && !leafNames.contains cur then
          say s!"pre-commit: wildcard arm in the IR walk `{cur}` ({f}:{i + 1}):
  {l.trimAscii}
  Spell every constructor, or the next Ir constructor silently falls
  through (AGENTS.md § When you add); the allowlisted frozen sites live in
  precommit.lean."

  -- Role reads outside the resolver, and catch-alls in the registry's row table.
  for (f, lines) in coreTexts do
    for (i, l) in roleReads f lines do
      say s!"pre-commit: a colour role read outside its resolver ({f}:{i + 1}):
  {l.trimAscii}
  A role resolves at one site (`Design.at`, Ir.lean's `section DesignResolve`)
  from one registry (DesignRole.lean); a key string read elsewhere is a
  second default chain, and an author colour of that name would satisfy it.
  Fix: read `Design.at pal s r`, `Design.declared? pal r` or a `Design` field."
    if f == "LeanTex/Core/DesignRole.lean" then
      for i in roleRowWildcards lines do
        say s!"pre-commit: a catch-all arm in `Role.row` ({f}:{i + 1}).
  Every role owes its own row; a wildcard gives a new role another's data.
  Fix: write the role's row."

  -- Per-file counts against the frozen baseline: a commit may lower one, never raise it.
  for (f, lines) in coreTexts do
    let n := bangCount lines
    let base := ((bangBaseline.find? (·.1 == f)).map (·.2)).getD 0
    if n > base then
      say s!"pre-commit: new ]! index in {f}: {n} sites, baseline {base}.
  An index is proved in bounds or defaulted, since a miss aborts the whole
  run (AGENTS.md § Lean rules).
  Fix: use `for h :` bounds, getD, or a proof-carrying index; the per-file
  count may only fall (lower its bangBaseline row in scripts/precommit.lean
  when you remove sites)."

  -- A top-level def name in two test files is a helper's second caller (AGENTS.md § Repository).
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
  the second caller appears (AGENTS.md § Repository).
  Fix: keep one `{name}` in Tests/Support.lean and delete the copies."
  for f in testFiles do
    unless f == "Tests/Support/Check.lean" do
      let lines := ((← IO.FS.readFile f).splitOn "\n").toArray
      for (code, row) in (codeOnly lines).zipIdx do
        if failureListWrite code then
          say s!"pre-commit: {f}:{row + 1} writes a failure list itself.
  A check block records through `check` or `failures` (Tests/Support/Check.lean), the helper every
  block shares (AGENTS.md § Repository).
  Fix: write `check ref name ok`, or `let t := check ref` for a block's own prefix."

  -- A tier producer's selftest is built on `Scoreboard.tierSelftest`.
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

def main (args : List String) : IO UInt32 := do
  if args.contains "--selftest" then
    return (← selftest)
  let src ← match parseSource args with
    | .ok s => pure s
    | .error e =>
      IO.eprintln s!"pre-commit: {e}"
      return 1
  let sel := src.diffSel
  let ranged := src matches .range _
  -- Only the hook may stop at an empty change list; a range still owes its commits' privacy.
  let staged ← match sel with
    | none => pure ([] : List String)
    | some s => pure (((← git (#["diff", "--name-only"] ++ s)).splitOn "\n").filter (!·.isEmpty))
  if src == .index && staged.isEmpty then
    return 0

  -- Read first, so every message below passes through its masking.
  let privacy ← denylist
  let redact : String → String := fun msg => match privacy with
    | some m => m.redact msg
    | none => msg
  let failed ← IO.mkRef false
  let say (msg : String) : IO Unit := do
    IO.eprintln (redact msg)
    failed.set true

  -- Over every staged file, before the relevance gate skips a commit with no source.
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

  -- A range reads its tip's tree; the hook and the tree read the index and the working files.
  let tip := match src with
    | .index => some ""
    | .range r => rangeTip r
    | .tree => none
  let tracked ← match src, tip with
    | .range _, some rev => git #["ls-tree", "-r", "-z", "--name-only", "--full-tree", rev]
    | _, _ => git #["ls-files", "-z"]
  let atTip : Std.HashSet String := ((tracked.splitOn "\x00").filter (!·.isEmpty)).foldl
    (·.insert ·) {}
  let judgedBytes (paths : Array String) : IO (Array (String × ByteArray)) := do
    match src, tip with
    | .range _, some rev =>
      let present := paths.filter atTip.contains
      pure (present.zip (← catBlobs (present.map (rev ++ ":" ++ ·))))
    | _, _ => paths.filterMapM fun (f : String) => do
      unless ← System.FilePath.pathExists f do return none
      return some (f, ← IO.FS.readBinFile f)
  let addedPaths ← match src with
    | .range r => addedNames #[r]
    | _ => pure #[]
  let collisions := caseCollisions ((tracked.splitOn "\x00").filter (!·.isEmpty)).toArray
  let collisions := if ranged then collisionsTouching addedPaths collisions else collisions
  if !collisions.isEmpty then
    let hits := String.intercalate "\n" (collisions.toList.map fun (a, b) => s!"  {a}\n  {b}")
    say s!"pre-commit: two tracked paths differ only by case:
{hits}
  Fix: rename one. A case-insensitive checkout keeps one of the two, and for
  a Lean module the compiled .olean names collide as well."

  -- The rule documents' shape and every section pointer, before the relevance gate; a range judges
  -- what it changes.
  let mut heads : List (String × List String) := []
  for (doc, bytes) in ← judgedBytes sectionDocs.toArray do
    let (text, encoding) := ruleDocText doc bytes
    if let some fault := encoding then say fault
    heads := (doc, docHeadings text) :: heads
    if !ranged || staged.contains doc then
      for fault in capFaults doc text do
        say s!"pre-commit: {fault}.
  A rule document is read whole at the start of every session, so it states
  rules and names their checks (PRINCIPLES.md § Rules are checks).
  Fix: fold the rule into the check it names, its contract into that check's
  docstring, or carry an over-wide line onto the next."
      for (n, l) in datedLines text do
        say s!"pre-commit: {doc}:{n} dates a rule:
  {l}
  A rule states what holds; the day it was learned belongs to the commit that
  learned it (PRINCIPLES.md § Rules are checks).
  Fix: cut the date or the story; it belongs in the commit message."
  for (_, hook) in ← judgedBytes (if !ranged || staged.contains hookPath then #[hookPath] else #[]) do
    let skipped ← hookSkippedDocs (Privacy.textOfBytes hook)
    unless skipped.isEmpty do
      say s!"pre-commit: {hookPath} lets a commit touching only {String.intercalate " or " skipped} skip this gate:
  its staged-name pattern must match every rule document, or the caps, the
  dated-rule check and the pointer checks above never read an edit to one
  until landing (PRINCIPLES.md § Rules are checks).
  Fix: add the document to the `^(AGENTS|PRINCIPLES|THEOREMS)\\.md$` alternative."
  let trackedPaths := ((tracked.splitOn "\x00").filter (!·.isEmpty)).toArray
  let roots := vendoredRoots trackedPaths
  let prose := trackedPaths.filter fun p =>
    (p.endsWith ".lean" || p.endsWith ".md") && !vendored roots p
  let addedFiles := Privacy.uniq ((addedLines fullDiff).map (·.1))
  let sources := (← judgedBytes (if ranged then prose.filter (addedFiles.contains ·) else prose)).map
    fun (f, b) => (f, Privacy.textOfBytes b)
  let addedAt : Std.HashSet (String × Nat) :=
    (addedLines fullDiff).foldl (fun acc (f, n, _) => acc.insert (f, n)) {}
  let adds (f : String) (n : Nat) : Bool := !ranged || addedAt.contains (f, n)
  let dangling := (danglingSectionRefs heads sources).filter fun (f, n, _) => adds f n
  if !dangling.isEmpty then
    let hits := String.intercalate "\n" (dangling.toList.map fun (f, n, r) => s!"  {f}:{n}: {r}")
    say s!"pre-commit: a section pointer names no heading of its document:
{hits}
  A help text or a docstring defers to a rule by pointing at its section; the
  pointer names a `## ` heading exactly and ends at punctuation.
  Fix: point at the heading as it reads now, or restore the section."
  let loose := (looseRuleRefs (sources.filter fun (f, _) => !sectionDocs.contains f)).filter
    fun (f, n, _) => adds f n
  if !loose.isEmpty then
    let hits := String.intercalate "\n" (loose.toList.map fun (f, n, l) => s!"  {f}:{n}: {l}")
    say s!"pre-commit: a comment points into a rule document by nickname or bare name:
{hits}
  A rule's address is its section, which the pointer check above holds to the
  document; a nickname outlives the rule it named (PRINCIPLES.md § Rules are checks).
  Fix: write `AGENTS.md{sectionMark} <heading>`, or the same into `PRINCIPLES.md`,
  for the section the rule stands in now."

  -- The hook and a range read the lines they add; the tree reads every tracked text file.
  let homeLines ← if src == .index || ranged then pure (addedLines fullDiff) else do
    let (code, out, err) ← runBytes "git" #["grep", "-I", "-n", "-z", "-E", "/(home|Users)/"]
    if code == 0 then pure (grepRecords (Privacy.textOfBytes out))
    else if code == 1 then pure #[]
    else
      IO.eprintln s!"pre-commit: git grep failed:\n{Privacy.textOfBytes err}"
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

  -- The hook reads what the commit adds, a range what it adds and its commits, and the tree the
  -- staged tree and unpushed commits.
  match privacy with
  | none =>
    IO.println "pre-commit: this clone keeps no info/private-terms in its git directory; \
the privacy check is skipped."
  | some m =>
    let (hits, refused) ← match src with
      | .index => pure ((← privacyStaged m fullDiffBytes), none)
      | .range r => pure ((← privacyRange m r fullDiffBytes), none)
      | .tree => privacyTree m
    if let some why := refused then say s!"pre-commit: {why}"
    unless hits.isEmpty do
      let scope := match src with
        | .index => "in the staged changes"
        | .range _ => "in what the range adds or one of its commits"
        | .tree => "in the staged tree or an unpushed commit"
      say s!"pre-commit: a denylisted term {scope}, at:
{String.intercalate "\n" hits.toList}
  The local denylist (info/private-terms in the git common directory) holds
  personal and private-document terms; none may enter a commit message, nor
  the tree or a commit outside the citation's places (Privacy.citationPlaces).
  The term is never printed, and a path holding it is shown with that part
  as …; git ls-files or git show --stat names it.
  Fix: replace the text with invented words that exercise the same property,
  then re-stage. A term in an unpushed commit stays in what a push publishes
  even after a later commit removes it: rewrite that commit (amend, or
  squash it with the fix) before landing."

  if src == .index && !staged.any relevant then
    return (if ← failed.get then 1 else 0)

  -- A range may span a bump commit, so this reads the index alone.
  if src == .index && staged.contains "lean-toolchain" && staged.any (· != "lean-toolchain") then
    say "pre-commit: lean-toolchain changed together with other files.
  The toolchain tracks Lean's stable release, and a bump is deliberate and goes
  in its own commit (AGENTS.md § Build and verify).
  Fix: git restore --staged lean-toolchain, commit the rest, then commit the bump alone."

  if staged.any (·.startsWith "testdata/golden/") then
    -- A golden travels with a source change anywhere on its branch.
    let branchTouched ← do
      match ← mergeBaseMain with
      | some b =>
        pure (((← git #["diff", "--name-only", b ++ "..HEAD"]).splitOn "\n").filter
          (!·.isEmpty)).toArray
      | none => pure #[]
    if !staged.any goldenSource && !branchTouched.any goldenSource then
      say "pre-commit: testdata/golden/** changed without a .lean or testdata/corpus/*.tex or *.md change.
  Goldens are regenerated through the harness, never hand-edited (AGENTS.md § Build and verify).
  Fix: revert the golden files, or regenerate with: lake exe Tests --update"

  let diff ← match sel with
    | none => pure ""
    | some s => Privacy.textOfBytes <$> pinnedDiff (s ++ #["--", "*.lean"])
  for (file, lns) in addedByFile diff do
    for g in gates do
      if g.applies file then
        let bad := lns.filter g.flag
        if !bad.isEmpty then
          say s!"pre-commit: {g.what file}:
{String.intercalate "\n" bad.toList}
{g.help}"

  let docAdded := (addedLines fullDiff).filter (docRuleFile ·.1)
  let docFiles := Privacy.uniq (docAdded.map (·.1))
  let docTexts : Array (String × String) ← match tip with
    | some rev => do
      let blobs ← catBlobs (docFiles.map (rev ++ ":" ++ ·))
      pure (docFiles.zip (blobs.map Privacy.textOfBytes))
    | none => docFiles.filterMapM fun (f : String) => do
      unless ← System.FilePath.pathExists f do return none
      return some (f, ← sourceText f)
  let docHits := docTexts.flatMap fun (f, text) =>
    (docFindings text (docAdded.filterMap fun (g, n, _) => if g == f then some n else none)).map
      fun (n, what) => s!"  {f}:{n}: {what}"
  unless docHits.isEmpty do
    say s!"pre-commit: a comment breaks the documentation rule:
{String.intercalate "\n" docHits.toList}
  A docstring or comment is one sentence at most, only where the name does not say it, and carries
  no history, review, report id, date or commit hash (AGENTS.md § Lean rules).
  Fix: cut it to the contract it states, three lines at most, put the story in the commit message,
  and write a purpose as \"used for\"."

  -- A warn-once key spells its namespace at the call: a literal holding ':', alone or opening a
  -- concatenation.
  let addedInCore : List String := ((addedLines diff).filterMap fun (f, _, l) =>
    if f.startsWith "LeanTex/" then some l else none).toList
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
  so two constructs of one name cannot silence each other, and this check can see it
  (PRINCIPLES.md § One loss in one line)."

  -- A range leaves the whole tree to lint: it judges only what it adds.
  unless ranged do wholeTreeChecks say

  -- The lint driver runs these source checks alone; it owns the compiled checks.
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
