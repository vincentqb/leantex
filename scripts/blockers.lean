/-
The blocker ranking: the unknown constructs holding back the most documents; only the public
corpus's table reaches the tree, naming public definers only.
Usage: lake env lean --run scripts/blockers.lean [--rank [<list> <out>] | --screen <dir> <out> | --selftest]
-/
import LeanTex
import scripts.Board

open LeanTex.Core
open Scoreboard (sha256Hex Entry pinnedEntry parsePins namesLeantex insideCheckout)

def blockersPath : String := "testdata/coverage/blockers.tsv"

/-- The declared public corpus: one `<sha256>  <path>` line per document, the
path relative to the TeX distribution's root. -/
def manifestPath : String := "testdata/coverage/public-corpus.txt"

/-- The unknown-construct codes: the engine met a name nothing answers. -/
def blockerCodes : List String := ["W0301", "W0302"]

def die (code : UInt32) (msg : String) : IO UInt32 := do
  IO.eprintln msg
  return code

/-- An action whose failure is an answer, not an abort. -/
def orElse (x : IO α) (d : α) : IO α := do
  try x catch _ => pure d

def realPath? (p : String) : IO (Option String) :=
  orElse (do return some (← IO.FS.realPath p).toString) none

/-- The environment for any kpsewhich query that decides what is public: empty but for
`PATH`, so no shell setting moves an answer. -/
def emptiedEnv : IO (Array (String × Option String)) := do
  return #[("PATH", ← IO.getEnv "PATH")]

/-- The distribution's roots (TEXMFDIST, and TEXMFSYSDIST where set), each ending in `/`,
asked in `emptiedEnv`; empty when kpsewhich cannot answer, so nothing is public. -/
def publicRoots : IO (Array String) := do
  let env ← emptiedEnv
  let mut roots : Array String := #[]
  for v in #["TEXMFDIST", "TEXMFSYSDIST"] do
    let raw ← orElse (do
        let o ← IO.Process.output
          { cmd := "kpsewhich", args := #["-var-value", v], env, inheritEnv := false }
        pure (if o.exitCode == 0 then o.stdout.trimAscii.toString else "")) ""
    if raw.isEmpty then continue
    if let some p ← realPath? raw then
      let p := if p.endsWith "/" then p else p ++ "/"
      unless roots.contains p do roots := roots.push p
  return roots

def underRoots (roots : Array String) (resolved : String) : Bool :=
  roots.any (resolved.startsWith ·)

/-- A file the public tree holds, named by its own stem: built only by `PublicFile.of?`,
after its resolved path is checked against the roots and its stem against the load
argument. -/
structure PublicFile where
  private mk ::
  stem : String
deriving BEq, Inhabited

def PublicFile.of? (roots : Array String) (resolved load : String) : Option PublicFile :=
  if !underRoots roots resolved then none
  else
    let base := ((resolved.splitOn "/").getLast?).getD ""
    let stem := String.intercalate "." (base.splitOn ".").dropLast
    if stem.isEmpty || stem != load then none else some ⟨stem⟩

/-- A load argument that may be looked up by name; a load by path is a document's own
file. -/
def loadName? (n : String) : Option String :=
  if n.isEmpty || n.any (fun c => c == '/' || c == '\\' || c.isWhitespace || c.toNat < 32)
  then none else some n

/-- Where a construct comes from; the non-public owners carry no payload, so a folded row
is spelled by `Owner.render` alone. -/
inductive Owner where
  | primitive
  | kernel
  /-- A class file inside the distribution. -/
  | cls (file : PublicFile)
  /-- A package file inside the distribution. -/
  | pkg (file : PublicFile)
  /-- The document defines it. -/
  | document
  /-- A non-distribution class or package the document loads defines it: a load by path,
  TEXINPUTS, TEXMFHOME, the working directory. -/
  | nonpublic
  /-- Nothing the scan read defines it. -/
  | unattributed
deriving BEq, Inhabited

def Owner.render : Owner → String
  | .primitive => "primitive"
  | .kernel => "kernel"
  | .cls f => "class:" ++ f.stem
  | .pkg f => "pkg:" ++ f.stem
  | .document => "document"
  | .nonpublic => "nonpublic"
  | .unattributed => "unattributed"

def Owner.isPublic : Owner → Bool
  | .primitive | .kernel | .cls _ | .pkg _ => true
  | .document | .nonpublic | .unattributed => false

/-- An output the caller named, placed in a directory checked to lie outside every leantex
checkout; `Dest.of?` is its one constructor. -/
structure Dest where
  private mk ::
  dir : String
  name : String

/-- Where an output may be written: anywhere but a leantex checkout, found by walking up
from its resolved directory, which must exist; the name itself is not resolved. -/
def Dest.of? (out : String) : IO (Except String Dest) := do
  let fp := System.FilePath.mk out
  let some name := fp.fileName
    | return .error s!"{out}: names no file to write"
  let parent := (fp.parent.getD ".").toString
  let parent := if parent.isEmpty then "." else parent
  let some dir ← realPath? parent
    | return .error s!"{out}: its directory does not exist"
  if ← insideCheckout dir then
    return .error s!"{out}: inside a leantex checkout; write it outside every checkout"
  return .ok ⟨dir, name⟩

/-- Write an output, or a sibling of it (`suffix`), as a new file in the checked directory
renamed onto the name, so no planted link carries the write elsewhere. -/
def Dest.write (d : Dest) (suffix content : String) : IO (Except String Unit) := do
  let target := System.FilePath.mk d.dir / (d.name ++ suffix)
  let tmp := System.FilePath.mk d.dir /
    s!".{d.name}{suffix}.{← IO.Process.getPID}.{← IO.monoNanosNow}.tmp"
  let h ← match ← (IO.FS.Handle.mk tmp .writeNew).toBaseIO with
    | .ok h => pure h
    | .error e => return .error s!"{target}: cannot create a file beside it ({e})"
  let wrote ← (do h.putStr content; h.flush).toBaseIO
  let moved ← match wrote with
    | .ok () => (IO.FS.rename tmp target).toBaseIO
    | .error e => pure (.error e)
  match moved with
  | .ok () => return .ok ()
  | .error e =>
    let _ ← (IO.FS.removeFile tmp).toBaseIO
    return .error s!"{target}: not written ({e})"

/-- What one screening run learned; a kill and a tool that never ran say nothing about the
document. -/
inductive Screened where
  | builds
  | fails
  | killed
  | notRun
deriving Inhabited, BEq

def Screened.word : Screened → String
  | .builds => "builds" | .fails => "fails" | .killed => "killed" | .notRun => "not-run"

/-- `timeout`'s exit, read: 124 and 137 are kills, and 125–127 a tool that never ran. -/
def Screened.ofExit (code : UInt32) : Screened :=
  if code == 0 then .builds
  else if code == 124 || code == 137 then .killed
  else if code == 125 || code == 126 || code == 127 then .notRun
  else .fails

/-- Run lualatex on one file in a scratch directory, reading back only exit codes, so a
document's text never enters this process. -/
def buildsWithLualatex (path : String) : IO Screened := do
  let tmp ← IO.Process.output { cmd := "mktemp", args := #["-d"] }
  let dir := tmp.stdout.trimAscii.toString
  if dir.isEmpty then return .notRun
  try
    let c ← IO.Process.output { cmd := "cp", args := #[path, dir ++ "/doc.tex"] }
    if c.exitCode != 0 then return .notRun
    let r ← IO.Process.output
      { cmd := "timeout", cwd := some dir,
        args := #["60", "lualatex", "-halt-on-error", "-interaction=nonstopmode", "doc.tex"] }
    return Screened.ofExit r.exitCode
  catch _ => return .notRun
  finally
    let _ ← IO.Process.output { cmd := "rm", args := #["-r", dir] }

/-- How many lualatex runs stand at once, bounded so a kill means the document took a
minute. -/
def poolSize : Nat := 16

/-- Screen a directory of `.tex` files: the buildable list to `out`, each one with neither
verdict to `out.neither`, both through `Dest`. -/
def screen (dir out : String) : IO UInt32 := do
  let dest ← match ← Dest.of? out with
    | .ok d => pure d
    | .error why => return (← die 3 ("blockers: " ++ why))
  let files := (← System.FilePath.walkDir dir).filter (·.toString.endsWith ".tex")
  let sorted := files.map (·.toString) |>.qsort (· < ·)
  IO.println s!"blockers: screening {sorted.size} candidate(s) with lualatex, \
{poolSize} at a time"
  let mut ok : Array String := #[]
  let mut neither : Array String := #[]
  let mut failed := 0
  let mut i := 0
  while i < sorted.size do
    let stop := min sorted.size (i + poolSize)
    let mut batch : Array (String × Task (Except IO.Error Screened)) := #[]
    for k in [i:stop] do
      batch := batch.push (sorted[k]!, ← IO.asTask (buildsWithLualatex sorted[k]!))
    for (f, t) in batch do
      match t.get with
      | .ok .builds => ok := ok.push f
      | .ok .fails => failed := failed + 1
      | .ok s => neither := neither.push (s.word ++ "\t" ++ f)
      | .error _ => neither := neither.push (Screened.notRun.word ++ "\t" ++ f)
    i := stop
  if let .error e ← dest.write "" (ok.foldl (fun acc f => acc ++ f ++ "\n") "") then
    return (← die 3 ("blockers: " ++ e))
  if let .error e ← dest.write ".neither" (neither.foldl (fun acc f => acc ++ f ++ "\n") "") then
    return (← die 3 ("blockers: " ++ e))
  IO.println s!"blockers: {ok.size} build, {failed} do not, {neither.size} neither \
(killed or never run, in {out}.neither)"
  return 0

/-- Strip the namespace from a subject key: `ctrl:<name>`, `env:<name>`. -/
def constructOf (subject : String) : Option (String × String) :=
  match subject.splitOn ":" with
  | kind :: rest =>
    let name := String.intercalate ":" rest
    -- A subject carrying a control character is no construct.
    if name.isEmpty || name.any (fun c => Char.toNat c < 32) then none else some (kind, name)
  | [] => none

/-- Every construct one elaboration is blocked on, deduplicated, each kept
with the kind that namespaces it. -/
def blockersIn (ds : Array Diag) : Array (String × String) := Id.run do
  let mut out : Array (String × String) := #[]
  for d in ds do
    unless blockerCodes.contains d.code do continue
    if let some s := d.subject then
      if let some (kind, name) := constructOf s then
        if !out.contains (kind, name) then out := out.push (kind, name)
  return out.qsort (fun a b => a.1 ++ a.2 < b.1 ++ b.2)

/-- Whether an elaboration errored with no unknown name: unblocked here and still short of
P0. -/
def erroredIn (ds : Array Diag) : Bool :=
  ds.any (fun d => d.severity == .error)

/-- The package and class names a document loads. -/
def loadsOf (text : String) : Array String := Id.run do
  let mut out : Array String := #[]
  for marker in ["\\usepackage", "\\RequirePackage", "\\documentclass"] do
    let parts := text.splitOn marker
    for p in parts.drop 1 do
      let afterOpt :=
        if (p.trimAscii.toString).startsWith "[" then
          ((p.splitOn "]").drop 1 |> String.intercalate "]")
        else p
      match (afterOpt.splitOn "{").drop 1 |>.head? with
      | none => pure ()
      | some g =>
        for name in ((g.splitOn "}").headD "").splitOn "," do
          let n := name.trimAscii.toString
          if !n.isEmpty && !out.contains n then out := out.push n
  return out

/-- A character that can continue a control word in class, package and kernel files: a
letter, `@`, `_` or `:`. -/
def nameChar (c : Char) : Bool := c.isAlpha || c == '@' || c == '_' || c == ':'

/-- Whether this source defines the command, by the definer spellings a `.cls` or `.sty`
uses; a name defined by expansion is missed and falls through. -/
def defines (src name : String) : Bool :=
  let n := "\\" ++ name
  let braced := ["newcommand", "newcommand*", "renewcommand", "renewcommand*",
    "providecommand", "providecommand*", "DeclareRobustCommand", "DeclareRobustCommand*",
    "NewDocumentCommand", "DeclareDocumentCommand", "newrobustcmd", "newrobustcmd*"]
  let bareHeads := braced ++ ["def", "let", "cs_new:Npn", "cs_new_protected:Npn",
    "cs_set:Npn", "cs_set_protected:Npn", "cs_new_nopar:Npn", "cs_gset:Npn"]
  let envForms := ["\\newenvironment{" ++ name ++ "}", "\\newenvironment*{" ++ name ++ "}",
    "\\renewenvironment{" ++ name ++ "}", "\\NewDocumentEnvironment{" ++ name ++ "}"]
  let bracedForms := braced.map (fun h => "\\" ++ h ++ "{" ++ n ++ "}")
  if (bracedForms ++ envForms).any (fun pat => (src.splitOn pat).length > 1) then true
  else
    bareHeads.any fun h =>
      let pats := ["\\" ++ h ++ n, "\\" ++ h ++ " " ++ n]
      pats.any fun p =>
        (src.splitOn p).drop 1 |>.any fun after =>
          match after.toList with
          | [] => true
          | c :: _ => !nameChar c

/-- A file resolved for the scan: its real path and its text. -/
abbrev Resolver := String → IO (Option (String × String))

/-- Resolve through kpsewhich, follow symlinks and read, once per name: a list's documents
in the calling environment, the public corpus in `emptiedEnv`. -/
def kpseResolver (cache : IO.Ref (Array (String × Option (String × String))))
    (inherit : Bool) (env : Array (String × Option String)) : Resolver := fun file => do
  if let some (_, r) := (← cache.get).find? (·.1 == file) then return r
  let r ← orElse (do
      let o ← IO.Process.output
        { cmd := "kpsewhich", args := #[file], env, inheritEnv := inherit }
      let p := o.stdout.trimAscii.toString
      if o.exitCode != 0 || p.isEmpty then return none
      match ← realPath? p with
      | none => return none
      | some rp => return some (rp, ← IO.FS.readFile rp)) none
  cache.modify (·.push (file, r))
  return r

/-- Where a construct comes from, by the declared precedence; a class or package is public
only when its bare load name resolves inside the distribution to a file of that stem. -/
def ownerOf (roots : Array String) (resolve : Resolver) (docText name : String) :
    IO Owner := do
  if Compat.texPrimitives.contains name then return .primitive
  if defines docText name then return .document
  let loads := loadsOf docText
  for l in loads do
    if let some (path, src) ← resolve (l ++ ".cls") then
      if defines src name then
        match (loadName? l).bind (PublicFile.of? roots path) with
        | some f => return .cls f
        | none => return .nonpublic
  if let some (path, src) ← resolve "latex.ltx" then
    if defines src name then
      return (if underRoots roots path then .kernel else .nonpublic)
  for l in loads do
    if let some (path, src) ← resolve (l ++ ".sty") then
      if defines src name then
        match (loadName? l).bind (PublicFile.of? roots path) with
        | some f => return .pkg f
        | none => return .nonpublic
  return .unattributed

structure Rank where
  kind : String
  construct : String
  owner : Owner
  sole : Nat
  /-- Σ 1/|blockers|, in thousandths. -/
  share : Nat
  docs : Nat
deriving Inhabited, BEq

/-- A row as written, built by `publish` alone. -/
structure Row where
  kind : String
  construct : String
  owner : String
  sole : Nat
  share : Nat
  docs : Nat
deriving Inhabited, BEq

/-- Accumulate `sole`, `share` and the document count from one document's blocker set: n
blockers give each 1000/n thousandths, and one blocker also its `sole`. -/
def tally (acc : Array Rank) (blockers : Array (String × String))
    (owners : Array (String × Owner)) : Array Rank := Id.run do
  let n := blockers.size
  if n == 0 then return acc
  let piece := 1000 / n
  let mut out := acc
  for (kind, b) in blockers do
    let owner := (owners.find? (fun p => p.1 == b)).map (·.2) |>.getD .unattributed
    match out.findIdx? (fun r => r.construct == b && r.kind == kind) with
    | some i =>
      let r := out[i]!
      out := out.set! i { r with sole := r.sole + (if n == 1 then 1 else 0),
                                 share := r.share + piece, docs := r.docs + 1 }
    | none =>
      out := out.push { kind, construct := b, owner, sole := if n == 1 then 1 else 0,
                        share := piece, docs := 1 }
  return out

/-- The only way to a written row: a public owner's construct by name, every other owner
one aggregate row keyed by `Owner.render`; also returns how many names folded away. -/
def publish (rows : Array Rank) : Array Row × Nat := Id.run do
  let mut out : Array Row := #[]
  let mut folded := 0
  for r in rows do
    if r.owner.isPublic then
      out := out.push { kind := r.kind, construct := r.construct, owner := r.owner.render,
                        sole := r.sole, share := r.share, docs := r.docs }
    else
      folded := folded + 1
      let word := r.owner.render
      let key := "(" ++ word ++ ")"
      match out.findIdx? (fun q => q.construct == key) with
      | some i =>
        let q := out[i]!
        out := out.set! i { q with sole := q.sole + r.sole, share := q.share + r.share,
                                   docs := q.docs + r.docs }
      | none =>
        out := out.push { kind := "aggregate", construct := key, owner := word,
                          sole := r.sole, share := r.share, docs := r.docs }
  return (out, folded)

/-- A document's identity for counting: its bytes, not its path. -/
def contentKey (text : String) : String :=
  let b := text.toUTF8
  s!"{b.size}:{Flate.hex16 (Flate.adler32 b).toUInt64}"

structure Ranked where
  rows : Array Row
  folded : Nat
  distinct : Nat
  duplicates : Nat
  unreadable : Nat
  blocked : Nat
  erroredClean : Nat
  corpusKey : String

/-- Rank documents given as path and bytes, each read through the driver's decoding door
and elaborated alone; a text already seen is a duplicate. -/
def rankDocs (roots : Array String) (resolve : Resolver) (docs : Array (String × ByteArray)) :
    IO Ranked := do
  let mut acc : Array Rank := #[]
  let mut keys : Array String := #[]
  let mut duplicates := 0
  let mut unreadable := 0
  let mut blocked := 0
  let mut erroredClean := 0
  for (path, bytes) in docs do
    if bytes.isEmpty then
      unreadable := unreadable + 1
      continue
    let read := (Encoding.readDocument path bytes).1
    let text := read.text
    let key := contentKey text
    if keys.contains key then
      duplicates := duplicates + 1
      continue
    keys := keys.push key
    let ds := read.diags ++ (Elab.run path text).2
    let bs := blockersIn ds
    if bs.isEmpty then
      if erroredIn ds then erroredClean := erroredClean + 1
      continue
    blocked := blocked + 1
    let mut owners : Array (String × Owner) := #[]
    for (_, b) in bs do
      owners := owners.push (b, ← ownerOf roots resolve text b)
    acc := tally acc bs owners
  let (published, folded) := publish acc
  let sorted := published.qsort fun a b =>
    if a.sole != b.sole then a.sole > b.sole
    else if a.share != b.share then a.share > b.share
    else if a.construct != b.construct then a.construct < b.construct
    else a.kind < b.kind
  let corpusKey := contentKey ((keys.qsort (· < ·)).foldl (· ++ · ++ "\n") "")
  return { rows := sorted, folded, distinct := keys.size, duplicates, unreadable, blocked,
           erroredClean, corpusKey }

def renderTable (r : Ranked) (corpusLine texLine : String) : String :=
  let head :=
    "# The blocker ranking: constructs nothing in this engine answers, ranked by\n\
     # the documents they hold back. A report, never a gate. sole: documents this\n\
     # construct alone blocks. share: thousandths of a document summed over the\n\
     # documents it blocks, splitting each document between its blockers. docs:\n\
     # documents it appears in (an aggregate row sums its constructs'). kind: the\n\
     # subject namespace (ctrl | env | aggregate). owner: what defines it\n\
     # (primitive | kernel | class:<c> | pkg:<p>, a file inside the TeX\n\
     # distribution named by its own stem; or document | nonpublic | unattributed,\n\
     # each folded into one aggregate row carrying counts and no name).\n\
     # \"Blocked\" means \"has at least one unknown construct\", which is narrower\n\
     # than the parity ladder's P0: a document that elaborates with errors and no\n\
     # unknown name is unblocked here and still fails P0.\n" ++
    corpusLine ++
    s!"# corpus: {r.distinct} distinct document(s) (by content; {r.duplicates} duplicate \
path(s) and {r.unreadable} unreadable skipped), {r.blocked} with at least one blocker, \
key {r.corpusKey}\n" ++
    s!"# errored but unblocked: {r.erroredClean} document(s) — the P0 gap this table \
does not rank\n" ++
    s!"# names folded into aggregate rows: {r.folded}\n" ++
    texLine ++
    "kind\tconstruct\towner\tsole\tshare\tdocs\n"
  r.rows.foldl
    (fun acc w => acc ++ w.kind ++ "\t" ++ w.construct ++ "\t" ++ w.owner ++ "\t"
      ++ toString w.sole ++ "\t" ++ toString w.share ++ "\t" ++ toString w.docs ++ "\n") head

def texLine : IO String := do
  let v ← orElse (do
      return (← IO.Process.output { cmd := "lualatex", args := #["--version"] }).stdout) ""
  return s!"# tex: {((v.splitOn "\n").headD "").trimAscii.toString}\n"

/-- The manifest's entries: `sha256sum`'s format, one pinned document per
line, a path relative to the distribution's root. -/
def parseManifest (text : String) : Except String (Array Entry) := parsePins manifestPath text

/-- The manifest's entries, each resolved inside a root and read once; an absolute entry,
one leaving every root, or one whose bytes are not its pin's is refused. -/
def resolveManifest (roots : Array String) (entries : Array Entry) :
    IO (Except String (Array (String × ByteArray))) := do
  let mut out : Array (String × ByteArray) := #[]
  for e in entries do
    if e.path.startsWith "/" then return .error s!"{manifestPath}: '{e.path}' is absolute"
    let mut hit : Option String := none
    for r in roots do
      if hit.isNone then
        if let some p ← realPath? (r ++ e.path) then
          if underRoots roots p then hit := some p
    let some p := hit
      | return .error s!"{manifestPath}: '{e.path}' does not resolve inside the TeX \
distribution"
    let bytes ← orElse (IO.FS.readBinFile p) ByteArray.empty
    if sha256Hex bytes != e.pin then
      return .error s!"{manifestPath}: '{e.path}' does not hold the bytes its pin names"
    out := out.push (p, bytes)
  return .ok out

/-- A list's entries: one path per line, `#` lines and blank lines skipped. -/
def manifestEntries (text : String) : Array String :=
  ((text.splitOn "\n").filterMap fun l =>
    let l := l.trimAscii.toString
    if l.isEmpty || l.startsWith "#" then none else some l).toArray

/-- Rank the declared public corpus into the tree, every kpsewhich query in
`emptiedEnv`. -/
def rankTree : IO UInt32 := do
  let roots ← publicRoots
  if roots.isEmpty then
    return (← die 3 "blockers: kpsewhich names no TeX distribution, so nothing is public \
and nothing may be ranked into the tree")
  unless (← System.FilePath.pathExists manifestPath) do
    return (← die 3 s!"blockers: {manifestPath} is missing")
  let entries ← match parseManifest (← IO.FS.readFile manifestPath) with
    | .ok es => pure es
    | .error e => return (← die 3 ("blockers: " ++ e))
  match ← resolveManifest roots entries with
  | .error e => die 3 ("blockers: " ++ e)
  | .ok docs =>
    let cache ← IO.mkRef #[]
    let r ← rankDocs roots (kpseResolver cache false (← emptiedEnv)) docs
    let corpus := s!"# corpus-manifest: {manifestPath}, {entries.size} entr(ies), each \
resolved inside `kpsewhich -var-value TEXMFDIST` asked with only PATH set, and each \
holding the bytes its sha256 pin names\n"
    IO.FS.createDirAll "testdata/coverage"
    IO.FS.writeFile blockersPath (renderTable r corpus (← texLine))
    IO.println s!"blockers: wrote {blockersPath} — {r.rows.size} row(s) over {r.distinct} \
distinct document(s), {r.blocked} blocked, {r.folded} name(s) folded away"
    for w in r.rows.toList.take 20 do
      IO.println s!"  {w.sole}\t{w.share}\t{w.docs}\t{w.kind}:{w.construct}\t{w.owner}"
    return 0

/-- Rank any list to an output outside every checkout, through `Dest`, under the same
publish rule. -/
def rankList (resolve : Resolver) (listPath out : String) : IO UInt32 := do
  let dest ← match ← Dest.of? out with
    | .ok d => pure d
    | .error why => return (← die 3 ("blockers: " ++ why))
  unless (← System.FilePath.pathExists listPath) do
    return (← die 3 s!"blockers: {listPath} is missing — run --screen first")
  let roots ← publicRoots
  let mut docs : Array (String × ByteArray) := #[]
  for p in manifestEntries (← IO.FS.readFile listPath) do
    docs := docs.push (p, ← orElse (IO.FS.readBinFile p) ByteArray.empty)
  let r ← rankDocs roots resolve docs
  let corpus := "# corpus-manifest: none — a list outside the declared public corpus; \
this table does not belong in the tree\n"
  if let .error e ← dest.write "" (renderTable r corpus (← texLine)) then
    return (← die 3 ("blockers: " ++ e))
  IO.println s!"blockers: wrote {out} — {r.rows.size} row(s) over {r.distinct} distinct \
document(s), {r.blocked} blocked, {r.folded} name(s) folded away"
  return 0

/-- A link at an output's name into a checkout (symlink, dangling symlink, hard link, a
symlink at `<out>.neither`) through both shipped writers: the checkout keeps its bytes and
the output lands at the link's own name. -/
def linkedOutputs (expect : String → Bool → IO Unit) (dir : String) (resolve : Resolver)
    (list checkout : String) : IO Unit := do
  let ck := checkout ++ "/testdata/coverage"
  let table := ck ++ "/blockers.tsv"
  let manifest := ck ++ "/public-corpus.txt"
  IO.FS.writeFile table "sentinel table\n"
  IO.FS.writeFile manifest "sentinel manifest\n"
  let out := dir ++ "/outside"
  let empty := dir ++ "/empty"
  IO.FS.createDirAll out
  IO.FS.createDirAll empty
  let lnS (target link : String) : IO Unit := do
    let _ ← IO.Process.output { cmd := "ln", args := #["-s", target, link] }
  lnS table (out ++ "/sym.tsv")
  lnS (ck ++ "/zzdangling.tsv") (out ++ "/dangling.tsv")
  IO.FS.hardLink manifest (out ++ "/hard.tsv")
  lnS table (out ++ "/screen.txt")
  lnS (ck ++ "/zzneither.txt") (out ++ "/screen.txt.neither")
  lnS ck (out ++ "/dirlink")
  let codes := #[← rankList resolve list (out ++ "/sym.tsv"),
    ← rankList resolve list (out ++ "/dangling.tsv"),
    ← rankList resolve list (out ++ "/hard.tsv"),
    ← screen empty (out ++ "/screen.txt")]
  expect "an output named through a link is still written" (codes.all (· == 0))
  let regular (p : String) : IO Bool := do
    match ← (System.FilePath.symlinkMetadata p).toBaseIO with
    | .ok m => return m.type == .file
    | .error _ => return false
  expect "a symlink at <out> is replaced, not followed"
    ((← orElse (IO.FS.readFile table) "") == "sentinel table\n"
      && (← regular (out ++ "/sym.tsv")) && (← regular (out ++ "/screen.txt")))
  expect "a symlink at <out> that points at nothing creates nothing there"
    (!(← System.FilePath.pathExists (ck ++ "/zzdangling.tsv"))
      && (← regular (out ++ "/dangling.tsv")))
  expect "a hard link at <out> leaves its other name's bytes"
    ((← orElse (IO.FS.readFile manifest) "") == "sentinel manifest\n")
  expect "a symlink at <out>.neither is replaced, not followed"
    (!(← System.FilePath.pathExists (ck ++ "/zzneither.txt"))
      && (← regular (out ++ "/screen.txt.neither")))
  -- A link on the directory is resolved, so the checkout behind it is found and the output refused.
  let viaDir ← rankList resolve list (out ++ "/dirlink/zz.tsv")
  expect "an output under a linked directory inside a checkout is refused" (viaDir != 0)
  let mut files : Array String := #[]
  for p in ← System.FilePath.walkDir checkout do
    unless ← p.isDir do files := files.push p.toString
  expect "the checkout holds exactly the files it held"
    (files.qsort (· < ·) == #[checkout ++ "/lakefile.toml", manifest, table].qsort (· < ·))

/-- The pin against a scratch root: the declared bytes resolve, other bytes at the path
and a symlink out of the root are refused, and an entry with no pin is a fault. -/
def pinnedManifest (expect : String → Bool → IO Unit) (dir : String) : IO Unit := do
  let root := dir ++ "/proot"
  let doc := root ++ "/tex/latex/zzpin/doc.tex"
  IO.FS.createDirAll (root ++ "/tex/latex/zzpin")
  IO.FS.writeFile doc "declared bytes\n"
  IO.FS.writeFile (dir ++ "/zzpin-outside.tex") "declared bytes\n"
  let _ ← IO.Process.output
    { cmd := "ln", args := #["-s", dir ++ "/zzpin-outside.tex", root ++ "/tex/latex/zzpin/out.tex"] }
  let roots := #[((← realPath? root).getD root) ++ "/"]
  let pin := sha256Hex "declared bytes\n".toUTF8
  let resolvesOne (r : Except String (Array (String × ByteArray))) : Bool :=
    match r with
    | .ok xs => xs.size == 1
    | .error _ => false
  expect "a document holding its pinned bytes resolves"
    (resolvesOne (← resolveManifest roots #[{ pin, path := "tex/latex/zzpin/doc.tex" }]))
  IO.FS.writeFile doc "substituted bytes\n"
  expect "a substituted document is refused"
    (!resolvesOne (← resolveManifest roots #[{ pin, path := "tex/latex/zzpin/doc.tex" }]))
  expect "a symlink out of the root is refused, whatever it holds"
    (!resolvesOne (← resolveManifest roots #[{ pin, path := "tex/latex/zzpin/out.tex" }]))
  expect "an entry with no pin is a fault"
    (parseManifest "tex/latex/base/sample2e.tex\n" matches .error _)
  expect "an entry pinned with one space is a fault"
    (parseManifest (pin ++ " tex/a.tex\n") matches .error _)
  expect "a pinned entry parses, beside a comment"
    (match parseManifest ("# a note\n" ++ pinnedEntry pin "tex/a.tex" ++ "\n") with
      | .ok es => es == #[{ pin, path := "tex/a.tex" }]
      | .error _ => false)

/-- A shell pointing kpathsea at a planted tree, through the shipped `--rank`: each
setting alone leaves the planted tree non-public, an honest child succeeds, and a
shadowing TEXINPUTS writes the same table. -/
def hostileShell (expect : String → Bool → IO Unit) (dir : String) : IO Unit := do
  let hroot := dir ++ "/hroot"
  let pdir := hroot ++ "/tex/latex/zzplanthroot"
  IO.FS.createDirAll pdir
  let doc := "\\documentclass{article}\n\\usepackage{zzplanthsty}\n\\begin{document}\n\
\\zzplanthmacro\\ here.\n\\end{document}\n"
  IO.FS.writeFile (pdir ++ "/zzplanthdoc.tex") doc
  IO.FS.writeFile (pdir ++ "/zzplanthsty.sty")
    "\\ProvidesPackage{zzplanthsty}\n\\newcommand{\\zzplanthmacro}{s}\n"
  let cnf := dir ++ "/hcnf"
  IO.FS.createDirAll cnf
  IO.FS.writeFile (cnf ++ "/texmf.cnf") s!"TEXMFDIST = {hroot}\n"
  let cwd := dir ++ "/hcwd"
  IO.FS.createDirAll (cwd ++ "/testdata/coverage")
  let table := cwd ++ "/testdata/coverage/blockers.tsv"
  let manifest := cwd ++ "/testdata/coverage/public-corpus.txt"
  let lean := (← IO.appPath).toString
  let script := ((← IO.currentDir) / "scripts" / "blockers.lean").toString
  let child (env : Array (String × Option String)) : IO UInt32 := do
    let o ← IO.Process.output
      { cmd := lean, args := #["--run", script, "--rank"], cwd := some cwd, env }
    return o.exitCode
  let realDoc := "tex/latex/base/sample2e.tex"
  match (← publicRoots)[0]? with
  | none => expect "the host names a TeX distribution for the hostile-shell check" false
  | some root =>
    let bytes ← orElse (IO.FS.readBinFile (root ++ realDoc)) ByteArray.empty
    IO.FS.writeFile manifest (pinnedEntry (sha256Hex bytes) realDoc ++ "\n")
    let honest ← child #[]
    let honestTable ← orElse (IO.FS.readFile table) ""
    expect "an honest child ranks a pinned public document" (honest == 0 && !honestTable.isEmpty)
    let _ ← orElse (IO.FS.removeFile table) ()
    -- A TEXINPUTS shadowing the class with its own bytes leaves the table unchanged.
    let shadow := dir ++ "/hshadow"
    IO.FS.createDirAll shadow
    IO.FS.writeFile (shadow ++ "/article.cls")
      (← orElse (IO.FS.readFile (root ++ "tex/latex/base/article.cls")) "")
    let shadowed ← child #[("TEXINPUTS", some (shadow ++ "//:"))]
    expect "a shell's TEXINPUTS moves no attribution in the tree's table"
      (shadowed == 0 && (← orElse (IO.FS.readFile table) "") == honestTable)
    let _ ← orElse (IO.FS.removeFile table) ()
  IO.FS.writeFile manifest
    (pinnedEntry (sha256Hex doc.toUTF8) "tex/latex/zzplanthroot/zzplanthdoc.tex" ++ "\n")
  for (var, value) in #[("TEXMFDIST_kpsewhich", hroot), ("TEXMFSYSDIST_kpsewhich", hroot),
      ("TEXMFDIST", hroot), ("TEXMFCNF", cnf)] do
    let code ← child #[(var, some value), ("TEXINPUTS", some (hroot ++ "/tex//:"))]
    let mut leaked := false
    for f in ← System.FilePath.walkDir cwd do
      if (← f.isDir) || f.toString == manifest then continue
      if containsSub (← orElse (IO.FS.readFile f) "") "zzplanth" then leaked := true
    expect s!"a shell's {var} does not make a planted tree public"
      (code != 0 && !(← System.FilePath.pathExists table) && !leaked)
    let _ ← orElse (IO.FS.removeFile table) ()

/-- The queue's reader of this table fails loudly through the shipped `scoreboard
--queue`: a well-formed table ranks, a malformed row exits 2. -/
def queueReader (expect : String → Bool → IO Unit) (dir : String) : IO Unit := do
  let cwd := dir ++ "/qcwd"
  IO.FS.createDirAll (cwd ++ "/testdata/coverage")
  let table := cwd ++ "/testdata/coverage/blockers.tsv"
  let lean := (← IO.appPath).toString
  let script := ((← IO.currentDir) / "scripts" / "scoreboard.lean").toString
  let queue : IO (UInt32 × String) := do
    let o ← IO.Process.output
      { cmd := lean, args := #["--run", script, "--queue"], cwd := some cwd }
    return (o.exitCode, o.stdout)
  let good := "# a table\nkind\tconstruct\towner\tsole\tshare\tdocs\n\
ctrl\thspace\tkernel\t1\t1000\t1\naggregate\t(document)\tdocument\t0\t500\t1\n"
  IO.FS.writeFile table good
  let (ok, out) ← queue
  expect "the queue ranks a well-formed blocker table"
    (ok == 0 && containsSub out "queue: blocker ctrl:hspace owner=kernel sole=1")
  IO.FS.writeFile table (good ++ "hspace\tkernel\t1\t1000\t1\n")
  let (five, _) ← queue
  expect "a five-field blocker row stops the queue with exit 2" (five == 2)
  IO.FS.writeFile table (good ++ "ctrl\tvspace\tkernel\tone\t1000\t1\n")
  let (word, _) ← queue
  expect "a blocker count that is not an integer stops the queue with exit 2" (word == 2)

/-- The confinement rule end to end through the shipped writer: planted, private-looking
names behind every lookup a document can use, every file the writer left read back, and a
link at the output's name into a checkout. -/
def plantedCorpus (expect : String → Bool → IO Unit) : IO Unit := do
  let tmp ← IO.Process.output { cmd := "mktemp", args := #["-d"] }
  let dir := tmp.stdout.trimAscii.toString
  if dir.isEmpty then
    expect "a scratch directory for the planted corpus" false
    return
  try
    let styles := dir ++ "/styles"
    let report := dir ++ "/report"
    IO.FS.createDirAll styles
    IO.FS.createDirAll report
    IO.FS.writeFile (styles ++ "/zzplantstyleabs.sty")
      "\\ProvidesPackage{zzplantstyleabs}\n\\newcommand{\\zzplantedsecretabs}{s}\n"
    IO.FS.writeFile (styles ++ "/zzplantstyleenv.sty")
      "\\ProvidesPackage{zzplantstyleenv}\n\\newcommand{\\zzplantedsecretenv}{s}\n"
    IO.FS.writeFile (styles ++ "/zzplantclass.cls")
      "\\ProvidesClass{zzplantclass}\n\\LoadClass{article}\n\\newcommand{\\zzplantedsecretcls}{s}\n"
    let docs : Array (String × String) := #[
      ("abs", "\\documentclass{article}\n\\usepackage{" ++ styles ++ "/zzplantstyleabs}\n\
\\begin{document}\n\\zzplantedsecretabs\\ here.\n\\end{document}\n"),
      ("env", "\\documentclass{article}\n\\usepackage{zzplantstyleenv}\n\
\\begin{document}\n\\zzplantedsecretenv\\ here.\n\\end{document}\n"),
      ("cls", "\\documentclass{" ++ styles ++ "/zzplantclass}\n\
\\begin{document}\n\\zzplantedsecretcls\\ here.\n\\end{document}\n"),
      ("own", "\\documentclass{article}\n\\let\\zzplanteddocmacro\\relax\n\
\\begin{document}\n\\zzplanteddocmacro\\ and \\zzplantedunattributed\\ here.\n\
\\end{document}\n")]
    let mut list := ""
    for (n, t) in docs do
      IO.FS.writeFile (dir ++ "/" ++ n ++ ".tex") t
      list := list ++ dir ++ "/" ++ n ++ ".tex\n"
    -- The same bytes under a second path: one document, counted once.
    IO.FS.writeFile (dir ++ "/own-again.tex") ((docs[3]!).2)
    list := list ++ dir ++ "/own-again.tex\n"
    IO.FS.writeFile (dir ++ "/list.txt") list
    let cache ← IO.mkRef #[]
    let resolve := kpseResolver cache true #[("TEXINPUTS", some (styles ++ "//:"))]
    let out := report ++ "/blockers.tsv"
    let code ← rankList resolve (dir ++ "/list.txt") out
    expect "the planted corpus ranks to an output outside the checkout" (code == 0)
    let table ← orElse (IO.FS.readFile out) ""
    expect "the table was written" (!table.isEmpty)
    for f in ← System.FilePath.walkDir report do
      let text ← orElse (IO.FS.readFile f) ""
      expect s!"{f.fileName.getD ""} carries no planted identifier and no scratch path"
        (!containsSub text "zzplant" && !containsSub text dir)
    -- Not vacuous: the planted names were blockers, and they folded.
    expect "a style resolved outside the distribution folds to nonpublic"
      (containsSub table "aggregate\t(nonpublic)\tnonpublic\t")
    expect "a document's own macro folds to document"
      (containsSub table "aggregate\t(document)\tdocument\t")
    expect "a name nothing defines folds to unattributed"
      (containsSub table "aggregate\t(unattributed)\tunattributed\t")
    expect "the duplicate path is one document"
      (containsSub table "# corpus: 4 distinct document(s) (by content; 1 duplicate")
    -- An output inside a scratch checkout is refused and nothing is written.
    let fakeCheckout := dir ++ "/checkout"
    IO.FS.createDirAll (fakeCheckout ++ "/testdata/coverage")
    IO.FS.writeFile (fakeCheckout ++ "/lakefile.toml") "name = \"leantex\"\n"
    let inside := fakeCheckout ++ "/testdata/coverage/blockers.tsv"
    let refused ← rankList resolve (dir ++ "/list.txt") inside
    expect "an output inside a checkout is refused" (refused != 0)
    expect "and nothing was written there" (!(← System.FilePath.pathExists inside))
    linkedOutputs expect dir resolve (dir ++ "/list.txt") fakeCheckout
    pinnedManifest expect dir
    hostileShell expect dir
    queueReader expect dir
  finally
    let _ ← IO.Process.output { cmd := "rm", args := #["-r", dir] }

def selftest : IO UInt32 := do
  let ref ← IO.mkRef (#[] : Array String)
  let expect (name : String) (ok : Bool) : IO Unit := do
    unless ok do ref.modify (·.push name)
  expect "a subject's namespace is stripped"
    (constructOf "ctrl:\\foo" == some ("ctrl", "\\foo"))
  expect "an empty name is no construct" (constructOf "ctrl:" == none)
  expect "a control character is no construct" (constructOf "ctrl:\\\n" == none)
  let one := tally #[] #[("ctrl", "a")] #[("a", .kernel)]
  expect "a sole blocker takes the whole document"
    (one == #[{ kind := "ctrl", construct := "a", owner := .kernel, sole := 1,
                share := 1000, docs := 1 }])
  let four := tally #[] (#["a", "b", "c", "d"].map (("ctrl", ·))) #[]
  expect "four blockers split the document" (four.all fun r => r.sole == 0 && r.share == 250)
  expect "every blocker is recorded" (four.size == 4)
  let twice := tally one #[("ctrl", "a")] #[("a", .kernel)]
  expect "a construct blocking twice doubles"
    (twice == #[{ kind := "ctrl", construct := "a", owner := .kernel, sole := 2,
                  share := 2000, docs := 2 }])
  expect "an empty blocker set changes nothing" (tally one #[] #[] == one)
  let bothKinds := tally #[] #[("ctrl", "em"), ("env", "em")] #[]
  expect "a command and an environment of one name are two rows" (bothKinds.size == 2)
  -- A document in a declared 8-bit encoding is read as the driver's decoding door reads it.
  let latin := "\\documentclass{article}\n\\usepackage[latin1]{inputenc}\n\\begin{document}\nCaf".toUTF8
    ++ ⟨#[0xE9]⟩ ++ ".\n\\end{document}\n".toUTF8
  let latinRank ← rankDocs #[] (fun _ => pure none) #[("latin.tex", latin)]
  expect "a Latin-1 document is read through the decoding door, not skipped"
    (latinRank.unreadable == 0 && latinRank.distinct == 1)
  -- The public tree, and the one way into it.
  let roots := #["/r/dist/"]
  expect "a file inside the root is public"
    ((PublicFile.of? roots "/r/dist/tex/latex/a/amsmath.sty" "amsmath").map (·.stem)
      == some "amsmath")
  expect "a sibling directory sharing the prefix is not"
    ((PublicFile.of? roots "/r/dist-evil/tex/zz.sty" "zz").isNone)
  expect "the root's own name without its slash is not"
    ((PublicFile.of? roots "/r/dist" "dist").isNone)
  expect "nothing is public under no root" ((PublicFile.of? #[] "/r/dist/a.sty" "a").isNone)
  expect "a file whose stem is not the name that loaded it is not public"
    ((PublicFile.of? roots "/r/dist/tex/latex/base/zzrenamed.cls" "article").isNone)
  expect "SHA-256 of nothing"
    (sha256Hex ByteArray.empty
      == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
  expect "SHA-256 of abc"
    (sha256Hex "abc".toUTF8
      == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")
  expect "SHA-256 of a message that pads into a second block"
    (sha256Hex "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toUTF8
      == "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1")
  expect "a bare load name may be looked up" (loadName? "amsmath" == some "amsmath")
  expect "a load by path may not"
    ((loadName? "/abs/zz").isNone && (loadName? "sub/zz").isNone && (loadName? "").isNone)
  expect "the folded owners are three fixed words"
    ([Owner.document, .nonpublic, .unattributed].map Owner.render
      == ["document", "nonpublic", "unattributed"])
  expect "only the four public owners are public"
    ((Owner.cls default).isPublic && Owner.kernel.isPublic && Owner.primitive.isPublic
      && (Owner.pkg default).isPublic && !Owner.document.isPublic
      && !Owner.nonpublic.isPublic && !Owner.unattributed.isPublic)
  -- Attribution: public by where the definer resolved, never through a path load.
  let fake : Resolver := fun file => pure <|
    if file == "zzinside.sty" then some ("/r/dist/tex/latex/zzinside.sty", "\\newcommand{\\zzq}{}")
    else if file == "zzoutside.sty" then some ("/r/private/zzoutside.sty", "\\newcommand{\\zzq}{}")
    else if file == "/r/dist/tex/latex/zzinside.sty" then
      some ("/r/dist/tex/latex/zzinside.sty", "\\newcommand{\\zzq}{}")
    else if file == "zzalias.cls" then
      some ("/r/dist/tex/latex/zzrenamedcls.cls", "\\newcommand{\\zzq}{}")
    else none
  let o1 ← ownerOf roots fake "\\usepackage{zzinside}" "zzq"
  expect "a package inside the distribution is named by its file"
    (o1.render == "pkg:zzinside")
  let o2 ← ownerOf roots fake "\\usepackage{zzoutside}" "zzq"
  expect "the same definer outside the distribution is nonpublic" (o2 == .nonpublic)
  let o3 ← ownerOf roots fake "\\usepackage{/r/dist/tex/latex/zzinside}" "zzq"
  expect "a load by path is nonpublic even when the file is the distribution's"
    (o3 == .nonpublic)
  let o4 ← ownerOf roots fake "\\documentclass{zzalias}" "zzq"
  expect "a class that resolves to a file of another name is nonpublic" (o4 == .nonpublic)
  let mixed : Array Rank :=
    #[{ kind := "ctrl", construct := "hspace", owner := .kernel, sole := 3,
        share := 3000, docs := 3 },
      { kind := "ctrl", construct := "zzPrivateMacro", owner := .document, sole := 1,
        share := 1000, docs := 1 },
      { kind := "ctrl", construct := "zzOtherPrivate", owner := .document, sole := 0,
        share := 500, docs := 1 },
      { kind := "ctrl", construct := "zzStyleMacro", owner := .nonpublic, sole := 0,
        share := 200, docs := 1 },
      { kind := "env", construct := "zzUnknownThing", owner := .unattributed, sole := 2,
        share := 700, docs := 2 }]
  let (pub, folded) := publish mixed
  expect "folding reports how many names it removed" (folded == 4)
  expect "a private name cannot reach a written row"
    (!pub.any fun r => containsSub r.construct "zz" || containsSub r.owner "zz")
  expect "a public name survives folding" (pub.any fun r => r.construct == "hspace")
  expect "an aggregate row keeps the counts"
    ((pub.find? (·.construct == "(document)")).map (fun r => (r.sole, r.share, r.docs))
      == some (1, 1500, 2))
  expect "each non-public owner gets its own aggregate row"
    ((pub.filter (·.kind == "aggregate")).size == 3)
  -- The definer scan, in the spellings latex.ltx really uses.
  expect "a braced newcommand defines" (defines "\\newcommand{\\foo}[1]{x}" "foo")
  expect "a bare newcommand defines" (defines "\\newcommand\\foo{x}" "foo")
  expect "def defines" (defines "\\def\\foo#1{x}" "foo")
  expect "let defines without an equals sign" (defines "\\let\\foo\\bar" "foo")
  expect "DeclareRobustCommand defines bare" (defines "\\DeclareRobustCommand\\foo{x}" "foo")
  expect "expl3 defines" (defines "\\cs_new:Npn \\foo #1 {x}" "foo")
  expect "an environment definer defines" (defines "\\newenvironment{bar}{}{}" "bar")
  expect "a mention is not a definition" (defines "we use \\foo here" "foo" == false)
  expect "a longer name is not this one" (defines "\\newcommand\\foobar{x}" "foo" == false)
  expect "an @-name is not its prefix" (defines "\\def\\foo@bar{x}" "foo" == false)
  expect "an expl3 name is not its prefix" (defines "\\cs_new:Npn \\foo_bar:n {x}" "foo" == false)
  expect "usepackage lists are read"
    (loadsOf "\\usepackage{amsmath,graphicx}" == #["amsmath", "graphicx"])
  expect "an option group is skipped"
    (loadsOf "\\usepackage[margin=1in]{geometry}" == #["geometry"])
  expect "a class is a load" (loadsOf "\\documentclass{article}" == #["article"])
  -- Neither a kill nor a tool that never ran is a verdict.
  expect "timeout's own exits are read"
    (Screened.ofExit 0 == .builds && Screened.ofExit 1 == .fails
      && Screened.ofExit 124 == .killed && Screened.ofExit 137 == .killed
      && Screened.ofExit 125 == .notRun && Screened.ofExit 126 == .notRun
      && Screened.ofExit 127 == .notRun)
  expect "equal bytes are one document" (contentKey "abc" == contentKey "abc")
  expect "different bytes are two" (contentKey "abc" != contentKey "abd")
  expect "a lakefile naming leantex is a checkout, however it is spaced"
    (namesLeantex "[x]\nname = \"leantex\"\n" && namesLeantex "name=\"leantex\""
      && !namesLeantex "name = \"other\"" && !namesLeantex "")
  expect "an output inside the working tree is refused"
    ((← Dest.of? "testdata/coverage/zz.tsv") matches .error _)
  expect "an output under /tmp is not" ((← Dest.of? "/tmp/zz-blockers.tsv") matches .ok _)
  expect "an output that names a directory and no file is refused"
    ((← Dest.of? "/tmp/") matches .error _)
  -- The manifest can only name the distribution's own files.
  let realRoots ← publicRoots
  expect "the host names a TeX distribution" (!realRoots.isEmpty)
  if !realRoots.isEmpty then
    let esc ← resolveManifest realRoots #[{ pin := "", path := "../../../../../../../../../../tmp" }]
    expect "a manifest entry that leaves the distribution is refused" (esc matches .error _)
    let abs ← resolveManifest realRoots #[{ pin := "", path := "/tmp" }]
    expect "an absolute manifest entry is refused" (abs matches .error _)
  plantedCorpus expect
  let bad ← ref.get
  if bad.isEmpty then
    IO.println "blockers: selftest ok"
    return 0
  else
    for b in bad do IO.eprintln ("blockers: selftest failed: " ++ b)
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--screen", dir, out] => screen dir out
  | ["--rank"] => rankTree
  | ["--rank", list, out] => do
    let cache ← IO.mkRef #[]
    rankList (kpseResolver cache true #[]) list out
  | ["--selftest"] => selftest
  | _ => die 3 "usage: blockers [--rank | --rank <list> <out> | --screen <dir> <out> | \
--selftest]"
