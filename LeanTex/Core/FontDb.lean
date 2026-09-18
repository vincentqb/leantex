import Std.Data.HashMap
import Std.Data.HashSet
import LeanTex.Core.Font

namespace LeanTex.Core.FontDb

open LeanTex.Core.Font

/-- One installed face: the family it belongs to and which variant it is. -/
structure Face where
  path : String
  family : String
  subfamily : String
  bold : Bool
  italic : Bool
  fixedPitch : Bool
  /-- OS/2 usWeightClass: 400 is regular, 700 bold, 600 "Demi"/"Semibold". -/
  weight : Nat
  deriving Repr, Inhabited

/-- Which face of a family a piece of text wants. -/
structure Variant where
  bold : Bool := false
  italic : Bool := false
  deriving Repr, BEq, Inhabited

def searchDirs : List String :=
  ["/usr/share/fonts", "/usr/local/share/fonts", "/usr/share/texmf-dist/fonts/opentype",
   "/usr/share/texmf-dist/fonts/truetype",
   -- macOS. System faces are mostly .ttc collections, which the scan skips
   -- (see isFontFile); Supplemental and /Library hold plain .ttf/.otf.
   "/System/Library/Fonts", "/System/Library/Fonts/Supplemental", "/Library/Fonts",
   "/opt/homebrew/share/fonts"]

/-- Where else to look, from `LEANTEX_FONT_PATH` and `$HOME`. A TeX Live tree is
not always at `/usr/share`, and a user's own fonts are never there: without this
a document naming a font it demonstrably has gets told the font does not exist. -/
def extraDirs : IO (List String) := do
  let home := (← IO.getEnv "HOME").getD ""
  let userDirs :=
    if home.isEmpty then []
    else [home ++ "/.fonts", home ++ "/.local/share/fonts", home ++ "/Library/Fonts"]
  let env := (← IO.getEnv "LEANTEX_FONT_PATH").getD ""
  let fromEnv := (env.splitOn ":").filter (!·.isEmpty)
  return userDirs ++ fromEnv

private def isFontFile (p : String) : Bool :=
  -- Compare the extension only: lowercasing the whole path allocated a copy
  -- of every one of 3000 names and was most of the listing's time.
  -- `.ttc` and `.dfont` collections (macOS system fonts) are skipped here by
  -- construction: the scan never opens them, so they can never be reported
  -- as broken fonts. Parsing collections is out of scope (PLAN.md).
  let ext := (p.splitOn ".").getLast? |>.map String.toLower
  ext == some "ttf" || ext == some "otf"

/-- A sparse image of a font file holding only the tables `want` names, each
spliced at its true offset so `Font`'s table readers see a consistent file:
zeros elsewhere, nothing else read. `none` when the file is not sfnt-shaped
or a wanted table is absent or absurd. -/
def tableImage (path : String) (want : String → Bool) : IO (Option ByteArray) := do
  try
    let handle ← IO.FS.Handle.mk path .read
    let header ← handle.read 12
    if header.size < 12 then
      return none
    let numTables := (header[4]!).toNat * 256 + (header[5]!).toNat
    if numTables == 0 || numTables > 512 then
      return none
    let dir ← handle.read (16 * numTables).toUSize
    let mut wanted : Array (String × Nat × Nat) := #[]
    for k in [0:numTables] do
      let base := 16 * k
      if base + 16 ≤ dir.size then
        let tag := String.ofList ((dir.extract base (base + 4)).toList.map
          fun c => Char.ofNat c.toNat)
        let off := (((dir[base + 8]!).toNat * 256 + (dir[base + 9]!).toNat) * 256 +
          (dir[base + 10]!).toNat) * 256 + (dir[base + 11]!).toNat
        let len := (((dir[base + 12]!).toNat * 256 + (dir[base + 13]!).toNat) * 256 +
          (dir[base + 14]!).toNat) * 256 + (dir[base + 15]!).toNat
        if want tag then
          wanted := wanted.push (tag, off, len)
    if wanted.isEmpty then
      return none
    let maxEnd := wanted.foldl (fun acc (e : String × Nat × Nat) =>
      max acc (e.2.1 + e.2.2)) 0
    if maxEnd > 8 * 1024 * 1024 then
      return none
    -- Build a sparse image: zeros everywhere except header, directory, tables.
    let mut image : ByteArray := ByteArray.empty
    image := image ++ header ++ dir
    let mut pos := 12 + dir.size
    let sorted := wanted.qsort fun a b => a.2.1 < b.2.1
    for (_, off, len) in sorted do
      if off ≥ pos then
        image := image ++ (⟨Array.replicate (off - pos) 0⟩ : ByteArray)
        handle.rewind
        discard <| handle.read off.toUSize
        let chunk ← handle.read len.toUSize
        image := image ++ chunk
        pos := off + chunk.size
    return some image
  catch _ =>
    return none

/-- Read just enough of a font file to classify it: the table directory, then
the `name`, `OS/2`, `head`, and `post` tables. Full files are large (a
megabyte each is common) and a scan touches every installed face — `hmtx`
and `cmap` are what make that expensive, and classification needs neither,
so `probe` calls `classify` rather than `parse`. -/
def probe (path : String) : IO (Option Face) := do
  let some image ← tableImage path
    (fun tag => tag == "name" || tag == "OS/2" || tag == "head" || tag == "post")
    | return none
  match Font.classify image with
  | .ok f =>
    return some {
      path := path
      family := f.family
      subfamily := f.subfamily
      bold := f.isBold
      italic := f.isItalic
      fixedPitch := f.isFixedPitch
      weight := f.weight
    }
  | .error _ => return none

/-! ## The probe cache

Probing a face reads and classifies its tables; on a host with a TeX Live tree
that is ~2900 files and ~400 ms, the whole cost of a small build. Listing them
is 25 ms. So the classification of each file is cached on disk, keyed by the
file's path, size, and mtime: a face that changed on disk misses and is
probed again, one that vanished is never read, and a corrupt or missing cache
is a full rescan. Nothing about the cache can make the answer differ from a
scan, which is the property that lets it exist. -/

/-- `$XDG_CACHE_HOME/leantex`, or `~/.cache/leantex`; none without a home. -/
def cacheDir : IO (Option System.FilePath) := do
  let base ← match ← IO.getEnv "XDG_CACHE_HOME" with
    | some d => pure (some (System.FilePath.mk d))
    | none => match ← IO.getEnv "HOME" with
      | some h => pure (some (System.FilePath.mk h / ".cache"))
      | none => pure none
  return base.map (· / "leantex")

private def cachePath : IO (Option System.FilePath) := do
  return (← cacheDir).map (· / "fontdb.tsv")

/-- One line per file, tab-separated: the key (path, size, mtime joined by
tabs), then the classification — or nothing after the key for a file `probe`
rejected, so a rejected font is not read again on every run. Family names may
hold spaces and never tabs, which is why the format is TSV and not something
that needs an escaper. -/
private def faceLine (key : String) (f : Option Face) : String :=
  match f with
  | some f => String.intercalate "\t" [key, f.family, f.subfamily,
      toString f.bold, toString f.italic, toString f.fixedPitch, toString f.weight]
  | none => key

private def parseLine (line : String) : Option (String × Option Face) :=
  match line.splitOn "\t" with
  | [path, size, mtime, family, sub, bold, italic, fixed, weight] =>
    some (path ++ "\t" ++ size ++ "\t" ++ mtime, some
      { path, family, subfamily := sub, bold := bold == "true", italic := italic == "true"
        fixedPitch := fixed == "true", weight := weight.toNat?.getD 400 })
  | [path, size, mtime] => some (path ++ "\t" ++ size ++ "\t" ++ mtime, none)
  | _ => none

private def fileKey (path : String) : IO (Option (String × String)) := do
  try
    let md ← (System.FilePath.mk path).metadata
    return some (toString md.byteSize, s!"{md.modified.sec}.{md.modified.nsec}")
  catch _ => return none

/-! ## The listing cache

On a warm run the walk itself is what remains: a `readDir` per directory and
a stat per entry, ~50 ms on a host with a TeX Live tree — more than
everything else the scan does. The set of names under a directory is a
function of that directory's own entries, and POSIX moves a directory's
mtime whenever an entry is added, removed, or renamed, so each directory's
listing is cached keyed by its mtime: a hit costs one stat instead of a
listing. A file edited in place keeps its name — the cached listing stays
correct — and changes its own size or mtime, which the per-file probe key
catches. A new subdirectory appears in its parent's listing, whose mtime
moved, so the walk that first sees the parent fresh discovers it. As with
the probe cache, nothing here can make the answer differ from a real walk. -/

private def dirsPath : IO (Option System.FilePath) := do
  return (← cacheDir).map (· / "fontdb-dirs.tsv")

/-- One line per directory: path, mtime, then each entry in sorted order
prefixed `F` (a font file) or `D` (a subdirectory). Entries the walk skips
(non-font files) are not recorded; order is kept because resolution breaks
ties by scan order. -/
private def dirLine (path mtime : String) (entries : Array (Bool × String)) : String :=
  String.intercalate "\t" (path :: mtime :: entries.toList.map fun (isFont, n) =>
    (if isFont then "F" else "D") ++ n)

private def parseDirLine (line : String) :
    Option (String × String × Array (Bool × String)) := Id.run do
  match line.splitOn "\t" with
  | path :: mtime :: rest =>
    if path.isEmpty || mtime.isEmpty then
      return none
    let mut entries : Array (Bool × String) := #[]
    for e in rest do
      if e.startsWith "F" then
        entries := entries.push (true, (e.drop 1).toString)
      else if e.startsWith "D" then
        entries := entries.push (false, (e.drop 1).toString)
      else
        return none
    return some (path, mtime, entries)
  | _ => return none

/-- The walk behind `scanRoots`, through the listing cache. Structural on
`depth`: a directory tree is not an inductive type the checker can see, so
the bound is the recursion measure, and six is deeper than any font tree
goes. Accumulates the font files found, the listing of every directory
visited (for the cache rewrite), and whether any directory had to be listed
fresh. Listings are sorted: `readDir` returns filesystem order, which
differs between hosts, and resolution breaks ties by scan order. -/
private def walkCached (known : Std.HashMap String (String × Array (Bool × String))) :
    Nat → System.FilePath → Array String →
    Array (String × String × Array (Bool × String)) → Bool →
    IO (Array String × Array (String × String × Array (Bool × String)) × Bool)
  | 0, _, files, seen, dirty => pure (files, seen, dirty)
  | depth + 1, dir, files, seen, dirty => do
    match ← dir.metadata.toBaseIO with
    | .error _ => pure (files, seen, dirty)
    | .ok md =>
      let key := dir.toString
      let mtime := s!"{md.modified.sec}.{md.modified.nsec}"
      let hit := match known[key]? with
        | some (m, es) => if m == mtime then some es else none
        | none => none
      let (entries, freshlyListed) ← match hit with
        | some es => pure (es, false)
        | none => do
          let raw := (← try dir.readDir catch _ => pure #[]).qsort
            fun a b => a.fileName < b.fileName
          let mut es : Array (Bool × String) := #[]
          for e in raw do
            if isFontFile e.fileName then
              es := es.push (true, e.fileName)
            else if ← e.path.isDir then
              es := es.push (false, e.fileName)
          pure (es, true)
      let mut files := files
      let mut seen := seen.push (key, mtime, entries)
      let mut dirty := dirty || freshlyListed
      for (isFont, name) in entries do
        if isFont then
          files := files.push (dir / name).toString
        else
          let (f, s, d) ← walkCached known depth (dir / name) files seen dirty
          files := f
          seen := s
          dirty := d
      pure (files, seen, dirty)

/-- The built-in locations plus `dirs`, in resolution order. -/
def systemRoots (dirs : List String := []) : IO (List String) := do
  return searchDirs ++ (← extraDirs) ++ dirs

/-- The faces under exactly `roots`, classified, in root order then sorted
path order — so the result is a function of the directories' contents alone,
which is what lets a test suite scan a directory it ships and get the same
faces on every host. Cached by the caller. Probing opens and reads every
face, so chunks of files are probed in parallel; joining in chunk order keeps
the face array exactly what the sequential scan produced, which matters
because resolution prefers earlier faces on ties. -/
def scanRoots (roots : List String) : IO (Array Face) := do
  -- The walk, through the listing cache: a stat per unchanged directory.
  let dirsFile ← dirsPath
  let mut knownDirs : Std.HashMap String (String × Array (Bool × String)) := {}
  if let some df := dirsFile then
    if ← df.pathExists then
      let text ← try IO.FS.readFile df catch _ => pure ""
      for line in text.splitOn "\n" do
        if let some (path, mtime, entries) := parseDirLine line then
          knownDirs := knownDirs.insert path (mtime, entries)
  let mut files : Array String := #[]
  let mut seenDirs : Array (String × String × Array (Bool × String)) := #[]
  let mut dirsDirty := false
  for d in roots do
    let p := System.FilePath.mk d
    if ← p.pathExists then
      let (f, s, dirty) ← walkCached knownDirs 6 p files seenDirs dirsDirty
      files := f
      seenDirs := s
      dirsDirty := dirty
  -- Merged, not replaced: a scan of one small root (a document's own font
  -- directory, the test corpus) must not evict what other roots cost to list.
  if dirsDirty then
    if let some df := dirsFile then
      let mut merged := knownDirs
      for (k, m, es) in seenDirs do
        merged := merged.insert k (m, es)
      try
        if let some parent := df.parent then IO.FS.createDirAll parent
        IO.FS.writeFile df (String.intercalate "\n"
          (merged.toList.map fun (k, m, es) => dirLine k m es) ++ "\n")
      catch _ => pure ()
  -- What the cache remembers, keyed by path + size + mtime.
  let cacheFile ← cachePath
  let mut known : Std.HashMap String (Option Face) := {}
  if let some cf := cacheFile then
    if ← cf.pathExists then
      let text ← try IO.FS.readFile cf catch _ => pure ""
      for line in text.splitOn "\n" do
        if let some (key, face) := parseLine line then
          known := known.insert key face
  -- Hits come from the cache; misses are probed in parallel chunks, in
  -- listing order either way so resolution's tie-breaking is unchanged.
  -- The per-file keys are stats, thousands of them and nothing else touching
  -- the disk while they run, so they go in parallel chunks too.
  let chunk := 64
  let mut keyed : Array (String × Option (String × String)) := #[]
  let mut keyTasks : Array (Task (Except IO.Error
      (Array (String × Option (String × String))))) := #[]
  for c in [0:(files.size + chunk - 1) / chunk] do
    let slice := files.extract (c * chunk) ((c + 1) * chunk)
    keyTasks := keyTasks.push (← IO.asTask do
      let mut out : Array (String × Option (String × String)) := #[]
      for f in slice do
        out := out.push (f, ← fileKey f)
      return out)
  for t in keyTasks do
    match t.get with
    | .ok out => keyed := keyed ++ out
    | .error e => throw e
  let mut toProbe : Array (Nat × String) := #[]
  let mut result : Array (Option Face) := Array.replicate files.size none
  for h : i in [0:keyed.size] do
    let (f, k?) := keyed[i]
    match k? with
    | some (size, mtime) =>
      match known[f ++ "\t" ++ size ++ "\t" ++ mtime]? with
      | some face? => result := result.set! i face?
      | none => toProbe := toProbe.push (i, f)
    | none => toProbe := toProbe.push (i, f)
  let mut tasks : Array (Task (Except IO.Error (Array (Nat × Option Face)))) := #[]
  for c in [0:(toProbe.size + chunk - 1) / chunk] do
    let slice := toProbe.extract (c * chunk) ((c + 1) * chunk)
    tasks := tasks.push (← IO.asTask do
      let mut out : Array (Nat × Option Face) := #[]
      for (i, file) in slice do
        out := out.push (i, ← probe file)
      return out)
  for t in tasks do
    match t.get with
    | .ok out => for (i, face?) in out do result := result.set! i face?
    | .error e => throw e
  -- Rewrite the cache only when something was probed: the common case reads
  -- one file and writes none. Merged like the listing cache, so probing a
  -- new face under one root keeps every other root's classifications.
  if !toProbe.isEmpty then
    if let some cf := cacheFile then
      let mut merged := known
      for h : i in [0:keyed.size] do
        match keyed[i] with
        | (path, some (size, mtime)) =>
          merged := merged.insert (path ++ "\t" ++ size ++ "\t" ++ mtime) result[i]!
        | _ => pure ()
      try
        if let some parent := cf.parent then IO.FS.createDirAll parent
        IO.FS.writeFile cf (String.intercalate "\n"
          (merged.toList.map fun (key, face?) => faceLine key face?) ++ "\n")
      catch _ => pure ()
  return result.filterMap id

/-- All installed faces: the built-in locations plus `dirs`. -/
def scan (dirs : List String := []) : IO (Array Face) := do
  scanRoots (← systemRoots dirs)

private def norm (s : String) : String :=
  String.ofList ((s.toLower.toList).filter fun c => c.isAlphanum)

/-- Does `s` normalise to exactly `target` (itself already normalised, as
chars)? The same answer as `norm s == String.ofList target.toList` without
the four intermediate structures `norm` allocates per name: `resolve` asks
this of every installed face, and a build resolves twelve slot–variant
pairs, so on a 2856-face host the `norm` form was ~15 ms of every build —
most of what resolution cost. -/
private def normEq (s : String) (target : Array Char) : Bool :=
  let fin := s.foldl (init := some 0) fun i? c =>
    match i? with
    | none => none
    | some i =>
      let c := c.toLower
      if c.isAlphanum then
        if h : i < target.size then
          if target[i] == c then some (i + 1) else none
        else none
      else some i
  fin == some target.size

/-- Canonical subfamily names. A face whose subfamily is exactly one of these
is the family's plain face; anything else carries an extra descriptor
("Condensed Bold", "ExtraLight"), which must not win over the plain one —
condensed faces commonly share the typographic family name. -/
private def canonicalSubfamily (s : String) : Bool :=
  ["regular", "bold", "italic", "oblique", "bolditalic", "boldoblique",
   "book", "normal"].contains (norm s)

/-- Target weight for the requested variant. Real families ship a weight
axis, so "bold" means "as close to 700 as this family gets". -/
private def targetWeight (bold : Bool) : Nat := if bold then 700 else 400

/-- Rank candidates for a target weight: closest weight wins; ties prefer the
plain face over one carrying an extra descriptor ("Condensed Bold"), because
condensed faces commonly share the typographic family name. A remaining tie
(the same family installed twice, e.g. a system copy and a TeX Live copy)
goes to the earlier face in scan order — the property `scan`'s ordered join
exists to provide — so the first search directory that holds a family owns it. -/
private def pickWeighted (cands : Array Face) (target : Nat) : Option Face :=
  let sorted := cands.zipIdx.qsort fun (a, ia) (b, ib) =>
    let da := if a.weight ≥ target then a.weight - target else target - a.weight
    let db := if b.weight ≥ target then b.weight - target else target - b.weight
    if da != db then da < db
    else
      let ca := if canonicalSubfamily a.subfamily then 0 else 1
      let cb := if canonicalSubfamily b.subfamily then 0 else 1
      if ca != cb then ca < cb
      else if a.subfamily.length != b.subfamily.length then
        a.subfamily.length < b.subfamily.length
      else ia < ib
  sorted[0]?.map (·.1)

/-- The family a name denotes. A family name denotes itself. A font file name
(`LibertinusSerif-Regular.otf`) — fontspec's way of naming a font that ships
beside the document — denotes the family of the scanned face with that file
name, so its bold and italic are found the way every other family's are. -/
def familyOf (faces : Array Face) (name : String) : String :=
  if isFontFile name then
    match faces.find? fun f => (f.path.splitOn "/").getLast? == some name with
    | some f => f.family
    | none => name
  else name

/-- Best face for a family name and variant, plus whether the family really
offers what was asked for. A family whose heaviest face is "Demi" (600) is
serving a genuine bold, so that counts as satisfied; one with no italic at
all does not, and the caller warns.

A name that is no family may still name a face: fontspec documents ask for
"Fira Sans Light", the Light face of Fira Sans. Family plus subfamily
matches it exactly, the "… Italic" sibling comes along, and the named
weight serves as that name's regular — its bold stays unsatisfied and
warned, because picking a heavier face than the author named would be a
silent substitution. -/
def resolve (faces : Array Face) (family : String) (v : Variant) :
    Option (Face × Bool) :=
  let target := (norm (familyOf faces family)).toList.toArray
  let byFamily := faces.filter fun f => normEq f.family target
  let (inFamily, named) :=
    if byFamily.isEmpty then
      let targetItalic := target ++ "italic".toList.toArray
      (faces.filter fun f =>
        let key := f.family ++ f.subfamily
        normEq key target || normEq key targetItalic, true)
    else (byFamily, false)
  if inFamily.isEmpty then
    none
  else
    let want := if named then targetWeight false else targetWeight v.bold
    -- Italic is categorical: never substitute upright for italic silently.
    let matchingSlant := inFamily.filter fun f => f.italic == v.italic
    let pool := if matchingSlant.isEmpty then inFamily else matchingSlant
    match pickWeighted pool want with
    | none => none
    | some face =>
      let slantOk := face.italic == v.italic
      let weightOk :=
        if v.bold then face.weight ≥ 550 else face.weight ≤ 550
      some (face, slantOk && weightOk)

/-- The face a declared per-variant name denotes: a font file name is that
scanned file's own face; anything else resolves like a family or
family-plus-subfamily name. -/
def resolveNamed (faces : Array Face) (name : String) : Option Face :=
  if isFontFile name then
    faces.find? fun f => (f.path.splitOn "/").getLast? == some name
  else
    (resolve faces name {}).map (·.1)

/-- The face for one slot variant, and the W0006 message when the answer is
not what the document asked for. A face the document declared (fontspec's
`BoldFont=` and siblings) wins over the family's own variant and is met by
definition; a declared face the host lacks degrades to the family's best,
saying so. `none` only when the family itself has no face at all — the
caller's E0403. -/
def resolveVariant (faces : Array Face) (family : String) (declared : Option String)
    (v : Variant) : Option (Face × Option String) :=
  let want :=
    if v.bold && v.italic then "bold italic"
    else if v.bold then "bold"
    else if v.italic then "italic"
    else "regular"
  match declared with
  | some name =>
    match resolveNamed faces name with
    | some face => some (face, none)
    | none =>
      (resolve faces family v).map fun (face, _) =>
        (face, some s!"'{family}' declares '{name}' as its {want} face, \
          which is not installed; '{face.family} {face.subfamily}' substitutes")
  | none =>
    (resolve faces family v).map fun (face, satisfied) =>
      if satisfied then (face, none)
      else (face, some s!"'{family}' has no {want} face; \
        '{face.family} {face.subfamily}' substitutes")

/-- The documented candidate order every scan-derived pick shares
(`fallbackPicks`, `pickCompanion`, `firstMathFace`): family name
(normalised), upright before italic, weight nearest regular, then subfamily
and path. One ordering rule, so a face picked from the scan is a function
of what is installed, never of scan luck. -/
def faceLt (a b : Face) : Bool :=
  if norm a.family != norm b.family then norm a.family < norm b.family
  else if a.italic != b.italic then !a.italic && b.italic
  else
    let da := max a.weight 400 - min a.weight 400
    let db := max b.weight 400 - min b.weight 400
    if da != db then da < db
    else if a.subfamily != b.subfamily then a.subfamily < b.subfamily
    else a.path < b.path

/-- One fold step of `leastBy`: keep the lesser. -/
private def leastStep (lt : Face → Face → Bool) (best : Option Face) (f : Face) :
    Option Face :=
  match best with
  | none => some f
  | some b => if lt f b then some f else some b

/-- The least face under `lt`, by one fold. `leastBy_set_eq` is what it is
shaped for: the answer is a function of the set of faces, so a pick over it
cannot depend on scan order. -/
def leastBy (lt : Face → Face → Bool) (xs : Array Face) : Option Face :=
  xs.toList.foldl (leastStep lt) none

private theorem foldl_least (lt : Face → Face → Bool)
    (htrans : ∀ f g h, lt f g → lt g h → lt f h) :
    ∀ (l : List Face) (m0 : Face),
      (∀ f g, (f = m0 ∨ f ∈ l) → (g = m0 ∨ g ∈ l) → f = g ∨ lt f g ∨ lt g f) →
      ∃ m, List.foldl (leastStep lt) (some m0) l = some m ∧
        (m = m0 ∨ m ∈ l) ∧ ∀ f, (f = m0 ∨ f ∈ l) → f = m ∨ lt m f
  | [], m0, _ => ⟨m0, rfl, .inl rfl, fun f hf => by
      cases hf with
      | inl h => exact .inl h
      | inr h => cases h⟩
  | x :: rest, m0, htotal => by
    have lift : ∀ f, (f = x ∨ f ∈ rest) → (f = m0 ∨ f ∈ x :: rest) := fun f hf =>
      .inr (by cases hf with
        | inl h => exact h ▸ List.mem_cons_self
        | inr h => exact List.mem_cons_of_mem _ h)
    have liftM : ∀ f, (f = m0 ∨ f ∈ rest) → (f = m0 ∨ f ∈ x :: rest) := fun f hf =>
      hf.imp id (List.mem_cons_of_mem _)
    by_cases hx : lt x m0
    · obtain ⟨m, heq, hmem, hleast⟩ :=
        foldl_least lt htrans rest x
          (fun f g hf hg => htotal f g (lift f hf) (lift g hg))
      refine ⟨m, by simpa [leastStep, hx] using heq, lift m hmem, fun f hf => ?_⟩
      by_cases hfm : f = m
      · exact .inl hfm
      right
      cases hf with
      | inl hfm0 =>
        subst hfm0
        cases hleast x (.inl rfl) with
        | inl hxm => exact hxm ▸ hx
        | inr hmx => exact htrans m x f hmx hx
      | inr hfx =>
        cases List.mem_cons.mp hfx with
        | inl h =>
          cases hleast f (.inl h) with
          | inl h2 => exact absurd h2 hfm
          | inr h2 => exact h2
        | inr h =>
          cases hleast f (.inr h) with
          | inl h2 => exact absurd h2 hfm
          | inr h2 => exact h2
    · obtain ⟨m, heq, hmem, hleast⟩ :=
        foldl_least lt htrans rest m0
          (fun f g hf hg => htotal f g (liftM f hf) (liftM g hg))
      refine ⟨m, by simpa [leastStep, hx] using heq, liftM m hmem, fun f hf => ?_⟩
      by_cases hfm : f = m
      · exact .inl hfm
      right
      cases hf with
      | inl hfm0 =>
        cases hleast f (.inl hfm0) with
        | inl h2 => exact absurd h2 hfm
        | inr h2 => exact h2
      | inr hfx =>
        cases List.mem_cons.mp hfx with
        | inl hfx =>
          subst hfx
          cases htotal f m0 (.inr List.mem_cons_self) (.inl rfl) with
          | inl hfm0 =>
            cases hleast f (.inl hfm0) with
            | inl h2 => exact absurd h2 hfm
            | inr h2 => exact h2
          | inr hor =>
            cases hor with
            | inl hlt => exact absurd hlt hx
            | inr hgt =>
              cases hleast m0 (.inl rfl) with
              | inl hm0m => exact hm0m ▸ hgt
              | inr hmm0 => exact htrans m m0 f hmm0 hgt
        | inr hfr =>
          cases hleast f (.inr hfr) with
          | inl h2 => exact absurd h2 hfm
          | inr h2 => exact h2

private theorem leastBy_spec (lt : Face → Face → Bool)
    (htrans : ∀ f g h, lt f g → lt g h → lt f h) (xs : Array Face)
    (htotal : ∀ f g, f ∈ xs → g ∈ xs → f = g ∨ lt f g ∨ lt g f) :
    (xs.toList = [] ∧ leastBy lt xs = none) ∨
      ∃ m, leastBy lt xs = some m ∧ m ∈ xs ∧
        ∀ f, f ∈ xs → f = m ∨ lt m f := by
  unfold leastBy
  match h : xs.toList with
  | [] => exact .inl ⟨rfl, rfl⟩
  | x :: rest =>
    have hxs : ∀ f, (f = x ∨ f ∈ rest) → f ∈ xs := fun f hf => by
      rw [← Array.mem_toList_iff, h]
      cases hf with
      | inl h2 => exact h2 ▸ List.mem_cons_self
      | inr h2 => exact List.mem_cons_of_mem _ h2
    obtain ⟨m, heq, hmem, hleast⟩ :=
      foldl_least lt htrans rest x
        (fun f g hf hg => htotal f g (hxs f hf) (hxs g hg))
    refine .inr ⟨m, ?_, hxs m hmem, fun f hf => ?_⟩
    · simpa [leastStep] using heq
    · have : f = x ∨ f ∈ rest := by
        have := (Array.mem_toList_iff).mpr hf
        rw [h] at this
        exact List.mem_cons.mp this
      exact hleast f this

/-- Which face `leastBy` denotes is a function of the SET of faces: two
scans listing the same faces in any orders answer the same, provided the
order is transitive, asymmetric, and total on those faces. This is the
scan-order-independence core of `pickCompanion_set_eq`. -/
theorem leastBy_set_eq (lt : Face → Face → Bool)
    (htrans : ∀ f g h, lt f g → lt g h → lt f h)
    (hasym : ∀ f g, lt f g → ¬ lt g f)
    (a b : Array Face) (hmem : ∀ f, f ∈ a ↔ f ∈ b)
    (htotal : ∀ f g, f ∈ a → g ∈ a → f = g ∨ lt f g ∨ lt g f) :
    leastBy lt a = leastBy lt b := by
  have htotalB : ∀ f g, f ∈ b → g ∈ b → f = g ∨ lt f g ∨ lt g f := fun f g hf hg =>
    htotal f g ((hmem f).mpr hf) ((hmem g).mpr hg)
  cases leastBy_spec lt htrans a htotal with
  | inl ha =>
    cases leastBy_spec lt htrans b htotalB with
    | inl hb => rw [ha.2, hb.2]
    | inr hb =>
      obtain ⟨m, _, hmb, _⟩ := hb
      have : m ∈ a.toList := Array.mem_toList_iff.mpr ((hmem m).mpr hmb)
      rw [ha.1] at this
      cases this
  | inr ha =>
    obtain ⟨ma, heqa, hma, hlea⟩ := ha
    cases leastBy_spec lt htrans b htotalB with
    | inl hb =>
      have : ma ∈ b.toList := Array.mem_toList_iff.mpr ((hmem ma).mp hma)
      rw [hb.1] at this
      cases this
    | inr hb =>
      obtain ⟨mb, heqb, hmb, hleb⟩ := hb
      rw [heqa, heqb]
      by_cases hab : ma = mb
      · rw [hab]
      · cases hlea mb ((hmem mb).mpr hmb) with
        | inl h2 => exact absurd h2.symm hab
        | inr h2 =>
          cases hleb ma ((hmem ma).mp hma) with
          | inl h3 => exact absurd h3.symm (fun h => hab h.symm)
          | inr h3 => exact absurd h2 (hasym mb ma h3)

/-- One designed body↔math pairing, sourced: the body family a document
declares, its designed math companion, where the pairing is documented, and
the companion's licence (checked at the source). The engine ships none of
these faces — a row costs nothing until the host already has the face. -/
structure Pairing where
  body : String
  companion : String
  source : String
  license : String
  deriving Repr, Inhabited

/-- The designed math companions, as data: one row per body family name the
scan may report, each row citing where the pairing is documented and the
companion's licence. Rows whose licence could not be verified are omitted
until sourced. Sources:
- gust.org.pl/projects/e-foundry/tg-math — the TeX Gyre math companions of
  Pagella (Palatino/URW Palladio), Termes (Times/Nimbus Roman), Bonum
  (Bookman), Schola (Century Schoolbook), and DejaVu; GUST Font License.
- gust.org.pl/projects/e-foundry/lm-math — Latin Modern Math, the companion
  of Latin Modern (and Computer Modern's lineage); GUST Font License.
- stixfonts.org — STIX Two Math beside STIX Two Text; SIL OFL.
- ctan.org/pkg/libertinus — Libertinus Math beside Libertinus Serif; OFL.
- ctan.org/pkg/garamond-math — "should be used together with EB Garamond";
  OFL.
- ctan.org/pkg/erewhon-math — "Utopia-based OpenType math font" beside
  Erewhon; OFL.
- ctan.org/pkg/firamath — Fira Math, the sans math face designed to match
  Fira Sans; OFL. -/
def mathCompanions : Array Pairing := #[
  { body := "Palatino", companion := "TeX Gyre Pagella Math"
    source := "gust.org.pl/projects/e-foundry/tg-math", license := "GUST Font License" },
  { body := "Palatino Linotype", companion := "TeX Gyre Pagella Math"
    source := "gust.org.pl/projects/e-foundry/tg-math", license := "GUST Font License" },
  { body := "URW Palladio L", companion := "TeX Gyre Pagella Math"
    source := "gust.org.pl/projects/e-foundry/tg-math", license := "GUST Font License" },
  { body := "P052", companion := "TeX Gyre Pagella Math"
    source := "gust.org.pl/projects/e-foundry/tg-math", license := "GUST Font License" },
  { body := "TeX Gyre Pagella", companion := "TeX Gyre Pagella Math"
    source := "gust.org.pl/projects/e-foundry/tg-math", license := "GUST Font License" },
  { body := "Times", companion := "TeX Gyre Termes Math"
    source := "gust.org.pl/projects/e-foundry/tg-math", license := "GUST Font License" },
  { body := "Times New Roman", companion := "TeX Gyre Termes Math"
    source := "gust.org.pl/projects/e-foundry/tg-math", license := "GUST Font License" },
  { body := "Nimbus Roman", companion := "TeX Gyre Termes Math"
    source := "gust.org.pl/projects/e-foundry/tg-math", license := "GUST Font License" },
  { body := "Nimbus Roman No9 L", companion := "TeX Gyre Termes Math"
    source := "gust.org.pl/projects/e-foundry/tg-math", license := "GUST Font License" },
  { body := "Liberation Serif", companion := "TeX Gyre Termes Math"
    source := "gust.org.pl/projects/e-foundry/tg-math", license := "GUST Font License" },
  { body := "TeX Gyre Termes", companion := "TeX Gyre Termes Math"
    source := "gust.org.pl/projects/e-foundry/tg-math", license := "GUST Font License" },
  { body := "STIX Two Text", companion := "STIX Two Math"
    source := "stixfonts.org", license := "SIL Open Font License" },
  { body := "Bookman", companion := "TeX Gyre Bonum Math"
    source := "gust.org.pl/projects/e-foundry/tg-math", license := "GUST Font License" },
  { body := "URW Bookman", companion := "TeX Gyre Bonum Math"
    source := "gust.org.pl/projects/e-foundry/tg-math", license := "GUST Font License" },
  { body := "Bookman Old Style", companion := "TeX Gyre Bonum Math"
    source := "gust.org.pl/projects/e-foundry/tg-math", license := "GUST Font License" },
  { body := "TeX Gyre Bonum", companion := "TeX Gyre Bonum Math"
    source := "gust.org.pl/projects/e-foundry/tg-math", license := "GUST Font License" },
  { body := "Century Schoolbook", companion := "TeX Gyre Schola Math"
    source := "gust.org.pl/projects/e-foundry/tg-math", license := "GUST Font License" },
  { body := "Century Schoolbook L", companion := "TeX Gyre Schola Math"
    source := "gust.org.pl/projects/e-foundry/tg-math", license := "GUST Font License" },
  { body := "C059", companion := "TeX Gyre Schola Math"
    source := "gust.org.pl/projects/e-foundry/tg-math", license := "GUST Font License" },
  { body := "New Century Schoolbook", companion := "TeX Gyre Schola Math"
    source := "gust.org.pl/projects/e-foundry/tg-math", license := "GUST Font License" },
  { body := "TeX Gyre Schola", companion := "TeX Gyre Schola Math"
    source := "gust.org.pl/projects/e-foundry/tg-math", license := "GUST Font License" },
  { body := "DejaVu Serif", companion := "TeX Gyre DejaVu Math"
    source := "gust.org.pl/projects/e-foundry/tg-math", license := "GUST Font License" },
  { body := "DejaVu Sans", companion := "TeX Gyre DejaVu Math"
    source := "gust.org.pl/projects/e-foundry/tg-math", license := "GUST Font License" },
  { body := "Libertinus Serif", companion := "Libertinus Math"
    source := "ctan.org/pkg/libertinus", license := "SIL Open Font License" },
  { body := "EB Garamond", companion := "Garamond-Math"
    source := "ctan.org/pkg/garamond-math", license := "SIL Open Font License" },
  { body := "Utopia", companion := "Erewhon Math"
    source := "ctan.org/pkg/erewhon-math", license := "SIL Open Font License" },
  { body := "Erewhon", companion := "Erewhon Math"
    source := "ctan.org/pkg/erewhon-math", license := "SIL Open Font License" },
  { body := "Fira Sans", companion := "Fira Math"
    source := "ctan.org/pkg/firamath", license := "SIL Open Font License" },
  { body := "Latin Modern Roman", companion := "Latin Modern Math"
    source := "gust.org.pl/projects/e-foundry/lm-math", license := "GUST Font License" },
  { body := "CMU Serif", companion := "Latin Modern Math"
    source := "gust.org.pl/projects/e-foundry/lm-math", license := "GUST Font License" }]

/-- The designed math companion of `body` on this host: the sourced table
row naming the family, resolved against the scan as the least face (under
the one documented order) whose family is the row's companion. `none` when
no row names the family or the host lacks the companion face. -/
def pickCompanion (faces : Array Face) (body : String) : Option (Pairing × Face) := do
  let row ← mathCompanions.find? fun p =>
    normEq body ((norm p.body).toList.toArray)
  let face ← leastBy faceLt (faces.filter fun f =>
    normEq f.family ((norm row.companion).toList.toArray))
  return (row, face)

/-- Scan-order independence: the companion pick is a function of the set of
installed faces — the row is data and the face is `leastBy`'s least member
of the matching faces (the engine's one documented order, `faceLt`), so two
scans listing the same faces in any orders pick the same companion. The
order axioms are hypotheses because `faceLt` bottoms out in string
comparison, whose order lemmas the library does not carry; the suite checks
them over the shipped faces, and `fontcache-check` stays the end-to-end
oracle. -/
theorem pickCompanion_set_eq (a b : Array Face) (body : String)
    (hmem : ∀ f, f ∈ a ↔ f ∈ b)
    (htrans : ∀ f g h, faceLt f g → faceLt g h → faceLt f h)
    (hasym : ∀ f g, faceLt f g → ¬ faceLt g f)
    (htotal : ∀ f g, f ∈ a → g ∈ a → f = g ∨ faceLt f g ∨ faceLt g f) :
    pickCompanion a body = pickCompanion b body := by
  unfold pickCompanion
  cases mathCompanions.find? fun p => normEq body ((norm p.body).toList.toArray) with
  | none => rfl
  | some row =>
    have heq := leastBy_set_eq faceLt htrans hasym
      (a.filter fun f => normEq f.family ((norm row.companion).toList.toArray))
      (b.filter fun f => normEq f.family ((norm row.companion).toList.toArray))
      (fun f => by
        simp only [Array.mem_filter]
        exact and_congr_left fun _ => hmem f)
      (fun f g hf hg =>
        htotal f g (Array.mem_filter.mp hf).1 (Array.mem_filter.mp hg).1)
    show (leastBy faceLt (Array.filter (fun f => normEq f.family (norm row.companion).toList.toArray) a)).bind
        (fun face => some (row, face)) =
      (leastBy faceLt (Array.filter (fun f => normEq f.family (norm row.companion).toList.toArray) b)).bind
        (fun face => some (row, face))
    rw [heq]

/-- The face serving a document that declares no math face and whose body
family has no installed companion: the first installed face carrying an
OpenType MATH table, under the same documented order (`faceLt`). Only table
directories are read, and only until a MATH face answers; `none` when no
installed face has one — the caller degrades to source text, as today. -/
def firstMathFace (faces : Array Face) : IO (Option Face) := do
  for f in faces.qsort faceLt do
    if (← tableImage f.path (· == "MATH")).isSome then
      return some f
  return none

/-- The math face for a document that declares none: the body family's
designed companion when the host has it (with its table row), else the
first installed MATH-table face, else `none`. One decision, shared by the
driver and the test harness, so a fixture exercises the same resolution a
build runs. -/
def pickMathFace (faces : Array Face) (body : String) :
    IO (Option (Face × Option Pairing)) := do
  match pickCompanion faces body with
  | some (row, face) => return some (face, some row)
  | none => return (← firstMathFace faces).map ((·, none))

/-- For each scalar no declared face covers, the scanned face that will set
it. The order is documented, never scan luck: candidates are every scanned
face sorted by family name (normalised), upright before italic, weight
nearest regular, then subfamily and path — and the first whose cmap holds
the scalar wins. Only candidate cmaps are read, and only until every scalar
is served; a scalar no face covers is absent from the result. -/
def fallbackPicks (faces : Array Face) (needed : Array Char) :
    IO (Array (Char × String)) := do
  let sorted := faces.qsort faceLt
  let mut remaining := needed
  let mut out : Array (Char × String) := #[]
  for f in sorted do
    if remaining.isEmpty then
      break
    let some image ← tableImage f.path (· == "cmap") | continue
    let ranges := Font.cmapRanges image
    if ranges.isEmpty then
      continue
    let mut still : Array Char := #[]
    for c in remaining do
      if (Font.gidIn ranges c).isSome then
        out := out.push (c, f.path)
      else
        still := still.push c
    remaining := still
  return out

/-- Installed families that resemble a name: sharing a word, or within an
edit or two of it. `Nimbus Roman` finds `Nimbus Sans L` and `Nimbus Mono`;
`Libertinus` finds every Libertinus face. At most eight, closest first. -/
def nearest (families : Array String) (wanted : String) : Array String :=
  let words (s : String) : List String :=
    (s.toLower.splitOn " ").filter fun w => !w.isEmpty && w.length > 1
  let want := words wanted
  let score (fam : String) : Nat :=
    let got := words fam
    let shared := (want.filter got.contains).length
    -- Prefix of the first word counts too: `Nimbus` vs `NimbusSans`.
    let prefixHit := match want.head?, got.head? with
      | some a, some b => a.startsWith b || b.startsWith a
      | _, _ => false
    shared * 2 + (if prefixHit then 1 else 0)
  let scored := families.filterMap fun f =>
    let sc := score f
    if sc > 0 then some (sc, f) else none
  let sorted := scored.qsort fun a b => a.1 > b.1 || (a.1 == b.1 && a.2 < b.2)
  (sorted.extract 0 8).map (·.2)

/-- Family names present, sorted, for diagnostics and . -/
def families (faces : Array Face) : Array String := Id.run do
  -- One normalised key per face, kept in a set. The earlier `seen.any` with
  -- `norm` on both sides re-normalised every prior name for every face:
  -- four million string allocations and two seconds on a 2856-face host,
  -- paid on every failed font lookup.
  let mut keys : Std.HashSet String := {}
  let mut out : Array String := #[]
  for f in faces do
    let k := norm f.family
    unless keys.contains k do
      keys := keys.insert k
      out := out.push f.family
  return out.qsort (· < ·)

/-- Families tried, in order, when a document declares no `\fonts`. -/
def defaultFamilies : List String :=
  ["DejaVu Sans", "Helvetica Neue", "Helvetica", "Arial", "Liberation Sans",
   "Nimbus Sans", "Inter"]

/-- The family a document with no `\fonts` uses: the first preferred name
that resolves, else the first family calling itself sans, else the first
face of any kind. `none` only when no face is installed at all — so the
default exists on any host with any scannable font, by construction. -/
def defaultFamily (faces : Array Face) : Option String :=
  match defaultFamilies.find? fun n => (resolve faces n {}).isSome with
  | some n => some n
  | none =>
    match faces.find? fun f => ((norm f.family).splitOn "sans").length > 1 with
    | some f => some f.family
    | none => faces[0]?.map (·.family)

end LeanTex.Core.FontDb
