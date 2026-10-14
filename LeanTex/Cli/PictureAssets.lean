module

public import LeanTex.Cli.ConvCache
import LeanTex.Cli.FontDiscovery
import LeanTex.Cli.Host
import LeanTex.Cli.RunBounded
import LeanTex.Cli.ToolProbe
import LeanTex.Core.Flate
import LeanTex.Core.Utf8

/-! Fulfil standalone picture requests in owned scratch with checked cache answers,
assuming a tool finishes its writes before its invocation returns. -/

namespace LeanTex.Cli.PictureAssets

open LeanTex.Core

/-- A request as its cache keys it: the standalone, then one line per file it reads, by
path and content key. -/
public def keyed (wrapped : String) (inputs : Array (String × ByteArray)) : String :=
  inputs.foldl (fun s (p, b) => s ++ s!"% input {p} {Flate.contentKey b}\n") wrapped

public def key (wrapped : String) : String := Flate.contentKey wrapped.toUTF8

public def slotName (wrapped tool stamp version : String) : String :=
  ConvCache.slotName wrapped.toUTF8 "standalone-picture-v2"
    (String.intercalate "\u0000" [tool, stamp, version])

/-- An input's leading `..` steps and remaining components relative to the standalone, or
`none` for a path the scratch cannot hold. -/
public def stagePath (p : String) : Option (Nat × List String) :=
  if p.startsWith "/" then none else
  let comps := (p.splitOn "/").filter fun c => !c.isEmpty && c != "."
  let ups := (comps.takeWhile (· == "..")).length
  let rest := comps.drop ups
  if rest.isEmpty || rest.contains ".." then none else some (ups, rest)

private def below (root : System.FilePath) (levels : Nat) : System.FilePath :=
  (List.replicate levels "s").foldl (fun (p : System.FilePath) (c : String) => p / c) root

public structure Answer where
  result : ConvCache.Result
  cached : Bool := false

public def cacheDir : IO (Option System.FilePath) := do
  try
    let some root ← FontDiscovery.cacheDir | return none
    let dir := root / "pics"
    IO.FS.createDirAll dir
    return some dir
  catch _ => return none

private def readAnswer (path : System.FilePath) : IO (Option (Except String ByteArray)) := do
  return (← (IO.FS.readBinFile path).toBaseIO).toOption.bind ConvCache.decode

/-- A complete checked drawing of this request from the cache, the only answer that may
serve without a tool. -/
public def previous (dir : System.FilePath) (key : String) : IO (Option ByteArray) := do
  try
    let entries := (← dir.readDir).qsort (fun a b => a.fileName < b.fileName)
    for entry in entries do
      if entry.fileName.startsWith (key ++ "-") && entry.fileName.endsWith ".answer" then
        if let some (.ok bytes) ← readAnswer entry.path then return some bytes
    return none
  catch _ => return none

/-- The tool's error lines, or its last nonblank line, kept past scratch cleanup. -/
private def logTail (log : String) : String :=
  let lines := (log.splitOn "\n").filter (!·.trimAscii.toString.isEmpty)
  let bangs := lines.filter (·.startsWith "!")
  let picked := if bangs.isEmpty then lines.reverse.take 1 else bangs.take 3
  String.intercalate " · " (picked.map (·.trimAscii.toString))

private def produce (tool wrapped : String) (inputs : Array (String × ByteArray)) :
    IO ConvCache.Result := do
  try
    -- TeX engines choose their format by the invoked name, so a relative path keeps it.
    let command ← if tool.contains '/' && (System.FilePath.mk tool).isRelative then
        pure ((← IO.currentDir) / tool).toString
      else pure tool
    Host.withScratch fun scratch => do
      let staged := inputs.filterMap fun (p, b) => (stagePath p).map (·, b)
      let depth := staged.foldl (fun d ((ups, _), _) => max d ups) 0
      let work := below scratch depth
      IO.FS.createDirAll work
      for ((ups, rest), bytes) in staged do
        let target := rest.foldl (fun (p : System.FilePath) (c : String) => p / c)
          (below scratch (depth - ups))
        if let some parent := target.parent then IO.FS.createDirAll parent
        IO.FS.writeBinFile target bytes
      IO.FS.writeFile (work / "pic.tex") wrapped
      let ended ← RunBounded.runBounded command
        #["-interaction=batchmode", "-halt-on-error", "pic.tex"] work 120000
      let produced := work / "pic.pdf"
      let bytes ← if ← produced.pathExists then IO.FS.readBinFile produced
        else pure ByteArray.empty
      let logPath := work / "pic.log"
      let log ← if ← logPath.pathExists then
          pure (PicCache.Log.says ((logTail (Utf8.decode (← IO.FS.readBinFile logPath)).text).replace
            work.toString "<scratch>"))
        else pure PicCache.Log.absent
      -- The scratch directory's random name never reaches a reason.
      let said := PicCache.saidOf (ended.err.replace work.toString "<scratch>")
      return ConvCache.Result.ofRun ended.ran log said bytes
  catch e => return { outcome := .inconclusive (toString e) }

/-- Fulfil a request in its own scratch and publish one integrity-checked answer by atomic
rename; an unfinished attempt writes nothing. -/
public def fulfil (dir : Option System.FilePath) (tool stamp version wrapped : String)
    (inputs : Array (String × ByteArray) := #[]) : IO Answer := do
  let slot ← if !stamp.isEmpty && !version.isEmpty && (← ToolProbe.witness tool) == stamp then
      pure (dir.map (· / slotName (keyed wrapped inputs) tool stamp version))
    else pure none
  if let some path := slot then
    if let some answer ← readAnswer path then
      return { result := ConvCache.Result.replay answer, cached := true }
  let result ← produce tool wrapped inputs
  if let some path := slot then
    if (← ToolProbe.witness tool) == stamp then
      if let some answer := result.record? then
        try
          if let some parent := path.parent then IO.FS.createDirAll parent
          ConvCache.atomicWrite path (ConvCache.encode answer)
        catch _ => pure ()
  return { result }

end LeanTex.Cli.PictureAssets
