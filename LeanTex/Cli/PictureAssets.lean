import LeanTex.Cli.FontDiscovery
import LeanTex.Cli.ConvCache

/-! Fulfil standalone picture requests with owned scratch and checked cache
answers. Tools must finish their writers with the foreground invocation;
atomic publication protects readers, not arbitrary daemon descendants. -/

namespace LeanTex.Cli.PictureAssets

open LeanTex.Core

def key (wrapped : String) : String := Flate.contentKey wrapped.toUTF8

def slotName (wrapped tool stamp version : String) : String :=
  ConvCache.slotName wrapped.toUTF8 "standalone-picture"
    (String.intercalate "\u0000" [tool, stamp, version])

structure Answer where
  result : ConvCache.Result
  cached : Bool := false

def cacheDir : IO (Option System.FilePath) := do
  try
    let some root ← FontDiscovery.cacheDir | return none
    let dir := root / "pics"
    IO.FS.createDirAll dir
    return some dir
  catch _ => return none

private def readAnswer (path : System.FilePath) : IO (Option (Except String ByteArray)) := do
  return (← (IO.FS.readBinFile path).toBaseIO).toOption.bind ConvCache.decode

/-- Without a tool, only complete checked drawings of this request can
serve. Legacy raw PDFs and remembered refusals supply no such evidence. -/
def previous (dir : System.FilePath) (key : String) : IO (Option ByteArray) := do
  try
    let entries := (← dir.readDir).qsort (fun a b => a.fileName < b.fileName)
    for entry in entries do
      if entry.fileName.startsWith (key ++ "-") && entry.fileName.endsWith ".answer" then
        if let some (.ok bytes) ← readAnswer entry.path then return some bytes
    return none
  catch _ => return none

/-- Keep the tool's error lines, or its last nonblank line when there are
none, so the diagnostic survives scratch cleanup. -/
private def logTail (log : String) : String :=
  let lines := (log.splitOn "\n").filter (!·.trimAscii.toString.isEmpty)
  let bangs := lines.filter (·.startsWith "!")
  let picked := if bangs.isEmpty then lines.reverse.take 1 else bangs.take 3
  String.intercalate " · " (picked.map (·.trimAscii.toString))

private def produce (tool wrapped : String) : IO ConvCache.Result := do
  try
    -- Anchor relative paths to the caller, preserving the invoked alias:
    -- TeX engines use that name to choose their format.
    let command ← if tool.contains '/' && (System.FilePath.mk tool).isRelative then
        pure ((← IO.currentDir) / tool).toString
      else pure tool
    IO.FS.withTempDir fun work => do
      IO.FS.writeFile (work / "pic.tex") wrapped
      let ended ← RunBounded.runBounded command
        #["-interaction=batchmode", "-halt-on-error", "pic.tex"] work 120000
      let produced := work / "pic.pdf"
      let bytes ← if ← produced.pathExists then IO.FS.readBinFile produced
        else pure ByteArray.empty
      let logPath := work / "pic.log"
      let log ← if ← logPath.pathExists then
          pure (PicCache.Log.says (logTail (← IO.FS.readFile logPath)))
        else pure PicCache.Log.absent
      return { outcome := PicCache.outcome ended.ran (!bytes.isEmpty) log, bytes }
  catch e => return { outcome := .inconclusive (toString e) }

private def replay (answer : Except String ByteArray) : ConvCache.Result :=
  match answer with
  | .ok bytes => { outcome := .drawn, bytes }
  | .error why => { outcome := .refused why }

/-- Independent invocations never share scratch. Each captures its result
before cleanup, then publishes one integrity-checked answer by atomic rename.
Cache failures leave the produced answer intact; unfinished attempts write
nothing (`ConvCache.inconclusive_retried_exact`). -/
def fulfil (dir : Option System.FilePath) (tool stamp version wrapped : String) :
    IO Answer := do
  let slot ← if !stamp.isEmpty && !version.isEmpty && (← ToolProbe.witness tool) == stamp then
      pure (dir.map (· / slotName wrapped tool stamp version))
    else pure none
  if let some path := slot then
    if let some answer ← readAnswer path then return { result := replay answer, cached := true }
  let result ← produce tool wrapped
  if let some path := slot then
    if (← ToolProbe.witness tool) == stamp then
      if let some answer := result.record? then
        try
          if let some parent := path.parent then IO.FS.createDirAll parent
          ConvCache.atomicWrite path (ConvCache.encode answer)
        catch _ => pure ()
  return { result }

end LeanTex.Cli.PictureAssets
