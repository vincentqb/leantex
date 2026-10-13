module

public import LeanTex.Cli.PicCache
import LeanTex.Cli.FontDiscovery
import LeanTex.Cli.AtomicFile
import LeanTex.Cli.RunBounded
import LeanTex.Cli.ToolProbe
import LeanTex.Cli.Engine
import LeanTex.Core.Flate
import LeanTex.Core.SlotRecord
import LeanTex.Version

namespace LeanTex.Cli.ConvCache

open LeanTex.Core

public structure Result where
  outcome : PicCache.Outcome
  bytes : ByteArray := ByteArray.empty

public def Result.answer (r : Result) : Except String ByteArray :=
  match r.outcome with
  | .drawn => if r.bytes.isEmpty then .error "no usable output was produced" else .ok r.bytes
  | .refused why | .inconclusive why => .error why

public def Result.record? (r : Result) : Option (Except String ByteArray) :=
  match r.outcome with
  | .drawn => if r.bytes.isEmpty then none else some (.ok r.bytes)
  | .refused why => if why.isEmpty then none else some (.error why)
  | .inconclusive _ => none

public theorem inconclusive_retried_exact (why : String) (bytes : ByteArray) :
    Result.record? ⟨.inconclusive why, bytes⟩ = none := by rfl

public theorem annotate_record_exact (o : PicCache.Outcome) (log : PicCache.Log) (said : String)
    (bytes : ByteArray) :
    Result.record? ⟨PicCache.annotate o log said, bytes⟩ = Result.record? ⟨o, bytes⟩ := by
  cases o <;> cases log <;> simp only [PicCache.annotate] <;> (try split) <;> rfl

public theorem empty_retried_exact :
    Result.record? ⟨.drawn, ByteArray.empty⟩ = none := by rfl

public theorem refusal_replays_exact (why : String) (h : why.isEmpty = false) (bytes : ByteArray) :
    Result.record? ⟨.refused why, bytes⟩ = some (.error why) := by
  simp [Result.record?, h]

/-- A remembered answer read back as the result it records. -/
public def Result.replay : Except String ByteArray → Result
  | .ok bytes => { outcome := .drawn, bytes }
  | .error why => { outcome := .refused why }

public theorem replay_record_exact (r : Result) (a : Except String ByteArray)
    (h : r.record? = some a) :
    (Result.replay a).outcome = r.outcome ∧ (Result.replay a).answer = r.answer := by
  rcases r with ⟨outcome, bytes⟩
  cases outcome with
  | drawn =>
    by_cases hb : bytes.isEmpty
    · simp [Result.record?, hb] at h
    · simp only [Result.record?, hb] at h
      cases h
      simp [Result.replay, Result.answer, hb]
  | refused why =>
    by_cases hw : why.isEmpty
    · simp [Result.record?, hw] at h
    · simp only [Result.record?, hw] at h
      cases h
      simp [Result.replay, Result.answer]
  | inconclusive why => simp [Result.record?] at h

-- One envelope holds either answer, so racing writers cannot leave two verdicts for one slot.
public def encode (answer : Except String ByteArray) : ByteArray :=
  let (tag, payload) := match answer with
    | .ok bytes => ("O", bytes)
    | .error why => ("E", why.toUTF8)
  (tag ++ Flate.contentKey payload ++ "\n").toUTF8 ++ payload

public def decode (bytes : ByteArray) : Option (Except String ByteArray) := do
  if bytes.size ≤ 34 then none else do
    let header ← String.fromUTF8? (bytes.extract 0 34)
    let payload := bytes.extract 34 bytes.size
    let key := Flate.contentKey payload ++ "\n"
    if header == "O" ++ key then some (.ok payload)
    else if header == "E" ++ key then some (.error (← String.fromUTF8? payload))
    else none

public theorem replay_decode_exact (bytes : ByteArray) (a : Except String ByteArray)
    (h : decode bytes = some a) : (Result.replay a).answer = a := by
  cases a with
  | error why => rfl
  | ok payload =>
    unfold decode at h
    split at h
    · simp at h
    · rename_i hsize
      cases hh : String.fromUTF8? (bytes.extract 0 34) with
      | none => simp [hh] at h
      | some header =>
        simp only [hh, Option.bind_eq_bind, Option.bind_some] at h
        split at h
        · simp only [Option.some.injEq, Except.ok.injEq] at h
          subst h
          have hne : ¬bytes.size - 34 = 0 := by omega
          simp [Result.replay, Result.answer, ByteArray.isEmpty, hne]
        · split at h
          · cases hp : String.fromUTF8? (bytes.extract 34 bytes.size) <;> simp [hp] at h
          · simp at h

public def slotName (source : ByteArray) (recipe identity : String) : String :=
  let variant := Flate.contentKey (String.intercalate "\u0000"
    ["vector-cache-v3", LeanTex.version, recipe, identity]).toUTF8
  Flate.contentKey source ++ "-" ++ variant ++ ".answer"

public def atomicWrite (target : System.FilePath) (bytes : ByteArray) : IO Unit :=
  AtomicFile.write target bytes

private def versionBudgetMs : Nat := 2000

private def probeVersion (tool : String) : IO PicCache.Tool := do
  let args := if tool == "pdftocairo" then #["-v"] else #["--version"]
  let got ← RunBounded.runBounded tool args (← IO.currentDir) versionBudgetMs 100
  let line := ((got.out ++ "\n" ++ got.err).splitOn "\n").find?
    (fun s => !s.trimAscii.isEmpty)
  return PicCache.probed got.ran (line.getD "").trimAscii.toString

private def identify (dir : System.FilePath) (tool : String) : IO (Option String) := do
  let stamp ← ToolProbe.witness tool
  if stamp.isEmpty then return none
  let memoPath := dir / ("tool-" ++ Flate.contentKey tool.toUTF8 ++ ".ver")
  let memo := (← (IO.FS.readFile memoPath).toBaseIO).toOption.bind PicCache.readVersionMemo
  let answer ← match PicCache.versionStep memo stamp with
    | .remembered version => pure (.present version)
    | .probe =>
      let answer ← probeVersion tool
      if let .present version := answer then
        discard <| (atomicWrite memoPath (PicCache.versionMemo stamp version).toUTF8).toBaseIO
      pure answer
  if stamp != (← ToolProbe.witness tool) then return none
  match answer with
  | .absent _ => return none
  | .present version => return some (tool ++ "\n" ++ stamp ++ "\n" ++ version)

private def identity (dir : System.FilePath) (tools : Array String) : IO (Option String) := do
  try
    let mut ids := #[]
    for tool in tools do
      let some id ← identify dir tool | return none
      ids := ids.push id
    return some (String.intercalate "\u0000" ids.toList)
  catch _ => return none

private def cacheDir : IO (Option System.FilePath) := do
  try
    let some root ← FontDiscovery.cacheDir | return none
    let dir := root / "convs"
    IO.FS.createDirAll dir
    return some dir
  catch _ => return none

/-- The key a conversion's answer is stored under: format, the source's content key,
recipe, tool identity and engine. -/
public def slotKey (source : ByteArray) (recipe identity engine : String) : Array String :=
  #["conversion-v1", Flate.contentKey source, recipe, identity, engine]

/-- A slot's answer, whichever engine wrote it. -/
public def decodeSlot (bytes : ByteArray) : Option (Except String ByteArray) :=
  (SlotRecord.decode bytes).bind fun (_, record) => decode record

/-- `cachedResult` through the cache in `dir` for `engine`; missing either, nothing is
read or written. -/
public def cachedResultIn (dir : Option System.FilePath) (engine : Option String)
    (source : ByteArray) (recipe : String) (tools : Array String)
    (eligible : Bool) (produce : IO (Result × Bool)) : IO Result := do
  let slot ← if eligible then do
      let some dir := dir | pure none
      let some engine := engine | pure none
      let some id ← identity dir tools | pure none
      pure (some (dir / slotName source recipe id, dir, id, slotKey source recipe id engine))
    else pure none
  if let some (path, _, _, key) := slot then
    let stored := (← (IO.FS.readBinFile path).toBaseIO).toOption
    if let some answer := (stored.bind (SlotRecord.lookup key)).bind decode then
      return Result.replay answer
  let (got, independent) ← produce
  if independent then
    if let some (path, dir, before, key) := slot then
      -- A binary replaced during the attempt cannot fill the earlier slot.
      if (← identity dir tools) == some before then
        if let some answer := got.record? then
          let record := encode answer
          if SlotRecord.storable key record then
            discard <| (atomicWrite path (SlotRecord.encode key record)).toBaseIO
  return got

/-- The conversion's whole result, warm or fresh, so a caller can tell a refusal from an
unfinished attempt. -/
public def cachedResult (source : ByteArray) (recipe : String) (tools : Array String)
    (eligible : Bool) (produce : IO (Result × Bool)) : IO Result := do
  let dir ← if eligible then cacheDir else pure none
  cachedResultIn dir (← Engine.engineId) source recipe tools eligible produce

public def cached (source : ByteArray) (recipe : String) (tools : Array String)
    (eligible : Bool) (produce : IO (Result × Bool)) : IO (Except String ByteArray) :=
  Result.answer <$> cachedResult source recipe tools eligible produce

end LeanTex.Cli.ConvCache
