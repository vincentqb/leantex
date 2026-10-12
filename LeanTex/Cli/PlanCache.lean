module

public import LeanTex.Cli.Engine
public import LeanTex.Core.Image
import LeanTex.Cli.AtomicFile
import LeanTex.Core.Flate
import LeanTex.Core.SlotRecord

/-! The image plan cache: an included image's plan is the pure planner's
answer for its bytes and parameters, so it is kept under them and under the
engine that planned it, beside the font and boundary caches. -/

namespace LeanTex.Cli.PlanCache

open LeanTex.Core

/-- Where a plan is filed: by the *content* (so a re-exported file under the
same name re-plans and an unchanged one never does) and by the plan
parameters (every non-source input to `Image.plan`, so two plans that could
differ never share a slot — `planParams_serialize_inj`). No document or
output path enters it. -/
public def cachePath (dir : System.FilePath) (params : Image.PlanParams) (bytes : ByteArray) :
    System.FilePath :=
  dir / "imgs" / s!"{Flate.contentKey bytes}-{params.key}.img"

/-- **The key a plan is stored under**: the format, the source's content key,
the plan parameters and the engine that planned it
(`SlotRecord.lookup_exact`): an upgraded planner re-plans, and
`Image.decodeBin`'s magic orphans a format change. -/
public def slotKey (engine : String) (params : Image.PlanParams) (bytes : ByteArray) :
    Array String :=
  #["image-plan-v1", Flate.contentKey bytes, params.key, engine]

/-- Plan through the cache. The header is probed first; only a plan the
planner itself says does real work — an alpha PNG's inflate, split, deflate
(`Image.Plan.recodes`, `recodes_iff`) — is worth a disk read, and everything
else plans directly from the probe. The cached value is the pure plan's own
output (`Image.encodeBin`), so a hit equals a recomputation —
`decodeBin_encodeBin_id`, the transparency statement — and only a slot this
engine wrote answers. Returns whether this was a hit, for the phase line. -/
public def decodeCached (cache : Option Engine.Cache) (params : Image.PlanParams)
    (bytes : ByteArray) : IO (Except String Image.Plan × Bool) := do
  let src ← match Image.probe bytes with
    | .error e => return (.error e, false)
    | .ok src => pure src
  unless Image.Plan.recodes params src do return (Image.plan params src, false)
  let slot := cache.map fun c => (cachePath c.dir params bytes, slotKey c.engine params bytes)
  if let some (path, key) := slot then
    if let .ok blob ← (IO.FS.readBinFile path).toBaseIO then
      if let some pl := (SlotRecord.lookup key blob).bind Image.decodeBin then
        return (.ok pl, true)
  let res := Image.plan params src
  if let some (path, key) := slot then
    if let .ok pl := res then
      let blob := Image.encodeBin pl
      if SlotRecord.storable key blob then
        try
          if let some parent := path.parent then IO.FS.createDirAll parent
          AtomicFile.write path (SlotRecord.encode key blob)
        catch _ => pure ()
  return (res, false)

end LeanTex.Cli.PlanCache
