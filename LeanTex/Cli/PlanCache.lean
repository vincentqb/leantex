module

public import LeanTex.Cli.Engine
public import LeanTex.Core.Image
import LeanTex.Cli.AtomicFile
import LeanTex.Core.Flate
import LeanTex.Core.SlotRecord

/-! The image plan cache, keyed by an image's bytes, its plan parameters and the planning
engine. -/

namespace LeanTex.Cli.PlanCache

open LeanTex.Core

/-- Where a plan is filed: by the source's content and every plan parameter, never by a
path. -/
public def cachePath (dir : System.FilePath) (params : Image.PlanParams) (bytes : ByteArray) :
    System.FilePath :=
  dir / "imgs" / s!"{Flate.contentKey bytes}-{params.key}.img"

/-- The key a plan is stored under: format, content key, plan parameters and planning
engine. -/
public def slotKey (engine : String) (params : Image.PlanParams) (bytes : ByteArray) :
    Array String :=
  #["image-plan-v1", Flate.contentKey bytes, params.key, engine]

/-- Plan through the cache, read only for a plan that recodes; also returns whether it was
a hit. -/
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
