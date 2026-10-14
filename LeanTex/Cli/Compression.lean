module

public import LeanTex.Cli.Batch
public import LeanTex.Cli.Engine
import LeanTex.Cli.ConvCache
public import LeanTex.Core.Flate
import LeanTex.Core.SlotRecord

namespace LeanTex.Cli.Compression

open LeanTex.Core

/-- The flate cache, whose slots answer only the engine that wrote them. -/
public abbrev Cache := Engine.Cache

public def cachePath (root : System.FilePath) (input : ByteArray) : System.FilePath :=
  root / "flate" / s!"{Flate.contentKey input}.answer"

/-- The key a deflation is stored under: format, the input's content key and the
compressing engine. -/
public def slotKey (engine : String) (input : ByteArray) : Array String :=
  #["flate-v2", Flate.contentKey input, engine]

private def readCached? (cache : Cache) (input : ByteArray) (path : System.FilePath) :
    IO (Option ByteArray) := do
  let .ok stored ← (IO.FS.readBinFile path).toBaseIO | return none
  let some z := SlotRecord.lookup (slotKey cache.engine input) stored | return none
  return if z.size ≥ 8 && z[0]? == some 0x78 && z[1]? == some 0x9C then some z else none

private def deflateAtPath (slot : Option (Cache × System.FilePath)) (input : ByteArray)
    (compute : ByteArray → IO ByteArray) :
    IO ByteArray := do
  let some (cache, path) := slot | compute input
  if let some z ← readCached? cache input path then return z
  let z ← compute input
  let key := slotKey cache.engine input
  if SlotRecord.storable key z then
    try
      if let some parent := path.parent then IO.FS.createDirAll parent
      ConvCache.atomicWrite path (SlotRecord.encode key z)
    catch _ => pure ()
  return z

/-- Deflate through the cache; a cache failure falls back to computing. -/
public def deflateCachedAt (root : Option Cache) (input : ByteArray)
    (compute : ByteArray → IO ByteArray := fun b => pure (Flate.deflate b)) :
    IO ByteArray :=
  deflateAtPath (root.map fun c => (c, cachePath c.dir input)) input compute

public theorem deflateCachedAt_none_exact (input : ByteArray) (compute : ByteArray → IO ByteArray) :
    deflateCachedAt none input compute = compute input := by rfl

public def requests (root : Option Cache) (input : α → ByteArray)
    (jobs : Array α) : Array (System.FilePath × α) :=
  jobs.map fun job => (cachePath ((root.map (·.dir)).getD ".") (input job), job)

public theorem requests_exact (root : Option Cache) (input : α → ByteArray)
    (jobs : Array α) :
    (requests root input jobs).map Prod.snd = jobs := by
  simp [requests, Array.map_map, Function.comp_def]

public theorem requests_mem (root : Option Cache) (input : α → ByteArray)
    (jobs : Array α) (path : System.FilePath) (job : α) :
    (path, job) ∈ requests root input jobs ↔
      job ∈ jobs ∧ path = cachePath ((root.map (·.dir)).getD ".") (input job) := by
  simp only [requests, Array.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, hp, rfl⟩
    exact ⟨ha, hp.symm⟩
  · rintro ⟨hj, hp⟩
    exact ⟨job, hj, hp.symm, rfl⟩

public def fontJobs (fontCount : Nat) (keep : Array Nat)
    (programs : Array (ByteArray × Bool)) : Array (Nat × ByteArray) :=
  (keep.zip programs).filterMap fun (k, program, _) =>
    if k < fontCount then some (k, program) else none

public theorem fontJobs_mem (fontCount : Nat) (keep : Array Nat)
    (programs : Array (ByteArray × Bool)) (k : Nat) (program : ByteArray) :
    (k, program) ∈ fontJobs fontCount keep programs ↔
      k < fontCount ∧ ∃ subset, (k, program, subset) ∈ keep.zip programs := by
  rw [fontJobs, Array.mem_filterMap]
  constructor
  · rintro ⟨⟨i, input, subset⟩, hmem, hjob⟩
    by_cases hi : i < fontCount
    · simp only [hi, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hjob
      rcases hjob with ⟨rfl, rfl⟩
      exact ⟨hi, subset, hmem⟩
    · simp [hi] at hjob
  · rintro ⟨hk, subset, hmem⟩
    exact ⟨(k, program, subset), hmem, by simp [hk]⟩

public def storeFonts (fontCount : Nat) (done : Array (Nat × ByteArray)) :
    Array (Option ByteArray) :=
  done.foldl (fun out (k, z) => out.setIfInBounds k (some z))
    (Array.replicate fontCount none)

public theorem storeFonts_size_exact (fontCount : Nat) (done : Array (Nat × ByteArray)) :
    (storeFonts fontCount done).size = fontCount := by
  unfold storeFonts
  refine Array.foldl_induction (motive := fun _ (acc : Array (Option ByteArray)) =>
    acc.size = fontCount)
    (Array.size_replicate ..) ?_
  intro i acc ih
  simpa only [Array.size_setIfInBounds] using ih

private def mapCached (root : Option Cache) (input : α → ByteArray)
    (result : α → ByteArray → β) (jobs : Array α) (limit : Nat)
    (compute : ByteArray → IO ByteArray) : IO (Array β) := do
  let prepared := requests root input jobs
  if let some cache := root then
    let warm ← prepared.mapM fun (path, job) => do
      return (← readCached? cache (input job) path).map (result job)
    if let some out := (warm.mapM id : Option (Array β)) then return out
  let run := fun (path, job) => do
    let z ← deflateAtPath (root.map fun c => (c, path)) (input job) compute
    return result job z
  let mut out := #[]
  for batch in Batch.plan (limit - 1) Prod.fst prepared.toList do
    -- Singletons and streams below tokenize's 64 KiB table boundary skip worker startup.
    let done ← if batch.length ≤ 1 || batch.all (fun (_, job) => (input job).size < 65536) then do
        let answers ← batch.toArray.mapM fun job => (run job).toBaseIO
        EIO.ofExcept (answers.mapM id)
      else
        Batch.map limit Prod.fst run batch.toArray
    out := out ++ done
  return out

/-- Deflate rendered page streams through the cache, in source order. -/
public def pageStreams (root : Option Cache) (pages : Array ByteArray)
    (limit : Nat := 4)
    (compute : ByteArray → IO ByteArray := fun b => pure (Flate.deflate b)) :
    IO (Array (ByteArray × Option ByteArray)) :=
  mapCached root id (fun input z => (input, some z)) pages limit compute

/-- Deflated font programs by writer index, with the writer's truncated-zip and
last-assignment semantics for a repeated index. -/
public def fontZdata (root : Option Cache) (fontCount : Nat)
    (keep : Array Nat) (programs : Array (ByteArray × Bool))
    (limit : Nat := 4)
    (compute : ByteArray → IO ByteArray := fun b => pure (Flate.deflate b)) :
    IO (Array (Option ByteArray)) := do
  let done ← mapCached root Prod.snd (fun job z => (job.1, z))
    (fontJobs fontCount keep programs) limit compute
  return storeFonts fontCount done

/-- Each copied page's stored content, deflated through the cache by store entry. -/
public def formZdata (root : Option Cache) (contents : Array (Option ByteArray))
    (limit : Nat := 4)
    (compute : ByteArray → IO ByteArray := fun b => pure (Flate.deflate b)) :
    IO (Array (Option ByteArray)) := do
  let jobs := contents.zipIdx.filterMap fun (c, k) => c.map ((k, ·))
  let done ← mapCached root Prod.snd (fun job z => (job.1, z)) jobs limit compute
  return done.foldl (fun out (k, z) => out.setIfInBounds k (some z))
    (Array.replicate contents.size none)

public theorem pageBatches_exact (root : Option Cache) (pages : Array ByteArray)
    (limit : Nat) :
    (Batch.plan (limit - 1) Prod.fst (requests root id pages).toList).flatten.map Prod.snd =
      pages.toList := by
  rw [Batch.plan_exact]
  simpa only [Array.toList_map] using congrArg Array.toList (requests_exact root id pages)

public theorem pageBatches_contract (root : Option Cache) (pages : Array ByteArray)
    (limit : Nat) :
    ∀ batch ∈ Batch.plan (limit - 1) Prod.fst (requests root id pages).toList,
      batch.length ≤ max 1 limit ∧ (batch.map Prod.fst).Nodup := by
  intro batch h
  refine ⟨?_, Batch.plan_keys_nodup _ _ _ batch h⟩
  have := Batch.plan_bounded _ _ _ batch h
  omega

public theorem fontBatches_exact (root : Option Cache) (fontCount : Nat)
    (keep : Array Nat) (programs : Array (ByteArray × Bool)) (limit : Nat) :
    (Batch.plan (limit - 1) Prod.fst
      (requests root Prod.snd (fontJobs fontCount keep programs)).toList).flatten.map Prod.snd =
      (keep.toList.zip programs.toList).filterMap (fun (k, program, _) =>
        if k < fontCount then some (k, program) else none) := by
  rw [Batch.plan_exact]
  rw [← Array.toList_map, requests_exact]
  simp only [fontJobs, Array.toList_filterMap, Array.toList_zip]

public theorem fontBatches_contract (root : Option Cache) (fontCount : Nat)
    (keep : Array Nat) (programs : Array (ByteArray × Bool)) (limit : Nat) :
    ∀ batch ∈ Batch.plan (limit - 1) Prod.fst
        (requests root Prod.snd (fontJobs fontCount keep programs)).toList,
      batch.length ≤ max 1 limit ∧ (batch.map Prod.fst).Nodup := by
  intro batch h
  refine ⟨?_, Batch.plan_keys_nodup _ _ _ batch h⟩
  have := Batch.plan_bounded _ _ _ batch h
  omega

end LeanTex.Cli.Compression
