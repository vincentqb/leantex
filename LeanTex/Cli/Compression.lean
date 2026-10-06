import LeanTex.Cli.Batch
import LeanTex.Cli.ConvCache

namespace LeanTex.Cli.Compression

open LeanTex.Core

def cachePath (root : System.FilePath) (input : ByteArray) : System.FilePath :=
  -- The old .z files have no integrity envelope and may be partial.
  root / "flate" / s!"{Flate.contentKey input}-{LeanTex.version}.answer"

private def readCached? (path : System.FilePath) : IO (Option ByteArray) := do
  let .ok stored ← (IO.FS.readBinFile path).toBaseIO | return none
  let some (.ok z) := ConvCache.decode stored | return none
  return if z.size ≥ 8 && z[0]? == some 0x78 && z[1]? == some 0x9C then some z else none

private def deflateAtPath (path : Option System.FilePath) (input : ByteArray)
    (compute : ByteArray → IO ByteArray) :
    IO ByteArray := do
  let some path := path | compute input
  if let some z ← readCached? path then return z
  let z ← compute input
  try
    if let some parent := path.parent then IO.FS.createDirAll parent
    ConvCache.atomicWrite path (ConvCache.encode (.ok z))
  catch _ => pure ()
  return z

/-- Cache failures fall back to computation. The optional computation is an
effect seam; production uses the engine's compressor without changing its bytes. -/
def deflateCachedAt (root : Option System.FilePath) (input : ByteArray)
    (compute : ByteArray → IO ByteArray := fun b => pure (Flate.deflate b)) :
    IO ByteArray :=
  deflateAtPath (root.map (cachePath · input)) input compute

theorem deflateCachedAt_none_exact (input : ByteArray) (compute : ByteArray → IO ByteArray) :
    deflateCachedAt none input compute = compute input := rfl

def requests (root : Option System.FilePath) (input : α → ByteArray)
    (jobs : Array α) : Array (System.FilePath × α) :=
  jobs.map fun job => (cachePath (root.getD ".") (input job), job)

theorem requests_exact (root : Option System.FilePath) (input : α → ByteArray)
    (jobs : Array α) :
    (requests root input jobs).map Prod.snd = jobs := by
  simp [requests, Array.map_map, Function.comp_def]

theorem requests_mem (root : Option System.FilePath) (input : α → ByteArray)
    (jobs : Array α) (path : System.FilePath) (job : α) :
    (path, job) ∈ requests root input jobs ↔
      job ∈ jobs ∧ path = cachePath (root.getD ".") (input job) := by
  simp only [requests, Array.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, hp, rfl⟩
    exact ⟨ha, hp.symm⟩
  · rintro ⟨hj, hp⟩
    exact ⟨job, hj, hp.symm, rfl⟩

def fontJobs (fontCount : Nat) (keep : Array Nat)
    (programs : Array (ByteArray × Bool)) : Array (Nat × ByteArray) :=
  (keep.zip programs).filterMap fun (k, program, _) =>
    if k < fontCount then some (k, program) else none

theorem fontJobs_mem (fontCount : Nat) (keep : Array Nat)
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

def storeFonts (fontCount : Nat) (done : Array (Nat × ByteArray)) :
    Array (Option ByteArray) :=
  done.foldl (fun out (k, z) => out.setIfInBounds k (some z))
    (Array.replicate fontCount none)

theorem storeFonts_size_exact (fontCount : Nat) (done : Array (Nat × ByteArray)) :
    (storeFonts fontCount done).size = fontCount := by
  unfold storeFonts
  refine Array.foldl_induction (motive := fun _ (acc : Array (Option ByteArray)) =>
    acc.size = fontCount)
    (Array.size_replicate ..) ?_
  intro i acc ih
  simpa only [Array.size_setIfInBounds] using ih

theorem storeFonts_push_exact (fontCount : Nat) (done : Array (Nat × ByteArray))
    (k : Nat) (z : ByteArray) :
    storeFonts fontCount (done.push (k, z)) =
      (storeFonts fontCount done).setIfInBounds k (some z) := by
  simp only [storeFonts, Array.foldl_push]

private def mapCached (root : Option System.FilePath) (input : α → ByteArray)
    (result : α → ByteArray → β) (jobs : Array α) (limit : Nat)
    (compute : ByteArray → IO ByteArray) : IO (Array β) := do
  let prepared := requests root input jobs
  if root.isSome then
    let warm ← prepared.mapM fun (path, job) => do
      return (← readCached? path).map (result job)
    if let some out := (warm.mapM id : Option (Array β)) then return out
  -- A fully warm batch needs no tasks. Misses still go through the cache
  -- inside each task, so repeated content can reuse an earlier batch's write.
  Batch.map limit Prod.fst (fun (path, job) => do
    let z ← deflateAtPath (root.map fun _ => path) (input job) compute
    return result job z) prepared

/-- The driver supplies rendered page bytes in source order. -/
def pageStreams (root : Option System.FilePath) (pages : Array ByteArray)
    (limit : Nat := 4)
    (compute : ByteArray → IO ByteArray := fun b => pure (Flate.deflate b)) :
    IO (Array (ByteArray × Option ByteArray)) :=
  mapCached root id (fun input z => (input, some z)) pages limit compute

/-- Keep the writer's font indices, truncated zip, and last assignment
semantics even when the supplied keep list repeats an index. -/
def fontZdata (root : Option System.FilePath) (fontCount : Nat)
    (keep : Array Nat) (programs : Array (ByteArray × Bool))
    (limit : Nat := 4)
    (compute : ByteArray → IO ByteArray := fun b => pure (Flate.deflate b)) :
    IO (Array (Option ByteArray)) := do
  let done ← mapCached root Prod.snd (fun job z => (job.1, z))
    (fontJobs fontCount keep programs) limit compute
  return storeFonts fontCount done

-- These are the partitions consumed by mapCached's cold/mixed branch.
-- The captured key is also the path read and published by deflateAtPath.
theorem pageBatches_exact (root : Option System.FilePath) (pages : Array ByteArray)
    (limit : Nat) :
    (Batch.plan (limit - 1) Prod.fst (requests root id pages).toList).flatten.map Prod.snd =
      pages.toList := by
  rw [Batch.plan_exact]
  simpa only [Array.toList_map] using congrArg Array.toList (requests_exact root id pages)

theorem pageBatches_contract (root : Option System.FilePath) (pages : Array ByteArray)
    (limit : Nat) :
    ∀ batch ∈ Batch.plan (limit - 1) Prod.fst (requests root id pages).toList,
      batch.length ≤ max 1 limit ∧ (batch.map Prod.fst).Nodup := by
  intro batch h
  refine ⟨?_, Batch.plan_keys_nodup _ _ _ batch h⟩
  have := Batch.plan_bounded _ _ _ batch h
  omega

theorem fontBatches_exact (root : Option System.FilePath) (fontCount : Nat)
    (keep : Array Nat) (programs : Array (ByteArray × Bool)) (limit : Nat) :
    (Batch.plan (limit - 1) Prod.fst
      (requests root Prod.snd (fontJobs fontCount keep programs)).toList).flatten.map Prod.snd =
      (keep.toList.zip programs.toList).filterMap (fun (k, program, _) =>
        if k < fontCount then some (k, program) else none) := by
  rw [Batch.plan_exact]
  rw [← Array.toList_map, requests_exact]
  simp only [fontJobs, Array.toList_filterMap, Array.toList_zip]

theorem fontBatches_contract (root : Option System.FilePath) (fontCount : Nat)
    (keep : Array Nat) (programs : Array (ByteArray × Bool)) (limit : Nat) :
    ∀ batch ∈ Batch.plan (limit - 1) Prod.fst
        (requests root Prod.snd (fontJobs fontCount keep programs)).toList,
      batch.length ≤ max 1 limit ∧ (batch.map Prod.fst).Nodup := by
  intro batch h
  refine ⟨?_, Batch.plan_keys_nodup _ _ _ batch h⟩
  have := Batch.plan_bounded _ _ _ batch h
  omega

end LeanTex.Cli.Compression
