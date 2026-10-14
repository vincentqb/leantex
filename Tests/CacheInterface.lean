module

import LeanTex.Cli.ConvCache
import LeanTex.Cli.Compression
import LeanTex.Core.SlotRecord

/-! Cache clients use complete outcomes and source-ordered compression jobs.
Tool probing and persistence helpers remain behind that boundary. -/

open LeanTex.Cli

namespace Tests.CacheInterface

example : ConvCache.Result → Except String ByteArray := ConvCache.Result.answer
example : Except String ByteArray → ByteArray := ConvCache.encode
example : ByteArray → Option (Except String ByteArray) := ConvCache.decode
example : Except String ByteArray → ConvCache.Result := ConvCache.Result.replay
example : ByteArray → String → Array String → Bool → IO (ConvCache.Result × Bool) →
    IO ConvCache.Result := ConvCache.cachedResult
example : Option System.FilePath → Option String → ByteArray → String → Array String → Bool →
    IO (ConvCache.Result × Bool) → IO ConvCache.Result := ConvCache.cachedResultIn

example (bytes : ByteArray) (a : Except String ByteArray) (h : ConvCache.decode bytes = some a) :
    (ConvCache.Result.replay a).answer = a :=
  ConvCache.replay_decode_exact bytes a h
example (r : ConvCache.Result) (a : Except String ByteArray) (h : r.record? = some a) :
    (ConvCache.Result.replay a).outcome = r.outcome ∧
      (ConvCache.Result.replay a).answer = r.answer :=
  ConvCache.replay_record_exact r a h

example (why : String) (bytes : ByteArray) :
    ConvCache.Result.record? ⟨.inconclusive why, bytes⟩ = none :=
  ConvCache.inconclusive_retried_exact why bytes
example : PicCache.Ran → PicCache.Log → String → ByteArray → ConvCache.Result :=
  ConvCache.Result.ofRun
example (ran : PicCache.Ran) (log : PicCache.Log) (said : String) (bytes : ByteArray)
    (a : Except String ByteArray) :
    (ConvCache.Result.ofRun ran log said bytes).record? = some a ↔
      (ran = .exited 0 ∧ a = if bytes.isEmpty then .error "no PDF was produced" else .ok bytes) ∨
      ∃ c tail, ran = .exited (c + 1) ∧ c + 1 < 126 ∧ log = .says tail ∧
        a = .error (if tail.isEmpty then s!"exit code {c + 1}" else tail) :=
  ConvCache.record?_some_exact ran log said bytes a
example (r : ConvCache.Result) (a : Except String ByteArray) (h : r.record? = some a) :
    ConvCache.decode (ConvCache.encode a) = some a :=
  ConvCache.decode_encode_record_id r a h
example (r : ConvCache.Result) (a : Except String ByteArray) (h : r.record? = some a) :
    (ConvCache.decode (ConvCache.encode a)).map
        (fun x => ((ConvCache.Result.replay x).outcome, (ConvCache.Result.replay x).answer)) =
      some (r.outcome, r.answer) :=
  ConvCache.envelope_replay_exact r a h

example (input : ByteArray) (compute : ByteArray → IO ByteArray) :
    Compression.deflateCachedAt none input compute = compute input :=
  Compression.deflateCachedAt_none_exact input compute

example (root : Option Compression.Cache) (input : α → ByteArray) (jobs : Array α) :
    (Compression.requests root input jobs).map Prod.snd = jobs :=
  Compression.requests_exact root input jobs

example (root : Option Compression.Cache) (pages : Array ByteArray) (limit : Nat) :
    ∀ batch ∈ Batch.plan (limit - 1) Prod.fst
      (Compression.requests root id pages).toList,
      batch.length ≤ max 1 limit ∧ (batch.map Prod.fst).Nodup :=
  Compression.pageBatches_contract root pages limit

example : True := by
  fail_if_success have := ConvCache.versionBudgetMs
  fail_if_success have := ConvCache.probeVersion
  fail_if_success have := ConvCache.identify
  fail_if_success have := ConvCache.identity
  fail_if_success have := ConvCache.cacheDir
  fail_if_success have := Compression.readCached?
  fail_if_success have := Compression.deflateAtPath
  fail_if_success have := Compression.mapCached
  trivial

example : LeanTex.Core.SlotRecord.format.Fits ⟨#[1]⟩ := show 1 < 256 ^ 4 by decide

end Tests.CacheInterface
