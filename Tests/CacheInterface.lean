module

import LeanTex.Cli.ConvCache
import LeanTex.Cli.Compression

/-! Cache clients use complete outcomes and source-ordered compression jobs.
Tool probing and persistence helpers remain behind that boundary. -/

open LeanTex.Cli

namespace Tests.CacheInterface

example : ConvCache.Result → Except String ByteArray := ConvCache.Result.answer
example : Except String ByteArray → ByteArray := ConvCache.encode
example : ByteArray → Option (Except String ByteArray) := ConvCache.decode

example (why : String) (bytes : ByteArray) :
    ConvCache.Result.record? ⟨.inconclusive why, bytes⟩ = none :=
  ConvCache.inconclusive_retried_exact why bytes

example (input : ByteArray) (compute : ByteArray → IO ByteArray) :
    Compression.deflateCachedAt none input compute = compute input :=
  Compression.deflateCachedAt_none_exact input compute

example (root : Option System.FilePath) (input : α → ByteArray) (jobs : Array α) :
    (Compression.requests root input jobs).map Prod.snd = jobs :=
  Compression.requests_exact root input jobs

example (root : Option System.FilePath) (pages : Array ByteArray) (limit : Nat) :
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

end Tests.CacheInterface
