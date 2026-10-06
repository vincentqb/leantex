module

import LeanTex.Core.Color
import LeanTex.Core.Locale
import LeanTex.Core.Utf8
import LeanTex.Core.ListingHighlight
import LeanTex.Core.Html
import LeanTex.Core.LocaleContract
import LeanTex.Core.HyphenData
import LeanTex.Core.HyphenDataFr
import LeanTex.Core.HyphenDataDe
import LeanTex.Core.FaData
import LeanTex.Core.NfcData
import LeanTex.Core.TextSymData
import LeanTex.Cli.PicCache
import LeanTex.Cli.RunBounded
import LeanTex.Cli.ToolProbe

/-! Ordinary consumers can name the value types and contracts; lexical
traversal helpers remain implementation details. Serialization bodies needed
by downstream algebraic proofs are explicitly exposed. -/

open LeanTex.Core LeanTex.Cli

example : Ir.Color → String := Ir.Color.css
example (c : Ir.Color) :
    c.css = "#" ++ Ir.Color.hexByte c.r false ++ Ir.Color.hexByte c.g false ++
      Ir.Color.hexByte c.b false := by rfl
example : String → String := Locale.babelTagOf
example : ByteArray → Option Utf8.Err := Utf8.validate
example : Utf8.Err → String → Diag := Utf8.Err.toDiag
example : ListingHighlight.Language → Array String → Array (Array ListingHighlight.Token) :=
  ListingHighlight.tokenize
example (tokens : Array ListingHighlight.Token) :
    ListingHighlight.lineText tokens = tokens.foldl (fun s t => s ++ t.text) "" := by rfl
example (drawn : Bool) (refusal : Option String) :
    PicCache.step drawn refusal = .run ↔ drawn = false ∧ refusal = none :=
  PicCache.step_cold_exact drawn refusal
example : IO.Process.SpawnArgs → IO IO.Process.Output := RunBounded.output
example : String → IO PicCache.Tool := ToolProbe.probeVersion
example : Html.Node → Nat → String := Html.render
example (s : String) : '<' ∉ (Html.escapeText s).toList := Html.escapeText_no_lt s
example (s : String) : '"' ∉ (Html.escapeAttr s).toList := Html.escapeAttr_no_quote s
example (s : String) : '<' ∉ (Html.escapeJson s).toList := Html.escapeJson_no_lt s
example : (Locale.builtin.map (·.tag)).Nodup := Locale.builtin_tags_nodup
example : Array String :=
  #[HyphenData.patterns, HyphenDataFr.patterns, HyphenDataDe.patterns,
    FaData.table, NfcData.ccc]
example : List (String × Char) := TextSymData.symbols

example : True := by
  fail_if_success have := Utf8.seq
  fail_if_success have := Utf8.validate.go
  fail_if_success have := ListingHighlight.tokenAt
  fail_if_success have := ListingHighlight.scanWhile
  fail_if_success have := RunBounded.Capture
  fail_if_success have := RunBounded.capture
  fail_if_success have := ToolProbe.decodeMemo
  fail_if_success have := Html.rawPayload
  fail_if_success have := Html.escapeCharText
  fail_if_success have := Html.phrasingTags
  trivial
