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
import LeanTex.Core.Dim
import LeanTex.Core.Decl
import LeanTex.Core.Nfc
import LeanTex.Core.FaIcons
import LeanTex.Core.HtmlResource
import LeanTex.Core.Hyphen
import LeanTex.Core.Bib
import LeanTex.Core.Binary
import LeanTex.Core.Lex
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
example (n : Int) : Dim.pt n / Dim.spPerPt = n := Dim.pt_exact n
example (value size height : Dim.Sp) :
    (Dim.Length.ofSp value).resolve size height = value :=
  Dim.Length.resolve_ofSp value size height
example : String → String := Nfc.normalize
example : Thunk (Std.HashMap String FaIcons.Entry) := FaIcons.byName
example : String → Option Hyphen.Patterns := Hyphen.forTag
example (patterns : Hyphen.Patterns) (word : String) :
    ∀ p ∈ Hyphen.hyphenate patterns word,
      patterns.leftMin ≤ p ∧
        p + patterns.rightMin ≤ (word.toList.map Nfc.toLower).length :=
  Hyphen.hyphenate_respects_min patterns word
example : Bib.Entry → String → Option String := Bib.Entry.field?
example : String → Bib.Parsed := Bib.parse
example : String → Bib.Name := Bib.parseName
example : Bib.Name → String := Bib.Name.full
example : String → String → Array Lex.Token × Array Diag := Lex.lex
example (lineEnds : Nat) :
    (Lex.wsTokens false (lineEnds + 1)).tail = Lex.wsTokens true lineEnds :=
  Lex.blank_line_par_agree lineEnds
example (read : Binary.Reader α) (value : α) (encoded : ByteArray)
    (h : Binary.Reads read value encoded) : read.run encoded = some value :=
  Binary.Reads.run_id read value encoded h
example : String → Option Dim.Length := Decl.parseLength
example : String → Option Dim.SymGlue := Decl.parseGlue
example : String → Except String Decl.LenExpr := Decl.parseLengthSyntax
example : Option String → String → Except Decl.ColorSpecError Decl.ColorSpec :=
  Decl.parseColorSpec
example : Decl.ColorComponent → String := Decl.ColorComponent.pdfUnit
example (look : String → Option Dim.SymGlue) (name : String)
    (missing : look name = none) :
    Decl.LenExpr.eval look (.ref name) = .error name :=
  Decl.LenExpr.eval_absent_named look name missing
example : HtmlResource.Media.png.mime = "image/png" := by rfl
example (resources : Array HtmlResource.Embedded) (svgChecked : Array ByteArray)
    (script lang : String) (head body : Array Html.Node) :
    Except String (HtmlResource.ClosedPage script) :=
  HtmlResource.close resources svgChecked script lang head body

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
  fail_if_success have := Nfc.Tables
  fail_if_success have := Nfc.load
  fail_if_success have := Nfc.tables
  fail_if_success have := FaIcons.entries
  fail_if_success have := HtmlResource.CssScan
  fail_if_success have := Hyphen.parsePattern
  fail_if_success have := Hyphen.rawBreaks
  fail_if_success have := Bib.monthKeys
  fail_if_success have := Bib.readWhile
  fail_if_success have := Binary.Reader.arrayLoop
  fail_if_success have := Binary.array_acc
  fail_if_success have := Lex.scanWhile
  fail_if_success have := Lex.writtenControls
  fail_if_success have := Lex.verbEnvs
  fail_if_success have := Decl.parseScaled
  fail_if_success have := Decl.ETok
  fail_if_success have := Decl.exprToks
  fail_if_success have := Decl.exprParse
  fail_if_success have := Decl.unitScale
  trivial
