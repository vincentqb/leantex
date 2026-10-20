module

import LeanTex.Core.MdParse

/-! Ordinary consumers build and inspect the markdown AST and call the document reader; parser state
stays private. -/

open LeanTex.Core

namespace Tests.MdParseInterface

example : String → String → Array Md.Blk × Array Diag := Md.blocks
example : Inhabited Md.Inl := inferInstance
example : Inhabited Md.Blk := inferInstance
example : BEq Md.Inl := inferInstance
example : BEq Md.Blk := inferInstance
example : Repr Md.Inl := inferInstance
example : Repr Md.Blk := inferInstance

example (p : Pos) (body : Array Md.Inl) : Array Md.Inl :=
  #[.text "alpha" p, .code "beta" p, .emph body p, .strong body p,
    .link "https://example.org" "gamma" body p,
    .image "figure.png" "delta" body p, .anchor "delta" p, .soft p, .hard p,
    .cite #[.mk "epsilon" .normal body body, .mk "zeta" .authorInText #[] #[]] p,
    .citeText "eta" body p, .math false "x^2" p, .note "theta" body p]

example (p : Pos) (inlines : Array Md.Inl) (blocks : Array Md.Blk) : Array Md.Blk :=
  #[.para inlines p, .heading 2 inlines p, .code "text" "alpha" p,
    .rule p, .quote blocks p, .list true 1 true #[blocks] p,
    .disclosure inlines false blocks p, .disclosure inlines true blocks p,
    .table #[.none, .left, .right, .center] #[inlines] #[#[inlines]] p,
    .lean #[("file", "steps.lean"), ("show", "math")] p,
    .metadata #[{ key := "bibliography", value := .scalar "works.bib", pos := p }] p, .refs p,
    .note "theta" blocks p]

example (node : Md.Inl) : Pos :=
  match node with
  | .text _ p | .code _ p | .emph _ p | .strong _ p
  | .link _ _ _ p | .image _ _ _ p | .anchor _ p | .soft p | .hard p | .cite _ p
  | .citeText _ _ p | .math _ _ p | .note _ _ p => p

example (node : Md.Blk) : Pos :=
  match node with
  | .para _ p | .heading _ _ p | .code _ _ p | .rule p
  | .quote _ p | .disclosure _ _ _ p | .list _ _ _ _ p | .table _ _ _ p | .lean _ p
  | .metadata _ p | .refs p | .note _ _ p | .aside _ p => p

example : True := by
  fail_if_success have := Md.Line
  fail_if_success have := Md.splitLines
  fail_if_success have := Md.indentAt
  fail_if_success have := Md.HtmlMemo
  fail_if_success have := Md.htmlTagAt
  fail_if_success have := Md.HtmlTag
  fail_if_success have := Md.tagAt
  fail_if_success have := Md.endTagAt
  fail_if_success have := Md.htmlInlineAt
  fail_if_success have := Md.ITok
  fail_if_success have := Md.Chars
  fail_if_success have := Md.charsOfOne
  fail_if_success have := Md.scanInlines
  fail_if_success have := Md.matchEmphasis
  fail_if_success have := Md.buildInlines
  fail_if_success have := Md.inlines
  fail_if_success have := Md.citeListAt
  fail_if_success have := Md.metaFields
  fail_if_success have := Md.Strict
  fail_if_success have := Md.refuse
  trivial

end Tests.MdParseInterface
