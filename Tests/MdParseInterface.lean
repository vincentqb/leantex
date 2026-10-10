module

import LeanTex.Core.MdParse

/-! Ordinary consumers construct and inspect the markdown AST and call the
document reader. Scanners and intermediate parser state stay private. -/

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
    .image "figure.png" "delta" body p, .anchor "delta" p, .soft p, .hard p]

example (p : Pos) (inlines : Array Md.Inl) (blocks : Array Md.Blk) : Array Md.Blk :=
  #[.para inlines p, .heading 2 inlines p, .code "text" "alpha" p,
    .rule p, .quote blocks p, .list true 1 true #[blocks] p,
    .disclosure inlines blocks p,
    .table #[.none, .left, .right, .center] #[inlines] #[#[inlines]] p]

example (node : Md.Inl) : Pos :=
  match node with
  | .text _ p | .code _ p | .emph _ p | .strong _ p
  | .link _ _ _ p | .image _ _ _ p | .anchor _ p | .soft p | .hard p => p

example (node : Md.Blk) : Pos :=
  match node with
  | .para _ p | .heading _ _ p | .code _ _ p | .rule p
  | .quote _ p | .disclosure _ _ p | .list _ _ _ _ p | .table _ _ _ p => p

example : True := by
  fail_if_success have := Md.Line
  fail_if_success have := Md.splitLines
  fail_if_success have := Md.indentAt
  fail_if_success have := Md.HtmlMemo
  fail_if_success have := Md.htmlTagAt
  fail_if_success have := Md.ITok
  fail_if_success have := Md.Chars
  fail_if_success have := Md.charsOfOne
  fail_if_success have := Md.scanInlines
  fail_if_success have := Md.matchEmphasis
  fail_if_success have := Md.buildInlines
  fail_if_success have := Md.inlines
  fail_if_success have := Md.Strict
  fail_if_success have := Md.refuse
  trivial

end Tests.MdParseInterface
