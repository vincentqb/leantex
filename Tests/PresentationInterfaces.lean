module

import LeanTex.Core.Theme
import LeanTex.Core.BeamerColor
import LeanTex.Core.ColorContract
import LeanTex.Core.BibContract
import LeanTex.Core.MarkdownDoc

/-! Presentation consumers use theme values, colour resolution, and the
Markdown emitter. Installation accumulators and serialization helpers are
private; contracts remain available through ordinary imports. -/

open LeanTex.Core
open LeanTex.Core.Ir

namespace Tests.PresentationInterfaces

example : List Theme.Theme := Theme.builtin
example : String → Option Theme.Theme := Theme.find?
example : List String := Theme.names
example : ElementStyle → ElementStyle → ElementStyle := Theme.styleMerge
example : Theme.Theme → Theme.Decls → Theme.Decls := Theme.apply
example : Theme.Theme → Theme.Decls → Theme.Decls := Theme.applyUnder
example : Theme.Theme → Array (String × String) := Theme.declares
example : Theme.Theme → Theme.Decls → Array (String × String) := Theme.replaces

example : BeamerColor.State → String → Bool → String → Span →
    BeamerColor.State × List String := BeamerColor.State.declare
example : BeamerColor.State → String → Color → BeamerColor.State :=
  BeamerColor.State.native
example : BeamerColor.State → Palette →
    BeamerColor.State × Palette × List BeamerColor.Issue :=
  BeamerColor.State.resolve

example : Array Inline → String := MarkdownDoc.inlineText
example : Ir.HeadingLevel → String := MarkdownDoc.headingMarker
example : Doc → String := MarkdownDoc.emit

example (v : Nat) : (Color.pdfMilli v).toList.all (· != ' ') = true :=
  Color.pdfMilli_no_space v

example (a b : Color) (h : a.pdfComponents = b.pdfComponents) :
    a.r = b.r ∧ a.g = b.g ∧ a.b = b.b :=
  Color.pdfComponents_inj a b h

example : True := by
  fail_if_success have := Theme.installPalette
  fail_if_success have := Theme.installStyles
  fail_if_success have := Theme.styleWrites
  fail_if_success have := Theme.lineageTokens
  fail_if_success have := BeamerColor.Reading
  fail_if_success have := BeamerColor.read
  fail_if_success have := BeamerColor.unbrace
  fail_if_success have := MarkdownDoc.escapeText
  fail_if_success have := MarkdownDoc.blocksInto
  fail_if_success have := MarkdownDoc.tighten
  trivial

end Tests.PresentationInterfaces
