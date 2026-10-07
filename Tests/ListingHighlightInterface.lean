module

import LeanTex.Cli.ListingHighlight

/-! The listing boundary accepts requests and returns typed answers and
diagnostics. Its process bridge and failure assembly are private. -/

open LeanTex.Core

namespace Tests.ListingHighlightInterface

example : String → Array ListingReply.Request →
    IO (Array ListingReply.Answer × Array Diag) := LeanTex.Cli.ListingHighlight.fulfil
example (language source : String) : ListingReply.Request := { language, source }
example (request : ListingReply.Request) (tokens : Array (Array ListingHighlight.Token)) :
    ListingReply.Answer := { request, tokens }
example (answer : ListingReply.Answer) : String × Array (Array ListingHighlight.Token) :=
  (answer.request.source, answer.tokens)
example : BEq ListingReply.Request := inferInstance
example : Repr ListingReply.Answer := inferInstance

example : True := by
  fail_if_success have := LeanTex.Cli.ListingHighlight.bridge
  fail_if_success have := LeanTex.Cli.ListingHighlight.diagnostic
  fail_if_success have := LeanTex.Cli.ListingHighlight.failed
  trivial

end Tests.ListingHighlightInterface
