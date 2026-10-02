import Lean.Data.Json
import LeanTex.Core.Ir

/-!
The pure boundary for external listing classification. Source is normalized
once by the IR's verbatim reader; a tool supplies class names and exact text,
never HTML, colours, font names, code to evaluate, or a document replacement.

Pygments' token hierarchy and unprocessed-token interface are documented at
https://pygments.org/docs/tokens/ and https://pygments.org/docs/api/#lexers.
Projection follows whole dotted ancestors, most specific first. Our existing
Default/Friendly painter chooses the colours; these are not arbitrary
Pygments style definitions.
-/
namespace LeanTex.Core.ListingReply

open Lean (Json toJson)
open LeanTex.Core.ListingHighlight (Token Kind lineText)

structure Request where
  language : String
  source : String
  deriving BEq, Repr

/-- Normalize only at the frontend boundary. Calling `verbatimLines` on
`request.source` again would discard a retained initial blank line. -/
def Request.ofSource (language : String) (rawSource : String) : Request :=
  { language := language.trimAscii.toString.toLower
    source := String.intercalate "\n" (Ir.verbatimLines rawSource).toList }

def Request.lines (request : Request) : Array String :=
  if request.source.isEmpty then #[] else (request.source.splitOn "\n").toArray

/-- Classification data, always checked by `lookup` before installation.
The shared IR reader checks it again before either artifact consumes it. -/
structure Answer where
  request : Request
  tokens : Array (Array Token)
  deriving BEq, Repr

/-- Requests are leaves of the one generic document fold, including listings
inside captions, notes and nested containers. Styles share a classification. -/
-- conserves: none — this collector returns requests, not a rewritten document.
def requests (doc : Ir.Doc) : Array Request :=
  Ir.foldDoc (fun acc _ => acc) #[] doc (fb := fun acc block =>
    match block with
    | .verbatim _ source spec =>
      match spec.language with
      | none => acc
      | some language =>
        if (ListingHighlight.language? language.val).isSome then acc else
        let request := Request.ofSource language.val source
        if acc.contains request then acc else acc.push request
    | _ => acc)

/-- Exact content-key lookup, with the raw source checked at the install
site as well. A foreign, stale, or malformed answer cannot change code. -/
def lookup (answers : Array Answer) (language : String)
    (rawSource : String) : Option (Array (Array Token)) :=
  let request := Request.ofSource language rawSource
  match answers.find? (fun answer => answer.request == request) with
  | none => Option.none
  | some answer =>
    if answer.tokens.map lineText = Ir.verbatimLines rawSource then
      some answer.tokens
    else none

/-- A lookup is installable only for the original listing's exact lines. -/
theorem lookup_source_exact (answers : Array Answer) (language : String)
    (source : String) (highlight : Array (Array Token))
    (h : lookup answers language source = some highlight) :
    highlight.map lineText = Ir.verbatimLines source := by
  dsimp only [lookup] at h
  split at h
  · contradiction
  · split at h
    · cases Option.some.inj h
      assumption
    · contradiction

inductive Failure where
  | unavailable | unsupported | rejected | invalidReply | sourceMismatch | budget
  deriving BEq, Repr

def Failure.reason : Failure → String
  | .unavailable => "Pygments is unavailable"
  | .unsupported => "the installed Pygments has no built-in lexer for this language"
  | .rejected => "the built-in lexer could not classify this source"
  | .invalidReply => "the highlighter returned an invalid reply"
  | .sourceMismatch => "the highlighter did not preserve the source"
  | .budget => "the highlighter exceeded its resource limit"

/-- Source-valid plain data for a completed refusal. Its typed failure is
returned alongside it by `decode`; callers retaining answers must retain
failures too. Interrupted or unstarted attempts have no answer to remember. -/
def plainAnswer (request : Request) : Answer :=
  { request
    tokens := request.lines.map fun text => #[{ text }] }

theorem plainAnswer_source_exact (request : Request) :
    (plainAnswer request).tokens.map lineText = request.lines := by
  simp [plainAnswer, Array.map_map, Function.comp_def, lineText]

/-- Unrecognized namespaces, error tokens and punctuation stay plain.
`Name.Builtinish` is a Name, but never a Builtin; `Names` is not a Name. -/
def projectKind (tokenClass : String) : Kind :=
  let parts := tokenClass.splitOn "."
  let parts := if parts.head? == some "Token" then parts.drop 1 else parts
  match parts with
  | "Keyword" :: _ => .keyword
  | "Comment" :: _ => .comment
  | "Literal" :: "String" :: _ => .string
  | "Literal" :: "Number" :: _ => .number
  | "Name" :: "Builtin" :: _ => .builtin
  | "Name" :: _ => .name
  | "Operator" :: _ => .operator
  | _ => .plain

structure Classified where
  offset : Nat
  tokenClass : String
  text : String
  deriving BEq, Repr

/-- Split token text at LF without losing blank lines or indentation.
Empty chunks need no run. Validation below also checks the resulting lines,
so this representation step is not a second trusted lexer. -/
private def splitTokens (tokens : Array Classified) : Array (Array Token) := Id.run do
  let mut lines : Array (Array Token) := #[#[]]
  for token in tokens do
    let parts := token.text.splitOn "\n"
    for (part, i) in parts.zipIdx do
      if i > 0 then lines := lines.push #[]
      if !part.isEmpty then
        let last := lines.back!
        lines := lines.set! (lines.size - 1)
          (last.push { kind := projectKind token.tokenClass, text := part })
  return lines

/-- Offsets count Unicode characters, as Pygments does. Every token starts
where its predecessor ended; the whole text and every normalized line must
also match. Tab expansion and an inserted final LF both fail. -/
def ofTokens (request : Request) (tokens : Array Classified) : Except Failure Answer := do
  let (_, contiguous) := tokens.foldl (fun (offset, valid) token =>
    (offset + token.text.length, valid && token.offset == offset)) (0, true)
  if !contiguous then throw .sourceMismatch
  if tokens.foldl (fun text token => text ++ token.text) "" != request.source then
    throw .sourceMismatch
  let highlight := if request.source.isEmpty then #[] else splitTokens tokens
  if highlight.map lineText = request.lines then
    return { request, tokens := highlight }
  else throw .sourceMismatch

-- Operational protocol ceilings: one MiB of source per batch, at most 256
-- requests and 262144 token records, and sixteen MiB of UTF-8 JSON. These
-- limit allocation and process capture, not the syntax of any language.
def maxSourceBytes : Nat := 1024 * 1024
def maxRequests : Nat := 256
def maxTokens : Nat := 262144
def maxReplyBytes : Nat := 16 * 1024 * 1024

def withinBudget (rs : Array Request) : Bool :=
  rs.size ≤ maxRequests &&
    rs.foldl (fun bytes r => bytes + r.source.utf8ByteSize + r.language.utf8ByteSize) 0
      ≤ maxSourceBytes

/-- Only language and normalized source cross the process boundary as data. -/
def encode (rs : Array Request) : String :=
  (Json.mkObj [
    ("version", toJson (1 : Nat)),
    ("requests", Json.arr (rs.map fun request => Json.mkObj [
      ("language", toJson request.language),
      ("source", toJson request.source)]))]).compress

private def classified (value : Json) : Except String Classified := do
  return { offset := ← value.getObjValAs? Nat "offset"
           tokenClass := ← value.getObjValAs? String "kind"
           text := ← value.getObjValAs? String "text" }

/-- Decode a complete v1 batch or reject it as a whole. Reordered, missing
and repeated content keys never partially poison the cache. Per-request
errors are completed plain replies with a typed failure keyed by the request.
The CLI owns diagnostic translation; external error text is never its prose. -/
def decode (rs : Array Request) (body : String) :
    Except String (Array Answer × Array (Request × Failure)) := do
  if !withinBudget rs || body.utf8ByteSize > maxReplyBytes then
    throw "listing protocol resource limit exceeded"
  let value ← Json.parse body
  let version ← value.getObjValAs? Nat "version"
  if version != 1 then throw "unsupported listing protocol version"
  let provider ← value.getObjValAs? String "provider"
  if provider != "Pygments" then throw "unsupported listing provider"
  let _ ← value.getObjValAs? String "providerVersion"
  let results ← value.getObjValAs? (Array Json) "answers"
  if results.size != rs.size then throw "listing reply count differs from request count"
  let mut answers := #[]
  let mut failures := #[]
  let mut tokenCount := 0
  for h : i in [:rs.size] do
    let some result := results[i]? | throw "missing listing reply"
    let request := rs[i]
    let language ← result.getObjValAs? String "language"
    let source ← result.getObjValAs? String "source"
    if language != request.language || source != request.source then
      throw "listing reply content keys are not the requested order"
    match result.getObjVal? "tokens", result.getObjVal? "error" with
    | .ok values, .error _ =>
      let values ← values.getArr?
      tokenCount := tokenCount + values.size
      if tokenCount > maxTokens then throw "listing token count limit exceeded"
      let tokens ← values.mapM classified
      match ofTokens request tokens with
      | .ok answer => answers := answers.push answer
      | .error _ => throw "listing tokens do not reproduce the requested source"
    | .error _, .ok error =>
      let error ← error.getStr?
      if error.trimAscii.toString.isEmpty then throw "empty listing refusal"
      let failure := match error with
        | "unsupported" => Failure.unsupported
        | "unavailable" => Failure.unavailable
        | _ => Failure.rejected
      answers := answers.push (plainAnswer request)
      failures := failures.push (request, failure)
    | _, _ => throw "a listing answer must contain either tokens or an error"
  return (answers, failures)

end LeanTex.Core.ListingReply
