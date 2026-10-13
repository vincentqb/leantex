module

import Lean.Data.Json
public import LeanTex.Core.Ir

/-! The pure boundary for external listing classification (Pygments' token interface): a tool
supplies class names and exact text, never markup, colours, fonts or code. -/
namespace LeanTex.Core.ListingReply

open Lean (Json toJson)
open LeanTex.Core.ListingHighlight (Token Kind lineText)

public structure Request where
  language : String
  source : String
  deriving BEq, ReflBEq, LawfulBEq, Repr

/-- A request, its source normalized once here; normalizing again would drop a leading blank
line. -/
public def Request.ofSource (language : String) (rawSource : String) : Request :=
  { language := language.trimAscii.toString.toLower
    source := String.intercalate "\n" (Ir.verbatimLines rawSource).toList }

public def Request.lines (request : Request) : Array String :=
  if request.source.isEmpty then #[] else (request.source.splitOn "\n").toArray

/-- Classification data, checked by `lookup` before installation. -/
public structure Answer where
  request : Request
  tokens : Array (Array Token)
  deriving BEq, Repr

/-- The classification requests a document's listings and inline code make, for languages no
native lexer reads. -/
-- conserves: none — a collector of requests, not a rewritten document.
public def requests (doc : Ir.Doc) (inline : Array (String × String) := #[]) :
    Array Request :=
  let asked (acc : Array Request) (language source : String) : Array Request :=
    if (ListingHighlight.language? language).isSome then acc
    else
      let request := Request.ofSource language source
      if acc.contains request then acc else acc.push request
  let listings := Ir.foldDoc (fun acc _ => acc) #[] doc (fb := fun acc block =>
    match block with
    | .verbatim _ source spec =>
      match spec.language with
      | none => acc
      | some language => asked acc language.val source
    | _ => acc)
  inline.foldl (fun acc (language, source) => asked acc language source) listings

/-- Exact content-key lookup, the raw source checked again; a foreign or stale answer changes
nothing. -/
public def lookup (answers : Array Answer) (language : String)
    (rawSource : String) : Option (Array (Array Token)) :=
  let request := Request.ofSource language rawSource
  match answers.find? (fun answer => answer.request == request) with
  | none => Option.none
  | some answer =>
    if answer.tokens.map lineText = Ir.verbatimLines rawSource then
      some answer.tokens
    else none

public theorem lookup_contract (answers : Array Answer) (language : String)
    (source : String) (highlight : Array (Array Token))
    (h : lookup answers language source = some highlight) :
    (∃ answer ∈ answers, answer.request = Request.ofSource language source ∧
      answer.tokens = highlight) ∧
    highlight.map lineText = Ir.verbatimLines source := by
  dsimp only [lookup] at h
  split at h
  · contradiction
  · rename_i answer found
    split at h
    · cases Option.some.inj h
      have key : answer.request = Request.ofSource language source := by
        simpa using Array.find?_some found
      exact ⟨⟨answer, Array.mem_of_find?_eq_some found, key, rfl⟩, by assumption⟩
    · contradiction

public theorem lookup_source_exact (answers : Array Answer) (language : String)
    (source : String) (highlight : Array (Array Token))
    (h : lookup answers language source = some highlight) :
    highlight.map lineText = Ir.verbatimLines source :=
  (lookup_contract answers language source highlight h).2

public inductive Failure where
  | unavailable | unsupported | rejected | invalidReply | sourceMismatch | budget
  deriving BEq, Repr

public def Failure.reason : Failure → String
  | .unavailable => "Pygments is unavailable"
  | .unsupported => "the installed Pygments has no built-in lexer for this language"
  | .rejected => "the built-in lexer could not classify this source"
  | .invalidReply => "the highlighter returned an invalid reply"
  | .sourceMismatch => "the highlighter did not preserve the source"
  | .budget => "the highlighter exceeded its resource limit"

/-- Source-valid plain data for a completed refusal; its typed failure travels beside it. -/
public def plainAnswer (request : Request) : Answer :=
  { request
    tokens := request.lines.map fun text => #[{ text }] }

public theorem plainAnswer_source_exact (request : Request) :
    (plainAnswer request).tokens.map lineText = request.lines := by
  simp [plainAnswer, Array.map_map, Function.comp_def, lineText]

public structure Classified where
  offset : Nat
  tokenClass : String
  text : String
  deriving BEq, Repr

/-- Split token text at LF, keeping blank lines and indentation; adjacent chunks of one type
share a token. -/
private def splitTokens (tokens : Array Classified) : Array (Array Token) := Id.run do
  let mut lines : Array (Array Token) := #[#[]]
  for token in tokens do
    let kind := Kind.ofPygments token.tokenClass
    let parts := token.text.splitOn "\n"
    for (part, i) in parts.zipIdx do
      if i > 0 then lines := lines.push #[]
      -- The line is modified in place, never shared and copied per token.
      if !part.isEmpty then
        lines := lines.modify (lines.size - 1) fun last =>
          match last.back? with
          | some prev =>
            if prev.kind == kind then last.pop.push { prev with text := prev.text ++ part }
            else last.push { kind, text := part }
          | none => last.push { kind, text := part }
  return lines

/-- Validate a tool's tokens against the request, offsets in characters as Pygments counts them;
`terminalLf` admits one trailing LF. -/
public def ofTokens (request : Request) (tokens : Array Classified)
    (terminalLf : Bool := false) : Except Failure Answer :=
  let contiguous := (tokens.foldl (fun (offset, valid) token =>
    (offset + token.text.length, valid && token.offset == offset)) (0, true)).2
  let expected := if terminalLf then request.source ++ "\n" else request.source
  if !contiguous || tokens.foldl (fun text token => text ++ token.text) "" != expected then
    .error .sourceMismatch
  else
    let lines := splitTokens tokens
    let highlight := if request.source.isEmpty then #[] else
      if terminalLf then lines.pop else lines
    if highlight.map lineText = request.lines then
      .ok { request, tokens := highlight }
    else .error .sourceMismatch

public theorem ofTokens_source_exact (request : Request) (tokens : Array Classified)
    (terminalLf : Bool) (answer : Answer)
    (h : ofTokens request tokens terminalLf = .ok answer) :
    answer.request = request ∧ answer.tokens.map lineText = request.lines := by
  dsimp only [ofTokens] at h
  generalize (if terminalLf then request.source ++ "\n" else request.source) = expected at h
  generalize (if request.source.isEmpty then #[] else
    if terminalLf then (splitTokens tokens).pop else splitTokens tokens) = highlight at h
  split at h
  · contradiction
  · split at h
    · cases Except.ok.inj h
      exact ⟨rfl, by assumption⟩
    · contradiction

-- Protocol ceilings on allocation and capture: 1 MiB of source, 256 requests, 262144 token
-- records, 16 MiB of JSON.
public def maxSourceBytes : Nat := 1024 * 1024
public def maxRequests : Nat := 256
public def maxTokens : Nat := 262144
public def maxReplyBytes : Nat := 16 * 1024 * 1024

public def withinBudget (rs : Array Request) : Bool :=
  rs.size ≤ maxRequests &&
    rs.foldl (fun bytes r => bytes + r.source.utf8ByteSize + r.language.utf8ByteSize) 0
      ≤ maxSourceBytes

/-- The batch's wire form: only language and normalized source cross the process boundary. -/
public def encode (rs : Array Request) : String :=
  (Json.mkObj [
    ("version", toJson (1 : Nat)),
    ("requests", Json.arr (rs.map fun request => Json.mkObj [
      ("language", toJson request.language),
      ("source", toJson request.source)]))]).compress

private def classified (value : Json) : Except String Classified := do
  return { offset := ← value.getObjValAs? Nat "offset"
           tokenClass := ← value.getObjValAs? String "kind"
           text := ← value.getObjValAs? String "text" }

/-- Decode a complete v1 batch or reject it whole; a per-request error is a plain reply with a
typed failure. -/
public def decode (rs : Array Request) (body : String) (terminalLf : Bool := false) :
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
      match ofTokens request tokens terminalLf with
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
