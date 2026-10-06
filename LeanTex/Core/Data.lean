module

public import LeanTex.Core.Bib
public import LeanTex.Core.Parse

/-! Data-driven documents: `@job{…}` records read from a `.bib` file (or an
inline `\data{ @job{…} }` group), expanded into the document before
elaboration. The vocabulary is three spellings — `\val{var.field}`,
`\begin{foreach}{var}{kind}[sep]`, `\ifdata{var.field}{then}[else]` — and
one declaration, `\data{ file = "records.bib" }`. A braced field value is
body-language TeX: it is lexed by the document's own lexer and parsed by
the document's own parser at the use site (`valParsed`), so `\%`, `~`,
`\emph{}` and `\item` work inside a value and `expandData_covers` — a data
document elaborates as the document with the data inlined by hand — is
near-definitional. The line is drawn tight: no expressions, no filters, no
functions, no recursion, no indices; expansion is a bounded fold over the
finite record list, so the designed-terminating property of the language
survives by construction.

Reading the file is the driver's effect (`fileRefsAt` is the request value,
the `Ir.bibRefs` shape); this module only ever sees the text. -/

namespace LeanTex.Core.Data

open LeanTex.Core Parse

/-- A `\data` file request resolves by the bibliography's own rule:
records live in `.bib` files. -/
public abbrev sourceName := Bib.sourceName

/-- What a `\data{…}` group declares: `.inl name` for `file = "name"`,
`.inr text` for inline `@kind{…}` records, `none` when it is neither. -/
def dataDecl? (body : Array Raw) : Option (String ⊕ String) :=
  let txt := Parse.rawSrc body
  if txt.startsWith "@" then some (.inr txt)
  else
    match txt.splitOn "=" with
    | [k, v] =>
      if k.trimAscii.toString == "file" then
        let v := v.trimAscii.toString
        let v := if v.startsWith "\"" && v.endsWith "\"" && v.length ≥ 2 then
          ((v.drop 1).toString.dropEnd 1).toString else v
        if v.isEmpty then none else some (.inl v)
      else none
    | _ => none

/-- This surface scan pairs a command with its operand and carries the
input filename across wrappers; an IR leaf fold cannot read those siblings. -/
private def refsList (file : String) (out : Array (String × Span)) :
    List Raw → Array (String × Span)
  | [] => out
  | .ctrl "data" pos :: .group body _ :: rest
  | .ctrl "data" pos :: .space :: .group body _ :: rest =>
    match dataDecl? body with
    | some (.inl name) =>
      let out := if out.any (·.1 == name) then out else out.push (name, ⟨file, pos⟩)
      refsList file out rest
    | _ => refsList file out rest
  | .group body _ :: rest =>
    refsList file (refsList file out body.toList) rest
  | .env name body _ :: rest =>
    let innerFile := (Parse.inputEnvFile? name).getD file
    refsList file (refsList innerFile out body.toList) rest
  | _ :: rest => refsList file out rest
termination_by l => sizeOf l
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals (have hb : sizeOf body = 1 + sizeOf body.toList := rfl; omega)

/-- Every `.bib` source the document's `\data` declarations name, in
first-appearance order, deduplicated, with the complete first declaration
span. Input wrappers change the filename only within their own contents.
The driver fulfils these requests before elaboration, where the expansion
needs the records where `\begin{foreach}` stands. Files are effects, so
the core never opens one. -/
public def fileRefsAt (file : String) (raws : Array Raw) : Array (String × Span) :=
  refsList file #[] raws.toList

/-- A file wrapper's requests are exactly its body's requests under the
included filename, independent of the caller's filename and wrapper position. -/
public theorem fileRefsAt_input_exact (caller file name : String) (body : Array Raw) (pos : Pos)
    (h : Parse.inputEnvFile? name = some file) :
    fileRefsAt caller #[.env name body pos] = fileRefsAt file body := by
  simp [fileRefsAt, refsList, h]

/-- The filename-free view for callers that only load the named sources.
Diagnostics use `fileRefsAt` with the actual root filename. -/
public def fileRefs (raws : Array Raw) : Array (String × Pos) :=
  (fileRefsAt "" raws).map fun (name, span) => (name, span.pos)

private def hasDataList : List Raw → Bool
  | [] => false
  | .ctrl "data" _ :: _ => true
  | .group body _ :: rest | .env _ body _ :: rest =>
    hasDataList body.toList || hasDataList rest
  | _ :: rest => hasDataList rest
termination_by l => sizeOf l
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals (have hb : sizeOf body = 1 + sizeOf body.toList := rfl; omega)

/-- Does the document declare any `\data` at all? The driver's gate: no
declaration, no file scan, no expansion — a data-free document costs one
short-circuiting walk and nothing else, and its own `\val` or `foreach`
spellings stay its own (the vocabulary exists only where data does). -/
public def hasData (raws : Array Raw) : Bool :=
  hasDataList raws.toList

/-- The record store: every parsed record in declaration order, each with
the source name its text came from (the file a value's own diagnostics
must name). Records of one kind keep file order — `foreach` iterates them
as written. -/
structure Store where
  entries : Array (String × Bib.Entry) := #[]
  deriving Repr

/-- The distinct kinds the store carries, in first-appearance order: what
a diagnostic about an unknown kind can name. -/
def Store.kinds (st : Store) : Array String :=
  st.entries.foldl (fun out (_, e) =>
    if out.contains e.kind then out else out.push e.kind) #[]

/-- One `foreach` binding: the variable, its record, and where the record
stands — kind and 1-based position for the diagnostic, source name for the
value's own spans. -/
structure Binding where
  var : String
  index : Nat
  src : String
  entry : Bib.Entry

/-- Resolve a path's variable against the innermost-first bindings: the
binding and the field name, or the W0364 message and help. -/
def resolveVar (env : List Binding) (path : String) :
    Except (String × Option String) (Binding × String) :=
  match path.splitOn "." with
  | [v, f] =>
    let v := v.trimAscii.toString
    let f := f.trimAscii.toString.toLower
    if v.isEmpty || f.isEmpty then
      .error (s!"'{path}' is not a data path",
        some "a path is variable.field, as in '\\val{job.role}'")
    else
      match env.find? (·.var == v) with
      | none =>
        .error (s!"'{v}' is not bound here",
          some s!"'\\begin\{foreach}\{{v}}\{kind}' binds it over the '@kind' records")
      | some b => .ok (b, f)
  | _ =>
    .error (s!"'{path}' is not a data path",
      some "a path is variable.field, as in '\\val{job.role}'")

/-- Resolve `var.field`: the field's raw text and the source name it came
from, or the W0364 message and help — the absent-field message names the
entry's own fields, the E0403 nearest-names shape. -/
def resolvePath (env : List Binding) (path : String) :
    Except (String × Option String) (String × String) :=
  match resolveVar env path with
  | .error e => .error e
  | .ok (b, f) =>
    match b.entry.field? f with
    | some txt => .ok (b.src, txt)
    | none =>
      let carried := String.intercalate ", " (b.entry.fields.toList.map (·.1))
      .error (s!"'{f}' is absent in {b.entry.kind}[{b.index}]; its entries carry: {carried}",
        some s!"'\\ifdata\{{path}}\{…}' renders content only when the field is present")

/-- A field value's raws and diagnostics: the same lexer and the same
parser the document body went through — no data-specific lexing exists to
differ. This is decision 4 of the data design made structural, and the
function `expandData_covers` quantifies over. -/
def valParsed (src text : String) : Array Raw × Array Diag :=
  let (toks, lexDiags) := Lex.lex src text
  let (raws, parseDiags) := Parse.parse src toks
  (raws, lexDiags ++ parseDiags)

/-- The raws inside a leading `[…]` and the list past the closer: the
optional argument. Flat, as the elaborator's own optional scan is: the
first top-level `]` closes (a `]` inside a brace group is already a
`.group` node and cannot). -/
def bracketSplit : List Raw → List Raw × List Raw
  | [] => ([], [])
  | .sym ']' _ :: rest => ([], rest)
  | r :: rest =>
    let (a, b) := bracketSplit rest
    (r :: a, b)

private theorem bracketSplit_le (l : List Raw) :
    sizeOf (bracketSplit l).1 ≤ sizeOf l ∧ sizeOf (bracketSplit l).2 ≤ sizeOf l := by
  fun_induction bracketSplit l <;> simp_all <;> omega

/-- A leading optional `[…]`, possibly after one space: its raws (empty
when absent) and the list past it. An empty optional and an absent one
mean the same thing to both consumers — no separator, no else branch. -/
def optArg : List Raw → List Raw × List Raw
  | .sym '[' _ :: r1 | .space :: .sym '[' _ :: r1 => bracketSplit r1
  | l => ([], l)

private theorem optArg_le (l : List Raw) :
    sizeOf (optArg l).1 ≤ sizeOf l ∧ sizeOf (optArg l).2 ≤ sizeOf l := by
  unfold optArg
  split
  · rename_i r1
    have := bracketSplit_le r1
    simp <;> omega
  · rename_i r1
    have := bracketSplit_le r1
    simp <;> omega
  · cases l <;> simp <;> omega

/-- The arguments at the head of a `foreach` body — `{var}{kind}` and the
optional `[sep]` — with the iteration body; `none` when malformed. -/
def foreachArgs : List Raw → Option (String × String × (List Raw × List Raw))
  | .group varG _ :: .group kindG _ :: iter
  | .group varG _ :: .space :: .group kindG _ :: iter =>
    some (Parse.rawSrc varG, (Parse.rawSrc kindG).toLower, optArg iter)
  | _ => none

private theorem foreachArgs_le (l : List Raw) (v k : String) (s : List Raw × List Raw)
    (h : foreachArgs l = some (v, k, s)) :
    sizeOf s.1 ≤ sizeOf l ∧ sizeOf s.2 ≤ sizeOf l := by
  unfold foreachArgs at h
  split at h <;>
    simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    (obtain ⟨-, -, rfl⟩ := h
     rename_i iter
     have := optArg_le iter
     simp
     omega)

private structure St where
  sources : Array (String × String) := #[]
  store : Store := {}
  file : String := ""
  diags : Array Diag := #[]

private abbrev M := StateM St

private def say (code : DiagCode) (msg : String) (pos : Pos)
    (help : Option String := none) : M Unit :=
  modify fun st => { st with
    diags := st.diags.push (Diag.of code msg (some ⟨st.file, pos⟩) (help := help)) }

/-- Install one source's records: parse errors are W0352 — the same
contract the bibliography holds, one bad entry costs itself, never the
file — and the entries append in file order. -/
private def install (src text : String) : M Unit := do
  let parsed := Bib.parse text
  modify fun st => { st with
    diags := parsed.errors.foldl (fun ds (pos, msg) =>
      ds.push (Diag.of .W0352 s!"malformed .bib entry: {msg}; \
        the entry is skipped and the rest of '{src}' is kept" (some ⟨src, pos⟩))) st.diags
    store := ⟨parsed.entries.foldl (fun es e => es.push (src, e)) st.store.entries⟩ }

private def onData (pos : Pos) (body : Array Raw) : M Unit := do
  match dataDecl? body with
  | some (.inl name) =>
    match (← get).sources.find? (·.1 == name) with
    | some (_, text) => install name text
    | none => pure ()  -- the driver's missing-file diagnostic already fired
  | some (.inr text) => install (← get).file text
  | none =>
    say .E0320 "'\\data' takes file = \"name\" or inline '@kind{…}' records" pos

/-- The W0364 a `foreach` over an empty selection earns: an unknown kind
names what the store carries, an empty store says how to fill it. -/
private def sayNoRecords (kind : String) (pos : Pos) : M Unit := do
  let ks := (← get).store.kinds
  if ks.isEmpty then
    say .W0364 s!"no data records are declared before this point" pos
      (help := "'\\data{ file = \"records.bib\" }' declares them")
  else
    say .W0364 s!"no '@{kind}' records in the data; it carries: \
      {String.intercalate ", " (ks.toList.map ("@" ++ ·))}" pos

mutual

/-- The expansion walk. Substitution only: a spliced field value is content
and is never re-expanded, `foreach` iterates a finite record list, and
paths do not recurse — the fold is bounded by construction, no fuel. -/
-- conserves: none — the walk's whole job is substitution: `\val` splices a
-- field's raws in, `foreach` repeats its body, so a census equality over
-- the tree is false by design; the census statement is `expandData_covers`
-- below, on the public `expandData`.
private def expandList (env : List Binding) (out : Array Raw) :
    List Raw → M (Array Raw)
  | [] => pure out
  | .ctrl "data" pos :: .group body _ :: rest
  | .ctrl "data" pos :: .space :: .group body _ :: rest => do
    onData pos body
    expandList env out rest
  | .ctrl "data" pos :: rest => do
    say .E0304 "'\\data' needs a {…} group" pos
      (help := "'\\data{ file = \"records.bib\" }' or inline '\\data{ @kind{…} }'")
    expandList env out rest
  | .ctrl "val" pos :: .group body _ :: rest
  | .ctrl "val" pos :: .space :: .group body _ :: rest => do
    match resolvePath env (Parse.rawSrc body) with
    | .ok (src, txt) =>
      let (vraws, vdiags) := valParsed src txt
      modify fun st => { st with diags := st.diags ++ vdiags }
      expandList env (out ++ vraws) rest
    | .error (msg, help) =>
      say .W0364 msg pos help
      expandList env out rest
  | .ctrl "val" pos :: rest => do
    say .E0304 "'\\val' needs {variable.field}" pos
    expandList env out rest
  | .ctrl "ifdata" pos :: .group cond _ :: .group thenB _ :: rest
  | .ctrl "ifdata" pos :: .group cond _ :: .space :: .group thenB _ :: rest => do
    let present ← do
      match resolveVar env (Parse.rawSrc cond) with
      | .ok (b, f) => pure (b.entry.field? f).isSome
      | .error (msg, help) =>
        say .W0364 msg pos help
        pure false
    let s := optArg rest
    let out ← if present then expandList env out thenB.toList
      else expandList env out s.1
    expandList env out s.2
  | .ctrl "ifdata" pos :: rest => do
    say .E0304 "'\\ifdata' needs {variable.field} and {content}" pos
    expandList env out rest
  | .env "foreach" body pos :: rest => do
    match _hargs : foreachArgs body.toList with
    | some (var, kind, s) => do
      let sep ← expandList env #[] s.1
      let selected := (← get).store.entries.filter (·.2.kind == kind)
      if selected.isEmpty then
        sayNoRecords kind pos
      let bound := (selected.toList.zipIdx 1).map fun ((src, e), i) =>
        { var := var, index := i, src := src, entry := e : Binding }
      let out ← expandEach env s.2 sep out true bound
      expandList env out rest
    | none => do
      say .E0304 "'\\begin{foreach}' needs {variable} and {kind}" pos
      expandList env out rest
  | .group body p :: rest => do
    let inner ← expandList env #[] body.toList
    expandList env (out.push (.group inner p)) rest
  | .env n body p :: rest => do
    -- An `\input` wrapper switches the file its diagnostics name.
    match Parse.inputEnvFile? n with
    | some f =>
      let saved := (← get).file
      modify fun st => { st with file := f }
      let inner ← expandList env #[] body.toList
      modify fun st => { st with file := saved }
      expandList env (out.push (.env n inner p)) rest
    | none =>
      let inner ← expandList env #[] body.toList
      expandList env (out.push (.env n inner p)) rest
  | r :: rest => expandList env (out.push r) rest
termination_by l => (sizeOf l, 0)
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals try (have ho := optArg_le rest; omega)
  all_goals try
    (have hb : sizeOf thenB = 1 + sizeOf thenB.toList := rfl
     have ho := optArg_le rest
     omega)
  all_goals try
    (have hb : sizeOf body = 1 + sizeOf body.toList := rfl
     omega)
  all_goals
    (have hb : sizeOf body = 1 + sizeOf body.toList := rfl
     have hf := foreachArgs_le body.toList _ _ _ _hargs
     omega)

/-- One record after another: the body expands once per binding, the
expanded separator splices between iterations — Pandoc's `$sep$`, without
a filter. -/
private def expandEach (env : List Binding) (body : List Raw) (sep : Array Raw)
    (out : Array Raw) (first : Bool) : List Binding → M (Array Raw)
  | [] => pure out
  | b :: bs => do
    let out := if first then out else out ++ sep
    let out ← expandList (b :: env) out body
    expandEach env body sep out false bs
termination_by bs => (sizeOf body, bs.length + 1)
decreasing_by
  all_goals simp_wf
  all_goals omega

end

/-- Expand a document's data vocabulary: records install in document order
(data precedes use — a forward reference diagnoses as unresolved, so a
cycle is unrepresentable), `foreach` repeats its body over the records of
a kind in file order, `\val` splices a field's text through the document's
own lexer and parser, `\ifdata` branches on presence. A document that
declares no `\data` is returned untouched: the vocabulary exists only
where data does, so a document's own `\val` command stays its own. -/
public def expandData (file : String) (sources : Array (String × String))
    (raws : Array Raw) : Array Raw × Array Diag :=
  if !hasDataList raws.toList then (raws, #[])
  else
    let (out, st) := (expandList [] #[] raws.toList).run
      { sources := sources, file := file }
    (out, st.diags)

/-- `expandData_covers` — substitution, the data design's headline theorem:
a `\val` whose path resolves expands to exactly the raws of the field's
text through the document's own lexer and parser (`valParsed`), so the
elaboration of a data document is the elaboration of the document with the
data inlined by hand — there is no data-specific lexing or elaboration
left to differ, and every content theorem (census, escaping, layout)
applies to data documents unchanged. Near-definitional by design: the
`val` arm of the walk is literally this splice. -/
theorem expandData_covers (env : List Binding) (out : Array Raw)
    (st : St) (pos gp : Pos) (body : Array Raw) (src txt : String)
    (h : resolvePath env (Parse.rawSrc body) = .ok (src, txt)) :
    (expandList env out [.ctrl "val" pos, .group body gp]).run st =
      (out ++ (valParsed src txt).1,
       { st with diags := st.diags ++ (valParsed src txt).2 }) := by
  simp [expandList, h]
  rfl

end LeanTex.Core.Data
