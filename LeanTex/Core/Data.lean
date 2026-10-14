module

public import LeanTex.Core.Bib
public import LeanTex.Core.Parse

/-! Data-driven documents: `@kind{…}` records from a `.bib` file or an inline `\data` group,
expanded before elaboration through `\val`, `foreach` and `\ifdata` by a bounded fold. -/

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

/-- A surface scan pairing a command with its operand across input wrappers, which no leaf fold
reads. -/
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
decreasing_by raws_dec

/-- Every `.bib` source the document's `\data` declarations name, first appearance first, with
its declaration span. -/
public def fileRefsAt (file : String) (raws : Array Raw) : Array (String × Span) :=
  refsList file #[] raws.toList

public theorem fileRefsAt_input_exact (caller file name : String) (body : Array Raw) (pos : Pos)
    (h : Parse.inputEnvFile? name = some file) :
    fileRefsAt caller #[.env name body pos] = fileRefsAt file body := by
  simp [fileRefsAt, refsList, h]

/-- The filename-free view of `fileRefsAt`, for callers that only load the named sources. -/
public def fileRefs (raws : Array Raw) : Array (String × Pos) :=
  (fileRefsAt "" raws).map fun (name, span) => (name, span.pos)

private def hasDataList : List Raw → Bool
  | [] => false
  | .ctrl "data" _ :: _ => true
  | .group body _ :: rest | .env _ body _ :: rest =>
    hasDataList body.toList || hasDataList rest
  | _ :: rest => hasDataList rest
termination_by l => sizeOf l
decreasing_by raws_dec

/-- Does the document declare any `\data` at all? -/
public def hasData (raws : Array Raw) : Bool :=
  hasDataList raws.toList

/-- The record store: every parsed record in declaration order, with its source name. -/
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
binding and the field name, or the W0364 message, help and detail. -/
def resolveVar (env : List Binding) (path : String) :
    Except (String × Option String × Option String) (Binding × String) :=
  match path.splitOn "." with
  | [v, f] =>
    let v := v.trimAscii.toString
    let f := f.trimAscii.toString.toLower
    if v.isEmpty || f.isEmpty then
      .error (s!"'{path}' is not a data path",
        some "a path is variable.field, as in '\\val{job.role}'", none)
    else
      match env.find? (·.var == v) with
      | none =>
        .error (s!"'{v}' is not bound here",
          some s!"'\\begin\{foreach}\{{v}}\{kind}' binds it over the '@kind' records", none)
      | some b => .ok (b, f)
  | _ =>
    .error (s!"'{path}' is not a data path",
      some "a path is variable.field, as in '\\val{job.role}'", none)

/-- Resolve `var.field`: the field's raw text and source name, or the W0364 message and help. -/
def resolvePath (env : List Binding) (path : String) :
    Except (String × Option String × Option String) (String × String) :=
  match resolveVar env path with
  | .error e => .error e
  | .ok (b, f) =>
    match b.entry.field? f with
    | some txt => .ok (b.src, txt)
    | none =>
      let carried := String.intercalate ", " (b.entry.fields.toList.map (·.1))
      .error (s!"'{f}' is absent in a '@{b.entry.kind}' record",
        some s!"'\\ifdata\{{path}}\{…}' renders content only when the field is present",
        some s!"{b.entry.kind}[{b.index}] carries: {carried}")

/-- A field value's raws and diagnostics through the document's own lexer and parser. -/
def valParsed (src text : String) : Array Raw × Array Diag :=
  let (toks, lexDiags) := Lex.lex src text
  let (raws, parseDiags) := Parse.parse src toks
  (raws, lexDiags ++ parseDiags)

/-- The raws inside a leading `[…]` and the list past its first top-level `]`. -/
def bracketSplit : List Raw → List Raw × List Raw
  | [] => ([], [])
  | .sym ']' _ :: rest => ([], rest)
  | r :: rest =>
    let (a, b) := bracketSplit rest
    (r :: a, b)

private theorem bracketSplit_le (l : List Raw) :
    sizeOf (bracketSplit l).1 ≤ sizeOf l ∧ sizeOf (bracketSplit l).2 ≤ sizeOf l := by
  fun_induction bracketSplit l <;> simp_all <;> omega

/-- A leading optional `[…]`, maybe after one space: its raws, empty when absent, and the rest. -/
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
    (help : Option String := none) (detail : Option String := none) : M Unit :=
  modify fun st => { st with
    diags := st.diags.push (Diag.of code msg (some ⟨st.file, pos⟩) (help := help) (detail := detail)) }

/-- Install one source's records in file order; a parse error is W0352 and costs its entry. -/
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
    say .W0364 s!"no '@{kind}' records in the data" pos
      (detail := some s!"it carries: {String.intercalate ", " (ks.toList.map ("@" ++ ·))}")

mutual

/-- The expansion walk: substitution only, bounded by the finite record list. -/
-- conserves: none — substitution by design; `expandData_covers` states it
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
    | .error (msg, help, detail) =>
      say .W0364 msg pos help detail
      expandList env out rest
  | .ctrl "val" pos :: rest => do
    say .E0304 "'\\val' needs {variable.field}" pos
    expandList env out rest
  | .ctrl "ifdata" pos :: .group cond _ :: .group thenB _ :: rest
  | .ctrl "ifdata" pos :: .group cond _ :: .space :: .group thenB _ :: rest => do
    let present ← do
      match resolveVar env (Parse.rawSrc cond) with
      | .ok (b, f) => pure (b.entry.field? f).isSome
      | .error (msg, help, detail) =>
        say .W0364 msg pos help detail
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

/-- One record after another, the expanded separator between iterations. -/
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

/-- Expand a document's data vocabulary; a document declaring no `\data` is returned untouched. -/
public def expandData (file : String) (sources : Array (String × String))
    (raws : Array Raw) : Array Raw × Array Diag :=
  if !hasDataList raws.toList then (raws, #[])
  else
    let (out, st) := (expandList [] #[] raws.toList).run
      { sources := sources, file := file }
    (out, st.diags)

theorem expandData_covers (env : List Binding) (out : Array Raw)
    (st : St) (pos gp : Pos) (body : Array Raw) (src txt : String)
    (h : resolvePath env (Parse.rawSrc body) = .ok (src, txt)) :
    (expandList env out [.ctrl "val" pos, .group body gp]).run st =
      (out ++ (valParsed src txt).1,
       { st with diags := st.diags ++ (valParsed src txt).2 }) := by
  simp [expandList, h]
  rfl

end LeanTex.Core.Data
