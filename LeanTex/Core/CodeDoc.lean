module

public import LeanTex.Core.MdDesugar
public import LeanTex.Core.Parse
public import LeanTex.Core.Ir
public import LeanTex.Core.LeanStatement
import LeanTex.Core.Decl
import LeanTex.Core.Hex

/-! # Code files as documents

A source file read as its documentation comments, in markdown, and its code, as listings. -/

namespace LeanTex.Core.Code

open LeanTex.Core LeanTex.Core.Parse

/-- Where a documentation comment stands on the page. -/
public inductive Stand where
  /-- Where it is written. -/
  | inPlace
  /-- Above the code run just before it, which the declaration it documents opens. -/
  | aboveRun
  /-- Above all the code since the prose before it. -/
  | aboveAll
  deriving Repr, BEq, DecidableEq, Inhabited

/-- What a run of source characters is. -/
public inductive Kind where
  /-- Code, set as a listing. -/
  | code
  /-- A documentation comment, read as markdown; `module` marks the file's own description. -/
  | prose (module : Bool) (stand : Stand)
  /-- The leantex directive line. -/
  | directive
  /-- White space beside prose or a directive, or ending a code run, which ships nowhere. -/
  | blank
  /-- Where a paragraph Lean's answer gives stands beside the code it is of, by its index; it
  holds no character. -/
  | statement (index : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A cut a scanner makes: its kind and its character range. -/
public structure Cut where
  kind : Kind
  start : Nat
  stop : Nat
  deriving Repr, BEq, Inhabited

/-- A run of the source: its kind and its length in characters. -/
public structure Run where
  kind : Kind
  len : Nat
  deriving Repr, BEq, Inhabited

/-- A segment of the source: its kind, where it starts, and its characters. -/
public structure Seg where
  kind : Kind
  start : Nat
  text : List Char
  deriving Repr, BEq, Inhabited

/-- The white space a blank run may hold. -/
public def isWhite (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0C'

/-- A piece of the page, in reading order. -/
public inductive Piece where
  /-- A documentation comment. -/
  | prose (seg : Seg)
  /-- A listing: where its first code run starts, and the code runs it joins, in source order. -/
  | code (start : Nat) (text : List Char)
  /-- A paragraph Lean's answer gives, by its index: a statement, or code in a statement's place. -/
  | statement (index : Nat)
  deriving Repr, BEq, Inhabited

private inductive LeanMode where
  | str (interpolated : Bool)
  | term (depth : Nat)

private inductive PyTok where
  | name (start stop : Nat)
  /-- A string literal; `plain` when no `f`, `b` or `t` prefix makes it something else. -/
  | str (start stop : Nat) (plain : Bool)
  | op (c : Char)
  | other

/-- One logical line: where its first physical line starts, its indentation, and its tokens. -/
private structure PyLine where
  lineStart : Nat
  indent : Nat
  toks : Array PyTok

private inductive PyMode where
  | str (quote : Char) (triple raw f : Bool)
  | expr (depth : Nat)
  /-- A replacement field's format spec: text up to its `}`, a `{` opening a nested field. -/
  | spec

/-- A documentation comment's markdown, and for each of its lines the source line it stands on
and the columns before it there. -/
public structure Prose where
  text : String
  lines : Array (Nat × Nat)
  deriving Repr, Inhabited

/-- What reading a code file's pieces has gathered: the body, the reader's diagnostics, and the
title the file's description opens on. -/
public structure Acc where
  body : Array Raw := #[]
  diags : Array Diag := #[]
  title : Option (Array Raw) := none
  /-- Whether the body holds the title heading its description opens on. -/
  titled : Bool := false
  sawModule : Bool := false

/-- A reading of a Lean file's declarations its page sets. -/
public inductive View where
  | code
  | math
  deriving Repr, BEq, DecidableEq, Inhabited

/-- What a file's directive asks its page to show: its views in order, the declarations it
selects, and each view name that names none. -/
public structure Showing where
  views : List View := [.code]
  decls : Option (List String) := none
  unknown : List String := []
  deriving Repr, Inhabited

/-- What a page sets from a file's pieces: each statement's paragraph by index, and whether it
shows the file's code and documentation. -/
public structure PageSet where
  stmts : Array (Array Raw) := #[]
  code : Bool := true

/-- The kind a run's characters may carry: white space alone is blank, a directive is one line,
and anything else is code. -/
@[expose] public def guard (k : Kind) (cs : List Char) : Kind :=
  match k with
  | .blank => if cs.all isWhite then .blank else .code
  | .directive => if cs.all (· != '\n') then .directive else .code
  | .code => .code
  | .prose m st => .prose m st
  | .statement i => if cs.isEmpty then .statement i else .code

/-- The source cut into segments, each run taking its length from `base`; what no run takes is a
final code segment. -/
@[expose] public def segmentsFrom (base : Nat) : List Run → List Char → List Seg
  | [], [] => []
  | [], c :: cs => [⟨.code, base, c :: cs⟩]
  | r :: rs, cs =>
    ⟨guard r.kind (cs.take r.len), base, cs.take r.len⟩ ::
      segmentsFrom (base + r.len) rs (cs.drop r.len)

/-- Every source character stands in exactly one segment, in source order. -/
public theorem segmentsFrom_source_exact (base : Nat) (rs : List Run) (cs : List Char) :
    ((segmentsFrom base rs cs).map Seg.text).flatten = cs := by
  induction rs generalizing base cs with
  | nil => cases cs <;> simp [segmentsFrom]
  | cons r rs ih => simp [segmentsFrom, ih]


public def Piece.code? : Piece → Option (List Char)
  | .code _ t => some t
  | .prose _ | .statement _ => none

public def Piece.prose? : Piece → Option Seg
  | .prose s => some s
  | .code _ _ | .statement _ => none

/-- The open listing pushed as one piece, when it holds any code. -/
@[expose] public def flush (out : Array Piece) : List Seg → Array Piece
  | [] => out
  | s :: rest => out.push (.code s.start ((s :: rest).flatMap Seg.text))

/-- Segments in source order to pieces in page order: code joins into listings, and prose stands
where its `Stand` says. -/
@[expose] public def assembleGo (out : Array Piece) (pending : List Seg) : List Seg → Array Piece
  | [] => flush out pending
  | s :: rest =>
    match s.kind with
    | .code => assembleGo out (pending ++ [s]) rest
    | .blank | .directive => assembleGo out pending rest
    | .statement i => assembleGo ((flush out pending).push (.statement i)) [] rest
    | .prose _ .inPlace => assembleGo ((flush out pending).push (.prose s)) [] rest
    | .prose _ .aboveAll => assembleGo (out.push (.prose s)) pending rest
    | .prose _ .aboveRun =>
      match pending.getLast? with
      | none => assembleGo (out.push (.prose s)) [] rest
      | some h => assembleGo ((flush out pending.dropLast).push (.prose s)) [h] rest

@[expose] public def assemble (segs : List Seg) : Array Piece := assembleGo #[] [] segs

/-- Whether a segment is code. -/
@[expose] public def Seg.isCode (s : Seg) : Bool :=
  match s.kind with
  | .code => true
  | .prose _ _ | .directive | .blank | .statement _ => false

/-- The characters of a sequence's code segments, in order. -/
@[expose] public def codeOf (segs : List Seg) : List Char :=
  (segs.filter Seg.isCode).flatMap Seg.text

private theorem flush_code (out : Array Piece) (pending : List Seg) :
    ((flush out pending).toList.filterMap Piece.code?).flatten =
      (out.toList.filterMap Piece.code?).flatten ++ pending.flatMap Seg.text := by
  cases pending <;> simp [flush, Piece.code?]

private theorem flush_prose (out : Array Piece) (pending : List Seg) :
    (flush out pending).toList.filterMap Piece.prose? = out.toList.filterMap Piece.prose? := by
  cases pending <;> simp [flush, Piece.prose?]

private theorem push_prose_code (out : Array Piece) (s : Seg) :
    ((out.push (.prose s)).toList.filterMap Piece.code?).flatten =
      (out.toList.filterMap Piece.code?).flatten := by
  simp [Piece.code?]

private theorem push_statement_code (out : Array Piece) (i : Nat) :
    ((out.push (.statement i)).toList.filterMap Piece.code?).flatten =
      (out.toList.filterMap Piece.code?).flatten := by
  simp [Piece.code?]

private theorem codeOf_code (s : Seg) (rest : List Seg) (h : s.kind = .code) :
    codeOf (s :: rest) = s.text ++ codeOf rest := by
  simp [codeOf, Seg.isCode, h]

private theorem codeOf_other (s : Seg) (rest : List Seg) (h : s.isCode = false) :
    codeOf (s :: rest) = codeOf rest := by
  simp [codeOf, h]

private theorem assembleGo_code (out : Array Piece) (pending segs : List Seg) :
    ((assembleGo out pending segs).toList.filterMap Piece.code?).flatten =
      (out.toList.filterMap Piece.code?).flatten ++ pending.flatMap Seg.text ++ codeOf segs := by
  induction segs generalizing out pending with
  | nil => simp [assembleGo, flush_code, codeOf]
  | cons s rest ih =>
    unfold assembleGo
    rcases hk : s.kind with _ | ⟨m, st⟩ | _ | _ | i
    · simp only [ih, codeOf_code s rest hk, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.append_assoc]
    · have ho := codeOf_other s rest (by simp [Seg.isCode, hk])
      cases st with
      | inPlace => simp only [ih, push_prose_code, flush_code, ho, List.flatMap_nil, List.append_nil]
      | aboveAll => simp only [ih, push_prose_code, ho]
      | aboveRun =>
        rcases hl : pending.getLast? with _ | h
        · simp only [ih, push_prose_code, ho, List.getLast?_eq_none_iff.mp hl, List.flatMap_nil]
        · have hp : pending = pending.dropLast ++ [h] := by
            rw [List.getLast?_eq_some_iff] at hl
            obtain ⟨ys, rfl⟩ := hl
            simp
          simp only [ih, push_prose_code, flush_code, ho]
          conv => rhs; rw [hp]
          simp [List.append_assoc]
    · simp only [ih, codeOf_other s rest (by simp [Seg.isCode, hk])]
    · simp only [ih, codeOf_other s rest (by simp [Seg.isCode, hk])]
    · simp only [ih, push_statement_code, flush_code, codeOf_other s rest (by simp [Seg.isCode, hk]),
        List.flatMap_nil, List.append_nil]

/-- The listings, in page order, hold exactly the code segments, in source order. -/
public theorem assemble_code_exact (segs : List Seg) :
    ((assemble segs).toList.filterMap Piece.code?).flatten = codeOf segs := by
  simp [assemble, assembleGo_code]

/-- Whether a segment is a documentation comment. -/
@[expose] public def Seg.isProse (s : Seg) : Bool :=
  match s.kind with
  | .prose _ _ => true
  | .code | .directive | .blank | .statement _ => false

private theorem assembleGo_prose (out : Array Piece) (pending segs : List Seg) :
    (assembleGo out pending segs).toList.filterMap Piece.prose? =
      out.toList.filterMap Piece.prose? ++ segs.filter Seg.isProse := by
  induction segs generalizing out pending with
  | nil => simp [assembleGo, flush_prose]
  | cons s rest ih =>
    unfold assembleGo
    rcases hk : s.kind with _ | ⟨m, st⟩ | _ | _ | i
    · simp [ih, Seg.isProse, hk]
    · cases st with
      | inPlace => simp [ih, Seg.isProse, hk, flush_prose, Piece.prose?]
      | aboveAll => simp [ih, Seg.isProse, hk, Piece.prose?]
      | aboveRun =>
        rcases pending.getLast? with _ | h
        · simp [ih, Seg.isProse, hk, Piece.prose?]
        · simp [ih, Seg.isProse, hk, flush_prose, Piece.prose?]
    · simp [ih, Seg.isProse, hk]
    · simp [ih, Seg.isProse, hk]
    · simp [ih, Seg.isProse, hk, flush_prose, Piece.prose?]

/-- The documentation comments, in page order, are the prose segments in source order. -/
public theorem assemble_prose_exact (segs : List Seg) :
    (assemble segs).toList.filterMap Piece.prose? = segs.filter Seg.isProse := by
  simp [assemble, assembleGo_prose]


/-! ## Cutting the source -/

/-- The runs a sorted list of cuts leaves in a source of `size` characters, each gap a code run; a
cut that overlaps the one before it is dropped. -/
@[expose] public def runsGo (size : Nat) (out : Array Run) (pos : Nat) : List Cut → Array Run
  | [] => if pos < size then out.push ⟨.code, size - pos⟩ else out
  | c :: rest =>
    if c.start < pos || c.stop < c.start then runsGo size out pos rest
    else
      let out := if pos < c.start then out.push ⟨.code, c.start - pos⟩ else out
      runsGo size (out.push ⟨c.kind, c.stop - c.start⟩) c.stop rest


private def at? (src : Array Char) (i : Nat) (c : Char) : Bool := src[i]? == some c

/-- The index of the line end at or after `i`, the source's end when no line ends. -/
private def lineEnd (src : Array Char) (i : Nat) : Nat := Id.run do
  let mut j := i
  for _ in [i:src.size] do
    if at? src j '\n' then return j
    j := j + 1
  return src.size

/-- A code run's leading white space, code and trailing white space: the code keeps the
indentation of its first line and the end of its last. -/
private def trimCode (src : Array Char) (start len : Nat) : Nat × Nat × Nat := Id.run do
  let stop := start + len
  let mut first := stop
  for i in [start:stop] do
    if !(src[i]?.map isWhite).getD true then
      first := i
      break
  if first == stop then return (len, 0, 0)
  let mut lead := 0
  let mut sawLine := false
  for i in [start:first] do
    if at? src i '\n' then
      lead := i + 1 - start
      sawLine := true
  let midLine := start > 0 && !at? src (start - 1) '\n'
  if !sawLine && midLine then lead := first - start
  let mut last := first
  for i in [first:stop] do
    if !(src[i]?.map isWhite).getD true then last := i
  let mut codeEnd := last + 1
  for i in [last + 1:stop] do
    if at? src i '\n' then
      codeEnd := i + 1
      break
  return (lead, codeEnd - start - lead, stop - codeEnd)

/-- Every code run split into its white space and its code. -/
private def normalize (src : Array Char) (runs : List Run) : Array Run := Id.run do
  let mut out : Array Run := #[]
  let mut pos := 0
  for r in runs do
    if r.kind == .code then
      let (a, b, c) := trimCode src pos r.len
      if a > 0 then out := out.push ⟨.blank, a⟩
      if b > 0 then out := out.push ⟨.code, b⟩
      if c > 0 then out := out.push ⟨.blank, c⟩
    else out := out.push r
    pos := pos + r.len
  return out

/-- The directive's marker in a language's line comments. -/
public def directiveMarker : Ir.CodeLang → String
  | .lean => "-- leantex:"
  | .python | .bash => "# leantex:"

/-- The directive line, the first line or the one after a `#!` line, and its entries' text. -/
public def directive? (lang : Ir.CodeLang) (src : Array Char) : Option (Cut × String) :=
  let firstEnd := lineEnd src 0
  let shebang := at? src 0 '#' && at? src 1 '!'
  let lineStart := if shebang then firstEnd + 1 else 0
  let stop := if shebang then lineEnd src lineStart else firstEnd
  let line := String.ofList (src.extract lineStart stop).toList
  let lead := (line.toList.takeWhile (· == ' ')).length
  let body := String.ofList (line.toList.drop lead)
  let marker := directiveMarker lang
  if lineStart < src.size && body.startsWith marker then
    some (⟨.directive, lineStart + lead, stop⟩,
      (String.ofList (body.toList.drop marker.length)).trimAscii.toString)
  else none

/-- A directive's entries by key, each bare entry continuing the key before it. -/
public def keyedEntries (entries : List String) : List (String × List String) :=
  (entries.foldl (fun (acc : Array (String × List String)) e =>
    match Decl.splitEntry e with
    | some (k, v) => acc.push (k, [v])
    | none => match acc.back? with
      | some (k, vs) => acc.pop.push (k, vs.concat e.trimAscii.toString)
      | none => acc.push ("", [e.trimAscii.toString])) #[]).toList

/-- The keys a directive takes for what its page shows, which no declaration reads. -/
public def showKeys : List String := ["show", "decls"]

/-- Whether a page shows the mathematics view. -/
public def Showing.math (s : Showing) : Bool := s.views.contains .math

public def Showing.code (s : Showing) : Bool := s.views.contains .code

public def Showing.mathFirst (s : Showing) : Bool :=
  match s.views with
  | .math :: _ => true
  | _ => false

/-- What a file's directive asks its page to show: its `show` views, `code` where it names none a
file of its language has, and its `decls`. -/
public def showingOf (lang : Ir.CodeLang) (src : Array Char) : Showing :=
  match directive? lang src with
  | none => {}
  | some (_, value) =>
    let groups := keyedEntries (Decl.splitEntries value)
    let named := ((groups.find? (·.1 == "show")).map (·.2)).getD []
    let viewOf? (n : String) : Option View :=
      if n == "code" then some .code else if n == "math" && lang == .lean then some .math else none
    let views := (named.filterMap viewOf?).eraseDups
    { views := if views.isEmpty then [.code] else views
      decls := (groups.find? (·.1 == "decls")).map (·.2)
      unknown := named.filter fun n => (viewOf? n).isNone }

/-- The first line among a file's leading comments that spells a directive the reader does not
read, past its first line or the line after `#!`. -/
public def strayDirective? (lang : Ir.CodeLang) (src : Array Char) : Option Nat := Id.run do
  let marker := directiveMarker lang
  let read := (directive? lang src).map (·.1.start)
  let comment := match lang with
    | .lean => "--"
    | .python | .bash => "#"
  let mut i := 0
  for _ in [0:src.size + 1] do
    if i ≥ src.size then break
    let e := lineEnd src i
    let line := String.ofList (src.extract i e).toList
    let body := String.ofList (line.toList.dropWhile (· == ' '))
    if body.startsWith marker && read != some (i + (line.length - body.length)) then return some i
    unless body.isEmpty || body.startsWith comment do break
    i := e + 1
  return none

/-! ### Lean -/

private def leanLetterLike (c : Char) : Bool :=
  let v := c.val
  (0x3b1 ≤ v && v ≤ 0x3c9 && v != 0x3bb) || (0x391 ≤ v && v ≤ 0x3A9 && v != 0x3A0 && v != 0x3A3) ||
    (0x3ca ≤ v && v ≤ 0x3fb) || (0x1f00 ≤ v && v ≤ 0x1ffe) || (0x2100 ≤ v && v ≤ 0x214f) ||
    (0x1d49c ≤ v && v ≤ 0x1d59f)

private def leanIdRest (c : Char) : Bool :=
  let v := c.val
  c.isAlphanum || c == '_' || c == '\'' || c == '!' || c == '?' || leanLetterLike c ||
    (0x2080 ≤ v && v ≤ 0x2089) || (0x2090 ≤ v && v ≤ 0x209c) || (0x1d62 ≤ v && v ≤ 0x1d6a)

/-- Past the end of a Lean block comment whose body starts at `i`, nested comments read; `none`
when it never closes. -/
private def leanBlockEnd (src : Array Char) (i : Nat) : Option Nat := Id.run do
  let mut j := i
  let mut depth := 1
  for _ in [0:src.size] do
    if j ≥ src.size then return none
    if at? src j '/' && at? src (j + 1) '-' then
      depth := depth + 1
      j := j + 2
    else if at? src j '-' && at? src (j + 1) '/' then
      depth := depth - 1
      j := j + 2
      if depth == 0 then return some j
    else j := j + 1
  return none

/-- Past a Lean character literal opened at `i`, when one opens there. -/
private def leanCharEnd? (src : Array Char) (i : Nat) : Option Nat := Id.run do
  match src[i + 1]? with
  | some '\\' =>
    for k in [i + 3:i + 13] do
      if at? src k '\n' then return none
      if at? src k '\'' then return some (k + 1)
    return none
  | some '\n' | none => return none
  | some _ => return if at? src (i + 2) '\'' then some (i + 3) else none

/-- Past a Lean raw string literal whose `r` is at `i`, when one opens there. -/
private def leanRawEnd? (src : Array Char) (i : Nat) : Option Nat := Id.run do
  let mut hashes := 0
  for k in [i + 1:src.size] do
    if at? src k '#' then hashes := hashes + 1 else break
  if !at? src (i + 1 + hashes) '"' then return none
  for j in [i + 2 + hashes:src.size] do
    if at? src j '"' && (List.range hashes).all fun h => at? src (j + 1 + h) '#' then
      return some (j + 1 + hashes)
  return some src.size


/-- Past a Lean string literal whose quote is at `i`; an interpolated one reads its `{…}` terms as
code. -/
private def leanStringEnd (src : Array Char) (i : Nat) (interpolated : Bool) : Nat := Id.run do
  let mut stack : List LeanMode := [.str interpolated]
  let mut j := i + 1
  for _ in [0:src.size + 1] do
    if j ≥ src.size then return src.size
    let c := src.getD j ' '
    match stack with
    | [] => return j
    | .str interp :: rest =>
      if c == '\\' then j := j + 2
      else if c == '"' then
        stack := rest
        j := j + 1
        if rest.isEmpty then return j
      else if interp && c == '{' then
        stack := .term 0 :: stack
        j := j + 1
      else j := j + 1
    | .term d :: rest =>
      if c == '"' then
        stack := .str (j > 0 && at? src (j - 1) '!') :: stack
        j := j + 1
      else if c == '{' then
        stack := .term (d + 1) :: rest
        j := j + 1
      else if c == '}' then
        stack := if d == 0 then rest else .term (d - 1) :: rest
        j := j + 1
      else if c == '-' && at? src (j + 1) '-' then j := lineEnd src j
      else if c == '/' && at? src (j + 1) '-' then j := (leanBlockEnd src (j + 2)).getD src.size
      else if c == '\'' && !(j > 0 && (src[j - 1]?.map leanIdRest).getD false) then
        j := (leanCharEnd? src j).getD (j + 1)
      else j := j + 1
  return src.size

/-- Whether a line declares nothing: the header's `module`, `prelude` or an import, or a command
that only opens a scope or sets what follows reads. -/
private def leanHeaderLine (line : String) : Bool :=
  let words := (line.splitOn " ").filter (!·.isEmpty)
  match words with
  | "module" :: _ | "prelude" :: _ => true
  | _ =>
    let lead := words.takeWhile (· ∈ ["public", "private", "meta", "noncomputable", "@[expose]"])
    ((words.drop lead.length).head?.map (["import", "section", "namespace", "open",
      "set_option", "universe", "variable"].contains ·)).getD false

/-- The modules a Lean file's header imports, in order; `none` for a `prelude` file, whose
statements elaborate without `Init`. -/
public def leanImports? (text : String) : Option (Array String) := Id.run do
  let src := text.toList.toArray
  let mut out : Array String := #[]
  let mut i := 0
  let mut expectModule := false
  for _ in [0:src.size + 1] do
    if i ≥ src.size then break
    let c := src.getD i ' '
    if isWhite c then i := i + 1
    else if c == '-' && at? src (i + 1) '-' then i := lineEnd src i
    else if c == '/' && at? src (i + 1) '-' && !at? src (i + 2) '!' && !at? src (i + 2) '-' then
      i := (leanBlockEnd src (i + 2)).getD src.size
    else
      let mut j := i
      for _ in [i:src.size] do
        if isWhite (src.getD j ' ') then break
        j := j + 1
      let word := String.ofList (src.extract i j).toList
      i := j
      if expectModule then
        if word != "all" then
          out := out.push word
          expectModule := false
      else if word == "prelude" then return none
      else if word == "import" then expectModule := true
      else if !["module", "public", "private", "meta"].contains word then break
  return some out

/-- Past the `»` closing a guillemet name opened at `i`, or past the `«` when none closes it. -/
private def guillemetEnd (src : Array Char) (i : Nat) : Nat := Id.run do
  for k in [i + 1:src.size] do
    if at? src k '»' then return k + 1
  return i + 1

/-- A Lean file's documentation comments: every module doc and docstring that opens a line, a
module doc after the file's header alone standing above it. -/
private def leanCuts (src : Array Char) (dir : Option Cut) : Array Cut := Id.run do
  let mut out : Array Cut := dir.toArray
  let mut i := 0
  let mut header := true
  for _ in [0:src.size + 1] do
    if i ≥ src.size then break
    let c := src.getD i ' '
    let identBefore := i > 0 && (src[i - 1]?.map leanIdRest).getD false
    let lineStart := i == 0 || at? src (i - 1) '\n'
    if lineStart && c == '/' && at? src (i + 1) '-' &&
        (at? src (i + 2) '!' || at? src (i + 2) '-') then
      match leanBlockEnd src (i + 3) with
      | some e =>
        let module := at? src (i + 2) '!'
        let stand := if module && header then Stand.aboveAll else .inPlace
        header := false
        out := out.push ⟨.prose module stand, i, e⟩
        i := e
      | none => i := src.size
    else if c == '-' && at? src (i + 1) '-' then i := lineEnd src i
    else if c == '/' && at? src (i + 1) '-' then i := (leanBlockEnd src (i + 2)).getD src.size
    else if header && !isWhite c then
      if lineStart && leanHeaderLine (String.ofList (src.extract i (lineEnd src i)).toList) then
        i := lineEnd src i
      else header := false
    else if c == '"' then i := leanStringEnd src i (i > 0 && at? src (i - 1) '!')
    else if c == 'r' && !identBefore && (leanRawEnd? src i).isSome then
      i := (leanRawEnd? src i).getD (i + 1)
    else if c == '\'' && !identBefore then i := (leanCharEnd? src i).getD (i + 1)
    else if c == '«' then i := guillemetEnd src i
    else i := i + 1
  return out

/-! ### Python -/


private def pyPrefix (s : List Char) : Option (Bool × Bool) :=
  let l := s.map Char.toLower
  if l.length > 2 || l.isEmpty || !l.all ("rbuft".toList.contains ·) || l.eraseDups.length != l.length
    then none
  else some (l.contains 'r', l.any ("bft".toList.contains ·))

private def pyIdStart (c : Char) : Bool := c.isAlpha || c == '_' || c.val ≥ 0x80
private def pyIdRest (c : Char) : Bool := c.isAlphanum || c == '_' || c.val ≥ 0x80


/-- Past a Python string literal whose first quote is at `q`; an f-string reads its replacement
fields as code. -/
private def pyStringEnd (src : Array Char) (q : Nat) (raw f : Bool) : Nat := Id.run do
  let quote := src.getD q '"'
  let triple := at? src (q + 1) quote && at? src (q + 2) quote
  let mut stack : List PyMode := [.str quote triple raw f]
  let mut j := if triple then q + 3 else q + 1
  for _ in [0:src.size + 1] do
    if j ≥ src.size then return src.size
    let c := src.getD j ' '
    match stack with
    | [] => return j
    | .str qc tr _ fs :: rest =>
      if c == '\\' then j := j + 2
      else if tr && c == qc && at? src (j + 1) qc && at? src (j + 2) qc then
        stack := rest
        j := j + 3
        if rest.isEmpty then return j
      else if !tr && c == qc then
        stack := rest
        j := j + 1
        if rest.isEmpty then return j
      else if !tr && c == '\n' then
        stack := rest
        if rest.isEmpty then return j
      else if fs && c == '{' then
        if at? src (j + 1) '{' then j := j + 2
        else
          stack := .expr 0 :: stack
          j := j + 1
      else j := j + 1
    | .expr d :: rest =>
      if c == '\'' || c == '"' then
        let mut k := j
        for _ in [0:3] do
          if k > 0 && (src[k - 1]?.map pyIdRest).getD false then k := k - 1 else break
        let pre := pyPrefix (src.extract k j).toList
        let (r, fl) := pre.getD (false, false)
        let tr := at? src (j + 1) c && at? src (j + 2) c
        stack := .str c tr r (fl && (src.extract k j).toList.any (· ∈ ['f', 'F', 't', 'T'])) :: stack
        j := if tr then j + 3 else j + 1
      else if c == '(' || c == '[' || c == '{' then
        stack := .expr (d + 1) :: rest
        j := j + 1
      else if c == ')' || c == ']' || c == '}' then
        stack := if d == 0 then (if c == '}' then rest else stack) else .expr (d - 1) :: rest
        j := j + 1
      else if c == ':' && d == 0 then
        stack := .spec :: stack
        j := j + 1
      else j := j + 1
    | .spec :: rest =>
      if c == '{' then
        stack := .expr 0 :: stack
        j := j + 1
      else if c == '}' then
        stack := rest.drop 1
        j := j + 1
      else j := j + 1
  return src.size

/-- The column a physical line's first token stands at, tabs to the next multiple of eight. -/
private def pyColumn (src : Array Char) (lineStart tok : Nat) : Nat := Id.run do
  let mut col := 0
  for i in [lineStart:tok] do
    if at? src i '\t' then col := col + 8 - col % 8 else col := col + 1
  return col

/-- A Python file's logical lines, comments and blank lines dropped. -/
private def pyLines (src : Array Char) : Array PyLine := Id.run do
  let mut out : Array PyLine := #[]
  let mut cur : Array PyTok := #[]
  let mut start := 0
  let mut indent := 0
  let mut physical := 0
  let mut depth := 0
  let mut i := 0
  for _ in [0:src.size + 1] do
    if i ≥ src.size then break
    let c := src.getD i ' '
    let begin (cur : Array PyTok) : Bool := cur.isEmpty
    if c == '#' then i := lineEnd src i
    else if c == '\\' && (at? src (i + 1) '\n' || (at? src (i + 1) '\r' && at? src (i + 2) '\n')) then
      i := if at? src (i + 1) '\n' then i + 2 else i + 3
    else if c == '\n' then
      if depth == 0 && !cur.isEmpty then
        out := out.push ⟨start, indent, cur⟩
        cur := #[]
      i := i + 1
      physical := i
    else if isWhite c then i := i + 1
    else
      if begin cur then
        start := physical
        indent := pyColumn src physical i
      if pyIdStart c then
        let mut e := i
        for k in [i:src.size] do
          if (src[k]?.map pyIdRest).getD false then e := k + 1 else break
        match pyPrefix (src.extract i e).toList, src[e]? with
        | some (raw, special), some q =>
          if q == '\'' || q == '"' then
            let f := (src.extract i e).toList.any (· ∈ ['f', 'F', 't', 'T'])
            let stop := pyStringEnd src e raw f
            cur := cur.push (.str i stop !special)
            i := stop
          else
            cur := cur.push (.name i e)
            i := e
        | _, _ =>
          cur := cur.push (.name i e)
          i := e
      else if c == '\'' || c == '"' then
        let stop := pyStringEnd src i false false
        cur := cur.push (.str i stop true)
        i := stop
      else
        if c == '(' || c == '[' || c == '{' then depth := depth + 1
        else if c == ')' || c == ']' || c == '}' then depth := depth - 1
        cur := cur.push (if c.isDigit then .other else .op c)
        i := i + 1
  if !cur.isEmpty then out := out.push ⟨start, indent, cur⟩
  return out

private def pyNameIs (src : Array Char) (t : PyTok) (w : String) : Bool :=
  match t with
  | .name a b => (src.extract a b).toList == w.toList
  | .str _ _ _ | .op _ | .other => false

/-- Whether a logical line opens a `def` or `class` block whose body starts on a later line. -/
private def pyHeader (src : Array Char) (l : PyLine) : Bool :=
  let opens := match l.toks[0]?, l.toks[1]? with
    | some t, some u => pyNameIs src t "def" || pyNameIs src t "class" ||
        (pyNameIs src t "async" && pyNameIs src u "def")
    | some t, none => pyNameIs src t "def" || pyNameIs src t "class"
    | none, _ => false
  opens && match l.toks.back? with
    | some (.op ':') => true
    | _ => false

/-- Whether a logical line is a decorator. -/
private def pyDecorator (l : PyLine) : Bool :=
  match l.toks[0]? with
  | some (PyTok.op '@') => true
  | _ => false

/-- The docstring a logical line is, when it is one string literal and nothing else. -/
private def pyDocstring? (l : PyLine) : Option (Nat × Nat) :=
  match l.toks with
  | #[.str a b true] => some (a, b)
  | _ => none

/-- A Python file's docstrings: the module's above all the code before it, each `def` and
`class` docstring above its declaration's header. -/
private def pyCuts (src : Array Char) (dir : Option Cut) : Array Cut := Id.run do
  let lines := pyLines src
  let mut out : Array Cut := dir.toArray
  if let some (a, b) := lines[0]?.bind pyDocstring? then
    out := out.push ⟨.prose true .aboveAll, a, b⟩
  for k in [0:lines.size] do
    let some l := lines[k]? | break
    if !pyHeader src l then continue
    let some body := lines[k + 1]? | continue
    if body.indent ≤ l.indent then continue
    let some (a, b) := pyDocstring? body | continue
    let mut first := k
    for _ in [0:k] do
      match lines[first - 1]? with
      | some d =>
        if first > 0 && d.indent == l.indent && pyDecorator d then first := first - 1
        else break
      | none => break
    let headerStart := (lines[first]?.map (·.lineStart)).getD l.lineStart
    out := (out.push ⟨.code, headerStart, a⟩).push ⟨.prose false .aboveRun, a, b⟩
  return out

/-! ### Bash -/

/-- Whether a line's first character other than a space or tab is `#`, and where it stands. -/
private def commentLine? (src : Array Char) (i : Nat) : Option Nat := Id.run do
  for k in [i:src.size] do
    match src[k]? with
    | some ' ' | some '\t' => continue
    | some '#' => return if at? src (k + 1) '!' then none else some k
    | _ => return none
  return none

/-- A shell script's leading comment block, after its `#!` line and the directive, above the
code before it. -/
private def bashCuts (src : Array Char) (dir : Option Cut) : Array Cut := Id.run do
  let mut out : Array Cut := dir.toArray
  let mut i := if at? src 0 '#' && at? src 1 '!' then lineEnd src 0 + 1 else 0
  if let some d := dir then i := max i (lineEnd src d.stop + 1)
  for _ in [0:src.size] do
    if i ≥ src.size then break
    let e := lineEnd src i
    if (List.range (e - i)).all fun k => (src[i + k]?.map isWhite).getD true then i := e + 1 else break
  let some start := commentLine? src i | return out
  let mut stop := lineEnd src i
  let mut j := stop + 1
  for _ in [0:src.size] do
    if j ≥ src.size then break
    match commentLine? src j with
    | some _ =>
      stop := lineEnd src j
      j := stop + 1
    | none => break
  return out.push ⟨.prose true .aboveAll, start, stop⟩

/-- The cuts a language's scanner makes in a source. -/
public def cutsOf (lang : Ir.CodeLang) (src : Array Char) : Array Cut :=
  let dir := (directive? lang src).map (·.1)
  match lang with
  | .lean => leanCuts src dir
  | .python => pyCuts src dir
  | .bash => bashCuts src dir

/-- A source cut into segments: the scanner's cuts, the gaps between them as code, every code run's
white space apart. -/
public def segmentsOf (lang : Ir.CodeLang) (text : String) : List Seg :=
  let src := text.toList.toArray
  let runs := normalize src (runsGo src.size #[] 0 (cutsOf lang src).toList).toList
  segmentsFrom 0 runs.toList text.toList

/-- Every character of the source stands in exactly one of its segments, in source order. -/
public theorem segmentsOf_source_exact (lang : Ir.CodeLang) (text : String) :
    ((segmentsOf lang text).map Seg.text).flatten = text.toList :=
  segmentsFrom_source_exact _ _ _

private theorem segmentsFrom_guarded (base : Nat) (rs : List Run) (cs : List Char) :
    ∀ s ∈ segmentsFrom base rs cs, ∃ k, s.kind = guard k s.text := by
  induction rs generalizing base cs with
  | nil =>
    cases cs with
    | nil => simp [segmentsFrom]
    | cons c cs => simp [segmentsFrom]; exact ⟨.code, rfl⟩
  | cons r rs ih =>
    intro s hs
    simp only [segmentsFrom, List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact ⟨r.kind, rfl⟩
    · exact ih _ _ s hs

private theorem guard_blank (k : Kind) (cs : List Char) (h : guard k cs = .blank) :
    cs.all isWhite := by
  cases k with
  | blank => simp only [guard] at h; split at h <;> simp_all
  | directive => simp only [guard] at h; split at h <;> simp_all
  | code => simp [guard] at h
  | prose m st => simp [guard] at h
  | statement i => simp only [guard] at h; split at h <;> simp_all

private theorem guard_directive (k : Kind) (cs : List Char) (h : guard k cs = .directive) :
    cs.all (· != '\n') := by
  cases k with
  | blank => simp only [guard] at h; split at h <;> simp_all
  | directive => simp only [guard] at h; split at h <;> simp_all
  | code => simp [guard] at h
  | prose m st => simp [guard] at h
  | statement i => simp only [guard] at h; split at h <;> simp_all

/-- A blank segment holds white space alone, so a page that ships none of it loses no code. -/
public theorem segmentsOf_blank_white (lang : Ir.CodeLang) (text : String) :
    ∀ s ∈ segmentsOf lang text, s.kind = .blank → s.text.all isWhite := by
  intro s hs hk
  obtain ⟨k, hg⟩ := segmentsFrom_guarded _ _ _ s hs
  exact guard_blank k s.text (hg ▸ hk)

/-- A directive segment is one line of the source. -/
public theorem segmentsOf_directive_line (lang : Ir.CodeLang) (text : String) :
    ∀ s ∈ segmentsOf lang text, s.kind = .directive → s.text.all (· != '\n') := by
  intro s hs hk
  obtain ⟨k, hg⟩ := segmentsFrom_guarded _ _ _ s hs
  exact guard_directive k s.text (hg ▸ hk)

/-! ## Prose -/


/-- Python's `inspect.cleandoc` over lines that carry their place: the first line's leading spaces
and, under `dedent`, the rest's common indentation removed, blank lines at either end dropped. -/
public def cleanLines (raw : Array (Nat × Nat × List Char)) (dedent : Bool := true) :
    Array (Nat × Nat × List Char) := Id.run do
  let expand (l : List Char) : List Char := Id.run do
    let mut out : Array Char := #[]
    for c in l do
      if c == '\t' then
        out := out ++ Array.replicate (8 - out.size % 8) ' '
      else out := out.push c
    return out.toList
  let lines := raw.map fun (ln, col, t) => (ln, col, expand t)
  let lead (t : List Char) : Nat := (t.takeWhile (· == ' ')).length
  let margin := (lines.extract 1 lines.size).foldl (fun m (_, _, t) =>
    if lead t < t.length then some ((m.map (min · (lead t))).getD (lead t)) else m) none
  let mut out : Array (Nat × Nat × List Char) := #[]
  for (ln, col, t) in lines, k in [0:lines.size] do
    if k == 0 then out := out.push (ln, col + lead t, t.drop (lead t))
    else
      let m := if dedent then margin.getD 0 else 0
      out := out.push (ln, col + min m t.length, t.drop m)
  while out.back?.any (·.2.2.isEmpty) do out := out.pop
  let first := (out.findIdx? (!·.2.2.isEmpty)).getD out.size
  return out.extract first out.size

/-- The prose of lines that carry their place. -/
private def proseOf (lines : Array (Nat × Nat × List Char)) (dedent : Bool := true) : Prose :=
  let clean := cleanLines lines dedent
  { text := String.intercalate "\n" (clean.toList.map fun (_, _, t) => String.ofList t)
    lines := clean.map fun (ln, col, _) => (ln, col) }

/-- Text split at its line ends, each line with its source line and the columns before it. -/
private def placed (text : List Char) (line col : Nat) : Array (Nat × Nat × List Char) :=
  ((text.splitOn '\n').toArray.zipIdx).map fun (t, k) => (line + k, if k == 0 then col else 0, t)

private def simpleEscape? : Char → Option Char
  | '\\' => some '\\'
  | '\'' => some '\''
  | '"' => some '"'
  | 'n' => some '\n'
  | 't' => some '\t'
  | 'r' => some '\r'
  | 'a' => some '\x07'
  | 'b' => some '\x08'
  | 'f' => some '\x0C'
  | 'v' => some '\x0B'
  | _ => none

/-- The value of the Python escape whose backslash is at `i`, and the index past it; `none` where
Python keeps the backslash. -/
private def pyEscape? (a : Array Char) (i : Nat) : Option (List Char × Nat) :=
  a[i + 1]?.bind fun d =>
    if d == '\n' then some ([], i + 2)
    else if let some e := simpleEscape? d then some ([e], i + 2)
    else if d == 'x' || d == 'u' || d == 'U' then
      let n := if d == 'x' then 2 else if d == 'u' then 4 else 8
      let ds := (a.extract (i + 2) (i + 2 + n)).toList
      let v := Hex.value? ds
      v.bind fun v => if ds.length == n && v < 0x110000 then some ([Char.ofNat v], i + 2 + n) else none
    else if '0' ≤ d && d ≤ '7' then
      let ds := ((a.extract (i + 1) (i + 4)).toList.takeWhile fun c => '0' ≤ c && c ≤ '7')
      some ([Char.ofNat (ds.foldl (fun m c => m * 8 + (c.toNat - '0'.toNat)) 0)], i + 1 + ds.length)
    else none

/-- A Python string literal's value, its escapes read as Python reads a `str`'s. -/
public def pyUnescape (cs : List Char) : List Char := Id.run do
  let a := cs.toArray
  let mut out : Array Char := #[]
  let mut i := 0
  for _ in [0:a.size + 1] do
    if i ≥ a.size then break
    let c := a.getD i ' '
    match (if c == '\\' then pyEscape? a i else none) with
    | some (e, next) =>
      out := out ++ e.toArray
      i := next
    | none =>
      out := out.push c
      i := i + 1
  return out.toList

/-- A docstring's prose with each doctest, its `>>>` line through the next blank line, indented
apart as a code block. -/
private def doctests (pr : Prose) : Prose := Id.run do
  let ls := (pr.text.splitOn "\n").toArray
  let mut text : Array String := #[]
  let mut places : Array (Nat × Nat) := #[]
  let mut inTest := false
  for l in ls, k in [0:ls.size] do
    let place := pr.lines.getD k (0, 0)
    if l.trimAscii.isEmpty then inTest := false
    else if !inTest && l.startsWith ">>>" then
      inTest := true
      if k > 0 && !(ls.getD (k - 1) "").trimAscii.isEmpty then
        text := text.push ""
        places := places.push place
    if inTest then
      text := text.push ("    " ++ l)
      places := places.push (place.1, place.2 - 4)
    else
      text := text.push l
      places := places.push place
  return { text := "\n".intercalate text.toList, lines := places }

/-- A documentation comment's prose, in a language's syntax, from where it stands. -/
public def proseIn (lang : Ir.CodeLang) (text : List Char) (line col : Nat) : Prose :=
  match lang with
  | .lean =>
    let inner := (((text.drop 3).reverse.drop 2).dropWhile fun c => c == ' ' || c == '\t').reverse
    proseOf (placed inner line (col + 3))
  | .python =>
    let pre := (text.takeWhile fun c => c != '"' && c != '\'').length
    let rest := text.drop pre
    let q := rest.headD '"'
    let quotes := if rest.take 3 == [q, q, q] then 3 else 1
    let body := rest.drop quotes
    let closed := body.length ≥ quotes && (body.reverse.take quotes).all (· == q)
    let inner := if closed then (body.reverse.drop quotes).reverse else body
    let raw := (text.take pre).any (· ∈ ['r', 'R'])
    doctests (proseOf (placed (if raw then inner else pyUnescape inner) line (col + pre + quotes)))
  | .bash =>
    let lines := (placed text line col).map fun (ln, c, t) =>
      let lead := (t.takeWhile fun ch => ch == ' ' || ch == '\t').length
      let rest := (t.drop lead).drop 1
      let sp := if rest.head? == some ' ' then 1 else 0
      (ln, c + lead + 1 + sp, rest.drop sp)
    proseOf lines (dedent := false)

/-- A position in a prose's markdown at the place it stands in the source. -/
public def Prose.place (pr : Prose) (p : Pos) : Pos :=
  match pr.lines[p.line - 1]? with
  | some (ln, col) => if p.line == 0 then p else { p with line := ln, col := col + p.col }
  | none => p

mutual

/-- A raw with every position moved by `f`. -/
public def mapPos (f : Pos → Pos) : Raw → Raw
  | .word s p => .word s (f p)
  | .space => .space
  | .par p => .par (f p)
  | .ctrl n p => .ctrl n (f p)
  | .sym c p => .sym c (f p)
  | .group body p => .group (mapPosList f #[] body.toList) (f p)
  | .math d body p => .math d (mapPosList f #[] body.toList) (f p)
  | .env n body p => .env n (mapPosList f #[] body.toList) (f p)
  | .verb e s p => .verb e s (f p)

public def mapPosList (f : Pos → Pos) (acc : Array Raw) : List Raw → Array Raw
  | [] => acc
  | r :: rest => mapPosList f (acc.push (mapPos f r)) rest

end

/-! ## The document -/

/-- The option head of a code language's listings, its language crossing as the IR's own value. -/
public def listingHead (lang : Ir.CodeLang) : String :=
  match Ir.listingLang? lang.listing with
  | some l => "[language=" ++ l.val ++ "]"
  | none => ""

/-- A listing of code under its language's head. -/
public def listingRaw (lang : Ir.CodeLang) (code : String) (p : Pos) : Raw :=
  .verb "lstlisting" (listingHead lang ++ "\n" ++ code) p

/-- The inline raws of the heading a raw opens, given the raws after it. -/
@[expose] public def headingBody? (r : Raw) : List Raw → Option (Array Raw)
  | .word star _ :: .group body _ :: _ =>
    match r with
    | .ctrl n _ => if star == "*" && (Parse.headingControl? n).isSome then some body else none
    | .word .. | .space | .par _ | .sym .. | .group .. | .math .. | .env .. | .verb .. => none
  | _ => none

/-- The inline raws of the heading a prose's raws open on. -/
@[expose] public def openingHeading? : List Raw → Option (Array Raw)
  | [] => none
  | r :: rest => headingBody? r rest

/-- A prose's raws with the heading they open on raised to the document's title. -/
@[expose] public def retitle : List Raw → List Raw
  | [] => []
  | r :: rest =>
    match r, headingBody? r rest with
    | .ctrl _ p, some _ => .ctrl (Parse.headingControl .title) p :: rest
    | _, _ => r :: rest

/-- The text of a `\output` body that `Decl.splitEntries` reads back as exactly these entries. -/
public def outputSource? (entries : List String) : Option String :=
  let s := String.intercalate ", " entries
  if Decl.splitEntries s == entries then some s else none

/-- The directive's entries as the declarations that take them: `theme` as `\theme`, the rest as
one `\output`. -/
public def directiveRaws (value : String) (p : Pos) : Array Raw :=
  let entries := (Decl.splitEntries value).foldl (fun (acc : Array String × Bool) e =>
    match Decl.splitEntry e with
    | some (k, _) => if showKeys.contains k then (acc.1, true) else (acc.1.push e, false)
    | none => if acc.2 then acc else (acc.1.push e, false)) (#[], false) |>.1.toList
  let isTheme (e : String) : Bool := (Decl.splitEntry e).map (·.1) == some "theme"
  let themes := entries.filterMap fun e =>
    match Decl.splitEntry e with
    | some ("theme", v) => some v
    | _ => none
  let rest := entries.filter (!isTheme ·)
  let one (name v : String) : Array Raw := #[.ctrl name p, .group #[.word v p] p]
  let output := if rest.isEmpty then #[] else
    match outputSource? rest with
    | some s => one "output" s
    | none => (rest.map (one "output")).toArray.flatten
  (themes.map (one "theme")).toArray.flatten ++ output

/-- Where each line of a source starts. -/
public def lineStarts (src : Array Char) : Array Nat := Id.run do
  let mut out : Array Nat := #[0]
  for c in src, i in [0:src.size] do
    if c == '\n' then out := out.push (i + 1)
  return out

/-- A source offset's line and column, both from one. -/
public def lineCol (starts : Array Nat) (offset : Nat) : Nat × Nat := Id.run do
  let mut lo := 0
  let mut hi := starts.size
  for _ in [0:starts.size] do
    if lo + 1 ≥ hi then break
    let mid := (lo + hi) / 2
    if starts.getD mid 0 ≤ offset then lo := mid else hi := mid
  return (lo + 1, offset - starts.getD lo 0 + 1)

/-- The file's name without its directories. -/
public def baseName (file : String) : String :=
  ((file.splitOn "/").getLast?).getD file

/-- Whether a segment is the file's description: a module doc standing above the code before it. -/
@[expose] public def Seg.describesFile (s : Seg) : Bool :=
  match s.kind with
  | .prose true .aboveAll => true
  | .prose _ _ | .code | .directive | .blank | .statement _ => false


/-- A documentation comment through the markdown reader, at the place it stands; `opens` raises
the heading it opens on to the document's title. -/
@[expose] public def proseRaws (lang : Ir.CodeLang) (file : String) (starts : Array Nat)
    (seg : Seg) (opens : Bool) : Array Raw × Array Diag :=
  let place := lineCol starts seg.start
  let prose := proseIn lang seg.text place.1 (place.2 - 1)
  let read := Md.desugar file prose.text .docstring
  let raws := mapPosList prose.place #[] read.1.toList
  (if opens then (retitle raws.toList).toArray else raws,
    read.2.map fun d => { d with span := d.span.map fun sp => { sp with pos := prose.place sp.pos } })

/-! ## Statements -/

/-- A source offset from its line, from one, and its column, from zero. -/
public def offsetOf (starts : Array Nat) (place : Nat × Nat) : Nat :=
  starts.getD (place.1 - 1) 0 + place.2

/-- Whether one place stands at or before another. -/
private def atOrBefore (a b : Nat × Nat) : Bool := a.1 < b.1 || (a.1 == b.1 && a.2 ≤ b.2)

/-- Whether one declaration's range holds another's and is larger. -/
private def holds (outer inner : LeanFacts.Decl) : Bool :=
  atOrBefore outer.start inner.start && atOrBefore inner.stop outer.stop &&
    (outer.start != inner.start || outer.stop != inner.stop)

/-- One code segment cut at each of `cuts` (offsets, in order, inside it), a statement segment
standing at each cut. -/
@[expose] public def splitCode (start : Nat) (text : List Char) : List (Nat × Nat) → List Seg
  | [] => if text.isEmpty then [] else [⟨.code, start, text⟩]
  | (k, i) :: rest =>
    let n := k - start
    let before : List Seg := if (text.take n).isEmpty then [] else [⟨.code, start, text.take n⟩]
    before ++ ⟨.statement i, start + n, []⟩ :: splitCode (start + n) (text.drop n) rest

/-- Where a statement cuts a code segment: at the start of the line its declaration's code
begins on, never before the segment. -/
@[expose] public def cutAt (starts : Array Nat) (segStart off : Nat) : Nat :=
  let p := max off segStart
  max segStart (starts.getD ((lineCol starts p).1 - 1) 0)

/-- The segments after `acc` with a statement segment at each anchor, an offset and a paragraph's
index: a code segment cut at the start of the line the offset stands on, a statement due before
another segment standing before it. -/
@[expose] public def withStatementsGo (starts : Array Nat) (acc : Array Seg) :
    List (Nat × Nat) → List Seg → Array Seg
  | anchors, [] => acc ++ (anchors.map fun (off, i) => (⟨.statement i, off, []⟩ : Seg)).toArray
  | anchors, s :: rest =>
    match s.kind with
    | .code =>
      let here := anchors.takeWhile (·.1 < s.start + s.text.length)
      let cuts := here.map fun (off, i) => (cutAt starts s.start off, i)
      withStatementsGo starts (acc ++ (splitCode s.start s.text cuts).toArray)
        (anchors.drop here.length) rest
    | .prose _ _ | .directive | .blank | .statement _ =>
      let due := anchors.takeWhile (·.1 ≤ s.start)
      let stood := acc ++ (due.map fun (off, i) => (⟨.statement i, off, []⟩ : Seg)).toArray
      withStatementsGo starts (stood.push s) (anchors.drop due.length) rest

@[expose] public def withStatements (starts : Array Nat) (anchors : List (Nat × Nat))
    (segs : List Seg) : List Seg :=
  (withStatementsGo starts #[] anchors segs).toList

private theorem codeOf_append (a b : List Seg) : codeOf (a ++ b) = codeOf a ++ codeOf b := by
  simp [codeOf, List.filter_append, List.flatMap_append]

private theorem drop_of_take_nil {n : Nat} {l : List Char} (h : (l.take n).isEmpty = true) :
    l.drop n = l := by
  calc l.drop n = l.take n ++ l.drop n := by rw [List.isEmpty_iff.mp h]; rfl
    _ = l := List.take_append_drop _ _

private theorem splitCode_text (start : Nat) (text : List Char) (cuts : List (Nat × Nat)) :
    (splitCode start text cuts).flatMap Seg.text = text := by
  induction cuts generalizing start text with
  | nil =>
    unfold splitCode
    split
    · rename_i h; simp [List.isEmpty_iff.mp h]
    · simp
  | cons c rest ih =>
    obtain ⟨k, i⟩ := c
    simp only [splitCode, List.flatMap_append, List.flatMap_cons, ih]
    split
    · rename_i h; simpa using drop_of_take_nil h
    · simp

private theorem splitCode_code (start : Nat) (text : List Char) (cuts : List (Nat × Nat)) :
    codeOf (splitCode start text cuts) = text := by
  induction cuts generalizing start text with
  | nil =>
    unfold splitCode
    split
    · rename_i h; simp [codeOf, List.isEmpty_iff.mp h]
    · rw [codeOf_code _ [] rfl]; simp [codeOf]
  | cons c rest ih =>
    obtain ⟨k, i⟩ := c
    simp only [splitCode]
    rw [codeOf_append, codeOf_other _ _ (by simp [Seg.isCode]), ih]
    split
    · rename_i h; simpa [codeOf] using drop_of_take_nil h
    · rw [codeOf_code _ [] rfl]; simp [codeOf]

private theorem codeOf_statements (l : List (Nat × Nat)) :
    codeOf (l.map fun (off, i) => (⟨.statement i, off, []⟩ : Seg)) = [] := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    obtain ⟨off, i⟩ := a
    rw [List.map_cons, codeOf_other _ _ (by simp [Seg.isCode]), ih]

private theorem withStatementsGo_code (starts : Array Nat) (acc : Array Seg)
    (anchors : List (Nat × Nat)) (segs : List Seg) :
    codeOf (withStatementsGo starts acc anchors segs).toList = codeOf acc.toList ++ codeOf segs := by
  induction segs generalizing acc anchors with
  | nil =>
    simp only [withStatementsGo, Array.toList_append, codeOf_append, codeOf_statements]
    simp [codeOf]
  | cons s rest ih =>
    unfold withStatementsGo
    rcases hk : s.kind with _ | ⟨m, st⟩ | _ | _ | i
    · simp only [ih, Array.toList_append, codeOf_append, splitCode_code, codeOf_code s rest hk,
        List.append_assoc]
    all_goals
      simp only [ih, Array.toList_push, Array.toList_append, codeOf_append, codeOf_statements,
        codeOf_other s rest (by simp [Seg.isCode, hk])]
      simp [codeOf, Seg.isCode, hk]

/-- Statements stand between listings and hold no code: the code the segments hold, in source
order, is the code they held. -/
public theorem withStatements_code_exact (starts : Array Nat) (anchors : List (Nat × Nat))
    (segs : List Seg) : codeOf (withStatements starts anchors segs) = codeOf segs := by
  unfold withStatements
  rw [withStatementsGo_code]
  simp [codeOf]

/-- The page a file reads into, in order: its pieces, a statement at each anchor. -/
@[expose] public def pagePieces (lang : Ir.CodeLang) (text : String) (anchors : List (Nat × Nat)) :
    Array Piece :=
  assemble (withStatements (lineStarts text.toList.toArray) anchors (segmentsOf lang text))

/-- A page's code pieces hold exactly the file's code segments, in source order, whatever
statements stand between them; a page that shows code sets each as one listing of it
(`pieceRaws_code_exact`). -/
public theorem pagePieces_code_exact (lang : Ir.CodeLang) (text : String)
    (anchors : List (Nat × Nat)) :
    ((pagePieces lang text anchors).toList.filterMap Piece.code?).flatten =
      codeOf (segmentsOf lang text) := by
  rw [pagePieces, assemble_code_exact, withStatements_code_exact]

/-- A line free to break, and no space: zero glue. -/
public def breakRaws (pos : Pos) : Array Raw := #[.ctrl "hspace" pos, .group #[.word "0pt" pos] pos]

/-- One formula after a paragraph's raws, a word space before it where the one before asks for
it, else a bare break; and whether the next asks for one. -/
@[expose] public def displayStep (pos : Pos) (st : Array Raw × Bool)
    (formula : Array LeanNotation.Math × Bool) : Array Raw × Bool :=
  ((st.1.append (if st.2 then #[.space] else breakRaws pos)).push
    (.math false (LeanStatement.Math.listRaws pos #[] formula.1.toList) pos), formula.2)

/-- The paragraph a declaration's statement sets as, ragged right: its kind in bold, its name as
code, marked when Lean holds a theorem unproved, then its formulas, each after a word space where
the one before asks for it, else after a bare break. -/
public def displayRaws (d : LeanFacts.Decl) (formulas : Array (Array LeanNotation.Math × Bool))
    (pos : Pos) : Array Raw :=
  let close : Array Raw := if d.kind == .theorem && !d.proved then
      #[.word "," pos, .space, .word "unproved)." pos] else #[.word ")." pos]
  let head : Array Raw := #[.ctrl "textbf" pos, .group #[.word d.kind.label pos] pos,
    .space, .word "(" pos, .ctrl "texttt" pos, .group (Md.textRaws d.name pos) pos] ++ close
  #[.env "flushleft" (formulas.foldl (displayStep pos) (head, true)).1 pos]

/-- Why a declaration's statement is not set, when it is not. -/
private def unset? (d : LeanFacts.Decl) : Option String :=
  match d.type with
  | none => some "is too large to set"
  | some t => if t.elaborated then none else some "did not elaborate"

/-- Where a place in the source stands as a diagnostic's position. -/
private def posAt (place : Nat × Nat) : Pos := { line := place.1, col := place.2 + 1 }

/-- Where a declaration's statement stands on the page: its source's first line and column. -/
private def posOf (d : LeanFacts.Decl) : Pos := posAt d.start

/-- The code characters a file's segments hold from offset `lo` up to `hi`, a last line end
aside. -/
public def codeWithin (segs : List Seg) (lo hi : Nat) : List Char :=
  let code := (segs.filter Seg.isCode).flatMap fun s =>
    (s.text.zipIdx s.start).filterMap fun (c, k) => if lo ≤ k && k < hi then some c else none
  if code.getLast? == some '\n' then code.dropLast else code

/-- The offset the first code character from `lo` up to `hi` stands at. -/
public def firstCode? (segs : List Seg) (lo hi : Nat) : Option Nat :=
  (segs.find? fun s => s.isCode && lo < s.start + s.text.length && s.start < hi).map
    fun s => max lo s.start

/-- The listing a declaration's code sets as in its statement's place: the code its lines hold,
from the line its command opens on through its last, its documentation aside. -/
public def codeFor (starts : Array Nat) (src : Array Char) (segs : List Seg)
    (head stop : Nat × Nat) : Array Raw :=
  let lo := starts.getD (head.1 - 1) 0
  let hi := starts.getD stop.1 src.size
  match firstCode? segs lo hi with
  | some first =>
    let code := codeWithin segs lo hi
    if code.isEmpty then #[] else
      #[listingRaw .lean (String.ofList code) { line := (lineCol starts first).1 - 1 }]
  | none => #[]

/-- What a page sets for one declaration Lean answered for, when it is chosen: its statement where
Lean gave one, else, on a page that shows no code, its code in the statement's place. -/
public def declPara (facts : LeanFacts.Facts) (starts : Array Nat) (src : Array Char)
    (segs : List Seg) (code wanted : Bool) (d : LeanFacts.Decl) : Array Raw :=
  if !wanted then #[] else
    match d.type, unset? d with
    | some t, none => displayRaws d (LeanStatement.statementMath facts d t) (posOf d)
    | _, _ => if code then #[] else codeFor starts src segs d.head d.stop

/-- Where a statement stands before its declaration's code: the line the command that writes it
opens on, or the code after the documentation that line holds. -/
private def beforeAnchor (starts : Array Nat) (segs : List Seg) (head : Nat × Nat) : Option Nat :=
  let off := offsetOf starts head
  (segs.find? fun s => s.isCode && off < s.start + s.text.length).map fun s => max off s.start

/-- Where a statement stands after its declaration's code: the start of the line after it. -/
private def afterAnchor (src : Array Char) (starts : Array Nat) (stop : Nat × Nat) : Nat :=
  starts.getD stop.1 src.size

/-- What Lean's answer gives a page: each declaration's paragraph by index, then each failed one's,
the anchors of those set, and one note per statement asked for and not set, both in source order;
a page that shows no code sets a declaration's code where its statement cannot stand. -/
public def statementsOf (file : String) (starts : Array Nat) (src : Array Char) (segs : List Seg)
    (showing : Showing) (facts : LeanFacts.Facts) :
    Array (Array Raw) × List (Nat × Nat) × Array Diag :=
  let ds := facts.decls
  let names (n : String) (named : String) : Bool := n == named || n.endsWith ("." ++ named)
  let chosen (n : String) : Bool := match showing.decls with
    | none => true
    | some ns => ns.any (names n)
  let wanted (d : LeanFacts.Decl) : Bool :=
    (showing.decls.isSome || !ds.any (holds · d)) && chosen d.name
  let code := showing.code
  let paras := ds.map fun d => declPara facts starts src segs code (wanted d) d
  let failedParas := facts.failed.map fun f =>
    if chosen f.name && !code then codeFor starts src segs f.head f.stop else #[]
  let anchorOf (head stop : Nat × Nat) : Option Nat :=
    if showing.mathFirst then beforeAnchor starts segs head else some (afterAnchor src starts stop)
  let anchors := ds.zipIdx.filterMap fun (d, i) =>
    if wanted d && ((unset? d).isNone || !code) then (anchorOf d.head d.stop).map (·, i)
    else none
  let failedAnchors := facts.failed.zipIdx.filterMap fun (f, j) =>
    if chosen f.name && !code then (anchorOf f.head f.stop).map (·, ds.size + j) else none
  let instead := if code then "its code is set without it" else "its code is set in its place"
  let insteadOfNone := if code then "its code is set without a statement"
    else "its code is set in place of a statement"
  let unsetNotes := ds.filterMap fun d =>
    if wanted d then (unset? d).map fun why => (d.start,
      Diag.of .W0414 s!"the statement of '{d.name}' {why} in Lean; {instead}"
        (some ⟨file, posOf d⟩) (subject := some s!"lean:{d.name}"))
    else none
  let failedNotes := facts.failed.filterMap fun f =>
    if chosen f.name then some (f.start,
      Diag.of .W0414 s!"Lean added nothing for '{f.name}'; {insteadOfNone}"
        (some ⟨file, posAt f.start⟩) (subject := some s!"lean:{f.name}"))
    else none
  let unnamed := ((showing.decls.getD []).filter fun n =>
    !ds.any (names ·.name n) && !facts.failed.any (names ·.name n)).toArray.map fun n => ((1, 0),
      Diag.of .W0414 s!"`decls` names '{n}', which Lean's answer does not hold; nothing is set \
for it" (some ⟨file, {}⟩) (subject := some s!"lean:{n}"))
  let notes := (unsetNotes ++ failedNotes ++ unnamed).qsort fun a b =>
    a.1.1 < b.1.1 || (a.1.1 == b.1.1 && a.1.2 < b.1.2)
  let all := anchors ++ failedAnchors
  (paras ++ failedParas, (all.qsort (·.1 < ·.1)).toList, notes.map (·.2))

/-- What a page sets from Lean's answer, when it has one. -/
@[expose] public def statementsFor (file : String) (starts : Array Nat) (src : Array Char)
    (segs : List Seg) (showing : Showing) :
    Option LeanFacts.Facts → Array (Array Raw) × List (Nat × Nat) × Array Diag
  | some f => statementsOf file starts src segs showing f
  | none => (#[], [], #[])

/-- What one piece adds to the body: a listing for code and the markdown reader's raws for prose,
where the page shows them, and its paragraph for a statement. -/
@[expose] public def pieceRaws (lang : Ir.CodeLang) (file : String) (starts : Array Nat)
    (page : PageSet) (opens : Bool) : Piece → Array Raw
  | .code start code => if page.code then
      #[listingRaw lang (String.ofList code) { line := (lineCol starts start).1 - 1 }] else #[]
  | .prose seg => if page.code then (proseRaws lang file starts seg opens).1 else #[]
  | .statement i => page.stmts.getD i #[]

/-- The raws a piece's title is read from: its prose's, whether or not the page shows it. -/
@[expose] public def titleSource (lang : Ir.CodeLang) (file : String) (starts : Array Nat)
    (opens : Bool) : Piece → Array Raw
  | .prose seg => (proseRaws lang file starts seg opens).1
  | .code _ _ | .statement _ => #[]

/-- Whether a piece is the file's description the title is read from, given what came before. -/
@[expose] public def Acc.opens (acc : Acc) : Piece → Bool
  | .code _ _ | .statement _ => false
  | .prose seg => !acc.sawModule && seg.describesFile

/-- One piece read into the body, the file's description opening on the document's title. -/
@[expose] public def pieceStep (lang : Ir.CodeLang) (file : String) (starts : Array Nat)
    (page : PageSet) (acc : Acc) (piece : Piece) : Acc :=
  let opens := acc.opens piece
  let read := match piece with
    | .prose seg => proseRaws lang file starts seg opens
    | .code _ _ | .statement _ => (#[], #[])
  let raws := match piece with
    | .prose _ => if page.code then read.1 else #[]
    | .code _ _ | .statement _ => pieceRaws lang file starts page opens piece
  let heading := if opens then openingHeading? read.1.toList else none
  { body := acc.body ++ raws, diags := acc.diags ++ (if page.code then read.2 else #[])
    title := if opens then heading else acc.title
    titled := acc.titled || (page.code && heading.isSome)
    sawModule := acc.sawModule || opens }

/-- One piece adds its raws to the body, and the title its prose opens on when it opens the
document. -/
public theorem pieceStep_exact (lang : Ir.CodeLang) (file : String) (starts : Array Nat)
    (page : PageSet) (acc : Acc) (p : Piece) :
    (pieceStep lang file starts page acc p).body =
        acc.body ++ pieceRaws lang file starts page (acc.opens p) p ∧
      (pieceStep lang file starts page acc p).title = (if acc.opens p then
        openingHeading? (titleSource lang file starts (acc.opens p) p).toList else acc.title) := by
  cases p <;> exact ⟨rfl, by simp only [pieceStep, titleSource]; split <;> rfl⟩

/-- A code file's pieces read in page order, statements standing at their anchors. -/
@[expose] public def readPieces (lang : Ir.CodeLang) (file text : String)
    (page : PageSet) (anchors : List (Nat × Nat)) : Acc :=
  (pagePieces lang text anchors).toList.foldl
    (pieceStep lang file (lineStarts text.toList.toArray) page) {}

/-- A code piece adds its listing, holding its code exactly, wherever the page shows code. -/
public theorem pieceRaws_code_exact (lang : Ir.CodeLang) (file : String) (starts : Array Nat)
    (page : PageSet) (h : page.code = true) (opens : Bool) (start : Nat) (code : List Char) :
    pieceRaws lang file starts page opens (.code start code) =
      #[listingRaw lang (String.ofList code) { line := (lineCol starts start).1 - 1 }] := by
  simp [pieceRaws, h]

private theorem foldl_body (lang : Ir.CodeLang) (file : String) (starts : Array Nat)
    (page : PageSet) :
    ∀ (ps : List Piece) (acc : Acc), ∃ opens : List Bool, opens.length = ps.length ∧
      (ps.foldl (pieceStep lang file starts page) acc).body.toList =
        acc.body.toList ++
          (ps.zip opens).flatMap fun (p, o) => (pieceRaws lang file starts page o p).toList
  | [], acc => ⟨[], rfl, by simp⟩
  | p :: rest, acc => by
    obtain ⟨opens, hlen, hbody⟩ :=
      foldl_body lang file starts page rest (pieceStep lang file starts page acc p)
    refine ⟨acc.opens p :: opens, by simp [hlen], ?_⟩
    rw [List.foldl_cons, hbody]
    simp [(pieceStep_exact lang file starts page acc p).1, List.append_assoc]

/-- The body is the page's pieces' raws in page order, each piece adding `pieceRaws` under a
flag saying whether it opens the document. -/
public theorem readPieces_body_exact (lang : Ir.CodeLang) (file text : String)
    (page : PageSet) (anchors : List (Nat × Nat)) :
    ∃ opens : List Bool, opens.length = (pagePieces lang text anchors).size ∧
      (readPieces lang file text page anchors).body.toList =
        ((pagePieces lang text anchors).toList.zip opens).flatMap fun (p, o) =>
          (pieceRaws lang file (lineStarts text.toList.toArray) page o p).toList := by
  obtain ⟨opens, hlen, hbody⟩ := foldl_body lang file (lineStarts text.toList.toArray) page
    (pagePieces lang text anchors).toList {}
  exact ⟨opens, by simpa using hlen, by simpa [readPieces] using hbody⟩

/-- What a page sets from a file and Lean's answer: what it shows, where each paragraph Lean's
answer gives stands, and the notes; a page asked for mathematics Lean gave no answer for shows the
file's code. -/
@[expose] public def planOf (lang : Ir.CodeLang) (file text : String)
    (facts : Option LeanFacts.Facts) : PageSet × List (Nat × Nat) × Array Diag :=
  let src := text.toList.toArray
  let showing := showingOf lang src
  let answer := if showing.math then facts else none
  let st := statementsFor file (lineStarts src) src (segmentsOf lang text) showing answer
  ({ stmts := st.1, code := showing.code || answer.isNone }, st.2.1, st.2.2)

/-- With no answer from Lean, a page shows the file's code, whatever its directive asks. -/
public theorem planOf_unanswered_exact (lang : Ir.CodeLang) (file text : String) :
    (planOf lang file text none).1.code = true := by
  simp [planOf]

/-- A code file read into the surface AST: documentation comments as markdown, code as listings,
each statement beside its declaration's code as the views order them, the title and directive as
the preamble's declarations, the file's name the title where no description opens on one. -/
@[expose] public def read (lang : Ir.CodeLang) (file text : String)
    (facts : Option LeanFacts.Facts := none) : Array Raw × Array Diag :=
  let src := text.toList.toArray
  let starts := lineStarts src
  let showing := showingOf lang src
  let plan := planOf lang file text facts
  let acc := readPieces lang file text plan.1 plan.2.1
  let origin : Pos := {}
  let directive := match directive? lang src with
    | some (cut, value) =>
      let (line, col) := lineCol starts cut.start
      directiveRaws value { line, col }
    | none => #[]
  let titleRaws := acc.title.getD (Md.textRaws (baseName file) origin)
  let body := if acc.titled then acc.body
    else Parse.headingRaws .title titleRaws origin ++ acc.body
  let preamble : Array Raw := #[.ctrl "title" origin, .group titleRaws origin] ++ directive
  let stray := (strayDirective? lang src).map fun off =>
    let (line, col) := lineCol starts off
    Diag.of .W0387 "a leantex directive is read only on a file's first line, or the line after \
'#!'; this one stays as written" (some ⟨file, { line, col }⟩)
      (help := s!"move it to the file's first line, or the line after `#!`: `{directiveMarker lang} …`")
      (subject := some "code:directive")
  let dirPos : Pos := match directive? lang src with
    | some (cut, _) => let (line, col) := lineCol starts cut.start; { line, col }
    | none => origin
  let views := showing.unknown.toArray.map fun n =>
    Diag.of .W0110 s!"`show` names '{n}', which is no view of this file; the page sets without it"
      (some ⟨file, dirPos⟩) (help := "name `code`, or for a Lean file `math`")
      (subject := some s!"code:show:{n}")
  (preamble.push (.env "document" body origin), views ++ acc.diags ++ plan.2.2 ++ stray.toArray)

private theorem ite_prefix (b : Bool) (x y : Array Raw) :
    (if b = true then x else y ++ x) = (if b = true then #[] else y) ++ x := by
  cases b <;> simp

/-- A code file's raws close on its document, whose body ends with its pieces' raws under the
page its plan sets. -/
public theorem read_body_exact (lang : Ir.CodeLang) (file text : String)
    (facts : Option LeanFacts.Facts) :
    ∃ head : Array Raw, (read lang file text facts).1.back? =
      some (.env "document" (head ++ (readPieces lang file text (planOf lang file text facts).1
        (planOf lang file text facts).2.1).body) {}) := by
  unfold read
  simp only [Array.back?_push, ite_prefix]
  exact ⟨_, rfl⟩

end LeanTex.Core.Code
