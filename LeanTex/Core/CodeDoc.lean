module

public import LeanTex.Core.MdDesugar
public import LeanTex.Core.Parse
public import LeanTex.Core.Ir
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
  sawModule : Bool := false

/-- The kind a run's characters may carry: white space alone is blank, a directive is one line,
and anything else is code. -/
@[expose] public def guard (k : Kind) (cs : List Char) : Kind :=
  match k with
  | .blank => if cs.all isWhite then .blank else .code
  | .directive => if cs.all (· != '\n') then .directive else .code
  | .code => .code
  | .prose m st => .prose m st

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
  | .prose _ => none

public def Piece.prose? : Piece → Option Seg
  | .prose s => some s
  | .code _ _ => none

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
  | .prose _ _ | .directive | .blank => false

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
    rcases hk : s.kind with _ | ⟨m, st⟩ | _ | _
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

/-- The listings, in page order, hold exactly the code segments, in source order. -/
public theorem assemble_code_exact (segs : List Seg) :
    ((assemble segs).toList.filterMap Piece.code?).flatten = codeOf segs := by
  simp [assemble, assembleGo_code]

/-- Whether a segment is a documentation comment. -/
@[expose] public def Seg.isProse (s : Seg) : Bool :=
  match s.kind with
  | .prose _ _ => true
  | .code | .directive | .blank => false

private theorem assembleGo_prose (out : Array Piece) (pending segs : List Seg) :
    (assembleGo out pending segs).toList.filterMap Piece.prose? =
      out.toList.filterMap Piece.prose? ++ segs.filter Seg.isProse := by
  induction segs generalizing out pending with
  | nil => simp [assembleGo, flush_prose]
  | cons s rest ih =>
    unfold assembleGo
    rcases hk : s.kind with _ | ⟨m, st⟩ | _ | _
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

private theorem guard_directive (k : Kind) (cs : List Char) (h : guard k cs = .directive) :
    cs.all (· != '\n') := by
  cases k with
  | blank => simp only [guard] at h; split at h <;> simp_all
  | directive => simp only [guard] at h; split at h <;> simp_all
  | code => simp [guard] at h
  | prose m st => simp [guard] at h

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
  let entries := Decl.splitEntries value
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
  | .prose _ _ | .code | .directive | .blank => false


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

/-- What one piece adds to the body: a listing for code, the markdown reader's raws for prose. -/
@[expose] public def pieceRaws (lang : Ir.CodeLang) (file : String) (starts : Array Nat)
    (opens : Bool) : Piece → Array Raw
  | .code start code => #[listingRaw lang (String.ofList code) { line := (lineCol starts start).1 - 1 }]
  | .prose seg => (proseRaws lang file starts seg opens).1

/-- Whether a piece is the file's description the title is read from, given what came before. -/
@[expose] public def Acc.opens (acc : Acc) : Piece → Bool
  | .code _ _ => false
  | .prose seg => !acc.sawModule && seg.describesFile

/-- One piece read into the body, the file's description opening on the document's title. -/
@[expose] public def pieceStep (lang : Ir.CodeLang) (file : String) (starts : Array Nat)
    (acc : Acc) (piece : Piece) : Acc :=
  let opens := acc.opens piece
  let (raws, diags) := match piece with
    | .code _ _ => (pieceRaws lang file starts opens piece, #[])
    | .prose seg => proseRaws lang file starts seg opens
  { body := acc.body ++ raws, diags := acc.diags ++ diags
    title := if opens then openingHeading? raws.toList else acc.title
    sawModule := acc.sawModule || opens }

/-- One piece adds its raws to the body, and the title it opens on when it opens the document. -/
public theorem pieceStep_exact (lang : Ir.CodeLang) (file : String) (starts : Array Nat)
    (acc : Acc) (p : Piece) :
    (pieceStep lang file starts acc p).body = acc.body ++ pieceRaws lang file starts (acc.opens p) p ∧
      (pieceStep lang file starts acc p).title = (if acc.opens p then
        openingHeading? (pieceRaws lang file starts (acc.opens p) p).toList else acc.title) := by
  cases p <;> exact ⟨rfl, rfl⟩

/-- A code file's pieces read in page order. -/
@[expose] public def readPieces (lang : Ir.CodeLang) (file text : String) : Acc :=
  (assemble (segmentsOf lang text)).toList.foldl (pieceStep lang file (lineStarts text.toList.toArray)) {}

/-- A code piece adds its listing, holding its code exactly, whatever came before it. -/
public theorem pieceRaws_code_exact (lang : Ir.CodeLang) (file : String) (starts : Array Nat)
    (opens : Bool) (start : Nat) (code : List Char) :
    pieceRaws lang file starts opens (.code start code) =
      #[listingRaw lang (String.ofList code) { line := (lineCol starts start).1 - 1 }] := rfl

private theorem foldl_body (lang : Ir.CodeLang) (file : String) (starts : Array Nat) :
    ∀ (ps : List Piece) (acc : Acc), ∃ opens : List Bool, opens.length = ps.length ∧
      (ps.foldl (pieceStep lang file starts) acc).body.toList =
        acc.body.toList ++ (ps.zip opens).flatMap fun (p, o) => (pieceRaws lang file starts o p).toList
  | [], acc => ⟨[], rfl, by simp⟩
  | p :: rest, acc => by
    obtain ⟨opens, hlen, hbody⟩ := foldl_body lang file starts rest (pieceStep lang file starts acc p)
    refine ⟨acc.opens p :: opens, by simp [hlen], ?_⟩
    rw [List.foldl_cons, hbody]
    simp [(pieceStep_exact lang file starts acc p).1, List.append_assoc]

/-- The body is the pieces' raws in page order, each piece adding `pieceRaws` under a flag
saying whether it opens the document. -/
public theorem readPieces_body_exact (lang : Ir.CodeLang) (file text : String) :
    ∃ opens : List Bool, opens.length = (assemble (segmentsOf lang text)).size ∧
      (readPieces lang file text).body.toList =
        ((assemble (segmentsOf lang text)).toList.zip opens).flatMap fun (p, o) =>
          (pieceRaws lang file (lineStarts text.toList.toArray) o p).toList := by
  obtain ⟨opens, hlen, hbody⟩ :=
    foldl_body lang file (lineStarts text.toList.toArray) (assemble (segmentsOf lang text)).toList {}
  exact ⟨opens, by simpa using hlen, by simpa [readPieces] using hbody⟩

/-- A code file read into the surface AST: its documentation comments through the markdown reader,
its code as listings, its title and directive as the preamble's declarations, the file's name the
title heading where no description opens on a heading. -/
@[expose] public def read (lang : Ir.CodeLang) (file text : String) : Array Raw × Array Diag :=
  let src := text.toList.toArray
  let starts := lineStarts src
  let acc := readPieces lang file text
  let origin : Pos := {}
  let directive := match directive? lang src with
    | some (cut, value) =>
      let (line, col) := lineCol starts cut.start
      directiveRaws value { line, col }
    | none => #[]
  let titleRaws := acc.title.getD (Md.textRaws (baseName file) origin)
  let body := if acc.title.isSome then acc.body
    else Parse.headingRaws .title titleRaws origin ++ acc.body
  let preamble : Array Raw := #[.ctrl "title" origin, .group titleRaws origin] ++ directive
  let stray := (strayDirective? lang src).map fun off =>
    let (line, col) := lineCol starts off
    Diag.of .W0387 "a leantex directive is read only on a file's first line, or the line after \
'#!'; this one stays as written" (some ⟨file, { line, col }⟩)
      (help := s!"move it to the file's first line, or the line after `#!`: `{directiveMarker lang} …`")
      (subject := some "code:directive")
  (preamble.push (.env "document" body origin), acc.diags ++ stray.toArray)

/-- A code file's raws close on its document, whose body ends with its pieces' raws. -/
public theorem read_body_exact (lang : Ir.CodeLang) (file text : String) :
    ∃ head : Array Raw, (read lang file text).1.back? =
      some (.env "document" (head ++ (readPieces lang file text).body) {}) := by
  unfold read
  simp only [Array.back?_push]
  split
  · exact ⟨#[], by simp⟩
  · exact ⟨_, rfl⟩

end LeanTex.Core.Code
