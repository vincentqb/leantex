module

public import LeanTex.Core.MdDesugar
public import LeanTex.Core.Parse
public import LeanTex.Core.Ir
public import LeanTex.Core.LeanStatement
public import LeanTex.Core.LeanProse
public import LeanTex.Core.CodeLink
import LeanTex.Core.Decl
import LeanTex.Core.Hex
public import LeanTex.Core.UnusedSetting

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
  /-- Where a paragraph the file's facts give stands beside the code it is of, by its index; it
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
  /-- A paragraph the file's facts give, by its index: a statement, or code in a statement's
  place. -/
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
  /-- Whether the body's documentation cites a work. -/
  cited : Bool := false
  /-- Where the body's documentation heads its own references, so the list stands there. -/
  refsAt : Option Nat := none

/-- A reading of a Lean file's declarations its page sets. -/
public inductive View where
  | code
  | math
  | prose
  /-- An inclusion's documentation as prose, where it stands between its code's listings. -/
  | docs
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A view's name in a `show` value. -/
public def View.name : View → String
  | .code => "code"
  | .math => "math"
  | .prose => "prose"
  | .docs => "docs"

public def View.all : List View := [.code, .math, .prose, .docs]

/-- Whether a page of a file of `lang` sets the view; the documentation view only an inclusion's,
whose options nothing else reads. -/
public def View.setBy (v : View) (lang : Ir.CodeLang) (alone : Bool) : Bool :=
  match v with
  | .code => true
  | .math | .prose => lang == .lean
  | .docs => lang == .lean && alone

/-- What a page does with a theorem's proof: shows it, folds it into a disclosure, or sets Lean's
`⋯` in its place. -/
public inductive Proofs where
  | show
  | collapse
  | remove
  deriving Repr, BEq, DecidableEq, Inhabited

/-- What a page is asked to show: its views in order, the declarations it selects, what it does
with proofs, the link a declaration's name reaches, each value it cannot read, and the phrases it
declares by name and template. -/
public structure Showing where
  views : List View := [.code]
  decls : Option (List String) := none
  unknown : List String := []
  proofs : Proofs := .show
  link : Option String := none
  /-- The facts file the document declares for the file, else the exporter's own. -/
  facts : Option String := none
  /-- The bibliography files the document declares for the file's documentation, else its
  project's `docs/references.bib`. -/
  bibliography : List String := []
  /-- The style the page's citations set in, alpha where none is declared. -/
  bibStyle : Option String := none
  /-- Each option value the page cannot read, as its key and value. -/
  unread : List (String × String) := []
  /-- Each key no option of the page's names, where nothing else reads the entries. -/
  strange : List String := []
  /-- The keys written. -/
  written : List String := []
  phrases : List (String × String) := []
  deriving Repr, BEq, Inhabited

/-- A proof a page folds or removes: its source offsets, and the paragraph standing for it where
it folds. -/
public structure ProofFold where
  start : Nat
  stop : Nat
  /-- The paragraph standing for it: its disclosure where it folds; where it is removed, an empty
  one that ends its listing at `cut`, where the removal spans lines. -/
  index : Nat
  remove : Bool
  cut : Option Nat
  deriving Repr, BEq, Inhabited

/-- What a page sets from a file's pieces: each paragraph by index, whether it shows the file's
code and documentation, and the proofs it folds or removes. -/
public structure PageSet where
  stmts : Array (Array Raw) := #[]
  code : Bool := true
  folds : List ProofFold := []
  /-- The keys of the bibliography the page's documentation cites into, where it has one. -/
  cites : Option (Std.HashSet String) := none

/-- A page citing into the bibliography whose keys `keys` are. -/
@[expose] public def PageSet.citing (page : PageSet) (keys : Option (Std.HashSet String)) : PageSet :=
  { page with cites := keys }

public theorem PageSet.citing_stmts (page : PageSet) (keys : Option (Std.HashSet String)) :
    (page.citing keys).stmts = page.stmts := rfl

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

/-- How an option key's value reads. -/
public inductive KeyRead where
  /-- A comma list, each of TeX's entries losing one layer of braces or quotes. -/
  | list
  /-- One value, TeX's continuation entries joined by `sep` before it loses one layer. -/
  | joined (sep : String)
  deriving Repr, BEq

/-- A key a directive or an inclusion takes for what its page shows: its name, how its value
reads, and whether an inclusion honours it. -/
public structure ShowKey where
  name : String
  read : KeyRead
  included : Bool

public def showKeyRows : List ShowKey :=
  [⟨"show", .list, true⟩, ⟨"decls", .list, true⟩, ⟨"proofs", .joined ", ", true⟩,
   ⟨"link", .joined ",", true⟩, ⟨"facts", .joined ",", true⟩, ⟨"bibliography", .list, true⟩,
   ⟨"biblio-style", .joined ",", false⟩]

/-- The keys a directive takes for what its page shows, which no declaration reads. -/
public def showKeys : List String := showKeyRows.map (·.name)

/-- The keys an inclusion honours. -/
public def inclusionKeys : List String := (showKeyRows.filter (·.included)).map (·.name)

/-- The prefix of the directive keys that declare a constant's phrase. -/
public def phraseKey : String := "phrase."

/-- How a key's value reads: a phrase's as prose, a key no row names as one value. -/
public def keyRead (k : String) : KeyRead :=
  match showKeyRows.find? (·.name == k) with
  | some r => r.read
  | none => if k.startsWith phraseKey then .joined ", " else .joined ","

/-- Whether a directive key says what its page shows, which no declaration reads. -/
public def showKey (k : String) : Bool := showKeys.contains k || k.startsWith phraseKey

/-- Whether a page shows the mathematics view. -/
public def Showing.math (s : Showing) : Bool := s.views.contains .math

public def Showing.code (s : Showing) : Bool := s.views.contains .code

public def Showing.prose (s : Showing) : Bool := s.views.contains .prose

/-- Whether an inclusion sets its documentation as prose, as the file's page does. -/
public def Showing.docs (s : Showing) : Bool := s.views.contains .docs

/-- Whether a page sets a declaration's statement, which its facts give. -/
public def Showing.statements (s : Showing) : Bool := s.math || s.prose

/-- The views that set a declaration's statement before its code, and those after it. -/
public def Showing.around (s : Showing) : List View × List View :=
  (s.views.takeWhile (· != .code), (s.views.dropWhile (· != .code)).filter (· != .code))

/-- A value with its surrounding quotes or braces taken off. -/
public def unwrapValue (v : String) : String :=
  let t := v.trimAscii.toString
  if t.length ≥ 2 && ((t.startsWith "\"" && t.endsWith "\"") || (t.startsWith "{" && t.endsWith "}"))
  then ((t.drop 1).dropEnd 1).trimAscii.toString else t

/-- The value each key of option entries takes as TeX and a directive spell them: bare entries
continue the key before them, read as the key reads them (`keyRead`). -/
public def entryValues (entries : List String) : List (String × String) :=
  (keyedEntries entries).map fun (k, vs) =>
    (k, if k.isEmpty then vs.headD "" else match keyRead k with
      | .list => ",".intercalate (vs.map unwrapValue)
      | .joined sep => unwrapValue (sep.intercalate vs))

/-- What option values by key ask a page of a file of `lang` to show: its `show` views, `code` where
it names none the language sets, its `decls`, `proofs`, `link` and phrases, a key written twice
taking its last value; `alone` where nothing else reads the options, so any other key is strange. -/
public def showingOfValues (lang : Ir.CodeLang) (values : List (String × String))
    (alone : Bool := false) : Showing :=
  let value (k : String) : Option String := (values.reverse.find? (·.1 == k)).map (·.2)
  let listField (k : String) : Option (List String) := (value k).map fun v => match keyRead k with
    | .list => (v.splitOn ",").map (·.trimAscii.toString) |>.filter (!·.isEmpty)
    | .joined _ => [v]
  let named := (listField "show").getD []
  let viewOf? (n : String) : Option View :=
    View.all.find? fun v => v.name == n && v.setBy lang alone
  let views := (named.filterMap viewOf?).eraseDups
  let decls := (listField "decls").filter (!·.isEmpty)
  let (proofs, unread) := match value "proofs" with
    | none | some "show" => (Proofs.show, [])
    | some "collapse" => (.collapse, [])
    | some "remove" => (.remove, [])
    | some v => (.show, [("proofs", v)])
  { views := if views.isEmpty then [.code] else views
    decls, proofs, unread
    link := value "link"
    facts := value "facts"
    bibliography := (listField "bibliography").getD []
    bibStyle := value "biblio-style"
    unknown := named.filter fun n => (viewOf? n).isNone
    strange := if alone then values.filterMap fun (k, v) =>
        if showKey k then none else some (if k.isEmpty then v else k)
      else []
    written := values.map (·.1)
    phrases := values.filterMap fun (k, v) =>
      if k.startsWith phraseKey then some ((k.drop phraseKey.length).toString, v) else none }

/-- What option entries, as TeX and a directive spell them, ask a page of a file of `lang` to show. -/
public def showingOfEntries (lang : Ir.CodeLang) (entries : List String) (alone : Bool := false) :
    Showing :=
  showingOfValues lang (entryValues entries) alone

/-- What a markdown Lean division asks its inclusion to show, each attribute's value as written and an
attribute without a key named as it is written. -/
public def showingOfDivision (d : Md.LeanDivision) : Showing :=
  showingOfValues .lean (d.attrs.toList.map fun (k, v) =>
    (k, if k.isEmpty then "=" ++ v else v.trimAscii.toString)) (alone := true)

/-- What a file's directive asks its page to show. -/
public def showingOf (lang : Ir.CodeLang) (src : Array Char) : Showing :=
  match directive? lang src with
  | none => {}
  | some (_, value) => showingOfEntries lang (Decl.splitEntries value)

/-- Whether a page reads its facts: it shows statements, or folds or removes proofs, whose places
only Lean's syntax tree gives. -/
public def Showing.asks (s : Showing) : Bool := s.statements || s.proofs != .show

/-- The notes for options a page, or an inclusion (`page` false), cannot honour: a link with no
statement to carry it, facts nothing reads, keys only a Lean file's page reads written for another
language, a `decls` naming nothing, and on a page a `decls` with no statement to choose. -/
public def Showing.idle (s : Showing) (lang : Ir.CodeLang) (request : Span) (page : Bool := true) :
    Array Diag :=
  let sets := if page then "the page sets as if it were not written"
    else "the file is included as if it were not written"
  let note (key what help : String) : Diag :=
    Diag.of .W0110 s!"`{key}` {what}; {sets}" (some request) (help := help)
      (subject := some s!"code:{key}")
  let foreign := if lang == .lean then [] else
    ((showKeys.filter (· != "show")).filter s.written.contains).map fun k =>
      note k "is read only on a Lean file's page" "delete it, or write it in a Lean file's directive"
  let uncited := if lang == .lean && !page && !s.docs && s.written.contains "bibliography" then
      [note "bibliography" "names the bibliography an inclusion's documentation cites into, and \
this one sets its documentation as code" "write `show = docs`, or delete `bibliography`"]
    else []
  let restyled := if lang == .lean && !page && s.written.contains "biblio-style" then
      [note "biblio-style" "names a page's citation style, and an inclusion's citations set in its \
document's" "delete it"]
    else []
  let docsAlone := if lang == .lean && !page && s.docs &&
      (s.views.length > 1 || s.decls.isSome || s.proofs != .show) then
      [Diag.of .W0110 "`show` names `docs` with another view, `decls` or `proofs`; the file is \
included as its page sets it, documentation as prose, without them" (some request)
        (help := "write `show = docs` alone, or drop `docs`") (subject := some "code:show")]
    else []
  let unlinked := if lang == .lean && s.link.isSome && !s.statements then
      [note "link" "links statements' names, and none is set" "write `show = math, code`"]
    else []
  let unread := if lang == .lean && s.facts.isSome && !s.asks && (page || s.decls.isNone) then
      [note "facts"
        "names the file statements and proofs' places are read from, and nothing reads them"
        "write `show = math, code`, or delete `facts`"]
    else []
  let empty := if lang == .lean && s.written.contains "decls" && s.decls.isNone then
      [note "decls" "names no declaration" "name one, or delete `decls` to set every one"]
    else []
  let unchosen := if page && lang == .lean && s.decls.isSome && !s.statements then
      [note "decls" "chooses the declarations whose statements a page sets, and it sets none"
        "write `show = math, code`"]
    else []
  (foreign ++ unlinked ++ unread ++ uncited ++ restyled ++ docsAlone ++ empty ++ unchosen).toArray

/-- What a page that reads its facts sets when it has none that line up. -/
public def Showing.lost (s : Showing) : String :=
  match s.statements, s.proofs != .show with
  | true, true => "its code is set without statements and its proofs as written"
  | true, false => "its code is set without statements"
  | false, _ => "its proofs are set as written"

/-- What an inclusion sets with no facts that line up: the whole file, in place of the declarations
a `decls` chooses, without statements and with its proofs as written where it asked for either. -/
public def Showing.lostIncluded (s : Showing) : String :=
  match s.decls with
  | none => if s.asks then s.lost else "it is included whole"
  | some _ =>
    let parts := (if s.statements then [", without statements"] else []) ++
      (if s.proofs != .show then [", its proofs as written"] else [])
    let said := String.join parts
    "it is included whole in place of the declarations `decls` names" ++ said

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
    | some (k, _) => if showKey k then (acc.1, true) else (acc.1.push e, false)
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
    (known : Option (Std.HashSet String)) (seg : Seg) (opens : Bool) : Array Raw × Array Diag :=
  let place := lineCol starts seg.start
  let prose := proseIn lang seg.text place.1 (place.2 - 1)
  let read := Md.desugar file prose.text .docstring (known := if lang == .lean then known else none)
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

/-- Characters as segments: their trailing white space blank, the rest code. -/
public def trimmedRun (start : Nat) (cs : Array Char) : Array Seg :=
  let body := (cs.toList.reverse.dropWhile isWhite).reverse
  let tail := cs.toList.drop body.length
  (if body.isEmpty then #[] else #[⟨.code, start, body⟩]) ++
    (if tail.isEmpty then #[] else #[⟨.blank, start + body.length, tail⟩])

/-- What happens to a segment's code at an offset: a fold or a removal opens or closes, or a
removal's listing ends. -/
public inductive FoldEvent where
  | foldOpen (index : Nat)
  | removeOpen
  /-- A fold closes, the blank lines after it blank; a removal closes, its line's rest kept. -/
  | close (folded : Bool)
  | cut (index : Nat)

/-- A fold's events at their offsets, a close and a cut before what opens at the same offset. -/
public def foldEvents (folds : List ProofFold) : Array (Nat × Nat × FoldEvent) :=
  let one (f : ProofFold) : List (Nat × Nat × FoldEvent) :=
    if f.remove then
      [(f.start, 1, .removeOpen), (f.stop, 0, .close false)] ++ f.cut.toList.map (·, 0, .cut f.index)
    else [(f.start, 1, .foldOpen f.index), (f.stop, 0, .close true)]
  ((folds.flatMap one).mergeSort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1 ≤ b.2.1)).toArray

/-- The index of the first event at or after offset `k`. -/
public def firstEventAt (events : Array (Nat × Nat × FoldEvent)) (k : Nat) : Nat := Id.run do
  let mut lo := 0
  let mut hi := events.size
  for _ in [0:events.size] do
    if lo ≥ hi then break
    let mid := (lo + hi) / 2
    if ((events[mid]?.map (·.1)).getD 0) < k then lo := mid + 1 else hi := mid
  return lo

/-- One code segment with each fold's characters taken out, in one pass from its first event: a
fold's statement segment, the white space around it blank but the next line's indentation; a
removal's `⋯` in its place and, where its listing ends, an empty statement segment. -/
public def cutFolds (events : Array (Nat × Nat × FoldEvent)) (s : Seg) : List Seg := Id.run do
  let mut e := firstEventAt events s.start
  let mut out : Array Seg := #[]
  let mut cur : Array Char := #[]
  let mut curStart := s.start
  let mut inside := false
  let mut lead := false
  let mut atLine := false
  let mut pend : Array Char := #[]
  let mut pendStart := s.start
  let ending := s.start + s.text.length
  for (c, k) in (s.text.zipIdx s.start) ++ [(' ', ending)] do
    for _ in [e:events.size] do
      let some (at_, _, ev) := events[e]? | break
      if at_ > k then break
      match ev with
      | .foldOpen i =>
        let pending : Array Seg := if pend.isEmpty then #[] else #[⟨.blank, pendStart, pend.toList⟩]
        out := ((out ++ trimmedRun curStart cur) ++ pending).push ⟨.statement i, k, []⟩
        cur := #[]
        pend := #[]
        inside := true
      | .removeOpen =>
        unless cur.isEmpty do out := out.push ⟨.code, curStart, cur.toList⟩
        out := out.push ⟨.code, k, ['⋯']⟩
        cur := #[]
        inside := true
      | .close folded =>
        lead := folded
        atLine := false
        inside := false
        curStart := k
      | .cut i =>
        out := (out ++ trimmedRun curStart cur).push ⟨.statement i, k, []⟩
        cur := #[]
        curStart := k
        lead := true
        atLine := true
      e := e + 1
    if k == ending || inside then continue
    if lead && isWhite c then
      if pend.isEmpty then pendStart := k
      pend := pend.push c
    else
      if lead then
        let kept := (pend.toList.reverse.takeWhile (· != '\n')).length
        let lines := if atLine || pend.contains '\n' then pend.size - kept else pend.size
        unless lines == 0 do out := out.push ⟨.blank, pendStart, pend.toList.take lines⟩
        cur := (pend.toList.drop lines).toArray
        curStart := pendStart + lines
        pend := #[]
        lead := false
      if cur.isEmpty then curStart := k
      cur := cur.push c
  unless pend.isEmpty do out := out.push ⟨.blank, pendStart, pend.toList⟩
  unless cur.isEmpty do out := out.push ⟨.code, curStart, cur.toList⟩
  return out.toList

/-- The segments with each one a fold covers whole read as code and joined to the code beside it,
so a fold never spans two segments. -/
public def coverFolds (folds : List ProofFold) (segs : List Seg) : List Seg :=
  let covered (s : Seg) : Bool :=
    folds.any fun f => f.start ≤ s.start && s.start + s.text.length ≤ f.stop
  let step (acc : Array Seg × Bool) (s : Seg) : Array Seg × Bool :=
    let taken := !s.isCode && covered s
    let s : Seg := if taken then { s with kind := .code } else s
    match acc.1.back? with
    | some p =>
      if (taken || acc.2) && p.isCode && s.isCode && p.start + p.text.length == s.start then
        (acc.1.pop.push { p with text := p.text ++ s.text }, taken)
      else (acc.1.push s, taken)
    | none => (acc.1.push s, taken)
  (segs.foldl step (#[], false)).1.toList

/-- The segments with each fold cut out of the code it stands in. -/
@[expose] public def withFolds (folds : List ProofFold) (segs : List Seg) : List Seg :=
  if folds.isEmpty then segs else
    let events := foldEvents folds
    (coverFolds folds segs).flatMap fun s => if s.isCode then cutFolds events s else [s]

public theorem withFolds_nil (segs : List Seg) : withFolds [] segs = segs := by
  simp [withFolds]

/-- The page a file reads into, in order: its pieces, each fold cut out, a statement at each
anchor. -/
@[expose] public def pagePieces (lang : Ir.CodeLang) (text : String) (folds : List ProofFold)
    (anchors : List (Nat × Nat)) : Array Piece :=
  assemble (withStatements (lineStarts text.toList.toArray) anchors
    (withFolds folds (segmentsOf lang text)))

/-- A page's code pieces hold exactly its segments' code, in source order, whatever statements
stand between them, which with no fold is the file's code; a page that shows code sets each one
holding more than white space as one listing of it (`pieceRaws_code_exact`). -/
public theorem pagePieces_code_exact (lang : Ir.CodeLang) (text : String) (folds : List ProofFold)
    (anchors : List (Nat × Nat)) :
    ((pagePieces lang text folds anchors).toList.filterMap Piece.code?).flatten =
      codeOf (withFolds folds (segmentsOf lang text)) := by
  rw [pagePieces, assemble_code_exact, withStatements_code_exact]

/-- A line free to break, and no space: zero glue. -/
public def breakRaws (pos : Pos) : Array Raw := #[.ctrl "hspace" pos, .group #[.word "0pt" pos] pos]

/-- One formula as inline mathematics. -/
@[expose] public def formulaRaw (pos : Pos) (m : Array LeanNotation.Math) : Raw :=
  .math false (LeanStatement.Math.listRaws pos #[] m.toList) pos

/-- One formula after a paragraph's raws, a word space before it where the one before asks for
it, else a bare break; and whether the next asks for one. -/
@[expose] public def displayStep (pos : Pos) (st : Array Raw × Bool)
    (formula : Array LeanNotation.Math × Bool) : Array Raw × Bool :=
  ((st.1.append (if st.2 then #[.space] else breakRaws pos)).push (formulaRaw pos formula.1),
    formula.2)

/-- Where a file stands for its links: the commit its repository holds it at, its path there, and
whether it differs from that commit, each where the host could say. -/
public structure LinkPlace where
  commit : Option String := none
  path : Option String := none
  /-- Whether the file differs from that commit, none where git could not say. -/
  dirty : Option Bool := none
  /-- Whether that commit holds the file. -/
  tracked : Bool := false
  deriving Repr, BEq, Inhabited

/-- Whether a file's place gives every part a template names that git answers: the commit only
with the file's state there and the commit holding it, the path only as the commit holds it. -/
public def placeGives (template : String) (place : LinkPlace) : Bool :=
  let names (part : String) : Bool := (template.splitOn part).length > 1
  (!names "{commit}" || (place.commit.isSome && place.dirty.isSome && place.tracked)) &&
    (!names "{path}" || place.path.isSome)

/-- A template's parts and what each declaration fills them with. -/
private def linkParts (d : LeanFacts.Decl) (place : LinkPlace) : List (String × Option String) :=
  templateParts.zip [some (urlPart false d.name), some (urlPart false d.moduleName),
    place.path.map (urlPart true), some (toString d.start.1), some (toString d.stop.1),
    place.commit.map (urlPart false)]

/-- A template's link for one declaration, none where it names a part the file's place lacks. -/
public def expandLink (template : String) (d : LeanFacts.Decl) (place : LinkPlace) :
    Option String :=
  expandParts template (linkParts d place)

/-- A declaration's name as code, linked where a link is given. -/
@[expose] public def nameRaws (d : LeanFacts.Decl) (pos : Pos) (link : Option String) : Array Raw :=
  let name : Array Raw := #[.ctrl "texttt" pos, .group (Md.textRaws d.name pos) pos]
  match link with
  | some url => #[.ctrl "href" pos, .group #[.word url pos] pos, .group name pos]
  | none => name

/-- A declaration's head: its kind in bold and its name as code, linked where a link is given,
marked when Lean holds a theorem unproved. -/
public def headRaws (d : LeanFacts.Decl) (pos : Pos) (link : Option String := none) : Array Raw :=
  let close : Array Raw := if d.kind == .theorem && !d.proved then
      #[.word "," pos, .space, .word "unproved)." pos] else #[.word ")." pos]
  #[.ctrl "textbf" pos, .group #[.word d.kind.label pos] pos, .space, .word "(" pos] ++
    nameRaws d pos link ++ close

/-- The paragraph a declaration's statement sets as, ragged right: its head, then its formulas,
each after a word space where the one before asks for it, else after a bare break. -/
public def displayRaws (d : LeanFacts.Decl) (formulas : Array (Array LeanNotation.Math × Bool))
    (pos : Pos) (link : Option String := none) : Array Raw :=
  #[.env "flushleft" (formulas.foldl (displayStep pos) (headRaws d pos link, true)).1 pos]

/-- A leaf's formulas as inline mathematics, a line free to break between them. -/
public def leafRaws (pos : Pos) : LeanProse.Leaf → Array Raw
  | [] => #[]
  | m :: rest => rest.foldl (fun acc q => (acc ++ breakRaws pos).push (formulaRaw pos q))
      #[formulaRaw pos m]

/-- A token's raws, its word capitalized while the sentence still opens, and whether it still
opens after it: past an opening parenthesis it does. -/
public def tokRaws (pos : Pos) (opening : Bool) : LeanProse.Tok LeanProse.Leaf → Array Raw × Bool
  | .w "(" => (#[.word "(" pos], opening)
  | .w s => (#[.word (if opening then s.capitalize else s) pos], false)
  | .leaf l => (leafRaws pos l, false)

/-- A sentence's tokens as text, its opening word capitalized, each leaf as inline mathematics, a
word space between tokens but where they join, and a full stop. -/
public def sentenceRaws (pos : Pos) (toks : List (LeanProse.Tok LeanProse.Leaf)) : Array Raw :=
  let step (acc : Array Raw × Option (LeanProse.Tok LeanProse.Leaf) × Bool)
      (t : LeanProse.Tok LeanProse.Leaf) :
      Array Raw × Option (LeanProse.Tok LeanProse.Leaf) × Bool :=
    let gap : Array Raw :=
      if acc.2.1.isNone || LeanProse.Tok.joins acc.2.1 t then #[] else #[.space]
    let r := tokRaws pos acc.2.2 t
    (acc.1 ++ gap ++ r.1, some t, r.2)
  (toks.foldl step (#[], none, true)).1.push (.word "." pos)

/-- The paragraph a declaration's statement sets as in words, ragged right: its head, then its
sentence, a line free to break between words. -/
public def wordsRaws (d : LeanFacts.Decl) (s : LeanProse.Stmt LeanProse.Leaf) (pos : Pos)
    (link : Option String := none) : Array Raw :=
  #[.env "flushleft" ((headRaws d pos link).push .space ++ sentenceRaws pos (LeanProse.render s)) pos]

/-- Why a declaration's statement is not set, when it is not. -/
private def unset? (d : LeanFacts.Decl) : Option String :=
  match d.type with
  | none => some "is too large to set"
  | some t => if t.elaborated then none else some "did not elaborate"

/-- Where a place in the source stands as a diagnostic's position. -/
private def posAt (place : Nat × Nat) : Pos := { line := place.1, col := place.2 + 1 }

/-- Where a declaration's statement stands on the page: its source's first line and column. -/
private def posOf (d : LeanFacts.Decl) : Pos := posAt d.start

/-- Pieces as raws: each code piece the listings `listing` sets, each statement its paragraph,
prose nothing. -/
@[expose] public def piecesRaws (listing : Nat → List Char → Array Raw) (paras : Array (Array Raw))
    (pieces : Array Piece) : Array Raw :=
  pieces.foldl (fun acc p => match p with
    | .code start text => acc.append (listing start text)
    | .statement i => acc.append (paras.getD i #[])
    | .prose _ => acc) #[]

/-- The code segments' characters from offset `lo` up to `hi`, as code segments. -/
public def clipCode (segs : List Seg) (lo hi : Nat) : List Seg :=
  segs.filterMap fun s => if !s.isCode then none else
    let cs := (s.text.zipIdx s.start).filter fun (_, k) => lo ≤ k && k < hi
    cs.head?.map fun (_, k) => ⟨.code, k, cs.map (·.1)⟩

/-- A code file's listing whose first line stands at `start`, its trailing white space aside. -/
@[expose] public def fileListing (starts : Array Nat) (start : Nat) (code : List Char) : Array Raw :=
  let body := (code.reverse.dropWhile isWhite).reverse
  if body.isEmpty then #[]
  else #[listingRaw .lean (String.ofList body) { line := (lineCol starts start).1 - 1 }]

/-- The listings a declaration's code sets as in its statement's place: the code its lines hold,
from the line its command opens on through its last, its documentation aside, each fold cut out
and its paragraph from `paras`. -/
public def codeFor (starts : Array Nat) (src : Array Char) (segs : List Seg)
    (folds : List ProofFold) (paras : Array (Array Raw)) (head stop : Nat × Nat) : Array Raw :=
  let lo := starts.getD (head.1 - 1) 0
  let hi := starts.getD stop.1 src.size
  piecesRaws (fileListing starts) paras (assemble (withFolds folds (clipCode segs lo hi)))

/-- Where a file's directive stands, as a diagnostic's position, else the file's start. -/
public def directivePos (lang : Ir.CodeLang) (src : Array Char) : Pos :=
  match directive? lang src with
  | some (cut, _) => let (line, col) := lineCol (lineStarts src) cut.start; { line, col }
  | none => {}

/-- Why a declared phrase is refused, as its note says it, with its help. -/
private def refusalWords (name : String) : LeanProse.Refusal → String × String
  | .unknown => (s!"'phrase.{name}' names no constant a statement of this file names; the \
phrase is not used", "write the constant's name as a statement uses it after `phrase.`")
  | .ambiguous => (s!"'phrase.{name}' names more than one constant; the phrase is not used",
    "write the constant's full name after `phrase.`")
  | .twice => (s!"'phrase.{name}' gives its constant a second phrase; the first stands",
    "keep one `phrase.` entry for each constant")
  | .shape => (s!"'phrase.{name}' is no template the prose view reads; its constant is set as \
mathematics", "number its slots `#1`, `#2`, … once each, write no comma, parenthesis, brace or \
quote, and open it with a word, or a slot then a word, the grammar keeps for itself none of, as \
`if`, `and`, `both`")
  | .arity _ _ => (s!"the slots of 'phrase.{name}' are not its constant's explicit arguments; its \
constant is set as mathematics", "write one slot `#k` for the k-th explicit argument, for each")
  | .clash => (s!"the words of 'phrase.{name}' open as another template's do; its constant is \
set as mathematics", "open it with words no other `phrase.` entry or relation opens with")
  | .connective => (s!"'phrase.{name}' names a connective or quantifier the prose view says \
itself; the phrase is not used", "drop this `phrase.` entry")
  | .unused => (s!"no sentence this page sets uses 'phrase.{name}'; the phrase changes nothing",
    "check its constant's name and explicit arguments, or drop this `phrase.` entry")
  | .unshown true => (s!"'phrase.{name}' stands on a page that says no statement in words; the \
phrase is not used", "add `prose` to `show`, or drop this `phrase.` entry")
  | .unshown false => (s!"'phrase.{name}' stands in a file whose statements are never said in \
words; the phrase is not used", "drop this `phrase.` entry: only a Lean file's statements are")

/-- The note naming a declared phrase a page refuses, at the directive. -/
public def refusalNote (file : String) (pos : Pos) (name : String) (r : LeanProse.Refusal) :
    Diag :=
  let (msg, help) := refusalWords name r
  let detail := match r with
    | .arity slots args => some s!"slots: {slots}; explicit arguments: {args}"
    | .unknown | .ambiguous | .twice | .shape | .clash | .connective | .unused | .unshown _ => none
  Diag.of .W0416 msg (some ⟨file, pos⟩) (help := help) (subject := some s!"code:phrase:{name}")
    (detail := detail)

/-- Why a declaration's statement is not said in words, as its note says it. -/
private def unsaidWhy : LeanProse.Unsaid → String
  | .named h => s!"refers to its hypothesis '{h}'"
  | .local n => s!"defines '{n}' locally"
  | .function => "is a function"
  | .notProp => "is no proposition"

/-- The note naming a declaration whose statement words cannot say. -/
public def unsaidNote (file : String) (d : LeanFacts.Decl) (u : LeanProse.Unsaid) : Diag :=
  Diag.of .W0415 s!"words cannot say '{d.name}', which {unsaidWhy u}; it is set as mathematics"
    (some ⟨file, posOf d⟩) (subject := some s!"prose:{d.name}")

/-- A view's paragraph for a declaration whose statement the facts give, the note when its words fall
back to its mathematics, which a page that shows the math view sets once, and the templates its
words use. -/
public def viewPara (file : String) (facts : LeanFacts.Facts) (tb : LeanProse.Table)
    (withMath : Bool) (link : Option String) (d : LeanFacts.Decl) (t : LeanFacts.Term) :
    View → Array Raw × Array Diag × Array LeanProse.Template
  | .code => (#[], #[], #[])
  -- The documentation view sets the file's comments, no declaration's paragraph.
  | .docs => (#[], #[], #[])
  | .math => (displayRaws d (LeanStatement.statementMath facts d t) (posOf d) link, #[], #[])
  | .prose =>
    match LeanProse.proseOf facts tb d t with
    | .ok s => (wordsRaws d s (posOf d) link, #[], s.templates #[])
    | .error u =>
      (if withMath then #[] else displayRaws d (LeanStatement.statementMath facts d t) (posOf d) link,
        #[unsaidNote file d u], #[])

/-- What a page sets for one declaration the facts hold, when it is chosen, in the views given:
each view's paragraph where the facts give a statement, its name linked where a link is given, else, on
a page that shows no code, its code in the statement's place; its views' notes and templates. -/
public def declPara (file : String) (facts : LeanFacts.Facts) (tb : LeanProse.Table)
    (starts : Array Nat) (src : Array Char) (segs : List Seg) (folds : List ProofFold)
    (paras : Array (Array Raw)) (code withMath wanted : Bool) (views : List View)
    (link : Option String) (d : LeanFacts.Decl) :
    Array Raw × Array Diag × Array LeanProse.Template :=
  if !wanted || views.isEmpty then (#[], #[], #[]) else
    match d.type, unset? d with
    | some t, none => views.foldl (fun acc v =>
        let p := viewPara file facts tb withMath link d t v
        (acc.1 ++ p.1, acc.2.1 ++ p.2.1, acc.2.2 ++ p.2.2)) (#[], #[], #[])
    | _, _ => (if code then #[] else codeFor starts src segs folds paras d.head d.stop, #[], #[])

/-- Where a statement stands before its declaration's code: the line the command that writes it
opens on, or the code after the documentation that line holds. -/
private def beforeAnchor (starts : Array Nat) (segs : List Seg) (head : Nat × Nat) : Option Nat :=
  let off := offsetOf starts head
  (segs.find? fun s => s.isCode && off < s.start + s.text.length).map fun s => max off s.start

/-- Where a statement stands after its declaration's code: the start of the line after it. -/
private def afterAnchor (src : Array Char) (starts : Array Nat) (stop : Nat × Nat) : Nat :=
  starts.getD stop.1 src.size

/-- The notes a declared link owes: the parts its template names that the file's place lacks, or
the file's changes since the commit it reaches. -/
public def linkNotes (request : Span) (showing : Showing) (place : LinkPlace) : Array Diag :=
  match showing.link with
  | none => #[]
  | some l =>
    let template := linkTemplate l
    let names (part : String) : Bool := (template.splitOn part).length > 1
    let unlinked := "a link names the file's commit or path, which git could not give; the names \
set unlinked"
    let unlinkedHelp := "build the file in the git repository that tracks it, or write a `link` with \
no `{commit}` or `{path}`"
    let changed := "the file has changes its commit does not hold; its links show the committed text"
    if !placeGives template place then
      #[Diag.of .W0432 unlinked (some request) (subject := some s!"code:link:{request.file}")
          (help := unlinkedHelp)]
    else if names "{commit}" && place.dirty == some true then
      #[Diag.of .W0431 changed (some request) (subject := some s!"code:link:{request.file}")
          (help := "commit the file, or write a `link` that names no `{commit}`")]
    else #[]

/-- Whether a declaration's name is a name `decls` gives: the whole name, or its last parts. -/
private def namedAs (n named : String) : Bool := n == named || n.endsWith ("." ++ named)

/-- One note for each name `decls` gives that the facts hold no theorem, definition or axiom
by, at the request. -/
public def unnamedNotes (showing : Showing) (facts : LeanFacts.Facts) (request : Span) :
    Array Diag :=
  ((showing.decls.getD []).filter fun n =>
    !facts.decls.any (namedAs ·.name n) && !facts.failed.any (namedAs ·.name n)).toArray.map fun n =>
      Diag.of .W0110 s!"`decls` names '{n}', which is no theorem, definition or axiom in the \
file's facts; nothing is set for it" (some request) (subject := some s!"code:decls:{n}")
        (help := "name a theorem, definition or axiom the file declares")

/-- Each declaration's paragraphs before and after its code by index, then each failed one's, the
anchors set and the notes, in source order; a page with no code sets a declaration's code, folds cut
out, where its statement cannot stand, and a link's notes once a statement is set. -/
public def statementsOf (file : String) (starts : Array Nat) (src : Array Char) (segs : List Seg)
    (showing : Showing) (declared : LeanProse.Declared) (facts : LeanFacts.Facts)
    (place : LinkPlace := {}) (folds : List ProofFold := []) (foldParas : Array (Array Raw) := #[])
    (request : Span := ⟨file, {}⟩) : Array (Array Raw) × List (Nat × Nat) × Array Diag :=
  let tb := declared.table
  let ds := facts.decls
  let chosen (n : String) : Bool := match showing.decls with
    | none => true
    | some ns => ns.any (namedAs n)
  let wanted (d : LeanFacts.Decl) : Bool :=
    (showing.decls.isSome || !ds.any (holds · d)) && chosen d.name
  let code := showing.code
  let linkOf (d : LeanFacts.Decl) : Option String := showing.link.bind fun l =>
    if placeGives (linkTemplate l) place then expandLink (linkTemplate l) d place else none
  let paras0 := Array.replicate (2 * ds.size + facts.failed.size) (#[] : Array Raw) ++ foldParas
  let before := showing.around.1
  let after := showing.around.2
  let para (views : List View) (d : LeanFacts.Decl) :
      Array Raw × Array Diag × Array LeanProse.Template :=
    declPara file facts tb starts src segs folds paras0 code showing.math (wanted d) views (linkOf d) d
  let befores := ds.map (para before)
  let afters := ds.map (para after)
  let paras := befores.map (·.1) ++ afters.map (·.1)
  let failedParas := facts.failed.map fun f =>
    if chosen f.name && !code then codeFor starts src segs folds paras0 f.head f.stop else #[]
  let anchors := ds.zipIdx.filterMap fun (d, i) =>
    if wanted d && !before.isEmpty && ((unset? d).isNone || !code) then
      (beforeAnchor starts segs d.head).map fun off => ([off, 1, d.start.1, d.start.2], i)
    else none
  let afterAnchors := ds.zipIdx.filterMap fun (d, i) =>
    if wanted d && !after.isEmpty && (unset? d).isNone then
      some ([afterAnchor src starts d.stop, 0, d.start.1, d.start.2], ds.size + i)
    else none
  let failedAnchors := facts.failed.zipIdx.filterMap fun (f, j) =>
    if chosen f.name && !code then
      (beforeAnchor starts segs f.head).map fun off => ([off, 1, f.start.1, f.start.2], 2 * ds.size + j)
    else none
  let viewNotes := (ds.zip (befores.zip afters)).toList.flatMap fun (d, b, a) =>
    (b.2.1 ++ a.2.1).toList.map (d.start, ·)
  let used := (befores ++ afters).foldl (fun acc p => acc ++ p.2.2) #[]
  let unused := declared.phrases.filterMap fun (name, t) =>
    if showing.prose && !used.contains t then some (refusalNote request.file request.pos name .unused)
    else none
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
  let notes := (unsetNotes ++ failedNotes ++ viewNotes.toArray).qsort fun a b =>
    a.1.1 < b.1.1 || (a.1.1 == b.1.1 && a.1.2 < b.1.2)
  let set := ds.any fun d => wanted d && (unset? d).isNone
  let links := if set then linkNotes request showing place else #[]
  let all := (anchors ++ afterAnchors ++ failedAnchors).qsort fun a b => decide (a.1 < b.1)
  (paras ++ failedParas, (all.map fun (key, i) => (key.headD 0, i)).toList,
    unused ++ unnamedNotes showing facts request ++ notes.map (·.2) ++ links)

/-- What a page sets from the file's facts, when it has them. -/
@[expose] public def statementsFor (file : String) (starts : Array Nat) (src : Array Char)
    (segs : List Seg) (showing : Showing) (declared : LeanProse.Declared) (place : LinkPlace)
    (folds : List ProofFold) (foldParas : Array (Array Raw)) (request : Span) :
    Option LeanFacts.Facts → Array (Array Raw) × List (Nat × Nat) × Array Diag
  | some f => statementsOf file starts src segs showing declared f place folds foldParas request
  | none => (#[], [], #[])

/-- The first offset at or after `i` that holds no white space. -/
private def skipWhite (src : Array Char) (i : Nat) : Nat := Id.run do
  let mut j := i
  for _ in [i:src.size] do
    if (src[j]?.map isWhite).getD false then j := j + 1 else break
  return j

/-- The offset of the line end at or after `i`. -/
private def lineEndAt (src : Array Char) (i : Nat) : Nat := Id.run do
  let mut j := i
  for _ in [i:src.size] do
    if src[j]? == some '\n' then break
    j := j + 1
  return j

/-- The offset past the block comment opening at `i`, nested ones inside it, where it closes
before `stop`. -/
private def blockCommentEnd (src : Array Char) (i stop : Nat) : Option Nat := Id.run do
  let mut depth := 0
  let mut k := i
  for _ in [i:stop] do
    if k + 1 ≥ stop then break
    if src[k]? == some '/' && src[k + 1]? == some '-' then
      depth := depth + 1
      k := k + 2
    else if src[k]? == some '-' && src[k + 1]? == some '/' then
      depth := depth - 1
      k := k + 2
      if depth == 0 then return some k
    else k := k + 1
  return none

/-- Whether a line holds nothing from `i` to its end but white space, block comments that close on
it and a line comment. -/
private def restIsComment (src : Array Char) (i : Nat) : Bool := Id.run do
  let stop := lineEndAt src i
  let mut k := i
  for _ in [i:stop + 1] do
    if k ≥ stop then return true
    let c := src.getD k ' '
    if c == ' ' || c == '\t' || c == '\r' then k := k + 1
    else if c == '-' && src[k + 1]? == some '-' then return true
    else if c == '/' && src[k + 1]? == some '-' then
      match blockCommentEnd src k stop with
      | some e => k := e
      | none => return false
    else return false
  return true

/-- Each top-level theorem's proof a page folds or removes, at Lean's span, indexed from `first`: a
fold takes the proof from its line (or, after a bare `:= by`, the next) through its closing
comments, one standing on its signature's line left in place; a removal takes the proof itself. -/
public def foldsOf (starts : Array Nat) (src : Array Char) (proofs : Proofs)
    (facts : LeanFacts.Facts) (first : Nat) : List ProofFold :=
  let ds := facts.decls.toList.filter fun d => d.kind == .theorem && !facts.decls.any (holds · d)
  let failed := facts.failed.toList.filter (·.kind == .theorem)
  let spans := (ds.map (·.proof) ++ failed.map (·.proof)).filterMap fun p => p.map fun (a, b) =>
    let o := offsetOf starts a
    let o := if src[o]? == some ':' && src[o + 1]? == some '=' then skipWhite src (o + 2) else o
    (o, offsetOf starts b)
  let sorted := (spans.filter fun (a, b) => a < b).mergeSort (·.1 ≤ ·.1)
  let shaped := sorted.filterMap fun (t, e) =>
    let lineEnd := lineEndAt src e
    let multi := (src.extract t e).any (· == '\n')
    if proofs == .remove then
      some (t, e, if multi then some (min src.size (lineEnd + 1)) else none)
    else
      let lineStart := starts.getD ((lineCol starts t).1 - 1) 0
      let opens := (src.extract lineStart t).all isWhite
      let bareBy := src[t]? == some 'b' && src[t + 1]? == some 'y' && restIsComment src (t + 2)
      let start := if opens then lineStart
        else if bareBy then min src.size (lineEndAt src t + 1) else t
      let stop := if restIsComment src e then lineEnd else e
      if (opens || multi) && start < stop then some (start, stop, none) else none
  shaped.zipIdx.map fun ((a, b, c), j) =>
    { start := a, stop := b, index := first + j, remove := proofs == .remove, cut := c }

/-- A folded proof as a disclosure whose summary is "Proof" and whose body is its listing, its first
line at its source column; a removed proof's paragraph is empty. -/
public def foldRaws (starts : Array Nat) (src : Array Char) (f : ProofFold) : Array Raw :=
  if f.remove then #[] else
  let text := (src.extract f.start f.stop).toList
  let blank := text.takeWhile isWhite
  let lead := blank.length - (blank.reverse.takeWhile (· != '\n')).length
  let code := ((text.drop lead).reverse.dropWhile isWhite).reverse
  let at_ := lineCol starts (f.start + lead)
  let pos : Pos := { line := at_.1, col := at_.2 }
  Md.disclosureRaws #[.word "Proof" pos]
    #[listingRaw .lean (String.ofList code) { line := at_.1 - 1 }] false pos

/-- What one piece adds to the body: a listing for code and the markdown reader's raws for prose,
where the page shows them, and its paragraph for a statement. -/
@[expose] public def pieceRaws (lang : Ir.CodeLang) (file : String) (starts : Array Nat)
    (page : PageSet) (opens : Bool) : Piece → Array Raw
  | .code start code => if page.code && code.any (!isWhite ·) then
      #[listingRaw lang (String.ofList code) { line := (lineCol starts start).1 - 1 }] else #[]
  | .prose seg => if page.code then (proseRaws lang file starts page.cites seg opens).1 else #[]
  | .statement i => page.stmts.getD i #[]

/-- The raws a piece's title is read from: its prose's, whether or not the page shows it. -/
@[expose] public def titleSource (lang : Ir.CodeLang) (file : String) (starts : Array Nat)
    (known : Option (Std.HashSet String)) (opens : Bool) : Piece → Array Raw
  | .prose seg => (proseRaws lang file starts known seg opens).1
  | .code _ _ | .statement _ => #[]

/-- Where raws' section headed References ends, which the page's list closes: before the next
heading of its rank or above, else at their end; none where no heading names References. -/
public def referencesEnd (raws : Array Raw) : Option Nat :=
  let step (st : Option Nat × Option Nat) (i : Nat) : Option Nat × Option Nat :=
    match st, raws[i]?, raws[i + 2]? with
    | (rank, none), some (.ctrl n _), some (.group body _) =>
      match Parse.headingControl? n, rank with
      | some lvl, some r => if Ir.headingRank lvl ≤ r then (rank, some i) else (rank, none)
      | some lvl, none =>
        if (rawSrc body).trimAscii.toString.toLower == "references" then
          (some (Ir.headingRank lvl), none)
        else (none, none)
      | none, _ => (rank, none)
    | st, _, _ => st
  match (List.range raws.size).foldl step (none, none) with
  | (some _, some e) => some e
  | (some _, none) => some raws.size
  | (none, _) => none

mutual

/-- Whether raws hold a citation command, `\nocite` among them, inside a group or an environment too. -/
public def citesRaw : Raw → Bool
  | .ctrl n _ => n.startsWith "cite" || n == "nocite"
  | .group body _ => citesRaws body.toList
  | .env _ body _ => citesRaws body.toList
  | .math _ body _ => citesRaws body.toList
  | .word .. | .space | .par _ | .sym .. | .verb .. => false

public def citesRaws : List Raw → Bool
  | [] => false
  | r :: rest => citesRaw r || citesRaws rest

end

/-- Whether a piece is the file's description the title is read from, given what came before. -/
@[expose] public def Acc.opens (acc : Acc) : Piece → Bool
  | .code _ _ | .statement _ => false
  | .prose seg => !acc.sawModule && seg.describesFile

/-- One piece read into the body, the file's description opening on the document's title. -/
@[expose] public def pieceStep (lang : Ir.CodeLang) (file : String) (starts : Array Nat)
    (page : PageSet) (acc : Acc) (piece : Piece) : Acc :=
  let opens := acc.opens piece
  let read := match piece with
    | .prose seg => proseRaws lang file starts page.cites seg opens
    | .code _ _ | .statement _ => (#[], #[])
  let raws := match piece with
    | .prose _ => if page.code then read.1 else #[]
    | .code _ _ | .statement _ => pieceRaws lang file starts page opens piece
  let heading := if opens then openingHeading? read.1.toList else none
  { body := acc.body ++ raws, diags := acc.diags ++ (if page.code then read.2 else #[])
    title := if opens then heading else acc.title
    titled := acc.titled || (page.code && heading.isSome)
    sawModule := acc.sawModule || opens
    cited := acc.cited || (page.code && citesRaws read.1.toList)
    refsAt := if acc.refsAt.isNone && page.code then (referencesEnd raws).map (acc.body.size + ·)
      else acc.refsAt }

/-- One piece adds its raws to the body, and the title its prose opens on when it opens the
document. -/
public theorem pieceStep_exact (lang : Ir.CodeLang) (file : String) (starts : Array Nat)
    (page : PageSet) (acc : Acc) (p : Piece) :
    (pieceStep lang file starts page acc p).body =
        acc.body ++ pieceRaws lang file starts page (acc.opens p) p ∧
      (pieceStep lang file starts page acc p).title = (if acc.opens p then
        openingHeading? (titleSource lang file starts page.cites (acc.opens p) p).toList
        else acc.title) := by
  cases p <;> exact ⟨rfl, by simp only [pieceStep, titleSource]; split <;> rfl⟩

/-- A code file's pieces read in page order, statements standing at their anchors. -/
@[expose] public def readPieces (lang : Ir.CodeLang) (file text : String)
    (page : PageSet) (anchors : List (Nat × Nat)) : Acc :=
  (pagePieces lang text page.folds anchors).toList.foldl
    (pieceStep lang file (lineStarts text.toList.toArray) page) {}

/-- A code piece holding more than white space adds its listing, holding its code exactly, wherever
the page shows code. -/
public theorem pieceRaws_code_exact (lang : Ir.CodeLang) (file : String) (starts : Array Nat)
    (page : PageSet) (h : page.code = true) (opens : Bool) (start : Nat) (code : List Char)
    (hw : code.any (!isWhite ·) = true) :
    pieceRaws lang file starts page opens (.code start code) =
      #[listingRaw lang (String.ofList code) { line := (lineCol starts start).1 - 1 }] := by
  simp [pieceRaws, h, hw]

/-- A code piece of white space alone sets nothing, so no listing on a page is empty. -/
public theorem pieceRaws_white_exact (lang : Ir.CodeLang) (file : String) (starts : Array Nat)
    (page : PageSet) (opens : Bool) (start : Nat) (code : List Char)
    (hw : code.any (!isWhite ·) = false) :
    pieceRaws lang file starts page opens (.code start code) = #[] := by
  simp [pieceRaws, hw]

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
    ∃ opens : List Bool, opens.length = (pagePieces lang text page.folds anchors).size ∧
      (readPieces lang file text page anchors).body.toList =
        ((pagePieces lang text page.folds anchors).toList.zip opens).flatMap fun (p, o) =>
          (pieceRaws lang file (lineStarts text.toList.toArray) page o p).toList := by
  obtain ⟨opens, hlen, hbody⟩ := foldl_body lang file (lineStarts text.toList.toArray) page
    (pagePieces lang text page.folds anchors).toList {}
  exact ⟨opens, by simpa using hlen, by simpa [readPieces] using hbody⟩

/-- The prose view's table a page or an inclusion reads its phrases into, from the file's facts where
its statements have them, with each phrase a page that says nothing in words refuses. -/
public def declaredFor (lang : Ir.CodeLang) (showing : Showing) (stated : Option LeanFacts.Facts) :
    LeanProse.Declared :=
  let unshown : Array (String × LeanProse.Refusal) := if showing.prose then #[] else
    (showing.phrases.map fun e => (e.1, .unshown (lang == .lean))).toArray
  match stated with
  | some f => if showing.prose then LeanProse.tableFor f showing.phrases
    else ⟨LeanProse.coreTable f.collectionFirst, [], unshown, #[]⟩
  | none => ⟨LeanProse.coreTable true, [], unshown, #[]⟩

/-- What a page sets from a file and its facts: what it shows, where each paragraph the facts
give stands, and the notes; a page asked for statements it has no facts for shows the file's
code. -/
@[expose] public def planOf (lang : Ir.CodeLang) (file text : String)
    (facts : Option LeanFacts.Facts) (place : LinkPlace := {}) :
    PageSet × List (Nat × Nat) × Array Diag :=
  let src := text.toList.toArray
  let starts := lineStarts src
  let showing := showingOf lang src
  let answer := if showing.asks then facts else none
  let stated := if showing.statements then answer else none
  let first := (stated.map fun f => 2 * f.decls.size + f.failed.size).getD 0
  let folds := match answer with
    | some f => if showing.proofs != .show then foldsOf starts src showing.proofs f first else []
    | none => []
  let foldParas := (folds.map (foldRaws starts src)).toArray
  let declared := declaredFor lang showing stated
  let refused := declared.refused.map fun (name, r) =>
    refusalNote file (directivePos lang src) name r
  let st := statementsFor file starts src (segmentsOf lang text) showing declared place folds foldParas
    ⟨file, directivePos lang src⟩ stated
  ({ stmts := st.1 ++ foldParas, code := showing.code || answer.isNone
     folds := if showing.code then folds else [] }, st.2.1, refused ++ st.2.2)

/-- Code as an included listing, wrapping its long lines, whose first line stands at `start`, its
trailing white space aside. -/
@[expose] public def listingAt (starts : Array Nat) (start : Nat) (code : List Char) : Array Raw :=
  let body := (code.reverse.dropWhile isWhite).reverse
  let head := ((listingHead .lean).dropEnd 1).toString ++ ",breaklines]"
  if body.isEmpty then #[] else
    #[.verb "lstlisting" (head ++ "\n" ++ String.ofList body) { line := (lineCol starts start).1 - 1 }]

/-- Names in backticks, the last after "or". -/
public def namesOr (names : List String) : String :=
  match names.reverse with
  | [] => ""
  | last :: rest =>
    let init := rest.reverse.map (s!"`{·}`")
    if init.isEmpty then s!"`{last}`" else s!"{", ".intercalate init} or `{last}`"

/-- A Lean file's documentation view: its code as listings and its documentation as prose citing into
`known`, as its page sets them. -/
@[expose] public def docsRaws (file text : String) (starts : Array Nat)
    (known : Option (Std.HashSet String)) : Array Raw × Array Diag :=
  (pagePieces .lean text [] []).foldl (init := (#[], #[])) fun (acc : Array Raw × Array Diag) piece =>
    match piece with
    | .code start code => (acc.1 ++ listingAt starts start code, acc.2)
    | .prose seg =>
      let read := proseRaws .lean file starts known seg false
      (acc.1 ++ read.1, acc.2 ++ read.2)
    | .statement _ => acc

/-- The raws an inclusion's chosen declarations set, each by its offset, in source order. -/
@[expose] public def chosenRaws (items : Array (Nat × Array Raw)) : Array Raw :=
  (items.toList.mergeSort fun a b => decide (a.1 ≤ b.1)).foldl (fun acc x => acc ++ x.2) #[]

/-- The bibliography a page's documentation cites into: the file as the document names it, and the
keys of its entries. -/
public structure Refs where
  path : String
  keys : Std.HashSet String

/-- A Lean file included at `request`, which `entry` names: one listing where nothing reads facts or
none line up; with no `decls`, the whole file with each statement at its declaration and
its folds cut out; else each chosen declaration's views in order. -/
public def includeLean (file text : String) (showing : Showing) (facts : Option LeanFacts.Facts)
    (place : LinkPlace) (request : Span) (entry : String) (refs : Option Refs := none) :
    Array Raw × Array Diag :=
  let src := text.toList.toArray
  let starts := lineStarts src
  let unread := showing.unread.toArray.map fun (k, v) =>
    Diag.of .W0110 s!"`{k}` takes no value '{v}'; the file is included as if it were not written"
      (some request) (help := "write `proofs = show`, `collapse` or `remove`")
      (subject := some s!"code:{k}:{v}")
  let strange := showing.strange.toArray.map fun k =>
    let valueless := inclusionKeys.contains k
    let what := if valueless then s!"`{k}` is written without a value" else s!"{entry} has no option '{k}'"
    Diag.of .W0110 s!"{what}; the file is included as if it were not written" (some request)
      (help := if valueless then s!"write `{k} = …`"
        else s!"name {", ".intercalate (inclusionKeys.map (s!"`{·}`"))} or a `{phraseKey}` entry")
      (subject := some s!"code:option:{k}")
  let views := showing.unknown.toArray.map fun n =>
    Diag.of .W0110 s!"`show` names '{n}', which is no view of a Lean file; it is included without \
it" (some request) (help := s!"name {namesOr (View.all.map (·.name))}")
      (subject := some s!"code:show:{n}")
  let idle := showing.idle .lean request (page := false)
  let notes := views ++ unread ++ strange ++ idle
  let wrap (raws : Array Raw) : Array Raw := #[.env (Parse.nativeInputEnv file) raws request.pos]
  let whole : List Seg := [⟨.code, 0, text.toList⟩]
  -- The documentation view sets the file as its page does, citing into its bibliography's keys.
  if showing.docs then
    let read := docsRaws file text starts (refs.map (·.keys))
    let unsaid := (declaredFor .lean showing none).refused.map fun (name, r) =>
      refusalNote request.file request.pos name r
    (wrap read.1, notes ++ unsaid ++ read.2)
  else
  match (if showing.asks || showing.decls.isSome then facts else none) with
  | none =>
    let unsaid := (declaredFor .lean showing none).refused.map fun (name, r) =>
      refusalNote request.file request.pos name r
    (wrap (listingAt starts 0 text.toList), notes ++ unsaid)
  | some f =>
    let stated := if showing.statements then some f else none
    let first := (stated.map fun f => 2 * f.decls.size + f.failed.size).getD 0
    let folds := if showing.proofs != .show then foldsOf starts src showing.proofs f first else []
    let foldParas := (folds.map (foldRaws starts src)).toArray
    let declared := declaredFor .lean showing stated
    let refused := declared.refused.map fun (name, r) => refusalNote request.file request.pos name r
    let st := statementsFor file starts src whole showing declared place folds foldParas request
      stated
    let paras := st.1 ++ foldParas
    let code (head stop : Nat × Nat) : Array Raw :=
      piecesRaws (listingAt starts) paras (assemble (withFolds folds (clipCode whole
        (starts.getD (head.1 - 1) 0) (starts.getD stop.1 src.size))))
    match showing.decls with
    | none =>
      let shown := if showing.code then folds else []
      let pieces := assemble (withStatements starts st.2.1 (withFolds shown whole))
      let body := piecesRaws (fun s t => if showing.code then listingAt starts s t else #[]) paras
        pieces
      (wrap body, notes ++ refused ++ st.2.2)
    | some _ =>
      let ds := f.decls.qsort fun a b => offsetOf starts a.start < offsetOf starts b.start
      let chosen (n : String) : Bool := (showing.decls.getD []).any (namedAs n)
      let around (k : Nat) : Array Raw := if stated.isSome then paras.getD k #[] else #[]
      let one (d : LeanFacts.Decl) (i : Nat) : Array Raw :=
        around i ++ (if showing.code then code d.head d.stop else #[]) ++ around (f.decls.size + i)
      let index (d : LeanFacts.Decl) : Nat := (f.decls.findIdx? (· == d)).getD 0
      let items := (ds.filter (chosen ·.name)).map (fun d => (offsetOf starts d.head, one d (index d))) ++
        (f.failed.filter (chosen ·.name)).map fun fl => (offsetOf starts fl.head, code fl.head fl.stop)
      let body := chosenRaws items
      let named := if showing.statements then #[] else unnamedNotes showing f request
      (wrap body, notes ++ refused ++ st.2.2 ++ named)

/-- The body with the reference list its documentation's citations call for: under the
documentation's own References heading where it has one, else at its end under its own heading;
in the declared style, else alpha, whose labels doc-gen4's follow. -/
@[expose] public def placedBody (acc : Acc) (refs : Option Refs) (style : Option String) : Array Raw :=
  let p : Pos := {}
  let named := style.getD "alpha"
  match refs with
  | some r => if !acc.cited then acc.body else
    match acc.refsAt with
    | some k =>
      let list : Array Raw := #[.par p, .ctrl Parse.markdownBibControl p, .group #[.word named p] p,
        .group #[.word r.path p] p]
      acc.body.extract 0 k ++ list ++ acc.body.extract k acc.body.size
    | none =>
      acc.body ++ #[.par p, .ctrl "bibliographystyle" p, .group #[.word named p] p,
        .ctrl "bibliography" p, .group #[.word r.path p] p]
  | none => acc.body

/-- A page without a bibliography is its pieces' raws alone. -/
public theorem placedBody_none (acc : Acc) (style : Option String) :
    placedBody acc none style = acc.body := rfl

/-- One spelling of a file a reference list names: its folders resolved and `.bib` dropped. -/
public def listedName (name : String) : String :=
  let t := name.trimAscii.toString
  let parts : Array String := (t.splitOn "/").foldl (init := #[]) fun out c =>
    if c.isEmpty || c == "." then out
    else if c == ".." && !out.isEmpty && out.back? != some ".." then out.pop
    else out.push c
  let joined := (if t.startsWith "/" then "/" else "") ++ "/".intercalate parts.toList
  if joined.endsWith ".bib" then (joined.dropEnd 4).toString else joined

/-- A list's files, `body` as written, with each of `names` it does not name already after them. -/
private def joinedFiles (names : Array String) (body : Array Raw) (pos : Pos) : Array Raw :=
  let own := Ir.bibSourceNames (rawSrc body).trimAscii.toString
  let extra := names.foldl (init := (#[] : Array String)) fun out n =>
    if n.contains ',' || (own ++ out).any (listedName · == listedName n) then out else out.push n
  if extra.isEmpty then body else #[.word (",".intercalate (own ++ extra).toList) pos]

/-- The raws with the first reference list naming files, `\bibliography`, biblatex's
`\printbibliography` or the markdown one, joined by `names`; `done` once one is. -/
private def joinList (names : Array String) (done : Bool) (out : Array Raw) :
    List Raw → Bool × Array Raw
  | [] => (done, out)
  | .ctrl "printbibliography" p :: rest =>
    if done then joinList names done (out.push (.ctrl "printbibliography" p)) rest
    else
      let added := names.foldl (init := out) fun out n =>
        (out.push (.ctrl "addbibresource" p)).push (.group #[.word n p] p)
      joinList names true (added.push (.ctrl "printbibliography" p)) rest
  | .ctrl n p :: .group st sp :: .group body gp :: rest =>
    if !done && n == Parse.markdownBibControl then
      joinList names true (((out.push (.ctrl n p)).push (.group st sp)).push
        (.group (joinedFiles names body gp) gp)) rest
    else if !done && n == "bibliography" then
      joinList names true ((out.push (.ctrl n p)).push (.group (joinedFiles names st sp) sp))
        (.group body gp :: rest)
    else joinList names done (out.push (.ctrl n p)) (.group st sp :: .group body gp :: rest)
  | .ctrl n p :: .group body gp :: rest =>
    if !done && n == "bibliography" then
      joinList names true ((out.push (.ctrl n p)).push (.group (joinedFiles names body gp) gp)) rest
    else joinList names done (out.push (.ctrl n p)) (.group body gp :: rest)
  | .ctrl n p :: .space :: .group body gp :: rest =>
    if !done && n == "bibliography" then
      joinList names true (((out.push (.ctrl n p)).push .space).push
        (.group (joinedFiles names body gp) gp)) rest
    else joinList names done (out.push (.ctrl n p)) (.space :: .group body gp :: rest)
  | .group body p :: rest =>
    let (done, inner) := joinList names done #[] body.toList
    joinList names done (out.push (.group inner p)) rest
  | .env n body p :: rest =>
    let (done, inner) := joinList names done #[] body.toList
    joinList names done (out.push (.env n inner p)) rest
  | r :: rest => joinList names done (out.push r) rest
termination_by l => sizeOf l
decreasing_by raws_dec

/-- The raws a citation command's keys stand in after its notes, `[…]` groups. -/
private def keysGroup : List Raw → Option (Array Raw)
  | .sym '[' _ :: .group _ _ :: .sym ']' _ :: rest => keysGroup rest
  | .group body _ :: _ => some body
  | _ => none

/-- The keys raws cite, `\nocite`'s among them, inside a group or an environment too, onto `out`. -/
private def citedList (out : Array String) : List Raw → Array String
  | [] => out
  | .ctrl n _ :: rest =>
    let out := if n.startsWith "cite" || n == "nocite" then
        match keysGroup rest with
        | some body => ((rawSrc body).splitOn ",").foldl (init := out) fun out k =>
            out.push k.trimAscii.toString
        | none => out
      else out
    citedList out rest
  | .group body _ :: rest => citedList (citedList out body.toList) rest
  | .env _ body _ :: rest => citedList (citedList out body.toList) rest
  | _ :: rest => citedList out rest
termination_by l => sizeOf l
decreasing_by raws_dec

/-- The keys raws cite. -/
public def citedKeys (raws : Array Raw) : Array String := citedList #[] raws.toList

/-- A document whose inclusions cite into the files `names`: its first reference list naming files
reads them too, after its own, so a key both hold is set from the document's. -/
public def joinBibliography (raws : Array Raw) (names : Array String) : Array Raw :=
  if names.isEmpty then raws else (joinList names false #[] raws.toList).2

/-- With no answer from Lean, a page shows the file's code, whatever its directive asks. -/
public theorem planOf_unanswered_exact (lang : Ir.CodeLang) (file text : String) :
    (planOf lang file text none).1.code = true := by
  simp [planOf]

/-- A code file read into the surface AST: documentation comments as markdown, code as listings,
each statement beside its declaration's code as the views order them, the title and directive as
the preamble's declarations, the file's name the title where no description opens on one. -/
@[expose] public def read (lang : Ir.CodeLang) (file text : String)
    (facts : Option LeanFacts.Facts := none) (place : LinkPlace := {}) (refs : Option Refs := none) :
    Array Raw × Array Diag :=
  let src := text.toList.toArray
  let starts := lineStarts src
  let showing := showingOf lang src
  let plan := planOf lang file text facts place
  let acc := readPieces lang file text (plan.1.citing (refs.map (·.keys))) plan.2.1
  let origin : Pos := {}
  let directive := match directive? lang src with
    | some (cut, value) =>
      let (line, col) := lineCol starts cut.start
      directiveRaws value { line, col }
    | none => #[]
  let titleRaws := acc.title.getD (Md.textRaws (baseName file) origin)
  let placed := placedBody acc refs showing.bibStyle
  let body := if acc.titled then placed else Parse.headingRaws .title titleRaws origin ++ placed
  let preamble : Array Raw := #[.ctrl "title" origin, .group titleRaws origin] ++ directive
  let stray := (strayDirective? lang src).map fun off =>
    let (line, col) := lineCol starts off
    Diag.of .W0387 "a leantex directive is read only on a file's first line, or the line after \
'#!'; this one stays as written" (some ⟨file, { line, col }⟩)
      (help := s!"move it to the file's first line, or the line after `#!`: `{directiveMarker lang} …`")
      (subject := some "code:directive")
  let views := showing.unknown.toArray.map fun n =>
    Diag.of .W0110 s!"`show` names '{n}', which is no view of this file; the page sets without it"
      (some ⟨file, directivePos lang src⟩)
      (help := s!"name {namesOr ((View.all.filter (·.setBy lang false)).map (·.name))}")
      (subject := some s!"code:show:{n}")
  let unread := showing.unread.toArray.map fun (k, v) =>
    Diag.of .W0110 s!"`{k}` takes no value '{v}'; the page sets as if it were not written"
      (some ⟨file, directivePos lang src⟩) (help := "write `proofs = show`, `collapse` or `remove`")
      (subject := some s!"code:{k}:{v}")
  let idle := showing.idle lang ⟨file, directivePos lang src⟩
  -- premise: Tests.UnusedSettings.metadataChecks — a page citing nothing reads none of these
  let uncited := if lang != .lean || refs.isNone || acc.cited then #[] else
    (#["bibliography", "biblio-style"].filter showing.written.contains).map fun k =>
      UnusedSetting.directiveDiag file k (directivePos lang src)
  (preamble.push (.env "document" body origin),
    views ++ unread ++ idle ++ uncited ++ acc.diags ++ plan.2.2 ++ stray.toArray)

private theorem ite_prefix (b : Bool) (x y : Array Raw) :
    (if b = true then x else y ++ x) = (if b = true then #[] else y) ++ x := by
  cases b <;> simp

/-- A code file's raws close on its document, whose body ends with its pieces' raws under the
page its plan sets, the reference list its citations call for placed among them. -/
public theorem read_body_exact (lang : Ir.CodeLang) (file text : String)
    (facts : Option LeanFacts.Facts) (place : LinkPlace) (refs : Option Refs) :
    ∃ head : Array Raw, (read lang file text facts place refs).1.back? =
      some (.env "document" (head ++ placedBody (readPieces lang file text
        ((planOf lang file text facts place).1.citing (refs.map (·.keys)))
        (planOf lang file text facts place).2.1) refs (showingOf lang text.toList.toArray).bibStyle)
        {}) := by
  unfold read
  simp only [Array.back?_push, ite_prefix]
  exact ⟨_, rfl⟩

end LeanTex.Core.Code
