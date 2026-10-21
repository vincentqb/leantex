module

public import LeanTex.Core.Elab
public import LeanTex.Core.BibStyle
import LeanTex.Core.MathParse

/-! The field reading a build gives its reference list: each field read by the
document's own elaborator, as LaTeX reads a `.bbl`. -/

namespace LeanTex.Core.Bib

/-- Whether text holds no control word, environment or
verbatim anywhere in it. -/
private def controlFree : List Parse.Raw → Bool
  | [] => true
  | .ctrl _ _ :: _ => false
  | .env _ _ _ :: _ => false
  | .verb _ _ _ :: _ => false
  | .group body _ :: rest => controlFree body.toList && controlFree rest
  | .math _ body _ :: rest => controlFree body.toList && controlFree rest
  | _ :: rest => controlFree rest
termination_by l => sizeOf l
decreasing_by raws_dec

/-- Control words the compatibility pass leaves as they stand in a field. -/
public def compatInert : List String :=
  ["emph", "textit", "textbf", "textsc", "texttt", "textsf", "textrm", "textsl", "textup",
   "textmd", "textnormal", "url", "href",
   "'", "`", "^", "\"", "~", "=", ".", "u", "v", "H", "c", "d", "b", "r", "k", "t",
   "&", "%", "$", "#", "_", "{", "}", " ", ",", "-", "/",
   "o", "O", "ss", "aa", "AA", "ae", "AE", "l", "L", "i", "j", "oe", "OE",
   "dag", "S", "P", "copyright", "ldots", "dots", "TeX", "LaTeX", "textquoteleft",
   "textquoteright", "ensuremath", "em"]

/-- Control words the compatibility pass leaves as they
stand inside a formula. -/
public def compatInertMath : Thunk (Std.HashSet String) :=
  Thunk.mk fun _ => MathParse.ctrlAtom.foldl (init := {}) fun s (n, _, _) => s.insert n

/-- Whether a field's text needs the compatibility pass. -/
private def compatNeeded (inMath : Bool) : List Parse.Raw → Bool
  | [] => false
  | .ctrl n _ :: rest =>
    !(compatInert.contains n || (inMath && compatInertMath.get.contains n)) ||
      compatNeeded inMath rest
  | .env _ _ _ :: _ => true
  | .verb _ _ _ :: _ => true
  | .group body _ :: rest => compatNeeded inMath body.toList || compatNeeded inMath rest
  | .math _ body _ :: rest => compatNeeded true body.toList || compatNeeded inMath rest
  | _ :: rest => compatNeeded inMath rest
termination_by l => sizeOf l
decreasing_by raws_dec

/-- The context a build reads its reference list's fields
in, computed once per document. -/
public structure FieldDoor.Context where
  plan : Elab.DocBodyPlan
  st0 : Elab.ESt
  inherited : List String

/-- A field door: its context, computed the first time a
field needs the elaborator. -/
public structure FieldDoor where
  context : Thunk FieldDoor.Context

public def FieldDoor.of (file : String) (p : Elab.Prepared) : FieldDoor :=
  { context := Thunk.mk fun _ =>
      let (plan, st0) := Elab.preparedBody file p
      -- A field's note numbers where its list stands.
      let st0 := { st0 with ctr := { st0.ctr with fnDefer := true } }
      { plan, st0, inherited := (plan.ctx.user.extract 0 plan.ctx.limit).toList.map (·.name) } }

/-- The noncharacter a field's `%` crosses the lexer as. -/
private def percentMark : Char := '\uFDD0'

private def dollarMark : Char := '\uFDD1'

/-- A field's `%` read as the character it is, never as
TeX's comment character. -/
private def markReserved (s : String) : Option (String × Nat) := Id.run do
  if (!s.contains '%' && !s.contains '$') || s.contains percentMark || s.contains dollarMark then
    return none
  let cs := s.toList.toArray
  let mut out := ""
  let mut n := 0
  let mut marked := false
  let mut urlDepth : Option Nat := none
  let mut depth := 0
  let mut i := 0
  for _ in [0:cs.size + 1] do
    if h : i < cs.size then
      let c := cs[i]
      if c == '\\' then
        let mut j := i + 1
        for _ in [i + 1:cs.size] do
          if (cs[j]?.map Char.isAlpha).getD false then j := j + 1 else break
        if j == i + 1 then
          out := out.push c
          if let some d := cs[i + 1]? then out := out.push d
          i := i + 2
        else
          let name := String.ofList (cs.extract (i + 1) j).toList
          out := out ++ "\\" ++ name
          if urlDepth.isNone && (name == "url" || name == "nolinkurl" || name == "href") then
            -- TeX skips the spaces between a control word and its argument
            let mut k := j
            for _ in [j:cs.size] do
              if (cs[k]?.map fun c => c == ' ' || c == '\t' || c == '\n').getD false then k := k + 1
              else break
            if cs[k]? == some '{' then urlDepth := some depth
          i := j
      else
        if c == '{' then depth := depth + 1
        if c == '}' then
          depth := depth - 1
          if urlDepth == some depth then urlDepth := none
        if c == '%' then
          out := out.push percentMark
          marked := true
          if urlDepth.isNone then n := n + 1
        else if c == '$' && urlDepth.isSome then
          out := out.push dollarMark
          marked := true
        else out := out.push c
        i := i + 1
    else break
  return if marked then some (out, n) else none

/-- `markReserved`'s marks set back to the `%` and `$` they stand for. -/
private def unmarkReserved (toks : Array Lex.Token) : Array Lex.Token :=
  let holds (w : String) : Bool := w.contains percentMark || w.contains dollarMark
  let back (w : String) :=
    (w.replace (String.singleton percentMark) "%").replace (String.singleton dollarMark) "$"
  toks.map fun t => match t.tok with
    | .word w => if holds w then { t with tok := .word (back w) } else t
    | .verb env w => if holds w then { t with tok := .verb env (back w) } else t
    | _ => t

/-- A `$` no other `$` closes, read as the character it is. -/
private def literalDollar (toks : Array Lex.Token) : Array Lex.Token × Nat :=
  let shifts := toks.foldl (fun n t => if t.tok == .math then n + 1 else n) 0
  if shifts % 2 == 0 then (toks, 0)
  else
    let (out, _) := toks.foldl (init := (#[], 0)) fun (out, k) t =>
      if t.tok == .math then
        (out.push (if k + 1 == shifts then { t with tok := .word "$" } else t), k + 1)
      else (out.push t, k)
    (out, 1)

/-- Whether a field's running text holds `&`, `#`, `^` or
`_` outside every formula. -/
private def textSyms : List Parse.Raw → Bool
  | [] => false
  | .sym c _ :: rest => "&#^_".contains c || textSyms rest
  | .group body _ :: rest => textSyms body.toList || textSyms rest
  | .env _ body _ :: rest => textSyms body.toList || textSyms rest
  | _ :: rest => textSyms rest
termination_by l => sizeOf l
decreasing_by raws_dec

/-- The note for one reserved character a field sets as itself. -/
private def reservedNote (span : Span) (c : Char) : Diag :=
  let reads : String × String := match c with
    | '&' => ("as an alignment tab outside a table and stops there", "\\&")
    | '#' => ("as a macro parameter and stops there", "\\#")
    | '^' => ("as a superscript outside a formula and stops there", "\\^{}")
    | '_' => ("as a subscript outside a formula and stops there", "\\_")
    | '$' => ("as opening a formula no '$' closes and stops there", "\\$")
    | _ => ("as a comment and drops the rest of the line", "\\%")
  Diag.of .N0030 (Diag.say .N0030 .character (Diag.Name.of c.toString)) (some span)
    (help := s!"LaTeX reads it {reads.1}: write it '{reads.2}' if the .bib must also build with LaTeX")
    (subject := some s!"bibfield:reserved:{c}")

/-- A block's own text, run into a line. -/
private def runIn (acc : Array Ir.Inline) (b : Ir.Block) : Array Ir.Inline :=
  let put (acc xs : Array Ir.Inline) : Array Ir.Inline :=
    if xs.isEmpty then acc else if acc.isEmpty then xs else acc.push (.text " ") ++ xs
  match b with
  | .para c => put acc c
  | .section _ _ _ t => put acc t
  | .equation _ c => put acc c
  | .table _ _ _ rows _ _ =>
    let cell (c : Array Ir.Block) : Array Ir.Inline := match Ir.cellLine? c with
      | some xs => xs
      | none => #[.text (" ".intercalate (c.toList.map fun b => Ir.blocksText #[b]))]
    rows.foldl (fun acc row => row.foldl (fun acc c => put acc (cell c)) acc) acc
  | .titled _ t _ => put acc t
  | .disclosure s _ _ => put acc s
  | .float _ _ _ _ c => put acc c
  | .verbatim _ s _ => put acc #[.text s]
  | _ => acc

/-- What a field's reading reports, settled: the inline reading where none of
its diagnostics is an error, else the blocks run in, else the plain reading. -/
private def settle (inline : Unit → Array Ir.Inline) (ds : Array Diag)
    (pics : Unit → Array (String × Ir.PicSrc))
    (notes : Unit → Array Diag) (marks : Array Diag)
    (blocks : Unit → Array Ir.Inline × Array Diag × Array (String × Ir.PicSrc))
    (plain : Unit → Array Ir.Inline × FieldReport) (unread : Diag) :
    Array Ir.Inline × FieldReport :=
  match ds.find? (·.severity == .error) with
  | none => (inline (), { diags := ds ++ marks ++ notes (), pictures := pics () })
  | some _ =>
    let b := blocks ()
    if b.2.1.any (·.severity == .error) then
      let p := plain ()
      (p.1, { diags := (p.2.diags ++ marks).push unread })
    else (b.1, { diags := (b.2.1 ++ marks).push unread, pictures := b.2.2 })

private theorem settle_contract (inline : Unit → Array Ir.Inline) (ds : Array Diag)
    (pics : Unit → Array (String × Ir.PicSrc))
    (notes : Unit → Array Diag) (marks : Array Diag)
    (blocks : Unit → Array Ir.Inline × Array Diag × Array (String × Ir.PicSrc))
    (plain : Unit → Array Ir.Inline × FieldReport) (unread : Diag)
    (hn : (notes ()).any (·.severity == .error) = false)
    (hm : marks.any (·.severity == .error) = false)
    (hp : (plain ()).2.diags.any (·.severity == .error) = false)
    (hu : (unread.severity == .error) = false) :
    (settle inline ds pics notes marks blocks plain unread).2.diags.any
      (·.severity == .error) = false := by
  unfold settle
  cases h : ds.find? (·.severity == .error) with
  | none =>
    have hds : ds.any (·.severity == .error) = false := by
      rw [Array.find?_eq_none] at h
      rw [Bool.eq_false_iff]
      intro ha
      obtain ⟨x, hx, he⟩ := Array.any_eq_true'.mp ha
      exact h x hx he
    simp only [Array.any_append, hds, hm, hn, Bool.or_false]
  | some _ =>
    by_cases hb : (blocks ()).2.1.any (·.severity == .error) = true
    · simp only [hb, ↓reduceIte, Array.any_push, Array.any_append, hp, hm, hu, Bool.or_false]
    · simp only [Bool.not_eq_true] at hb
      simp only [hb, Bool.false_eq_true, ↓reduceIte, Array.any_push, Array.any_append, hm, hu,
        Bool.or_false]

private theorem reservedNotes_ship (span : Span) (cs : Array Char) :
    (cs.map (reservedNote span)).any (·.severity == .error) = false := by
  rw [Bool.eq_false_iff]
  intro ha
  obtain ⟨d, hd, he⟩ := Array.any_eq_true'.mp ha
  obtain ⟨c, _, rfl⟩ := Array.mem_map.mp hd
  rw [show (reservedNote span c).severity = DiagCode.N0030.loss.severity from
    Diag.of_severity_full .N0030 _ _ _ _ _ _ _ _, DiagCode.fieldReading_ships.2.2] at he
  exact Bool.false_ne_true he

/-- The document's inline elaborator over one field's text,
where the body begins. -/
public def FieldDoor.readWith (door : FieldDoor) (alwaysCompat : Bool) : FieldReading :=
    fun span src =>
  let d := door.context.get
  let mark := markReserved src
  let lexed := Lex.lex span.file ((mark.map (·.1)).getD src)
  let toks := if mark.isSome then unmarkReserved lexed.1 else lexed.1
  let literal := literalDollar toks
  let parsed := Parse.parse span.file literal.1
  let raws := parsed.1
  let translated (always : Bool) : Array Parse.Raw × Array Parse.Raw × Array Diag :=
    let skip := if always then controlFree raws.toList else !compatNeeded false raws.toList
    let (rs, compatDs, warned) := if skip then (raws, #[], d.st0.warnedUnknown)
      else Compat.rewrite span.file raws (warned := d.st0.warnedUnknown) (inherited := d.inherited)
    let (here, textDs, _) := Compat.rewriteText span.file rs warned
    (here, here.map (Compat.rebase (fun _ => span.pos) true), compatDs ++ textDs)
  -- A field is TeX whatever the document's own surface.
  let ctx := { d.plan.ctx with file := span.file, argBody := true, surface := .tex, kept := false }
  let inline := translated alwaysCompat
  let read := (Elab.elabInlines ctx inline.2.1).run d.st0
  let ds := lexed.2 ++ parsed.2 ++ inline.2.2 ++
    read.2.diags.extract d.st0.diags.size read.2.diags.size
  let marks := (List.replicate ((mark.map (·.2)).getD 0) '%' ++
    List.replicate literal.2 '$').toArray.map (reservedNote span)
  let syms (_ : Unit) : Array Char := if !textSyms inline.1.toList then #[] else
    let strict := ((Elab.elabInlines { ctx with argBody := false } inline.1).run d.st0).2
    (strict.diags.extract d.st0.diags.size strict.diags.size).filterMap fun dg =>
      if dg.kind != .E0311 then none
      else match (dg.span.bind (·.pos.command)).map (·.toList) with
        | some [c] => if "&#^_".contains c then some c else none
        | _ => none
  let blocks (_ : Unit) : Array Ir.Inline × Array Diag × Array (String × Ir.PicSrc) :=
    let (_, rebased, cds) := translated true
    let (bs, bst) := (Elab.elabBlocks ctx rebased).run d.st0
    (Ir.eraseLocationInlines (Ir.foldBlocks runIn (fun acc _ => acc) #[] bs),
      lexed.2 ++ parsed.2 ++ cds ++ bst.diags.extract d.st0.diags.size bst.diags.size,
      bst.pictures.extract d.st0.pictures.size bst.pictures.size)
  let pics (_ : Unit) : Array (String × Ir.PicSrc) :=
    read.2.pictures.extract d.st0.pictures.size read.2.pictures.size
  settle (fun _ => Ir.eraseLocationInlines read.1) ds pics
    (fun _ => (syms ()).map (reservedNote span))
    marks blocks (fun _ => plainField src) (unreadDiag span src)

public theorem FieldDoor.readWith_ships_contract (door : FieldDoor) (alwaysCompat : Bool)
    (span : Span) (src : String) :
    (door.readWith alwaysCompat span src).2.diags.any (·.severity == .error) = false :=
  settle_contract _ _ _ _ _ _ _ _ (reservedNotes_ship span _) (reservedNotes_ship span _)
    (plainField_ships_contract src) (unreadDiag_ships span src)

/-- The reading a build gives a field, the compatibility
pass skipped where the field needs none. -/
public def FieldDoor.readFull (d : FieldDoor) : FieldReading := d.readWith false

/-- A field text the elaborator sets exactly as written. -/
public def asWritten? (s : String) : Option String := Id.run do
  let ws (c : Char) : Bool := c == ' ' || c == '\n' || c == '\t' || c == '\r'
  let ok (c : Char) : Bool :=
    (c.toNat < 128 && c.isAlphanum) || ws c || ".,;:!?()/+=*@-{}".contains c
  let mut out := ""
  let mut depth : Nat := 0
  let mut prev : Char := ' '
  let mut pendingSpace := false
  for c in s.toList do
    unless ok c do return none
    if c == '-' && prev == '-' then return none
    if (prev == '{' && ws c) || (ws prev && c == '}') then return none
    if c == '{' then depth := depth + 1
    else if c == '}' then
      if depth == 0 then return none
      depth := depth - 1
    else if ws c then pendingSpace := !out.isEmpty
    else
      if pendingSpace then out := out.push ' '
      pendingSpace := false
      out := out.push c
    prev := c
  if depth != 0 then return none
  return some out

/-- The document's own inline elaborator as a field reading. -/
public def FieldDoor.read (d : FieldDoor) : FieldReading := fun span src =>
  let src := src.trimAscii.toString
  match asWritten? src with
  | some t => (if t.isEmpty then #[] else #[.text t], {})
  | none => d.readFull span src

public theorem FieldDoor.read_ships_contract (door : FieldDoor) (span : Span) (src : String) :
    (door.read span src).2.diags.any (·.severity == .error) = false := by
  unfold FieldDoor.read
  dsimp only
  cases asWritten? src.trimAscii.toString with
  | some t => simp
  | none => exact door.readWith_ships_contract false span _

/-- The bibliography resolution a build runs, every field
read by the document's own elaborator. -/
public def resolve (file : String) (p : Elab.Prepared) (sources : Array (String × String))
    (doc : Ir.Doc) (sites : Array Ir.CiteSite := #[]) : Ir.Doc × Array Diag :=
  let door := FieldDoor.of file p
  apply sources doc door.read sites

/-- W0349 over the document a build ships, as the driver judges it. -/
public def refJudge (spans : Elab.ReqSpans) (doc : Ir.Doc) : Array Diag :=
  Ir.refDiags spans.labels
    (refSpanOf (Elab.ReqSpans.spanOf spans.refs) (spans.bib[0]?.map (·.2))
      (listRefKeys doc false)) doc

/-- A build's front-end diagnostics, accounted as the driver accounts them. -/
public def accountFront (body bib notes refs : Array Diag) : Array Diag :=
  Diag.tallySites (body ++ demoteRepeated body bib ++ notes ++ refs)

end LeanTex.Core.Bib
