module

public import LeanTex.Core.Elab
public import LeanTex.Core.BibStyle
import LeanTex.Core.MathParse

/-! The field reading a build gives its reference list. BibTeX and biber
write a `.bbl` that LaTeX reads in the document's own context, so a field's
`\url`, `\emph`, math, accents and quotes mean what they mean in the body:
the reading is the document's inline elaborator, in the context its body
opens with — the preamble's definitions, packages, styles and locale in
force. -/

namespace LeanTex.Core.Bib

/-- Text with no control word, environment or verbatim anywhere in it, a
group or a formula down included: nothing the compatibility pass reads,
which acts on control words and environments alone. -/
private def controlFree : List Parse.Raw → Bool
  | [] => true
  | .ctrl _ _ :: _ => false
  | .env _ _ _ :: _ => false
  | .verb _ _ _ :: _ => false
  | .group body _ :: rest => controlFree body.toList && controlFree rest
  | .math _ body _ :: rest => controlFree body.toList && controlFree rest
  | _ :: rest => controlFree rest
termination_by l => sizeOf l
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals
    (have hb : sizeOf body = 1 + sizeOf body.toList := by rfl
     omega)

/-- Control words the compatibility pass leaves as they stand in a field,
whatever arguments follow them: the text styles, URLs, accents, escapes,
letters and symbols the elaborator sets itself. A field whose every
control word is one of them skips the pass (`compatNeeded`), as text with
none does; `bibFieldDoorChecks` holds the two readings equal for each name,
in each argument shape a field gives one. -/
public def compatInert : List String :=
  ["emph", "textit", "textbf", "textsc", "texttt", "textsf", "textrm", "textsl", "textup",
   "textmd", "textnormal", "textsuperscript", "textsubscript", "url", "href",
   "'", "`", "^", "\"", "~", "=", ".", "u", "v", "H", "c", "d", "b", "r", "k", "t",
   "&", "%", "$", "#", "_", "{", "}", " ", ",", "-", "/",
   "o", "O", "ss", "aa", "AA", "ae", "AE", "l", "L", "i", "j", "oe", "OE",
   "dag", "S", "P", "copyright", "ldots", "dots", "TeX", "LaTeX", "textquoteleft",
   "textquoteright", "ensuremath", "sc", "it", "bf", "em", "tt", "rm", "sf"]

/-- Control words the compatibility pass leaves as they stand inside a
formula: each symbol the math parser sets as one atom (`MathParse.ctrlAtom`),
`\alpha` and `\leq` and the rest — a field's `$\alpha$` is no reason to run
the pass. `bibFieldDoorChecks` holds the two readings equal for each name,
in each formula shape a field gives one. -/
public def compatInertMath : Thunk (Std.HashSet String) :=
  Thunk.mk fun _ => MathParse.ctrlAtom.foldl (init := {}) fun s (n, _, _) => s.insert n

/-- Whether a field's text needs the compatibility pass: a control word
outside `compatInert` (inside a formula, outside `compatInertMath` too), an
environment or verbatim anywhere in it, a group or a formula down
included. -/
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
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals
    (have hb : sizeOf body = 1 + sizeOf body.toList := by rfl
     omega)

/-- The context a build reads its reference list's fields in, computed
once per document (`FieldDoor.of`): the body's opening plan and state
(`Elab.preparedBody`), and the preamble's definitions the compatibility
pass leaves for the elaborator to expand. A reading closes over one door;
a door built per field elaborated the whole preamble again for every field
the list read. -/
public structure FieldDoor.Context where
  plan : Elab.DocBodyPlan
  st0 : Elab.ESt
  inherited : List String

/-- A field door: its context, computed the first time a field needs the
elaborator and kept for every field after — a list whose every field reads
as written (`asWritten?`) never elaborates the preamble for it. -/
public structure FieldDoor where
  context : Thunk FieldDoor.Context

/-- The door of a prepared document. -/
public def FieldDoor.of (file : String) (p : Elab.Prepared) : FieldDoor :=
  { context := Thunk.mk fun _ =>
      let (plan, st0) := Elab.preparedBody file p
      -- a field's note numbers where its list stands (`Ir.numberNotesItems`)
      let st0 := { st0 with ctr := { st0.ctr with fnDefer := true } }
      { plan, st0, inherited := (plan.ctx.user.extract 0 plan.ctx.limit).toList.map (·.name) } }

/-- The noncharacters a field's `%`, and a URL argument's `$`, cross the
lexer as (U+FDD0 and U+FDD1, which Unicode reserves for a process's own use
and no text exchanges): characters the lexer reads as part of a word, set
back to `%` and `$` in the tokens. -/
private def percentMark : Char := '\uFDD0'

private def dollarMark : Char := '\uFDD1'

/-- A field's `%` read as the character it is, never as TeX's comment
character: BibTeX and biber hand a `.bib` value to LaTeX as the text it
spells, and LaTeX then drops the rest of the line after a `%` (BibTeX) or
stops at it (biber) — the author wrote the character. And a `$` inside a
`\url`, `\nolinkurl` or `\href` URL argument read as the character
url.sty and hyperref read there, never as a math shift TeX would pair with
a `$` outside the URL. Each `%` no backslash escapes travels the lexer as
`percentMark` and each such `$` as `dollarMark`; the count is of the `%`s
outside a URL argument, where url.sty reads a `%` as itself. `none` where
there is nothing to mark, or where the text already holds a mark, which
would not survive the return. -/
private def markReserved (s : String) : Option (String × Nat) := Id.run do
  if (!s.contains '%' && !s.contains '$') || s.contains percentMark || s.contains dollarMark then
    return none
  let cs := s.toList.toArray
  let mut out := ""
  let mut n := 0
  let mut marked := false
  -- the brace depth at which a URL argument opened, while inside one
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

/-- `markReserved`'s marks set back to the `%` and `$` they stand for, in
every token that can hold them. -/
private def unmarkReserved (toks : Array Lex.Token) : Array Lex.Token :=
  let holds (w : String) : Bool := w.contains percentMark || w.contains dollarMark
  let back (w : String) :=
    (w.replace (String.singleton percentMark) "%").replace (String.singleton dollarMark) "$"
  toks.map fun t => match t.tok with
    | .word w => if holds w then { t with tok := .word (back w) } else t
    | .verb env w => if holds w then { t with tok := .verb env (back w) } else t
    | _ => t

/-- A `$` no other `$` closes, read as the character it is: TeX pairs a
field's math shifts in order, so where their number is odd the last opens
a formula nothing ends — LaTeX stops there — and the author wrote a dollar
sign. The count is 1 where that `$` was the character. -/
private def literalDollar (toks : Array Lex.Token) : Array Lex.Token × Nat :=
  let shifts := toks.foldl (fun n t => if t.tok == .math then n + 1 else n) 0
  if shifts % 2 == 0 then (toks, 0)
  else
    let (out, _) := toks.foldl (init := (#[], 0)) fun (out, k) t =>
      if t.tok == .math then
        (out.push (if k + 1 == shifts then { t with tok := .word "$" } else t), k + 1)
      else (out.push t, k)
    (out, 1)

/-- Whether a field's running text holds a character TeX reserves there —
`&`, `#`, `^` or `_` outside every formula — anywhere a group or an
environment reaches: where the elaborator, reading the field as an
argument's tokens (`Elab.Ctx.argBody`), sets one as itself. -/
private def textSyms : List Parse.Raw → Bool
  | [] => false
  | .sym c _ :: rest => "&#^_".contains c || textSyms rest
  | .group body _ :: rest => textSyms body.toList || textSyms rest
  | .env _ body _ :: rest => textSyms body.toList || textSyms rest
  | _ :: rest => textSyms rest
termination_by l => sizeOf l
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals
    (have hb : sizeOf body = 1 + sizeOf body.toList := by rfl
     omega)

/-- One reserved character a field sets as itself, at the entry it stands
in: a note, since the page holds what the author wrote, named so a `.bib`
that must also build under LaTeX can be escaped. One subject per
character, so the run states each once with its count
(`Diag.tallySites`). -/
private def reservedNote (span : Span) (c : Char) : Diag :=
  let reads : String × String := match c with
    | '&' => ("as an alignment tab outside a table and stops there", "\\&")
    | '#' => ("as a macro parameter and stops there", "\\#")
    | '^' => ("as a superscript outside a formula and stops there", "\\^{}")
    | '_' => ("as a subscript outside a formula and stops there", "\\_")
    | '$' => ("as opening a formula no '$' closes and stops there", "\\$")
    | _ => ("as a comment and drops the rest of the line", "\\%")
  Diag.of .N0030 s!"'{c}' in a .bib field sets as the character; LaTeX reads it {reads.1}"
    (some span) (help := s!"write it '{reads.2}' if the .bib must also build with LaTeX")
    (subject := some s!"bibfield:reserved:{c}")

/-- A block's own text, run into a line: its inline content, after a space
where content stands before it. A leaf of `Ir.foldBlocks`, which reads a
list's items, a box's body and a float's in turn: what a field whose
markup the elaborator sets only between paragraphs sets in an entry
(`FieldDoor.readWith`). -/
private def runIn (acc : Array Ir.Inline) (b : Ir.Block) : Array Ir.Inline :=
  let put (acc xs : Array Ir.Inline) : Array Ir.Inline :=
    if xs.isEmpty then acc else if acc.isEmpty then xs else acc.push (.text " ") ++ xs
  match b with
  | .para c => put acc c
  | .section _ _ _ t => put acc t
  | .equation _ c => put acc c
  | .table _ _ _ rows _ _ => rows.foldl (fun acc row => row.foldl put acc) acc
  | .titled _ t _ => put acc t
  | .float _ _ _ _ c => put acc c
  | .verbatim _ s _ => put acc #[.text s]
  | _ => acc

/-- What a field's reading reports, settled: the inline reading's content
with its diagnostics, the marks and the notes, and the pictures it set
(`pics`), where none of its diagnostics is an error; else the blocks the
body would set (`blocks`, their pictures with them), where none of theirs
is; else the reading with no elaborator (`plain`), which sets no picture —
the refusal, either way, one warning (`unread`), the marks kept. Each
reading is a thunk, so a fallback runs only where the one before it
refused. -/
private def settle (inline : Unit → Array Ir.Inline) (ds : Array Diag)
    (pics : Unit → Array (String × String))
    (notes : Unit → Array Diag) (marks : Array Diag)
    (blocks : Unit → Array Ir.Inline × Array Diag × Array (String × String))
    (plain : Unit → Array Ir.Inline × FieldReport) (unread : Option String → Diag) :
    Array Ir.Inline × FieldReport :=
  match ds.find? (·.severity == .error) with
  | none => (inline (), { diags := ds ++ marks ++ notes (), pictures := pics () })
  | some refusal =>
    let b := blocks ()
    if b.2.1.any (·.severity == .error) then
      let p := plain ()
      (p.1, { diags := (p.2.diags ++ marks).push (unread (some refusal.message)) })
    else (b.1, { diags := (b.2.1 ++ marks).push (unread none), pictures := b.2.2 })

/-- A settled reading raises no error where its notes, marks, plain
reading and warning raise none: the inline reading's diagnostics pass only
where none is an error, and the blocks' only where none of theirs is. -/
private theorem settle_contract (inline : Unit → Array Ir.Inline) (ds : Array Diag)
    (pics : Unit → Array (String × String))
    (notes : Unit → Array Diag) (marks : Array Diag)
    (blocks : Unit → Array Ir.Inline × Array Diag × Array (String × String))
    (plain : Unit → Array Ir.Inline × FieldReport) (unread : Option String → Diag)
    (hn : (notes ()).any (·.severity == .error) = false)
    (hm : marks.any (·.severity == .error) = false)
    (hp : (plain ()).2.diags.any (·.severity == .error) = false)
    (hu : ∀ c, ((unread c).severity == .error) = false) :
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
  | some refusal =>
    by_cases hb : (blocks ()).2.1.any (·.severity == .error) = true
    · simp only [hb, ↓reduceIte, Array.any_push, Array.any_append, hp, hm, hu, Bool.or_false]
    · simp only [Bool.not_eq_true] at hb
      simp only [hb, Bool.false_eq_true, ↓reduceIte, Array.any_push, Array.any_append, hm, hu,
        Bool.or_false]

/-- Reserved characters' notes raise no error. -/
private theorem reservedNotes_ship (span : Span) (cs : Array Char) :
    (cs.map (reservedNote span)).any (·.severity == .error) = false := by
  rw [Bool.eq_false_iff]
  intro ha
  obtain ⟨d, hd, he⟩ := Array.any_eq_true'.mp ha
  obtain ⟨c, _, rfl⟩ := Array.mem_map.mp hd
  rw [show (reservedNote span c).severity = DiagCode.N0030.loss.severity from
    Diag.of_severity_full .N0030 _ _ _ _ _ _ _ _, DiagCode.fieldReading_ships.2.2] at he
  exact Bool.false_ne_true he

/-- The document's inline elaborator over one field's text, where the body
begins (the door's plan and state): the text lexed and parsed as the
`.bib`'s, translated by the compatibility pass the body's text went
through — the fragment door a `\style` value enters by, the preamble's
definitions left for the elaborator to expand; text with no control word
skips it, as there is nothing in it to translate, and so, unless
`alwaysCompat`, does text whose every control word the pass leaves as it
stands (`compatNeeded`) — its sites the entry's
own, elaborated as inline content with what that reported, and its source
wrappers erased: a reference-list entry carries no source spans, as before
it was elaborated. A character TeX reserves is the character it is, as an
argument's are (`Elab.Ctx.argBody`, `markReserved`, `literalDollar`): the
field always sets, and each such character is named once
(`reservedNote`), counted for `&`, `#`, `^` and `_` by the elaborator's
own reading — where it would have refused one. Every field starts from
the same state, so the reading is a function of the place and the text.

A field the inline reading refuses — an error, which LaTeX, reading the
`.bbl` in a paragraph, does not raise — never fails the build: the field
reads as the blocks the body would set, run into the entry as their text
(`runIn`), or, where those raise an error too, through the reading with no
elaborator (`plainField`), and one warning names it (W0429,
`unreadDiag`) in place of the refusal: no diagnostic the reading reports
is an error (`readWith_ships_contract`). -/
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
  let ctx := { d.plan.ctx with file := span.file, argBody := true }
  let inline := translated alwaysCompat
  let read := (Elab.elabInlines ctx inline.2.1).run d.st0
  let ds := lexed.2 ++ parsed.2 ++ inline.2.2 ++
    read.2.diags.extract d.st0.diags.size read.2.diags.size
  let marks := (List.replicate ((mark.map (·.2)).getD 0) '%' ++
    List.replicate literal.2 '$').toArray.map (reservedNote span)
  -- What the field's own reading set as itself, by the strict reading over
  -- the field's own positions: each `&`, `#`, `^` or `_` it refuses.
  let syms (_ : Unit) : Array Char := if !textSyms inline.1.toList then #[] else
    let strict := ((Elab.elabInlines { ctx with argBody := false } inline.1).run d.st0).2
    (strict.diags.extract d.st0.diags.size strict.diags.size).filterMap fun dg =>
      if dg.kind != .E0311 then none
      else match (dg.span.bind (·.pos.command)).map (·.toList) with
        | some [c] => if "&#^_".contains c then some c else none
        | _ => none
  -- The blocks the body would set, run into the entry as their text.
  let blocks (_ : Unit) : Array Ir.Inline × Array Diag × Array (String × String) :=
    let (_, rebased, cds) := translated true
    let (bs, bst) := (Elab.elabBlocks ctx rebased).run d.st0
    (Ir.eraseLocationInlines (Ir.foldBlocks runIn (fun acc _ => acc) #[] bs),
      lexed.2 ++ parsed.2 ++ cds ++ bst.diags.extract d.st0.diags.size bst.diags.size,
      bst.pictures.extract d.st0.pictures.size bst.pictures.size)
  -- The boundary pictures the field set, as the body's are recorded: what
  -- the document's request carries for the image each one stands as.
  let pics (_ : Unit) : Array (String × String) :=
    read.2.pictures.extract d.st0.pictures.size read.2.pictures.size
  settle (fun _ => Ir.eraseLocationInlines read.1) ds pics
    (fun _ => (syms ()).map (reservedNote span))
    marks blocks (fun _ => plainField src) (unreadDiag span src)

/-- **A field's reading never fails the build**: whatever its text and the
document around it, no diagnostic the reading reports is an error. A
refusal by the inline reading is the warning naming the field (W0429), the
field set by the blocks the body would set or by the reading with no
elaborator, which names only a formula's floor (W0012,
`plainField_ships_contract`); a reserved character is a note (N0030). -/
public theorem FieldDoor.readWith_ships_contract (door : FieldDoor) (alwaysCompat : Bool)
    (span : Span) (src : String) :
    (door.readWith alwaysCompat span src).2.diags.any (·.severity == .error) = false :=
  settle_contract _ _ _ _ _ _ _ _ (reservedNotes_ship span _) (reservedNotes_ship span _)
    (plainField_ships_contract src) (unreadDiag_ships span src)

/-- The reading a build gives a field (`readWith`), the compatibility pass
skipped where the field needs none (`compatNeeded`). -/
public def FieldDoor.readFull (d : FieldDoor) : FieldReading := d.readWith false

/-- A field text the elaborator sets exactly as written: ASCII letters and
digits, white space, a lone hyphen, the punctuation TeX prints as itself,
and brace groups, which only protect a title's case and set nothing — no
control sequence, math, tie, quote or dash ligature, or reserved character
— read with its braces dropped, its white space runs one space and its ends
trimmed. Most fields of a large `.bib` are such text, and the build reads
them without running the elaborator (`bibAsWrittenChecks` holds the two
readings equal). -/
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
    -- a dash ligature, and white space at a group's edge, are the
    -- elaborator's to read
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

/-- **The document's own inline elaborator, as a field reading**: a field's
text, its surrounding white space trimmed as BibTeX's and biber's readers
trim a value, as the body would set it (`FieldDoor.readFull`), its plain
spellings read without the elaborator (`asWritten?`). -/
public def FieldDoor.read (d : FieldDoor) : FieldReading := fun span src =>
  let src := src.trimAscii.toString
  match asWritten? src with
  | some t => (if t.isEmpty then #[] else #[.text t], {})
  | none => d.readFull span src

/-- **The reading a build gives a field never fails it**: a plain spelling
reports nothing, and every other field is read by `readWith`
(`readWith_ships_contract`). -/
public theorem FieldDoor.read_ships_contract (door : FieldDoor) (span : Span) (src : String) :
    (door.read span src).2.diags.any (·.severity == .error) = false := by
  unfold FieldDoor.read
  dsimp only
  cases asWritten? src.trimAscii.toString with
  | some t => simp
  | none => exact door.readWith_ships_contract false span _

/-- The bibliography resolution a build runs: `apply`, every field read by
the document's own elaborator through its door (`FieldDoor.read`), the door
built once. The driver and the test harness both resolve through this one
definition. -/
public def resolve (file : String) (p : Elab.Prepared) (sources : Array (String × String))
    (doc : Ir.Doc) : Ir.Doc × Array Diag :=
  let door := FieldDoor.of file p
  apply sources doc door.read

/-- W0349 over the document a build ships, as the driver judges it: the
body's references and the lists' at once (`Ir.refDiags`, whose census reads
a reference list's entries with the body), each key at the body's first
site, or, for a key only a list's entries hold, at the list's command
(`refSpanOf`). -/
public def refJudge (spans : Elab.ReqSpans) (doc : Ir.Doc) : Array Diag :=
  Ir.refDiags spans.labels
    (refSpanOf (Elab.ReqSpans.spanOf spans.refs) (spans.bib[0]?.map (·.2))
      (listRefKeys doc false)) doc

/-- A build's front-end diagnostics, accounted as the driver accounts them:
the body's, the reference list's — a loss a list repeats after the body
named it a note (`demoteRepeated`) — the input encoding's notes, then the
reference judge's over the resolved document (`refJudge`), every site
tallied together (`Diag.tallySites`). The driver and the test harness both
account through this one definition. -/
public def accountFront (body bib notes refs : Array Diag) : Array Diag :=
  Diag.tallySites (body ++ demoteRepeated body bib ++ notes ++ refs)

end LeanTex.Core.Bib
