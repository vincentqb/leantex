module

public import LeanTex.Core.Bib
public import LeanTex.Core.Ir
public import Std.Data.HashMap
import LeanTex.Core.MathParse

/-! How a field's TeX text becomes inline content. A reference list is body
text to LaTeX — BibTeX and biber write a `.bbl` the document reads in its
own context — so a field's `\url`, `\emph`, math and accents mean what they
mean in the body. The build reads them through the document's own inline
elaborator (`FieldText`, supplied by the driver, `Bib.FieldDoor.read`); a
document with no source context — an IR built by hand — reads them through
`plainField`, the reading that needs no elaborator. Verbatim fields (`url`,
`doi`, `eprint`) are never text to elaborate: `urlText` reads them as `\url`
reads its argument. -/

namespace LeanTex.Core.Bib

/-- What reading a field reported beside its content: the diagnostics, and
the boundary pictures it set — `(id, body)`, the pairs a document's request
carries (`Ir.Doc.pictureSrcs`): a field's `\tikz` is drawn where the body's
is, so the list adds its pictures to the document's as the body's own are
added. Two reports append in reading order. -/
public structure FieldReport where
  diags : Array Diag := #[]
  pictures : Array (String × String) := #[]
  deriving Inhabited, BEq

public instance : Append FieldReport :=
  ⟨fun a b => { diags := a.diags ++ b.diags, pictures := a.pictures ++ b.pictures }⟩

/-- A field's TeX text as inline content, with what reading it reported. -/
public abbrev FieldText := String → Array Ir.Inline × FieldReport

/-- The field reading for the entry that stands at a place in its `.bib`:
what a reading reports, and the sites of what it reads, are that entry's. -/
public abbrev FieldReading := Span → FieldText

/-- What a reference list has read of its field texts so far, by text: a
reading is a function of the place and the text, the place only naming
where what it reported stands — which the list sets to the entry reading
it — so one text is read once however many entries spell it. -/
public abbrev FieldCache := Std.HashMap String (Array Ir.Inline × FieldReport)

/-- A field's text through a reading, answered from the cache where the
text was read before. -/
public def FieldCache.read (cache : FieldCache) (cv : FieldText) (s : String) :
    (Array Ir.Inline × FieldReport) × FieldCache :=
  match cache.get? s with
  | some r => (r, cache)
  | none =>
    let r := cv s
    (r, cache.insert s r)

/-- A stored value split at its `$…$` spans: `(true, source)` for each span,
`(false, text)` between them. An escaped `\$` is text, and an unclosed span
keeps its dollar and stays text. -/
private def mathSpans (v : String) : Array (Bool × String) := Id.run do
  let cs := v.toList.toArray
  let mut out : Array (Bool × String) := #[]
  let mut cur := ""
  let mut inMath := false
  let mut i := 0
  for _ in [0:cs.size + 1] do
    if h : i < cs.size then
      let c := cs[i]
      if c == '\\' then
        cur := cur.push c
        if let some d := cs[i + 1]? then cur := cur.push d
        i := i + 2
      else if c == '$' then
        unless cur.isEmpty do out := out.push (inMath, cur)
        cur := ""
        inMath := !inMath
        i := i + 1
      else
        cur := cur.push c
        i := i + 1
    else break
  let tail := if inMath then "$".append cur else cur
  return if tail.isEmpty then out else out.push (false, tail)

/-- One `$…$` span as the elaborator sets inline math: the math parser's
atoms when it can model the span, else the span's floor, which the reading
names (W0012). -/
private def formulaOf (src : String) : Ir.Inline :=
  let (toks, _) := Lex.lex "" ("$" ++ src ++ "$")
  match (Parse.parse "" toks).1.toList with
  | [.math false body _] =>
    match MathParse.parseMath false body with
    | .ok (l, _) => .formula false (Parse.rawSrc body) l
    | .error _ => .math false (Parse.rawSrc body)
  | _ => .math false src

/-- A stored value read without an elaborator: the plain text `text` reads,
then the body's typographic punctuation (`Ir.smartPunct`: TeX's quote and
dash ligatures), each `$…$` span a formula. -/
public def fieldInlines (v : String) : Array Ir.Inline := Id.run do
  let spans := mathSpans v
  let mut out : Array Ir.Inline := #[]
  let mut pending := ""
  for (math, s) in spans, k in [0:spans.size] do
    if math then
      unless pending.isEmpty do out := out.push (.text (Ir.smartPunct pending))
      pending := ""
      out := out.push (formulaOf s)
    else
      let t := textSpan s (lead := k != 0)
      pending := pending ++ (if k + 1 == spans.size then t.trimAsciiEnd.toString else t)
  unless pending.isEmpty do out := out.push (.text (Ir.smartPunct pending))
  return out

/-- What a formula the math parser cannot model is named by in a field
read with no elaborator (W0012), keyed by its spelling. -/
private def mathFloorDiag (src : String) : Diag :=
  Diag.of .W0012 s!"math in a reference-list entry is not rendered yet; the formula sets as \
    its text content" (subject := some ("math:" ++ src))

/-- The reading with no elaborator behind it (`fieldInlines`): a formula
the math parser cannot model sets as its floor and is named once by its
spelling (W0012), as the elaborator names one in the body. -/
public def plainField : FieldText := fun v =>
  let out := fieldInlines v
  (out, { diags := (Ir.foldInlines (fun acc x => match x with
    | .math _ src => acc.push src
    | _ => acc) #[] out).map mathFloorDiag })

/-- **The reading with no elaborator raises no error**: it names a formula
it sets as its floor, and nothing else (`plainField`), so a field it reads
never fails a build. -/
public theorem plainField_ships_contract (v : String) :
    (plainField v).2.diags.any (·.severity == .error) = false := by
  rw [Bool.eq_false_iff]
  intro ha
  obtain ⟨d, hd, he⟩ := Array.any_eq_true'.mp ha
  obtain ⟨src, _, rfl⟩ := Array.mem_map.mp hd
  rw [show (mathFloorDiag src).severity = DiagCode.W0012.loss.severity from
    Diag.of_severity_full .W0012 _ _ _ _ _ _ _ _, DiagCode.fieldReading_ships.2.1] at he
  exact Bool.false_ne_true he

/-- `plainField` wherever the entry stands. -/
public def plainReading : FieldReading := fun _ => plainField

/-- The words a refused field's diagnostic opens with until the list names
the field it stands for (`nameUnread`). -/
private def unreadWho : String := "a .bib field"

/-- A field the document's elaborator refused where an entry stands, set
as its text (W0429): the blocks the body would set read run into the entry
where `cause` is none, else, where those did not read either, the reading
with no elaborator, and the refusal's own words. The field's text is the
literal it stands for (`trigger`), keyed by it until the list names the
field (`nameUnread`). -/
public def unreadDiag (span : Span) (src : String) (cause : Option String) : Diag :=
  let what := match cause with
    | none => "holds markup this engine sets only between paragraphs; it sets as its text, \
        run into the entry"
    | some c => s!"is not TeX this engine sets in an entry ({c}); it sets as its plain text"
  Diag.of .W0429 s!"{unreadWho} {what}" (some span)
    (subject := some ("bibfield:unread:" ++ src)) (trigger := some src)

/-- A refused field's diagnostic is a warning, never an error. -/
public theorem unreadDiag_ships (span : Span) (src : String) (cause : Option String) :
    ((unreadDiag span src cause).severity == .error) = false := by
  rw [show (unreadDiag span src cause).severity = DiagCode.W0429.loss.severity from
    Diag.of_severity_full .W0429 _ _ _ _ _ _ _ _]
  exact DiagCode.fieldReading_ships.1

/-- A refused field's diagnostic (`unreadDiag`) named for the field of
`e` whose text it read — in the `.bib`'s spelling where `written` holds the
entry as written — and keyed by the entry and the field; one whose text no
field holds whole (a name list as the style writes it) is keyed by the
entry. Every other diagnostic is returned as it is. -/
public def nameUnread (written : Option Entry) (e : Entry) (d : Diag) : Diag :=
  if d.kind != .W0429 then d else
  let src := d.trigger.getD ""
  let holds (x : Entry) : Option String :=
    (x.fields.find? (·.2.trimAscii.toString == src)).map (·.1)
  match (written.bind holds).orElse fun _ => holds e with
  | some f =>
    let rest := (d.message.drop unreadWho.length).toString
    { d with message := s!"the '{f}' field of '{e.key}'{rest}"
             subject := some s!"bibfield:unread:{e.key}:{f}" }
  | none => { d with subject := some s!"bibfield:unread:{e.key}" }

/-- A URL or DOI as `\url` reads it: braces dropped and an escaped character
itself, everything else verbatim — never `text`'s ligatures and ties, which
would turn `--` into a dash and `~` into a space. -/
public def urlText (u : String) : String := Id.run do
  let mut out := ""
  let mut esc := false
  for c in u.trimAscii.toString.toList do
    if esc then
      out := out.push c
      esc := false
    else if c == '\\' then esc := true
    else if c != '{' && c != '}' then out := out.push c
  return out

end LeanTex.Core.Bib
