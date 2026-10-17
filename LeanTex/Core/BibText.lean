module

public import LeanTex.Core.Bib
public import LeanTex.Core.Ir
public import Std.Data.HashMap
import LeanTex.Core.MathParse

/-! How a field's TeX text becomes inline content. -/

namespace LeanTex.Core.Bib

/-- What reading a field reported beside its content: the diagnostics and the
boundary pictures it set. -/
public structure FieldReport where
  diags : Array Diag := #[]
  pictures : Array (String × Ir.PicSrc) := #[]
  deriving Inhabited, BEq

public instance : Append FieldReport :=
  ⟨fun a b => { diags := a.diags ++ b.diags, pictures := a.pictures ++ b.pictures }⟩

/-- A field's TeX text as inline content, with what reading it reported. -/
public abbrev FieldText := String → Array Ir.Inline × FieldReport

/-- The field reading for the entry at a place in its `.bib`. -/
public abbrev FieldReading := Span → FieldText

/-- What a reference list has read of its field texts so far, by text. -/
public abbrev FieldCache := Std.HashMap String (Array Ir.Inline × FieldReport)

/-- A field's text through a reading, answered from the
cache where read before. -/
public def FieldCache.read (cache : FieldCache) (cv : FieldText) (s : String) :
    (Array Ir.Inline × FieldReport) × FieldCache :=
  match cache.get? s with
  | some r => (r, cache)
  | none =>
    let r := cv s
    (r, cache.insert s r)

/-- A stored value split at its `$…$` spans; an escaped `\$` is text and an
unclosed span stays text. -/
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

/-- One `$…$` span as inline math: the math parser's atoms,
else the span's floor (W0012). -/
private def formulaOf (src : String) : Ir.Inline :=
  let (toks, _) := Lex.lex "" ("$" ++ src ++ "$")
  match (Parse.parse "" toks).1.toList with
  | [.math false body _] =>
    match MathParse.parseMath false body with
    | .ok (l, _) => .formula false (Parse.rawSrc body) l
    | .error _ => .math false (Parse.rawSrc body)
  | _ => .math false src

/-- A stored value read without an elaborator: plain text, typographic
punctuation, each `$…$` span a formula. -/
public def fieldInlines (v : String) : Array Ir.Inline := Id.run do
  let spans := mathSpans v
  let mut out : Array Ir.Inline := #[]
  let mut pending := ""
  for (math, s) in spans, k in [0:spans.size] do
    if math then
      unless pending.isEmpty do out := out.push (.text (Ir.smartPunctAfter (Ir.quoteLead out) pending))
      pending := ""
      out := out.push (formulaOf s)
    else
      let t := textSpan s (lead := k != 0)
      pending := pending ++ (if k + 1 == spans.size then t.trimAsciiEnd.toString else t)
  unless pending.isEmpty do out := out.push (.text (Ir.smartPunctAfter (Ir.quoteLead out) pending))
  return out

/-- The diagnostic naming a formula the math parser cannot model (W0012). -/
private def mathFloorDiag (src : String) : Diag :=
  Diag.of .W0012 s!"math in a reference-list entry is not rendered yet; the formula sets as \
    its text content" (subject := some ("math:" ++ src))

/-- The reading with no elaborator behind it. -/
public def plainField : FieldText := fun v =>
  let out := fieldInlines v
  (out, { diags := (Ir.foldInlines (fun acc x => match x with
    | .math _ src => acc.push src
    | _ => acc) #[] out).map mathFloorDiag })

public theorem plainField_ships_contract (v : String) :
    (plainField v).2.diags.any (·.severity == .error) = false := by
  rw [Bool.eq_false_iff]
  intro ha
  obtain ⟨d, hd, he⟩ := Array.any_eq_true'.mp ha
  obtain ⟨src, _, rfl⟩ := Array.mem_map.mp hd
  rw [show (mathFloorDiag src).severity = DiagCode.W0012.loss.severity from
    Diag.of_severity_full .W0012 _ _ _ _ _ _ _ _, DiagCode.fieldReading_ships.2.1] at he
  exact Bool.false_ne_true he

public def plainReading : FieldReading := fun _ => plainField

/-- The words a refused field's diagnostic opens with until
the list names its field. -/
private def unreadWho : String := "a .bib field"

/-- The key prefix of a refused field's text until the list names its field. -/
private def unreadKey : String := "bibfield:unread:"

/-- A field the document's elaborator refused, set as its text (W0429). -/
public def unreadDiag (span : Span) (src : String) (cause : Option String) : Diag :=
  let what := match cause with
    | none => "holds markup this engine sets only between paragraphs; it sets as its text, \
        run into the entry"
    | some c => s!"is not TeX this engine sets in an entry ({c}); it sets as its plain text"
  Diag.of .W0429 s!"{unreadWho} {what}" (some span)
    (subject := some (unreadKey ++ src))

public theorem unreadDiag_ships (span : Span) (src : String) (cause : Option String) :
    ((unreadDiag span src cause).severity == .error) = false := by
  rw [show (unreadDiag span src cause).severity = DiagCode.W0429.loss.severity from
    Diag.of_severity_full .W0429 _ _ _ _ _ _ _ _]
  exact DiagCode.fieldReading_ships.1

/-- A refused field's diagnostic named for the field of `e`
whose text it read. -/
public def nameUnread (written : Option Entry) (e : Entry) (d : Diag) : Diag :=
  if d.kind != .W0429 then d else
  let src := match d.subject with
    | some k => if k.startsWith unreadKey then (k.drop unreadKey.length).toString else ""
    | none => ""
  let holds (x : Entry) : Option String :=
    (x.fields.find? (·.2.trimAscii.toString == src)).map (·.1)
  match (written.bind holds).orElse fun _ => holds e with
  | some f =>
    let rest := (d.message.drop unreadWho.length).toString
    { d with message := s!"the '{f}' field of '{e.key}'{rest}"
             subject := some s!"bibfield:unread:{e.key}:{f}" }
  | none => { d with subject := some s!"bibfield:unread:{e.key}" }

/-- A URL or DOI as `\url` reads it: braces dropped, escapes resolved,
everything else verbatim. -/
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
