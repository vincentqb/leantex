module

public import Tests.Diag
public import Tests.Artifact

public section

open LeanTex.Core LeanTex.Cli

namespace Tests.DiagDeletion

/-- The end of a balanced group opening at `i` with `opening`, past its closer. -/
private def groupEnd (cs : Array Char) (i : Nat) (opening closing : Char) : Nat := Id.run do
  let mut depth := 0
  for k in [i:cs.size] do
    let c := cs[k]?.getD ' '
    if c == opening then depth := depth + 1
    else if c == closing then
      depth := depth - 1
      if depth == 0 then return k + 1
  return cs.size

/-- The index past a control word at `i` with the spaces TeX skips and its `[...]` and `{...}`
groups. -/
private def invocationEnd (cs : Array Char) (i : Nat) : Nat := Id.run do
  let mut j := i + 1
  for _ in [i + 1:cs.size] do
    if (cs[j]?.map Char.isAlpha).getD false then j := j + 1 else break
  for _ in [j:cs.size] do
    if cs[j]? == some ' ' then j := j + 1 else break
  for _ in [j:cs.size] do
    match cs[j]? with
    | some '[' => j := groupEnd cs j '[' ']'
    | some '{' => j := groupEnd cs j '{' '}'
    | _ => break
  return j

/-- `line` without the construct a diagnostic at column `col` names: the command invocation
standing there, which carries the name; a `key = value` entry; or the name alone. -/
private def deleteConstruct (line name : String) (col : Nat) : Option String := do
  let cs := line.toList.toArray
  let start := col - 1
  guard (start < cs.size)
  let tail := String.ofList (cs.extract start cs.size).toList
  if cs[start]? == some '\\' then
    let stop := invocationEnd cs start
    let word := String.ofList ((cs.extract start stop).toList.takeWhile fun c =>
      c == '\\' || c.isAlpha)
    if word == name || (name.startsWith word && !(name.drop word.length).any Char.isAlpha) then
      pure (String.ofList (cs.extract 0 start).toList ++ String.ofList (cs.extract stop cs.size).toList)
    else
      -- An option or key the invocation carries: that entry alone, with its comma.
      let inner := String.ofList (cs.extract start stop).toList
      let parts := inner.splitOn name
      guard (parts.length == 2)
      let before := parts.headD ""
      let after := (parts.drop 1).headD ""
      let ec := after.toList.toArray
      let k := Id.run do
        let mut k := 0
        for _ in [0:ec.size] do
          match ec[k]? with
          | some ',' => k := k + 1; break
          | some '}' | some ']' | none => break
          | some '{' => k := groupEnd ec k '{' '}'
          | some _ => k := k + 1
        return k
      let kept := String.ofList (ec.extract k ec.size).toList
      let before := if ec[k - 1]? != some ',' && before.endsWith "," then (before.dropEnd 1).toString
        else before
      -- An entry that was its argument's whole content takes the invocation with it, an optional
      -- one its brackets.
      let middle := if before.endsWith "{" && kept.startsWith "}" then ""
        else if before.endsWith "[" && kept.startsWith "]" then
          (before.dropEnd 1).toString ++ (kept.drop 1).toString
        else before ++ kept
      pure (String.ofList (cs.extract 0 start).toList ++ middle ++
        String.ofList (cs.extract stop cs.size).toList)
  else
    guard (tail.startsWith name)
    let after := (tail.drop name.length).toString
    let rest := String.ofList (after.toList.dropWhile (· == ' '))
    let ec := after.toList.toArray
    let k := if rest.startsWith "=" then Id.run do
        let mut k := 0
        for _ in [0:ec.size] do
          match ec[k]? with
          | some ',' => k := k + 1; break
          | some '}' | some ']' | none => break
          | some '{' => k := groupEnd ec k '{' '}'
          | some _ => k := k + 1
        return k
      else 0
    pure (String.ofList (cs.extract 0 start).toList ++ String.ofList (ec.extract k ec.size).toList)

/-- What a tex source ships: its PDF's bytes, its web page and its markdown twin. -/
private def shipped (fs : Font.FontSet) (src : String) : ByteArray × String × String :=
  let doc := (elabStr src).1
  let out := layoutOf fs doc
  (driverPdf fs (Layout.Geom.ofPage doc.page) doc out, (HtmlDoc.emit {} doc).1,
    MarkdownDoc.emit doc)

/-- Is this a code whose word says its construct changed nothing. -/
def judged (c : DiagCode) : Bool :=
  (c.qual == .ignored || c.qual == .unused) && c.loss.severity != .error

/-- Why a code is not held to the deletion: its witnesses name nothing deletable, or the artifact
changes and the row says what the word does not. -/
inductive Gap where
  /-- Some records name nothing deletable; every record that does is held. -/
  | unjudged
  /-- A record's deletion changes an artifact. -/
  | changes
  /-- The deletion holds but cannot see the loss. -/
  | blind
  deriving BEq

/-- Codes the deletion does not hold, each with its gap and why: a baseline that may fall and never
rise. -/
def baseline : List (String × Gap × String) :=
  [("W0001", .unjudged, "the text after \\end{document} carries no span"),
   ("W0007", .unjudged, "its witness's running head is an HTML-only loss with no tex name"),
   ("W0013", .unjudged, "its witness is the driver's own record, with no source"),
   ("W0104", .unjudged, "the class options' records carry no span, the key a theme replaces \
stands on another line than the theme, and a package file's lines are out of the deletion's reach"),
   ("W0110", .unjudged, "the class option's record carries no span"),
   ("W0317", .unjudged, "the card's running head record carries no span"),
   ("W0355", .changes, "only the theme's templates are ignored; deleting it drops its palette"),
   ("W0369", .blind, "a face binding, which the suite's one font set cannot see"),
   ("W0392", .unjudged, "a markdown construct, which the deletion's tex sources do not hold"),
   ("W0399", .unjudged, "its witness's fill is an HTML-only loss with no tex name"),
   ("W0416", .unjudged, "a Lean file's directive, which the deletion's tex sources do not hold"),
   ("W0444", .unjudged, "its witness is a PDF/X probe's record, with no source"),
   ("W0445", .unjudged, "its witness is a PDF/X probe's record, with no source"),
   ("W0603", .unjudged, "its witness is the image reader's own record, with no source"),
   ("W0604", .unjudged, "its witness is the image reader's own record, with no source"),
   ("N0027", .unjudged, "its witness is the figure reader's own record, with no source"),
   ("N0104", .unjudged, "the overlay specification's <...> group, which the deletion does not read"),
   ("N0029", .unjudged, "a .bib field, which the deletion's tex sources do not hold"),
   ("N0103", .changes, "the short title's whole \\paragraph is the construct at its column"),
   ("N0359", .changes, "the nested note spans lines, which a one-line deletion cuts")]

/-- An ignored or unused construct changes nothing: each witness record of such a code, its
construct deleted, ships the same PDF, web page and markdown twin and no longer fires there, or the
baseline says why it is not so. -/
def ignoredDeletionChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some sans ← loadTestFont "OpenSans-Regular.ttf"
    | failures ref "deletion: OpenSans-Regular.ttf missing"; return
  let index := (List.range 3).flatMap fun slot =>
    [((slot, 400, false), 0), ((slot, 700, false), 0), ((slot, 400, true), 0),
     ((slot, 700, true), 0)]
  let fs : Font.FontSet := { fonts := #[sans], index := index.toArray }
  for (code, _, _) in baseline do
    t s!"deletion baseline {code}: one row, for a code the deletion judges"
      ((baseline.filter (·.1 == code)).length == 1 &&
        (DiagCode.all.filter judged).any (·.code == code))
  for c in DiagCode.all.filter judged do
    let row := baseline.find? (·.1 == c.code)
    let sources := (diagWitnessWith { sourceOnly := true } fs fs fs (fun _ => #[]) c).filterMap
      fun d => if d.subject == some (witnessSource "tex") then some d.message else none
    let mut seen := 0
    let mut held := 0
    let mut skipped := 0
    for src in sources do
      let fired := (elabLocated "t" src).2.filter (·.kind == c)
      if fired.isEmpty then continue
      let original := shipped fs src
      let lines := src.splitOn "\n"
      for d in fired do
        seen := seen + 1
        let deleted := d.span.bind fun sp => do
          let line ← lines[sp.pos.line - 1]?
          let name ← ((dvForm? d.message).bind (·.name)).map (·.text) <|> d.triggerText
          let kept ← deleteConstruct line name sp.pos.col
          pure ("\n".intercalate (lines.set (sp.pos.line - 1) kept), sp)
        match deleted with
        | none => skipped := skipped + 1
        | some (without, sp) =>
          let gone := !(elabLocated "t" without).2.any fun e =>
            e.kind == c && e.span.any (·.pos.line == sp.pos.line)
          let same := gone && shipped fs without == original
          if same then held := held + 1
          if row.isNone || row.any (·.2.1 == .unjudged) then
            t s!"deletion {c.code}: deleting its construct at {sp.pos.line}:{sp.pos.col} ships the \
same artifacts and drops the record" same
    match row with
    | none =>
      t s!"deletion {c.code}: every witness record names a construct it can delete ({skipped} of \
{seen} could not), or a baseline row says why" (seen > 0 && skipped == 0)
    | some (_, .unjudged, why) =>
      t s!"deletion {c.code}: the baseline row still describes a real gap ({why})"
        (seen == 0 || skipped > 0)
    | some (_, .blind, why) =>
      t s!"deletion {c.code}: the baseline row names a code its witnesses fire ({why})" (seen > 0)
    | some (_, .changes, why) =>
      t s!"deletion {c.code}: the baseline row still describes a real gap ({why})"
        (seen > 0 && held + skipped < seen)

end Tests.DiagDeletion
