module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests

/-- Delayed frame-title repair names the channel that supplied the winning
Beamer alias. The synthetic included source runs through preparation, body
elaboration, contrast realization, trigger attribution, and site accounting.
The pre-judge palette checks distinguish source ownership from paint order. -/
def beamerColorOriginsChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let root := "beamer-origins.tex"
  let child := "colors.sty"
  let soft : Ir.Color := { r := 0x88, g := 0x88, b := 0x88 }
  let white : Ir.Color := { r := 255, g := 255, b := 255 }
  let black : Ir.Color := { r := 0, g := 0, b := 0 }
  let parse (file text : String) := (Parse.parse file (Lex.lex file text).1).1
  let declare (name body : String) (star : Bool := false) :=
    "\\setbeamercolor" ++ (if star then "*" else "") ++
      "{" ++ name ++ "}{" ++ body ++ "}"
  let exercise (name source : String) (expected : Ir.Color)
      (origin : Option (Nat × String)) : IO Unit := do
    let raws := parse root
        "\\documentclass{beamer}\n\\definecolor{SoftInk}{HTML}{888888}\n" ++
      #[Parse.Raw.env (Parse.inputEnv child) (parse child source) {}] ++
      parse root
        "\\begin{document}\n\\begin{frame}{Heading}Body\\end{frame}\n\\end{document}"
    let prepared := Elab.prepare root raws
    let (plan, initial) := Elab.preparedBody root prepared
    let ((doc, table, report), state) := (Elab.runDocBody plan).run initial
    let (_, ds, _) := Elab.completePrepared root prepared #[] doc table report state
    let repairs := ds.filter fun d =>
      d.kind == .N0022 && d.subject.any (·.startsWith "frametitlefg:")
    t s!"beamer origins: {name}: winning foreground"
      ((doc.palette.find? "frametitlefg").any (· == expected))
    t s!"beamer origins: {name}: winning background"
      ((doc.palette.find? "frametitlebg").any (· == white))
    t s!"beamer origins: {name}: no input error"
      (!(ds.any fun d => d.severity == .error))
    match origin with
    | none =>
      t s!"beamer origins: {name}: overwritten low contrast raises no repair"
        (repairs.isEmpty && !(ds.any (·.kind == .W0345)))
    | some (line, trigger) =>
      t s!"beamer origins: {name}: exactly one repair for the declared pair"
        (repairs.size == 1 && repairs.all fun d =>
          d.subject == some (Ir.inkKey "frametitlefg" soft white))
      let observed := String.intercalate ", " (repairs.toList.map fun d =>
        let location := d.span.map (fun s => s!"{s.file}:{s.pos.line}:{s.pos.col}")
        s!"{location.getD "<no span>"} {d.trigger.getD "<no trigger>"}")
      t s!"beamer origins: {name}: owner {child}:{line}:1 {trigger}; observed {observed}"
        (repairs.size == 1 && repairs.all fun d =>
          d.span.any (fun s =>
            s.file == child && s.pos.line == line && s.pos.col == 1) &&
          d.trigger == some trigger)
  for (first, last) in [("frametitle", "headline"), ("headline", "frametitle")] do
    exercise s!"{first} then {last}"
      (declare first "fg=black,bg=white" ++ "\n" ++
        declare last "fg=SoftInk,bg=white")
      soft (some (2, "\\setbeamercolor"))
    exercise s!"{last} overwrites a failing {first}"
      (declare first "fg=SoftInk,bg=white" ++ "\n" ++
        declare last "fg=black,bg=white")
      black none
    exercise s!"inherited {last} wins over explicit {first}"
      (declare first "fg=black,bg=white" ++ "\n" ++
        "\\setbeamercolor{probe parent}{fg=SoftInk,bg=white}\n" ++
        declare last "parent=probe parent" true)
      soft (some (2, "\\setbeamercolor"))
    exercise s!"explicit {last} wins over inherited {first}"
      ("\\setbeamercolor{probe parent}{fg=black,bg=white}\n" ++
        declare first "parent=probe parent" true ++ "\n" ++
        declare last "parent=probe parent,fg=SoftInk" true)
      soft (some (3, "\\setbeamercolor"))
  exercise "later background keeps the winning foreground's earlier source"
    ("\\setbeamercolor{frametitle}{fg=black,bg=white}\n" ++
      "\\setbeamercolor{headline}{fg=SoftInk,bg=white}\n" ++
      "\\setbeamercolor{headline}{bg=white}")
    soft (some (2, "\\setbeamercolor"))
  exercise "late parent update owns the inherited foreground"
    ("\\setbeamercolor{frametitle}{fg=black,bg=white}\n" ++
      "\\setbeamercolor{probe parent}{fg=black,bg=white}\n" ++
      "\\setbeamercolor*{headline}{parent=probe parent}\n" ++
      "\\setbeamercolor{probe parent}{fg=SoftInk}")
    soft (some (4, "\\setbeamercolor"))
  exercise "parents retain independent channel owners"
    ("\\setbeamercolor{frametitle}{fg=black,bg=white}\n" ++
      "\\setbeamercolor{probe foreground}{fg=SoftInk}\n" ++
      "\\setbeamercolor{probe background}{bg=white}\n" ++
      "\\setbeamercolor*{headline}{parent={probe foreground,probe background}}")
    soft (some (2, "\\setbeamercolor"))
  exercise "a native winner retains its palette source"
    ("\\setbeamercolor{frametitle}{fg=black,bg=white}\n" ++
      "\\palette{frametitlefg=#888888,frametitlebg=#FFFFFF}")
    soft (some (2, "\\palette"))
  exercise "a use expression owns its explicit channel"
    ("\\setbeamercolor{probe source}{fg=SoftInk,bg=white}\n" ++
      "\\setbeamercolor*{headline}{use=probe source,fg=probe source.fg,bg=probe source.bg}")
    soft (some (2, "\\setbeamercolor"))
  -- An overwritten source must disappear even when the winning channel has
  -- no Beamer declaration site. These checks inspect the resolver's output.
  let site (line : Nat) : Span := ⟨child, { line := line, col := 1 }⟩
  let declared := (({} : BeamerColor.State).declare
    "frametitle" false "fg=red,bg=white" (site 1)).1
  let (resolved, painted, _) := declared.resolve {}
  let owns (s : BeamerColor.State) (key : String) (line : Nat) :=
    (s.origins.filter (·.1 == key)).size == 1 &&
      s.origins.any (fun (k, _, span) =>
        k == key && span.file == child && span.pos.line == line)
  t "beamer origins: explicit channels retain their own sites"
    (owns resolved "frametitlefg" 1 && owns resolved "frametitlebg" 1)
  let (native, _, _) := (resolved.native "frametitlefg" black).resolve
    (painted.declare "frametitlefg" black)
  t "beamer origins: native overwrite clears only its Beamer channel source"
    (!(native.origins.any (·.1 == "frametitlefg")) && owns native "frametitlebg" 1)
  let (defaults, defaultPalette, _) := (resolved.declare
    "headline" true "bg=white" (site 2)).1.resolve painted
  t "beamer origins: a default winner clears the earlier alias source"
    (!(defaults.origins.any (·.1 == "frametitlefg")) &&
      owns defaults "frametitlebg" 2)
  let (erased, erasedPalette, _) := (defaults.declare
    "headline" false "bg={}" (site 3)).1.resolve defaultPalette
  t "beamer origins: erased paint has no surviving channel source"
    ((erasedPalette.find? "frametitlebg").isNone &&
      !(erased.origins.any (·.1 == "frametitlebg")))
  let (repeated, _, _) := resolved.resolve painted
  t "beamer origins: repeated resolution rebuilds the same winning sources"
    (reprStr repeated.origins == reprStr resolved.origins)
end Tests
