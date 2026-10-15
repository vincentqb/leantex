module

public import LeanTex.Core.Ir
import LeanTex.Core.CodeLink

/-! # leanblueprint's commands

What a blueprint's statement or proof marks about its formalization, and the line its web page and
markdown twin set for the marks; the PDF sets none, as the package's print macros set nothing. -/

namespace LeanTex.Core.Blueprint

open LeanTex.Core LeanTex.Core.Ir

/-- What one statement or proof declares, each list in source order. -/
public structure Marks where
  names : Array String := #[]
  leanok : Bool := false
  mathlibok : Bool := false
  notready : Bool := false
  uses : Array String := #[]
  proves : Option String := none
  issue : Option String := none
  deriving Repr, BEq, Inhabited

/-- Where a blueprint's names and discussions link: `\dochome`'s API documentation and `\github`'s
repository. -/
public structure Site where
  dochome : Option String := none
  github : Option String := none
  deriving Repr, BEq, Inhabited

/-- The marks the innermost open statement or proof collects, and whether one is open. -/
public structure Scope where
  inside : Bool := false
  marks : Marks := {}
  deriving Repr, BEq, Inhabited

/-- The commands a statement or proof marks itself with, by the groups each takes. -/
public def markArity? : String → Option Nat
  | "lean" | "uses" | "proves" | "discussion" => some 1
  | "leanok" | "notready" | "mathlibok" => some 0
  | _ => none

/-- A comma list's entries as leanblueprint's list arguments read them: trimmed, empties dropped. -/
public def entries (s : String) : Array String :=
  (((s.splitOn ",").map (·.trimAscii.toString)).filter (!·.isEmpty)).toArray

/-- A discussion's issue as leanblueprint reads it: trimmed, its leading `#` dropped. -/
public def issueOf (s : String) : String :=
  (s.trimAscii.toString.dropWhile (· == '#')).trimAscii.toString

/-- The labels one command's group refers to: `\uses`'s list, or the label `\proves` names. -/
public def keys (name arg : String) : Array String :=
  match name with
  | "uses" => entries arg
  | "proves" => let k := arg.trimAscii.toString; if k.isEmpty then #[] else #[k]
  | _ => #[]

/-- The marks after one command, read from its group's text. -/
public def Marks.mark (m : Marks) (name arg : String) : Marks :=
  match name with
  | "lean" => { m with names := m.names ++ entries arg }
  | "leanok" => { m with leanok := true }
  | "mathlibok" => { m with mathlibok := true }
  | "notready" => { m with notready := true }
  | "uses" => { m with uses := m.uses ++ keys name arg }
  | "proves" => match (keys name arg)[0]? with
    | some k => { m with proves := some k }
    | none => m
  | "discussion" => if (issueOf arg).isEmpty then m else { m with issue := some (issueOf arg) }
  | _ => m

/-- A status its author marks a statement or proof with, in the web blueprint's precedence. -/
public inductive Status where
  | mathlib
  | formalized
  | notReady
  deriving Repr, BEq, DecidableEq, Inhabited

public def Marks.status (m : Marks) : Option Status :=
  if m.mathlibok then some .mathlib
  else if m.leanok then some .formalized
  else if m.notready then some .notReady
  else none

/-- The words a status sets: the author's mark, never a verdict. -/
public def Status.words : Status → String
  | .mathlib => "marked in Mathlib"
  | .formalized => "marked formalized"
  | .notReady => "marked not ready to formalize"

private def unslashed (url : String) : String :=
  if url.endsWith "/" then (url.dropEnd 1).toString else url

/-- A Lean name's link: leanblueprint's `{dochome}/find/#doc/{name}`, its name filled as a Lean
file's link template fills it; none without a `\dochome`. -/
public def nameLink (site : Site) (name : String) : Option String :=
  site.dochome.bind fun d =>
    Code.expandParts (unslashed d ++ "/find/#doc/{name}") [("{name}", some (Code.urlPart false name))]

/-- A discussion's link: the issue in `\github`'s repository, none without one. -/
public def issueLink (site : Site) (issue : String) : Option String :=
  let part := Code.urlPart false issue
  site.github.map fun g => unslashed g ++ "/issues/" ++ part

private def joined (sep : String) (parts : Array (Array Inline)) : Array Inline :=
  parts.foldl (init := #[]) fun acc p => (if acc.isEmpty then acc else acc.push (.text sep)) ++ p

/-- The line a statement's or proof's marks set, parts apart by semicolons: its Lean names as code,
linked where a `\dochome` declares their documentation, its status, what it proves and uses, and
its discussion; empty where it marks nothing. -/
public def line (styles : Styles) (site : Site) (m : Marks) : Array Inline :=
  let ref (key : String) : Array Inline := styles.linkInk "link" #[.ref key .headed "??" none]
  let names : Array (Array Inline) := m.names.map fun n =>
    let code : Inline := .styled .mono #[.text n]
    match nameLink site n with
    | some url => #[.link url (styles.linkInk "url" #[code])]
    | none => #[code]
  let parts : Array (Option (String × Array Inline)) :=
    #[if names.isEmpty then none else some ("Lean: ", joined ", " names),
      m.status.map fun s => (s.words, #[]),
      m.proves.map fun key => ("proves ", ref key),
      if m.uses.isEmpty then none else some ("uses ", joined ", " (m.uses.map ref)),
      m.issue.map fun i =>
        let words : Array Inline := #[.text s!"issue {i}"]
        ("discussed in ", match issueLink site i with
          | some url => #[.link url (styles.linkInk "url" words)]
          | none => words)]
  let kept := parts.filterMap id
  joined "; " (kept.mapIdx fun k (lead, rest) =>
    #[Inline.text (if k == 0 then lead.capitalize else lead)] ++ rest)

end LeanTex.Core.Blueprint
