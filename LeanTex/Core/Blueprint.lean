module

public import LeanTex.Core.Ir
import LeanTex.Core.CodeLink

/-! # leanblueprint's commands

What a blueprint's statement or proof marks about its formalization, and the line its web page and
markdown twin set for the marks; the PDF sets none, as the package's print macros set nothing. -/

namespace LeanTex.Core.Blueprint

open LeanTex.Core LeanTex.Core.Ir

/-- A command a statement or proof marks itself with. -/
public inductive Mark where
  | lean
  | leanok
  | uses
  | proves
  | notready
  | mathlibok
  | discussion
  deriving Repr, BEq, DecidableEq, Inhabited

public def Mark.name : Mark → String
  | .lean => "lean"
  | .leanok => "leanok"
  | .uses => "uses"
  | .proves => "proves"
  | .notready => "notready"
  | .mathlibok => "mathlibok"
  | .discussion => "discussion"

public def Mark.all : List Mark := [.lean, .leanok, .uses, .proves, .notready, .mathlibok, .discussion]

/-- The mark a control word names. -/
public def Mark.ofName? (n : String) : Option Mark := Mark.all.find? (·.name == n)

/-- Whether a mark takes a group: the names, labels or issue it reads. -/
public def Mark.takesGroup : Mark → Bool
  | .lean | .uses | .proves | .discussion => true
  | .leanok | .notready | .mathlibok => false

/-- Whether the print macros end a mark with `\ignorespaces`. -/
public def Mark.ignoresSpaces : Mark → Bool
  | .uses | .proves => true
  | .lean | .leanok | .notready | .mathlibok | .discussion => false

/-- What one statement or proof marks, each list in first-written order without repeats. -/
public structure Marks where
  names : Array String := #[]
  leanok : Bool := false
  mathlibok : Bool := false
  notready : Bool := false
  uses : Array String := #[]
  proves : Array String := #[]
  issue : Option String := none
  deriving Repr, BEq, Inhabited

/-- A blueprint's site declaration, which its links read. -/
public inductive SiteKey where
  /-- `\usepackage{blueprint}` itself, which makes the marks the package's. -/
  | package
  | github
  | dochome
  /-- The package's `link` option: a Lean file's link template. -/
  | link
  deriving Repr, BEq, DecidableEq, Inhabited

public def SiteKey.name : SiteKey → String
  | .package => "package"
  | .github => "github"
  | .dochome => "dochome"
  | .link => "link"

public def SiteKey.ofName? (n : String) : Option SiteKey :=
  [SiteKey.package, .github, .dochome, .link].find? (·.name == n)

/-- What a blueprint's links read: whether it loads the package, `\github`'s repository,
`\dochome`'s API documentation and the `link` template. -/
public structure Site where
  loaded : Bool := false
  github : Option String := none
  dochome : Option String := none
  link : Option String := none
  deriving Repr, BEq, Inhabited

public def Site.declare (s : Site) (key : SiteKey) (url : String) : Site :=
  match key with
  | .package => { s with loaded := true }
  | .github => { s with github := some url }
  | .dochome => { s with dochome := some url }
  | .link => { s with link := some url }

/-- The marks the innermost open statement or proof collects, and whether one is open. -/
public structure Scope where
  inside : Bool := false
  marks : Marks := {}
  deriving Repr, BEq, Inhabited

/-- A comma list's entries as leanblueprint's list arguments read them: trimmed, empties dropped. -/
public def entries (s : String) : Array String :=
  (((s.splitOn ",").map (·.trimAscii.toString)).filter (!·.isEmpty)).toArray

/-- A discussion's issue as leanblueprint reads it: trimmed, its leading `#` dropped. -/
public def issueOf (s : String) : String :=
  (s.trimAscii.toString.dropWhile (· == '#')).trimAscii.toString

/-- The labels a mark's group refers to: `\uses`'s and `\proves`'s lists. -/
public def Mark.keys (m : Mark) (arg : String) : Array String :=
  match m with
  | .uses | .proves => entries arg
  | .lean | .leanok | .notready | .mathlibok | .discussion => #[]

private def joinNew (xs ys : Array String) : Array String :=
  ys.foldl (fun acc y => if acc.contains y then acc else acc.push y) xs

/-- The marks after one command, read from its group's text. -/
public def Marks.mark (m : Marks) (k : Mark) (arg : String) : Marks :=
  match k with
  | .lean => { m with names := joinNew m.names (entries arg) }
  | .leanok => { m with leanok := true }
  | .mathlibok => { m with mathlibok := true }
  | .notready => { m with notready := true }
  | .uses => { m with uses := joinNew m.uses (k.keys arg) }
  | .proves => { m with proves := joinNew m.proves (k.keys arg) }
  | .discussion => if (issueOf arg).isEmpty then m else { m with issue := some (issueOf arg) }

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

/-- The words a status sets on a statement or a proof: its author's mark, never a verdict. -/
public def Status.words (proof : Bool) : Status → String
  | .mathlib => "marked in Mathlib"
  | .formalized => if proof then "proof marked formalized" else "statement marked formalized"
  | .notReady =>
    if proof then "proof marked not ready to formalize" else "statement marked not ready to formalize"

private def unslashed (url : String) : String :=
  if url.endsWith "/" then (url.dropEnd 1).toString else url

/-- The parts a `link` template names that a Lean name alone cannot fill. -/
public def Site.unfilled (s : Site) : List String :=
  match s.link with
  | some l =>
    let t := Code.linkTemplate l
    Code.templateParts.filter fun p => p != "{name}" && (t.splitOn p).length > 1
  | none => []

/-- A Lean name's link: the `link` template's `{name}` filled as a Lean file's link fills it, else
leanblueprint's `{dochome}/find/#doc/{name}`; none without either, or where `link` names a part a
name cannot fill. -/
public def nameLink (site : Site) (name : String) : Option String :=
  match site.link with
  | some l => Code.expandName l name
  | none => site.dochome.bind fun d => Code.expandName (unslashed d ++ "/find/#doc/{name}") name

/-- A discussion's link: the issue in `\github`'s repository, none without one. -/
public def issueLink (site : Site) (issue : String) : Option String :=
  let part := Code.urlPart false issue
  site.github.map fun g => unslashed g ++ "/issues/" ++ part

private def joined (sep : String) (parts : Array (Array Inline)) : Array Inline :=
  parts.foldl (init := #[]) fun acc p => (if acc.isEmpty then acc else acc.push (.text sep)) ++ p

/-- The line a statement's or proof's marks set, parts apart by semicolons: its Lean names as code,
linked through its site, its status, what it proves and uses, and its discussion, the words in
English, marked so where the page's language is another; empty where it marks nothing. -/
public def line (styles : Styles) (site : Site) (proof english : Bool) (m : Marks) :
    Array Inline :=
  let words (s : String) : Inline := if english then .text s else .styled (.lang "en") #[.text s]
  let ref (key : String) : Array Inline := styles.linkInk "link" #[.ref key .headed "??" none]
  let names : Array (Array Inline) := m.names.map fun n =>
    let code : Inline := .styled .mono #[.text n]
    match nameLink site n with
    | some url => #[.link url (styles.linkInk "url" #[code])]
    | none => #[code]
  let parts : Array (Option (String × Array Inline)) :=
    #[if names.isEmpty then none else some ("Lean: ", joined ", " names),
      m.status.map fun s => (s.words proof, #[]),
      if m.proves.isEmpty then none else some ("proves ", joined ", " (m.proves.map ref)),
      if m.uses.isEmpty then none else some ("uses ", joined ", " (m.uses.map ref)),
      m.issue.map fun i =>
        let said : Array Inline := #[words s!"issue {i}"]
        ("discussed in ", match issueLink site i with
          | some url => #[.link url (styles.linkInk "url" said)]
          | none => said)]
  joined "; " ((parts.filterMap id).mapIdx fun k (lead, rest) =>
    #[words (if k == 0 then lead.capitalize else lead)] ++ rest)

end LeanTex.Core.Blueprint
