module

public import LeanTex.Core.DesignRole

/-! The light screen's static reading of a page's colour CSS: `var()` chased through the custom
properties in scope and `light-dark()` read on its light side. -/

public section

open LeanTex.Core

/-- A CSS value split at its first comma outside parentheses: the part
before and the part after, the second empty where there is none. -/
def splitTopComma (v : String) : String × String := Id.run do
  let mut depth := 0
  let mut i := 0
  for c in v.toList do
    if c == '(' then depth := depth + 1
    else if c == ')' then depth := depth - 1
    else if c == ',' && depth == 0 then
      return ((v.take i).toString, (v.drop (i + 1)).toString)
    i := i + 1
  return (v, "")

/-- The light screen's side of a `light-dark()` pair; any other value as it
stands. -/
def lightSide (v : String) : String :=
  let v := v.trimAscii.toString
  if v.startsWith "light-dark(" && v.endsWith ")" then
    (splitTopComma ((v.drop 11).dropEnd 1).toString).1.trimAscii.toString
  else v

/-- The light screen's reading of a CSS value against the custom properties in force, nearest first,
eight steps deep. -/
def lightValue (vars : List (String × String)) (v : String) : String :=
  (List.range 8).foldl (fun v _ =>
    let v := lightSide v
    if v.startsWith "var(" && v.endsWith ")" then
      let (k, fb) := splitTopComma ((v.drop 4).dropEnd 1).toString
      (vars.lookup k.trimAscii.toString).getD (if fb.isEmpty then v else fb.trimAscii.toString)
    else v) v

/-- The custom properties a style attribute declares, nearest last as written. -/
def styleVars (style : String) : List (String × String) :=
  (style.splitOn ";").foldl (fun vars decl =>
    match splitTopComma' decl with
    | some (k, v) => if k.startsWith "--" then (k, v) :: vars else vars
    | none => vars) []
where
  splitTopComma' (decl : String) : Option (String × String) :=
    match decl.splitOn ":" with
    | k :: rest@(_ :: _) => some (k.trimAscii.toString, (":".intercalate rest).trimAscii.toString)
    | _ => none

/-- A style attribute with each ordinary declaration's value read by `lightValue`, custom properties
kept as written. -/
def lightStyle (vars : List (String × String)) (style : String) : String :=
  "; ".intercalate ((style.splitOn ";").filterMap fun decl =>
    match decl.splitOn ":" with
    | k :: rest@(_ :: _) =>
      let key := k.trimAscii.toString
      let v := (":".intercalate rest).trimAscii.toString
      some s!"{key}: {if key.startsWith "--" then v else lightValue vars v}"
    | _ => if decl.trimAscii.isEmpty then none else some decl.trimAscii.toString)

/-- A style attribute with every declaration's value, custom properties too, read by `lightValue`
against `vars` and its own properties. -/
def lightStyleAll (vars : List (String × String)) (style : String) : String :=
  let vars := styleVars style ++ vars
  "; ".intercalate ((style.splitOn ";").filterMap fun decl =>
    match decl.splitOn ":" with
    | k :: rest@(_ :: _) =>
      some s!"{k.trimAscii.toString}: {lightValue vars (":".intercalate rest).trimAscii.toString}"
    | _ => if decl.trimAscii.isEmpty then none else some decl.trimAscii.toString)

/-- A stylesheet's rules in order, each with its enclosing at-rule preludes, outermost first;
comments dropped. -/
def sheetRules (css : String) : Array (List String × String × String) := Id.run do
  let mut stack : List String := []
  let mut out : Array (List String × String × String) := #[]
  let mut cur := ""
  let mut rule : Option String := none
  let mut prev := ' '
  let mut comment := false
  for c in css.toList do
    if comment then
      if prev == '*' && c == '/' then
        comment := false
        prev := ' '
      else prev := c
      continue
    if prev == '/' && c == '*' then
      comment := true
      cur := (cur.dropEnd 1).toString
      prev := ' '
      continue
    prev := c
    match rule with
    | some sel =>
      if c == '}' then
        out := out.push (stack.reverse, sel, cur.trimAscii.toString)
        cur := ""
        rule := none
      else cur := cur.push c
    | none =>
      if c == '{' then
        let p := cur.trimAscii.toString
        cur := ""
        if p.startsWith "@" && !p.startsWith "@font-face" && !p.startsWith "@page" then
          stack := p :: stack
        else rule := some p
      else if c == '}' then
        stack := stack.drop 1
        cur := ""
      else if c == ';' then cur := ""
      else cur := cur.push c
  return out

/-- Whether a block's condition holds in a scheme, `more` asking more contrast (in print too). -/
def holdsIn (s : Ir.Scheme) (prelude : String) (more : Bool := s.more) : Bool :=
  if prelude.startsWith "@supports" then prelude.contains "light-dark"
  else if prelude == "@media (prefers-contrast: more)" then more
  else if prelude == "@media print" then s == .print
  else if prelude == "@media screen" then s != .print
  else prelude == "@media screen, print"

/-- The declarations of a rule's text, in order. -/
def cssDecls (decls : String) : List (String × String) :=
  (decls.splitOn ";").filterMap fun d =>
    match d.splitOn ":" with
    | k :: rest@(_ :: _) => some (k.trimAscii.toString, (":".intercalate rest).trimAscii.toString)
    | _ => none

/-- A property's value as CSS applies it from one block of declarations (a
style attribute, a rule's body): the last that states it. -/
def lastDecl (decls : List (String × String)) (prop : String) : Option String :=
  decls.foldl (fun acc (k, v) => if k == prop then some v else acc) none

/-- The `:root` declarations a scheme's cascade applies, in order. -/
def rootDeclsIn (s : Ir.Scheme) (rules : Array (List String × String × String))
    (more : Bool := s.more) : List (String × String) :=
  (rules.toList.filter fun (conds, sel, _) =>
    sel == ":root" && conds.all (holdsIn s · more)).flatMap fun (_, _, decls) => cssDecls decls

/-- The `:root` table a scheme's cascade gives, newest first, and whether its `light-dark()` pairs
read dark there. -/
def schemeRoot (css : String) (s : Ir.Scheme) (more : Bool := s.more) :
    List (String × String) × Bool :=
  let decls := rootDeclsIn s (sheetRules css) more
  let cs := ((decls.reverse.lookup "color-scheme").getD "light").splitOn " "
  let dark := if cs.contains "dark" && cs.contains "light" then s.onDark
    else cs.contains "dark"
  ((decls.filter (·.1.startsWith "--")).reverse, dark)

/-- The side of a `light-dark()` pair a reading takes; any other value as it
stands. -/
def sideOf (dark : Bool) (v : String) : String :=
  let v := v.trimAscii.toString
  if v.startsWith "light-dark(" && v.endsWith ")" then
    let (l, d) := splitTopComma ((v.drop 11).dropEnd 1).toString
    (if dark then d else l).trimAscii.toString
  else v

/-- A CSS value as a scheme reads it against the custom properties in force, nearest first, eight
steps deep. -/
def schemeRead (dark : Bool) (vars : List (String × String)) (v : String) : String :=
  (List.range 8).foldl (fun v _ =>
    let v := sideOf dark v
    if v.startsWith "var(" && v.endsWith ")" then
      let (k, fb) := splitTopComma ((v.drop 4).dropEnd 1).toString
      (vars.lookup k.trimAscii.toString).getD (if fb.isEmpty then v else fb.trimAscii.toString)
    else v) v
