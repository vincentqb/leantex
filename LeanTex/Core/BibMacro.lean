module

/-! The commands a `.bib`'s `@preamble` defines. BibTeX and biber copy the
preamble into the `.bbl` ahead of the list (bibtex.web's `preamble$`,
biber's `\preamble`), so its definitions are in force where the list's
fields are typeset and nowhere in what sorts them: `{\noopsort{1999}}2001`
prints `2001` and sorts by `19992001`. The engine reads the defining forms
`@preamble`s use — `\newcommand`, `\renewcommand`, `\providecommand`
(starred or not, the name braced or bare, `[n]` parameters) and `\def`
with `#1`… parameters — and expands their uses in a field's text before
the text is read; a use of a command no form defines stays for the reading,
which names it. -/

namespace LeanTex.Core.Bib

/-- One command a `@preamble` defines: its name, its parameter count, and
its body, `#1`… marking the arguments, written in terms of the commands
defined before it. -/
public structure Macro where
  name : String
  arity : Nat
  body : String
  deriving Repr, BEq, Inhabited

private def isLetter (c : Char) : Bool := ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')

/-- The balanced group opening at `cs[i]`: its body and the index after it. -/
private def groupAt (cs : Array Char) (i : Nat) : Option (String × Nat) := Id.run do
  if cs[i]? != some '{' then return none
  let mut depth := 0
  let mut body := ""
  let mut j := i
  for _ in [0:cs.size] do
    match cs[j]? with
    | some c =>
      if c == '\\' then
        body := body.push c
        if let some d := cs[j + 1]? then body := body.push d
        j := j + 2
        continue
      if c == '{' then
        depth := depth + 1
        if depth > 1 then body := body.push c
      else if c == '}' then
        depth := depth - 1
        if depth == 0 then return some (body, j + 1)
        body := body.push c
      else body := body.push c
      j := j + 1
    | none => return none
  return none

private def skipWs (cs : Array Char) (i : Nat) : Nat := Id.run do
  let mut j := i
  for _ in [0:cs.size] do
    match cs[j]? with
    | some c => if c == ' ' || c == '\n' || c == '\t' || c == '\r' then j := j + 1 else break
    | none => break
  return j

/-- The control word at `cs[i]` (a backslash): its name and the index after
it, a control symbol its one character. -/
private def ctrlAt (cs : Array Char) (i : Nat) : Option (String × Nat) := Id.run do
  if cs[i]? != some '\\' then return none
  let mut j := i + 1
  let mut name := ""
  for _ in [0:cs.size] do
    match cs[j]? with
    | some c => if isLetter c || c == '@' then name := name.push c; j := j + 1 else break
    | none => break
  if name.isEmpty then
    return cs[i + 1]?.map fun c => (String.singleton c, i + 2)
  return some (name, j)

/-- A text with the commands expanded once, outermost uses first: each use
of a defined name takes its arguments — a braced group's content, else the
next character or control sequence — and stands as its body with them in
place. The arguments go in as written; a use inside one is the next pass's.
`true` where a use was expanded. -/
private def expandOnce (ms : Array Macro) (s : String) : String × Bool := Id.run do
  let cs := s.toList.toArray
  let mut out := ""
  let mut changed := false
  let mut i := 0
  for _ in [0:cs.size + 1] do
    if h : i < cs.size then
      if cs[i] == '\\' then
        match ctrlAt cs i with
        | some (name, j) =>
          match ms.findRev? (·.name == name) with
          | some m =>
            let mut args : Array String := #[]
            -- TeX skips the spaces after a control word
            let mut k := if name.all isLetter then skipWs cs j else j
            for _ in [0:m.arity] do
              let k0 := skipWs cs k
              match groupAt cs k0 with
              | some (g, k1) =>
                args := args.push g
                k := k1
              | none =>
                match ctrlAt cs k0 with
                | some (n, k1) =>
                  args := args.push ("\\" ++ n)
                  k := k1
                | none =>
                  args := args.push ((cs[k0]?.map String.singleton).getD "")
                  k := k0 + 1
            let bodyCs := m.body.toList.toArray
            let mut b := ""
            let mut p := 0
            for _ in [0:bodyCs.size + 1] do
              if hp : p < bodyCs.size then
                let c := bodyCs[p]
                if c == '#' then
                  match bodyCs[p + 1]? with
                  | some d =>
                    if '1' ≤ d && d ≤ '9' then
                      b := b ++ (args[d.toNat - '1'.toNat]?.getD "")
                      p := p + 2
                    else
                      b := b.push c
                      p := p + 1
                  | none =>
                    b := b.push c
                    p := p + 1
                else
                  b := b.push c
                  p := p + 1
              else break
            out := out ++ b
            changed := true
            i := k
          | none =>
            out := out ++ String.ofList (cs.extract i j).toList
            i := j
        | none =>
          out := out.push cs[i]
          i := i + 1
      else
        out := out.push cs[i]
        i := i + 1
    else break
  return (out, changed)

/-- A text with the commands expanded, pass by pass until no use is left —
each pass removes one level of uses written inside arguments, so a text
needs at most as many passes as it is long — stopping where the text has
grown past what its uses could honestly make of it, the rest left for the
reading to name. -/
public def expandMacros (ms : Array Macro) (s : String) : String := Id.run do
  if ms.isEmpty || !s.contains '\\' then return s
  let cap := 64 * s.length + 4096
  let mut cur := s
  for _ in [0:s.length + 1] do
    let (next, changed) := expandOnce ms cur
    if !changed || next.length > cap then break
    cur := next
  return cur

/-- The definitions in a `@preamble`'s text, in order: `\newcommand`,
`\renewcommand`, `\providecommand` — starred or not, the name braced or
bare, `[n]` parameters — and `\def\name#1…#n{body}`, each body expanded
over the definitions before it, so a use never reaches a definition made
after the text it stands in. A `\providecommand` of a name already defined
defines nothing. -/
public def preambleMacros (texts : Array String) : Array Macro := Id.run do
  let mut ms : Array Macro := #[]
  for t in texts do
    let cs := t.toList.toArray
    let mut i := 0
    for _ in [0:cs.size + 1] do
      if h : i < cs.size then
        if cs[i] != '\\' then
          i := i + 1
          continue
        match ctrlAt cs i with
        | none => i := i + 1
        | some (cmd, j) =>
          if cmd == "newcommand" || cmd == "renewcommand" || cmd == "providecommand" then
            let j := if cs[j]? == some '*' then j + 1 else j
            let j := skipWs cs j
            let named : Option (String × Nat) :=
              match groupAt cs j with
              | some (g, k) =>
                let g := g.trimAscii.toString
                if g.startsWith "\\" then some ((g.drop 1).toString, k) else none
              | none => ctrlAt cs j
            match named with
            | none => i := j
            | some (name, k) =>
              let k := skipWs cs k
              let (arity, k) :=
                if cs[k]? == some '[' then
                  match (String.ofList (cs.extract (k + 1) cs.size).toList).splitOn "]" with
                  | n :: _ => (n.trimAscii.toString.toNat?.getD 0, k + n.length + 2)
                  | [] => (0, k)
                else (0, k)
              let k := skipWs cs k
              match groupAt cs k with
              | some (body, k') =>
                unless cmd == "providecommand" && ms.any (·.name == name) do
                  ms := ms.push { name, arity, body := expandMacros ms body }
                i := k'
              | none => i := k
          else if cmd == "def" then
            match ctrlAt cs (skipWs cs j) with
            | some (name, k) =>
              -- the parameter text: `#1#2…` up to the body's brace
              let mut arity := 0
              let mut p := k
              for _ in [0:cs.size] do
                if cs[p]? == some '#' then
                  arity := arity + 1
                  p := p + 2
                else break
              match groupAt cs (skipWs cs p) with
              | some (body, k') =>
                ms := ms.push { name, arity, body := expandMacros ms body }
                i := k'
              | none => i := p
            | none => i := j
          else i := j
      else break
  return ms

end LeanTex.Core.Bib
