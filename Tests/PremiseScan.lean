module

public import Tests.Support
public import Std.Data.HashMap
public import Std.Data.HashSet

public section

/-!
# Reading what the world premises are held to

The machinery behind `Tests/Premises.lean`: a lexer for Lean sources that
drops comments and reads strings, the spawn sites each source holds and the
tools they name, and the toolchain modules the engine's imports reach. The
registry, and the judge that holds it to what is read here, live there.
-/

namespace Premises

/-- The repository's own executables, which are Lean and no residue. -/
def selfBin : String := ".lake/build/bin/"

/-! ## Reading a source -/

inductive Kind where
  | ident
  | str
  | interp
  | num
  | sym
  deriving BEq, Repr, Inhabited

/-- One token: an identifier (dots included), a string literal's decoded
contents, the open or close of an interpolated string, a number, or one
symbol. `decl` is the declaration it stands in and `ns` the namespace;
`declares` marks the name a declaration keyword introduces, `hidden` a
private one, and `proof` a token of a theorem, a lemma or an example, which
no build runs. -/
structure Tok where
  kind : Kind
  text : String
  line : Nat
  col : Nat
  first : Bool
  decl : String := ""
  ns : String := ""
  declares : Bool := false
  hidden : Bool := false
  proof : Bool := false
  deriving Inhabited

private def isIdStart (c : UInt8) : Bool :=
  (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122) || c == 95

private def isDigit (c : UInt8) : Bool := 48 ≤ c && c ≤ 57

private def isIdRest (c : UInt8) : Bool :=
  isIdStart c || isDigit c || c == 39 || c == 33 || c == 63

private def utf8Len (c : UInt8) : Nat :=
  if c < 0x80 then 1 else if c < 0xE0 then 2 else if c < 0xF0 then 3 else 4

private def textOf (b : ByteArray) (i j : Nat) : String :=
  (String.fromUTF8? (b.extract i j)).getD "�"

private def tok (kind : Kind) (text : String) (line col : Nat) (first : Bool) : Tok :=
  { kind, text, line, col, first }

private def byteAt (b : ByteArray) (i : Nat) : UInt8 :=
  if h : i < b.size then b[i] else 0

/-- The tokens of a Lean source. Comments (nested block comments included)
and char literals are dropped; plain, raw and interpolated strings are
recognised, and the code inside an interpolation is read as code. -/
def lexRaw (src : String) : Array Tok := Id.run do
  let b := src.toUTF8
  let n := b.size
  let mut out : Array Tok := #[]
  let mut i := 0
  let mut line := 1
  let mut lineStart := 0
  let mut lastLine := 0
  let mut braces := 0
  let mut resume : List Nat := []
  let mut inInterp := false
  for _ in [0:n + 1] do
    if i ≥ n then break
    let c := byteAt b i
    if inInterp then
      if c == 92 then
        if byteAt b (i + 1) == 10 then
          line := line + 1
          lineStart := i + 2
        i := i + 2
      else if c == 34 then
        out := out.push (tok .interp "\"" line (i - lineStart) (lastLine != line))
        lastLine := line
        inInterp := false
        i := i + 1
      else if c == 123 then
        out := out.push (tok .sym "{" line (i - lineStart) (lastLine != line))
        lastLine := line
        resume := braces :: resume
        inInterp := false
        i := i + 1
      else
        if c == 10 then
          line := line + 1
          lineStart := i + 1
        i := i + 1
    else if c == 10 then
      line := line + 1
      lineStart := i + 1
      i := i + 1
    else if c == 32 || c == 9 || c == 13 then
      i := i + 1
    else if c == 45 && byteAt b (i + 1) == 45 then
      let mut j := i + 2
      for _ in [0:n] do
        if j ≥ n || byteAt b j == 10 then break
        j := j + 1
      i := j
    else if c == 47 && byteAt b (i + 1) == 45 then
      let mut depth := 1
      let mut j := i + 2
      for _ in [0:n] do
        if j ≥ n then break
        let d := byteAt b j
        if d == 47 && byteAt b (j + 1) == 45 then
          depth := depth + 1
          j := j + 2
        else if d == 45 && byteAt b (j + 1) == 47 then
          depth := depth - 1
          j := j + 2
          if depth == 0 then break
        else
          if d == 10 then
            line := line + 1
            lineStart := j + 1
          j := j + 1
      i := j
    else if c == 34 then
      let startLine := line
      let col := i - lineStart
      let mut acc := ByteArray.empty
      let mut j := i + 1
      for _ in [0:n] do
        if j ≥ n then break
        let d := byteAt b j
        if d == 34 then
          j := j + 1
          break
        if d == 92 then
          let e := byteAt b (j + 1)
          if e == 10 then
            line := line + 1
            j := j + 2
            lineStart := j
            for _ in [0:n] do
              if j < n && (byteAt b j == 32 || byteAt b j == 9) then j := j + 1 else break
          else
            let decoded : Option UInt8 :=
              if e == 110 then some 10 else if e == 116 then some 9
              else if e == 92 || e == 34 || e == 39 then some e else none
            acc := match decoded with
              | some v => acc.push v
              | none => (acc.push d).push e
            j := j + 2
        else
          if d == 10 then
            line := line + 1
            lineStart := j + 1
          acc := acc.push d
          j := j + 1
      out := out.push (tok .str ((String.fromUTF8? acc).getD "�") startLine col
        (lastLine != startLine))
      lastLine := startLine
      i := j
    else if c == 39 then
      if byteAt b (i + 1) == 92 then
        let mut k := i + 3
        let mut found := false
        for _ in [0:12] do
          if k < n && byteAt b k == 39 then
            found := true
            break
          k := k + 1
        if found then i := k + 1
        else
          out := out.push (tok .sym "'" line (i - lineStart) (lastLine != line))
          lastLine := line
          i := i + 1
      else
        let len := utf8Len (byteAt b (i + 1))
        if byteAt b (i + 1) != 39 && i + 1 < n && byteAt b (i + 1 + len) == 39 then
          i := i + 2 + len
        else
          out := out.push (tok .sym "'" line (i - lineStart) (lastLine != line))
          lastLine := line
          i := i + 1
    else if c == 114 && (byteAt b (i + 1) == 34 || byteAt b (i + 1) == 35) then
      let mut hashes := 0
      let mut k := i + 1
      for _ in [0:n] do
        if k < n && byteAt b k == 35 then
          hashes := hashes + 1
          k := k + 1
        else break
      if byteAt b k == 34 then
        let startLine := line
        let col := i - lineStart
        let body := k + 1
        let mut j := body
        let mut stop := n
        for _ in [0:n] do
          if j ≥ n then break
          if byteAt b j == 34 && (List.range hashes).all (fun h => byteAt b (j + 1 + h) == 35) then
            stop := j
            break
          if byteAt b j == 10 then
            line := line + 1
            lineStart := j + 1
          j := j + 1
        out := out.push (tok .str (textOf b body stop) startLine col (lastLine != startLine))
        lastLine := startLine
        i := min n (stop + 1 + hashes)
      else
        out := out.push (tok .ident "r" line (i - lineStart) (lastLine != line))
        lastLine := line
        i := i + 1
    else if isIdStart c then
      let mut j := i
      for _ in [0:n] do
        if j < n && isIdRest (byteAt b j) then j := j + 1
        else if j + 1 < n && byteAt b j == 46 && isIdStart (byteAt b (j + 1)) then j := j + 1
        else break
      let text := textOf b i j
      if text.endsWith "!" && byteAt b j == 34 then
        out := out.push (tok .interp (text ++ "\"") line (i - lineStart) (lastLine != line))
        inInterp := true
        i := j + 1
      else
        out := out.push (tok .ident text line (i - lineStart) (lastLine != line))
        i := j
      lastLine := line
    else if isDigit c then
      let mut j := i
      for _ in [0:n] do
        if j < n && (isIdRest (byteAt b j) || (byteAt b j == 46 && isDigit (byteAt b (j + 1)))) then
          j := j + 1
        else break
      out := out.push (tok .num (textOf b i j) line (i - lineStart) (lastLine != line))
      lastLine := line
      i := j
    else
      let len := utf8Len c
      let text := textOf b i (i + len)
      if c == 125 && resume.head? == some braces then
        out := out.push (tok .sym "}" line (i - lineStart) (lastLine != line))
        resume := resume.tail
        inInterp := true
      else
        if c == 123 then braces := braces + 1
        if c == 125 then braces := braces - 1
        out := out.push (tok .sym text line (i - lineStart) (lastLine != line))
      lastLine := line
      i := i + len
  return out

def declKeywords : List String :=
  ["def", "theorem", "abbrev", "instance", "structure", "inductive", "class", "opaque",
   "axiom", "example", "lemma", "macro", "syntax", "elab"]

/-- The keywords that open a command wherever they stand, a docstring, a
`set_option … in` or an indentation before them: Lean's reserved declaration
keywords and its initializers. `lemma` is no keyword of core Lean (`let lemma
:= 1` binds a name), so it opens a command only at a command's position
(`atCommand`). -/
def commandKeywords : List String :=
  ["def", "theorem", "abbrev", "instance", "structure", "inductive", "class", "opaque",
   "axiom", "example", "macro", "syntax", "elab", "initialize", "builtin_initialize"]

/-- The keywords that open and close a scope, reserved like the declaration
keywords, so each is a command wherever it stands. -/
def scopeWords : List String := ["namespace", "section", "mutual", "end"]

def modifierWords : List String :=
  ["private", "public", "protected", "noncomputable", "unsafe", "partial", "nonrec", "meta"]

/-- Is the token at `k` a command's keyword: on a line whose first token
stands at column 0, after nothing but modifiers and attribute groups? -/
def atCommand (ts : Array Tok) (k : Nat) : Bool := Id.run do
  let line := ts[k]!.line
  let mut j := k
  for _ in [0:k + 1] do
    if j == 0 || ts[j - 1]!.line != line then break
    j := j - 1
  unless ts[j]!.first && ts[j]!.col == 0 do return false
  let mut m := j
  for _ in [0:k + 1] do
    if m ≥ k then break
    let u := ts[m]!
    if u.kind == .sym && u.text == "@" && (ts[m + 1]?.map (·.text)) == some "[" then
      let mut depth := 0
      let mut e := m + 1
      for n in [m + 1:k] do
        let v := ts[n]!
        if v.kind == .sym && v.text == "[" then depth := depth + 1
        if v.kind == .sym && v.text == "]" then
          depth := depth - 1
          if depth == 0 then
            e := n
            break
      m := e + 1
    else if u.kind == .ident && modifierWords.contains u.text then m := m + 1
    else return false
  return m == k

/-- Does the token at `k` follow the one before it with nothing between? -/
def touches (ts : Array Tok) (k : Nat) : Bool :=
  k > 0 && ts[k - 1]!.line == ts[k]!.line && ts[k - 1]!.col + ts[k - 1]!.text.utf8ByteSize == ts[k]!.col

/-- Each token's declaration and namespace, and the names declarations
introduce, private ones marked, and whether it is a proof's: from a
`theorem`, `lemma` or `example` command to the next command or the proof's
`where`, whose helpers are code. A command keyword opens a command wherever
it stands (`commandKeywords`), and so does a scope keyword, except where
Lean reads a keyword as a name: inside an attribute (`@[…]`, `attribute
[…]`) or a syntax quotation, as a constructor after `|`, after `.`, a
backtick, `«` or `deriving`. `lemma` opens one only at a command's position,
so `let lemma := …` inside a definition declares nothing; an initializer is
a declaration named `initialize` unless it names its own. Any other token at
column 0 ends a proof. `namespace`, `section`, `mutual` and `end` scope as
Lean scopes them; a section and a mutual block name no namespace. -/
def lex (src : String) : Array Tok := Id.run do
  let ts := lexRaw src
  let mut out := ts
  let mut cur := ""
  let mut proof := false
  let mut scopes : Array (Option String) := #[]
  let mut ns := ""
  let mut attr := 0
  let mut quote := 0
  for k in [0:ts.size] do
    let t := ts[k]!
    let prev := if k > 0 then ts[k - 1]!.text else ""
    if t.kind == .sym && t.text == "(" then
      if quote > 0 then quote := quote + 1
      else if prev == "`" && touches ts k then quote := 1
    else if quote > 0 && t.kind == .sym && t.text == ")" then quote := quote - 1
    if t.kind == .sym && t.text == "[" then
      if attr > 0 || (prev == "@" && touches ts k) || prev == "attribute" then attr := attr + 1
    else if attr > 0 && t.kind == .sym && t.text == "]" then attr := attr - 1
    let raw := prev == "|" || prev == "«" || ((prev == "." || prev == "`") && touches ts k)
    let live := t.kind == .ident && attr == 0 && quote == 0 && !raw
    if live && scopeWords.contains t.text then
      let named : Option String := match ts[k + 1]? with
        | some nx => if nx.kind == .ident && nx.line == t.line then some nx.text else none
        | none => none
      match t.text, named with
      | "namespace", some n => scopes := scopes ++ ((n.splitOn ".").map some).toArray
      | "end", some n => scopes := scopes.extract 0 (scopes.size - (n.splitOn ".").length)
      | "end", none => scopes := scopes.pop
      | _, _ => scopes := scopes.push none
      ns := ".".intercalate (scopes.toList.filterMap id)
      proof := false
    let opens := live &&
      ((commandKeywords.contains t.text && prev != "deriving") || (t.text == "lemma" && atCommand ts k))
    if opens then
      proof := ["theorem", "lemma", "example"].contains t.text
      let initializer := t.text == "initialize" || t.text == "builtin_initialize"
      match ts[k + 1]? with
      | some nx =>
        let named := nx.kind == .ident && !declKeywords.contains nx.text &&
          !commandKeywords.contains nx.text && (!initializer || (ts[k + 2]?.map (·.text)) == some ":")
        if named then
          cur := nx.text
          let hidden := (k ≥ 1 && ts[k - 1]!.text == "private") ||
            (k ≥ 2 && ts[k - 2]!.text == "private" && ts[k - 2]!.line == t.line)
          out := out.set! (k + 1) { nx with declares := true, hidden }
        else cur := if initializer then "initialize" else t.text
      | none => cur := t.text
    else if t.first && t.col == 0 then proof := false
    if proof && t.kind == .ident && t.text == "where" then proof := false
    out := out.modify k fun x => { x with decl := cur, ns, proof }
  return out

def lastName (s : String) : String := (s.splitOn ".").getLastD s

def basename (s : String) : String := (s.splitOn "/").getLastD s

def stemOf (file : String) : String :=
  let last := basename file
  if last.endsWith ".lean" then (last.dropEnd 5).toString else last

def moduleOf (path : String) : String :=
  (if path.endsWith ".lean" then (path.dropEnd 5).toString else path).replace "/" "."

/-- One tokenised source: its identifiers indexed by last component, its
declarations by name, and the modules it imports. A strict source is the
engine's, where every spawn expression the scan cannot read is a fault; the
suite and the scripts are read for the tools they name outright. -/
structure Source where
  path : String
  strict : Bool
  toks : Array Tok
  byName : Std.HashMap String (Array Nat)
  declAt : Std.HashMap String Nat
  imports : Array String

def Source.of (path src : String) (strict : Bool := true) : Source := Id.run do
  let toks := lex src
  let mut byName : Std.HashMap String (Array Nat) := {}
  let mut declAt : Std.HashMap String Nat := {}
  let mut imports : Array String := #[]
  for k in [0:toks.size] do
    let t := toks[k]!
    if t.kind == .ident then
      let key := lastName t.text
      byName := byName.alter key fun seen => some ((seen.getD #[]).push k)
      if t.declares && !declAt.contains t.text then declAt := declAt.insert t.text k
      if t.text == "import" then
        let named := if (toks[k + 1]?.map (·.text)) == some "all" then toks[k + 2]? else toks[k + 1]?
        if let some nx := named then
          if nx.kind == .ident && nx.line == t.line then imports := imports.push nx.text
  return { path, strict, toks, byName, declAt, imports }

def Source.named (src : Source) (name : String) : Array Nat := src.byName.getD (lastName name) #[]

/-! ## Spawn sites -/

/-- Where a spawner's call carries the tool: positional argument `i`, or
the `cmd` field of the spawn record at positional argument `i`. -/
inductive Arg where
  | pos (i : Nat)
  | cmd (i : Nat)
  deriving BEq, Repr, Inhabited

/-- A function that runs the tool its call names: a runtime primitive, a
declaration that forwards its parameter to a spawner (named by its
namespace, as a caller spells it), or an alias, a local name bound to one. -/
structure Spawner where
  full : String
  home : String
  arg : Arg
  alias : Bool := false
  hidden : Bool := false
  deriving Inhabited

def Spawner.bare (s : Spawner) : String := lastName s.full

def Spawner.parent (s : Spawner) : String := ".".intercalate (s.full.splitOn ".").dropLast

def Spawner.same (a b : Spawner) : Bool := a.full == b.full && a.home == b.home

def primitives : Array Spawner :=
  #["spawn", "output", "run"].map fun p => { full := "IO.Process." ++ p, home := "", arg := .cmd 0 }

/-- Does token `t` of `src` name spawner `s`? A dotted name names the
spawner it is a dot-boundary suffix of. A bare name names it only where Lean
resolves it there: inside its namespace, or, for a top-level declaration, in
its file and the files importing it. A private spawner is seen in its file
alone, and an alias by its local name in its file alone. -/
def Spawner.sees (s : Spawner) (src : Source) (t : Tok) : Bool :=
  let id := if t.text.startsWith "_root_." then (t.text.drop 7).toString else t.text
  if s.alias then src.path == s.home && id == s.full
  else if s.hidden && src.path != s.home then false
  else if id.contains '.' then id == s.full || s.full.endsWith ("." ++ id)
  else id == s.bare &&
    (if s.parent.isEmpty then src.path == s.home || src.imports.contains (moduleOf s.home)
     else t.ns == s.parent || t.ns.startsWith (s.parent ++ "."))

/-- How an engine spawn expression that is no literal is resolved.
`forwards`: it is a parameter of the enclosing declaration (or its `cmd`
field, or the variable of a `for` over one), so that declaration is a
spawner and its calls are sites. `derives p`: it is a local the declaration
binds by a `let` reading its parameter `p`, which it forwards. `alias`: the
spawner is bound to a name in this file, and every call of the name here is
a site. `asked spawner home askers`: the tool of a run a host program asked
(`World.Ask.run`), where the programs that ask one are `askers`,
declarations of `home` only `spawner` calls; so `spawner` is a spawner whose
first argument names the tool, its calls are sites, and a run asked anywhere
else, or an asker called from anywhere else, is a fault. The rest read the
tools from a table in the source: Elab's `picTools` with the driver's
`pictureTool.getD` defaults; the `Op.spec` converters; `Spec.tools` with
them. -/
inductive Via where
  | forwards
  | derives (param : String)
  | alias (name : String)
  | asked (spawner home : String) (askers : List String)
  | pictureTools
  | converters
  | conversionTools
  deriving BEq, Repr

structure Route where
  file : String
  spawner : String
  expr : String
  via : Via


/-- What a scan reads: every source, tokenised, and the window of Elab.lean
that declares `picTools`. -/
structure Inputs where
  files : Array Source
  picTools : String
  /-- Every engine module's imports, read off its header, the modules the
  scan does not lex among them. -/
  graph : Std.HashMap String (Array String) := {}

structure Site where
  file : String
  line : Nat
  decl : String
  spawner : String
  expr : String
  tools : List String
  deriving Inhabited

/-- The engine's sites, the suite's and scripts' sites that name their tool
outright, theirs the scan cannot read, every spawner, and the faults. -/
structure Scan where
  sites : Array Site
  suite : Array Site
  blind : Array Site
  spawners : Array Spawner
  faults : Array String

def stopWords : List String :=
  ["then", "else", "do", "with", "in", "at", "catch", "finally", "from", "by", "if", "unless",
   "fun", "match", "let", "have", "show", "return", "where", "for", "try", "mut", "deriving"]

def opening (t : Tok) : Bool :=
  (t.kind == .sym && ["(", "[", "{", "⟨"].contains t.text) ||
    (t.kind == .interp && t.text != "\"")

def closing (t : Tok) : Bool :=
  (t.kind == .sym && [")", "]", "}", "⟩"].contains t.text) ||
    (t.kind == .interp && t.text == "\"")

/-- The last index of the balanced group opening at `k`. -/
def groupEnd (ts : Array Tok) (k : Nat) : Nat := Id.run do
  let mut depth := 0
  for j in [k:ts.size] do
    let t := ts[j]!
    if opening t then depth := depth + 1
    else if closing t then
      depth := depth - 1
      if depth == 0 then return j
  return ts.size - 1

/-- The column of the first token on `k`'s line. -/
def lineIndent (ts : Array Tok) (k : Nat) : Nat := Id.run do
  let line := ts[k]!.line
  let mut col := ts[k]!.col
  for m in [0:k + 1] do
    let t := ts[k - m]!
    if t.line != line then break
    col := t.col
  return col

/-- The positional arguments of the application headed at `k`: tokens on
its line, or on later lines indented past it, up to a keyword or operator.
A named argument `(x := …)` takes no position. -/
def argsAt (ts : Array Tok) (k : Nat) (need : Nat) : Array (Array Tok) := Id.run do
  let head := ts[k]!
  let ind := lineIndent ts k
  let mut args : Array (Array Tok) := #[]
  let mut j := k + 1
  for _ in [0:ts.size] do
    if args.size > need then break
    let some t := ts[j]? | break
    if t.line != head.line && t.first && t.col ≤ ind then break
    if t.kind == .sym && t.text == "#" && (ts[j + 1]?.map (·.text)) == some "[" then
      let e := groupEnd ts (j + 1)
      args := args.push (ts.extract j (e + 1))
      j := e + 1
    else if opening t then
      let e := groupEnd ts j
      let g := ts.extract j (e + 1)
      let named := t.text == "(" && (g[1]?.map (·.kind)) == some .ident &&
        (g[2]?.map (·.text)) == some ":" && (g[3]?.map (·.text)) == some "="
      unless named do args := args.push g
      j := e + 1
    else if t.kind == .sym && t.text == "." then
      match ts[j + 1]? with
      | some nx =>
        if nx.kind == .ident && nx.line == t.line then
          -- After a literal or a group, `.f` projects it; elsewhere `.c` is an argument.
          let prev := ts[j - 1]!
          if j > k + 1 && prev.line == t.line && (prev.kind == .str || closing prev) && !args.isEmpty then
            args := args.modify (args.size - 1) (· ++ #[t, nx])
          else args := args.push #[t, nx]
          j := j + 2
        else break
      | none => break
    else if (t.kind == .ident && !stopWords.contains t.text) || t.kind == .str || t.kind == .num then
      args := args.push #[t]
      j := j + 1
    else break
  return args

def render (g : Array Tok) : String :=
  " ".intercalate (g.toList.map fun t => if t.kind == .str then s!"\"{t.text}\"" else t.text)

/-- The `cmd` field of a spawn record group, up to the next field; a field
abbreviation (`{ cmd, args }`) is the name itself. -/
def cmdField (g : Array Tok) : Option (Array Tok) := Id.run do
  let mut depth := 0
  for k in [0:g.size] do
    let t := g[k]!
    if opening t then depth := depth + 1
    else if closing t then depth := depth - 1
    else if depth == 1 && t.kind == .ident && t.text == "cmd" && k > 0 &&
        ["{", ",", "with"].contains g[k - 1]!.text then
      let nx := (g[k + 1]?.map (·.text)).getD ""
      if nx == "," || nx == "}" then return some #[t]
      if nx == ":" && (g[k + 2]?.map (·.text)) == some "=" then
        let mut e := #[]
        let mut inner := 0
        for m in [k + 3:g.size] do
          let u := g[m]!
          if inner == 0 && (closing u || (u.kind == .sym && u.text == ",") ||
              (u.first && m > k + 3)) then break
          if opening u then inner := inner + 1
          if closing u then inner := inner - 1
          e := e.push u
        return some e
  return none

/-- Is the spawner at `k` an argument rather than an application's head? -/
def isValueUse (ts : Array Tok) (k : Nat) : Bool :=
  if k == 0 then false else
  match ts[k - 1]? with
  | some p =>
    p.line == ts[k]!.line &&
      ((p.kind == .ident && !stopWords.contains p.text) || p.kind == .str || p.kind == .num ||
        closing p)
  | none => false

/-- The tool expression of the call at `k` (`_` for a value use), and whether
it is a whole spawn record rather than the tool itself. -/
def exprAt (ts : Array Tok) (k : Nat) (s : Spawner) : Array Tok × String × Bool :=
  if isValueUse ts k then (#[], "_", false) else
  match s.arg with
  | .pos i =>
    match (argsAt ts k i)[i]? with
    | some g => (g, render g, false)
    | none => (#[], "_", false)
  | .cmd i =>
    match (argsAt ts k i)[i]? with
    | none => (#[], "_", false)
    | some g =>
      if (g[0]?.map (·.text)) == some "{" then
        match cmdField g with
        | some e => (e, render e, false)
        | none => (g, render g, true)
      else (g, render g, true)

/-- The tool spellings an expression states outright: one string, or an
array of strings, which may be empty. -/
def literalTools (expr : Array Tok) : Option (List String) :=
  match expr.toList with
  | [lit] => if lit.kind == .str then some [lit.text] else none
  | hash :: bracket :: rest =>
    if hash.text == "#" && bracket.text == "[" && (rest.getLast?.map (·.text)) == some "]" then
      let inner := rest.dropLast
      if inner.all (fun t => t.kind == .str || (t.kind == .sym && t.text == ",")) then
        some (inner.filterMap fun t => if t.kind == .str then some t.text else none)
      else none
    else none
  | _ => none

/-- The explicit binders of declaration `decl`'s header, in order. -/
def binders (src : Source) (decl : String) : Array String := Id.run do
  let ts := src.toks
  let some k := src.declAt.get? decl | return #[]
  let mut out := #[]
  let mut j := k + 1
  for _ in [0:ts.size] do
    let some t := ts[j]? | break
    if t.kind == .sym && t.text == ":" then break
    if t.kind == .sym && t.text == "|" then break
    if t.kind == .ident && t.text == "where" then break
    if opening t then
      let e := groupEnd ts j
      if t.text == "(" then
        for m in [j + 1:e] do
          let u := ts[m]!
          if u.kind == .ident then out := out.push u.text
          else break
      j := e + 1
    else j := j + 1
  return out

/-- The binder a `for <v> in <binder>` iterates within `decl`. -/
def iterated (ts : Array Tok) (decl v : String) : Option String := Id.run do
  for k in [0:ts.size] do
    let t := ts[k]!
    if t.decl == decl && t.kind == .ident && t.text == "for" &&
        (ts[k + 1]?.map (·.text)) == some v && (ts[k + 2]?.map (·.text)) == some "in" then
      if let some b := ts[k + 3]? then
        if b.kind == .ident then return some b.text
  return none

/-- The spawner a declaration becomes by handing its parameter `head` (or,
for a record, the record whose `cmd` is the tool) to a spawn. -/
def wrapperOf (src : Source) (site : Site) (head : String) (record : Bool) :
    Except String Spawner := do
  let some k := src.declAt.get? site.decl | throw s!"'{site.decl}' is no declaration the scan reads"
  let d := src.toks[k]!
  let bs := binders src site.decl
  let idx ← match bs.findIdx? (· == head), iterated src.toks site.decl head with
    | some i, _ => pure i
    | none, some over =>
      match bs.findIdx? (· == over) with
      | some i => pure i
      | none => throw s!"'{head}' iterates '{over}', which is no parameter of {site.decl}"
    | none, none => throw s!"'{head}' is no parameter of {site.decl}"
  let full := if d.ns.isEmpty then site.decl else d.ns ++ "." ++ site.decl
  return { full, home := src.path, arg := if record then .cmd idx else .pos idx, hidden := d.hidden }

def forwarded (src : Source) (site : Site) (expr : Array Tok) (whole : Bool) :
    Except String Spawner := do
  let some e := expr[0]? | throw "a forwarding route on a value use"
  unless expr.size == 1 && e.kind == .ident do throw s!"'{site.expr}' is not one name"
  match e.text.splitOn "." with
  | [head] => wrapperOf src site head whole
  | [head, "cmd"] => if whole then throw s!"'{site.expr}' is a record's field" else wrapperOf src site head true
  | _ => throw s!"'{site.expr}' is neither a parameter nor its cmd field"

/-- The right-hand side of the `let` that binds `name` in `decl`. -/
def letRhs (ts : Array Tok) (decl name : String) : Option (Array Tok) := Id.run do
  for k in [0:ts.size] do
    let t := ts[k]!
    if t.decl == decl && t.kind == .ident && t.text == "let" && (ts[k + 1]?.map (·.text)) == some name then
      let ind := lineIndent ts k
      let mut rhs := #[]
      for j in [k + 2:ts.size] do
        let u := ts[j]!
        if u.line != t.line && u.first && u.col ≤ ind then break
        rhs := rhs.push u
      return some rhs
  return none

/-- The spawner a declaration becomes when its spawn runs a local it binds
from its parameter `param` alone: the `let` reads `param` and spells no
string, which the scan could not tell from a tool. -/
def derived (src : Source) (site : Site) (expr : Array Tok) (param : String) :
    Except String Spawner := do
  let some e := expr[0]? | throw "a derived route on a value use"
  unless expr.size == 1 && e.kind == .ident && !e.text.contains '.' do
    throw s!"'{site.expr}' is not one local name"
  let some rhs := letRhs src.toks site.decl e.text | throw s!"{site.decl} binds no '{e.text}' by a let"
  unless rhs.any (fun u => u.kind == .ident && (u.text == param || u.text.startsWith (param ++ "."))) do
    throw s!"{site.decl} binds '{e.text}' by a let that does not read its parameter '{param}'"
  if rhs.any (·.kind == .str) then
    throw s!"{site.decl} binds '{e.text}' by a let that spells a string, which the scan cannot tell from a tool"
  wrapperOf src site param false

def strsAfter (ts : Array Tok) (decl : String) (before : List String) : List String := Id.run do
  let mut out := []
  for k in [0:ts.size] do
    let t := ts[k]!
    if t.decl == decl && t.kind == .str then
      let n := before.length
      let prev := (List.range n).map fun m => (ts[k - n + m]?.map (·.text)).getD ""
      if k ≥ n && prev == before then out := out ++ [t.text]
  return out

def picToolsOf (window : String) : List String := Id.run do
  let ts := lex window
  let mut out := []
  let mut on := false
  for k in [0:ts.size] do
    let t := ts[k]!
    if t.decl == "picTools" && t.kind == .sym && t.text == "[" then on := true
    else if on && t.kind == .sym && t.text == "]" then break
    else if on && t.kind == .str then out := out ++ [t.text]
  return out

/-- The tools a table route reads, or why it reads none. -/
def derive (inp : Inputs) (src : Source) : Via → Except String (List String)
  | .pictureTools => do
    let declared := picToolsOf inp.picTools
    if declared.isEmpty then throw "Elab's picTools list reads no tool"
    let defaults := inp.files.toList.flatMap fun f => Id.run do
      let mut out := []
      for k in f.named "getD" do
        if f.toks[k]!.text.endsWith "pictureTool.getD" then
          if let some v := f.toks[k + 1]? then
            if v.kind == .str then out := out ++ [v.text]
      return out
    return (declared ++ defaults).eraseDups
  | .converters => do
    let tools := strsAfter src.toks "Op.spec" ["⟨"]
    if tools.isEmpty then throw s!"{src.path}'s Op.spec table reads no converter"
    return tools.eraseDups
  | .conversionTools => do
    let validation := strsAfter src.toks "Spec.tools" ["#", "["]
    let converters := strsAfter src.toks "Op.spec" ["⟨"]
    if validation.isEmpty || converters.isEmpty then
      throw s!"{src.path}'s Spec.tools and Op.spec read no tool"
    return (validation ++ converters).eraseDups
  | .forwards | .derives _ | .alias _ | .asked .. => return []

/-- What an `open` or `export` names: its namespaces, and which of their
declarations it brings into scope, those its parenthesised list or its
`renaming` names, or else all but those it hides. -/
structure OpenClause where
  names : List String
  only : Option (List String)
  hides : List String

def OpenClause.exposes (c : OpenClause) (bare : String) : Bool :=
  match c.only with
  | some listed => listed.contains bare
  | none => !c.hides.contains bare

def openClause (ts : Array Tok) (k : Nat) : OpenClause := Id.run do
  let head := ts[k]!
  let ind := lineIndent ts k
  let within (u : Tok) : Bool := u.line == head.line || !u.first || u.col > ind
  let mut names : List String := []
  let mut j := k + 1
  for _ in [0:ts.size] do
    let some u := ts[j]? | break
    unless within u && u.kind == .ident do break
    if ["in", "hiding", "renaming"].contains u.text then break
    unless u.text == "scoped" do names := names ++ [u.text]
    j := j + 1
  let some u := ts[j]? | return { names, only := none, hides := [] }
  unless within u do return { names, only := none, hides := [] }
  if u.kind == .sym && u.text == "(" then
    let e := groupEnd ts j
    let listed := ((ts.extract (j + 1) e).toList.filter (·.kind == .ident)).map (·.text)
    return { names, only := some listed, hides := [] }
  if u.text == "renaming" then
    let mut sources : List String := []
    for m in [j + 1:ts.size] do
      let v := ts[m]!
      if !(within v) || v.text == "in" then break
      let arrow := (ts[m + 1]?.map (·.text)) == some "→" ||
        ((ts[m + 1]?.map (·.text)) == some "-" && (ts[m + 2]?.map (·.text)) == some ">")
      if v.kind == .ident && arrow then sources := sources ++ [v.text]
    return { names, only := some sources, hides := [] }
  if u.text == "hiding" then
    let mut hidden : List String := []
    for m in [j + 1:ts.size] do
      let v := ts[m]!
      if !(within v) || v.kind != .ident || v.text == "in" then break
      hidden := hidden ++ [v.text]
    return { names, only := none, hides := hidden }
  return { names, only := none, hides := [] }

def Route.key (r : Route) : String := s!"{r.file} {r.spawner} {r.expr}"

/-! ## Names a suite or script binds to its tool -/

/-- The top-level items of the group `g`, whose first token opens it and
whose last closes it, split at its commas. -/
def groupItems (g : Array Tok) : Array (Array Tok) := Id.run do
  let mut items : Array (Array Tok) := #[]
  let mut cur : Array Tok := #[]
  let mut depth := 0
  for t in g do
    if opening t then
      depth := depth + 1
      if depth == 1 then continue
    else if closing t then
      depth := depth - 1
      if depth == 0 then continue
    if depth == 1 && t.kind == .sym && t.text == "," then
      items := items.push cur
      cur := #[]
    else cur := cur.push t
  unless cur.isEmpty do items := items.push cur
  return items

/-- The functions that turn a literal into the path of a tool. -/
def pathFns : List String :=
  ["IO.FS.realPath", "System.FilePath.mk", "ToolProbe.onPath", "LeanTex.Cli.ToolProbe.onPath", "onPath"]

/-- The literal one result spells: a string, alone or as a path function's
argument, behind `←`, `some`, `pure`, `return` or parentheses, with any
`.toString` after it; or a path joined by `/` from names and strings that
ends in a string, read as the strings it ends in, joined. -/
def resultLiteral (seg : Array Tok) : Option String := Id.run do
  let mut xs := seg
  for _ in [0:seg.size + 1] do
    let n := xs.size
    if n ≥ 2 && xs[n - 2]!.text == "." && xs[n - 1]!.text == "toString" then
      xs := xs.extract 0 (n - 2)
    else if n ≥ 1 && (["←", "some", "pure", "return"].contains xs[0]!.text || pathFns.contains xs[0]!.text) then
      xs := xs.extract 1 n
    else if n ≥ 2 && xs[0]!.text == "(" && xs[0]!.kind == .sym && groupEnd xs 0 == n - 1 then
      xs := xs.extract 1 (n - 1)
    else break
  match xs.toList with
  | [lit] => return if lit.kind == .str then some lit.text else none
  | _ =>
    let n := xs.size
    let joined := n ≥ 3 && n % 2 == 1 && (List.range n).all fun k =>
      if k % 2 == 1 then xs[k]!.kind == .sym && xs[k]!.text == "/"
      else xs[k]!.kind == .ident || xs[k]!.kind == .str
    unless joined && xs[n - 1]!.kind == .str do return none
    let parts := ((List.range n).filter (· % 2 == 0)).reverse.map (xs[·]!)
    return some ("/".intercalate (parts.takeWhile (·.kind == .str) |>.reverse |>.map (·.text)))

/-- Each result an expression can take: the arms of a `match`, the branches
of an `if` chain, or the whole expression up to a pattern `let`'s `|`
alternative. Conditions and patterns are no result. -/
def results (rhs : Array Tok) : Array (Array Tok) := Id.run do
  let isMatch := (rhs[0]?.map (·.text)) == some "match"
  let mut out : Array (Array Tok) := #[]
  let mut cur : Array Tok := #[]
  let mut depth := 0
  let mut taking := !isMatch
  for k in [0:rhs.size] do
    let t := rhs[k]!
    if opening t then depth := depth + 1
    else if closing t then depth := depth - 1
    let top := depth == 0 && t.kind == .sym
    if top && t.text == "|" then
      if !isMatch then break
      if taking && !cur.isEmpty then out := out.push cur
      cur := #[]
      taking := false
      continue
    if isMatch && top && t.text == "=" && (rhs[k + 1]?.map (·.text)) == some ">" then
      taking := true
      continue
    if isMatch && top && t.text == ">" && k > 0 && rhs[k - 1]!.text == "=" then continue
    if !isMatch && depth == 0 && t.kind == .ident && (t.text == "then" || t.text == "else") then
      out := out.push cur
      cur := #[]
      continue
    if taking then cur := cur.push t
  unless cur.isEmpty do out := out.push cur
  return if isMatch then out else out.filter fun s => (s[0]?.map (·.text)) != some "if"

/-- A literal that can name a command: not empty, no flag, no white space. -/
def commandLike (s : String) : Bool :=
  !s.isEmpty && !s.startsWith "-" && !s.any Char.isWhitespace

/-- The literals the results of `rhs` spell, or none when none spells one.
A result that is no literal, such as a path the caller passes in, is not
read. -/
def resultLiterals (rhs : Array Tok) : Option (Array String) :=
  let lits := (results rhs).filterMap fun r => (resultLiteral r).filter commandLike
  if lits.isEmpty then none else some lits

/-- The last `let` before line `line` in `decl` binding `name` alone (`let`,
`let mut`, `let some`): its line, and its right-hand side from after `:=` or
`←` to the end of the binding. -/
def bindingRhs (ts : Array Tok) (decl name : String) (line : Nat) : Option (Nat × Array Tok) := Id.run do
  let mut found : Option (Nat × Array Tok) := none
  for k in [0:ts.size] do
    let t := ts[k]!
    if t.line > line then break
    unless t.decl == decl && t.kind == .ident && t.text == "let" do continue
    let mut j := k + 1
    if (ts[j]?.map (·.text)) == some "mut" then j := j + 1
    if (ts[j]?.map (·.text)) == some "some" then j := j + 1
    unless (ts[j]?.map (·.text)) == some name && (ts[j]?.map (·.kind)) == some .ident do continue
    let mut start := 0
    for m in [j + 1:ts.size] do
      let u := ts[m]!
      if u.line != t.line && u.first then break
      if u.text == "←" then
        start := m + 1
        break
      if u.text == ":" && (ts[m + 1]?.map (·.text)) == some "=" then
        start := m + 2
        break
    if start == 0 then continue
    let ind := lineIndent ts k
    let mut rhs := #[]
    for m in [start:ts.size] do
      let u := ts[m]!
      if u.line != t.line && u.first && u.col ≤ ind then break
      rhs := rhs.push u
    found := some (t.line, rhs)
  return found

/-- The last `for` before line `line` in `decl` whose pattern binds `name`,
alone or as a tuple's component: its line, and the literals it hands
`name` from the written list it iterates, inline or bound by a `let`, or
none when the list is not one the scan reads. -/
def forBinding (ts : Array Tok) (decl name : String) (line : Nat) : Option (Nat × Option (Array String)) := Id.run do
  let mut found : Option (Nat × Option (Array String)) := none
  for k in [0:ts.size] do
    let t := ts[k]!
    if t.line > line then break
    unless t.decl == decl && t.kind == .ident && t.text == "for" do continue
    let some p := ts[k + 1]? | continue
    let (pos, after) : Option Nat × Nat :=
      if p.kind == .ident && p.text == name then (none, k + 2)
      else if p.kind == .sym && p.text == "(" then
        let e := groupEnd ts (k + 1)
        match (groupItems (ts.extract (k + 1) (e + 1))).findIdx?
            (fun it => it.size == 1 && it[0]!.text == name) with
        | some i => (some i, e + 1)
        | none => (none, 0)
      else (none, 0)
    if after == 0 || (ts[after]?.map (·.text)) != some "in" then continue
    let c := if (ts[after + 1]?.map (·.text)) == some "#" then after + 2 else after + 1
    let written (g : Array Tok) : Bool := (g[0]?.map (·.text)) == some "[" && groupEnd g 0 == g.size - 1
    let list : Option (Array Tok) :=
      if (ts[c]?.map (·.text)) == some "[" then some (ts.extract c (groupEnd ts c + 1))
      else match ts[c]? with
        | some id =>
          if id.kind != .ident then none
          else (bindingRhs ts decl id.text t.line).bind fun (_, rhs) =>
            let rhs := if (rhs[0]?.map (·.text)) == some "#" then rhs.extract 1 rhs.size else rhs
            if written rhs then some rhs else none
        | none => none
    let lits := list.bind fun (g : Array Tok) =>
      let taken := (groupItems g).filterMap fun (el : Array Tok) =>
        let lit : Option String := match pos with
          | none => resultLiteral el
          | some i =>
            if (el[0]?.map (·.text)) == some "(" && groupEnd el 0 == el.size - 1 then
              ((groupItems el)[i]?).bind resultLiteral
            else none
        lit.filter commandLike
      if taken.isEmpty then none else some taken
    found := some (t.line, lits)
  return found

/-- The literals the top-level constant `name` is bound to, in `src` or in
a source it imports: a declaration with no explicit binders whose body
after `:=` spells them as `resultLiterals` reads. -/
def constLiterals (files : Array Source) (src : Source) (name : String) : Option (Array String) := Id.run do
  for f in files do
    unless f.path == src.path || src.imports.contains (moduleOf f.path) do continue
    let some k := f.declAt.get? name | continue
    unless (binders f name).isEmpty do continue
    let mut start := 0
    for m in [k + 1:f.toks.size] do
      let u := f.toks[m]!
      if u.decl != name then break
      if u.text == ":" && (f.toks[m + 1]?.map (·.text)) == some "=" then
        start := m + 2
        break
    if start == 0 then continue
    let mut body := #[]
    for m in [start:f.toks.size] do
      let u := f.toks[m]!
      if u.decl != name || (u.first && u.col == 0) then break
      body := body.push u
    return resultLiterals body
  return none

/-- The tools a suite or script spawn expression that is no literal names
through a binding the scan reads: the nearer of a `let` and a `for` in its
declaration, else a top-level constant, else a path joined to a literal;
for a whole spawn record bound by a `let`, its `cmd` field read the same
way. None when the binding is not one the scan reads. -/
def boundTools (files : Array Source) (src : Source) (site : Site) (expr : Array Tok) (whole : Bool) :
    Option (List String) :=
  let byName (x : Tok) : Option (Array String) :=
    if x.kind != .ident then none else
    let name := if x.text.endsWith ".toString" then (x.text.dropEnd 9).toString else x.text
    if name.contains '.' then none else
    let viaLet := bindingRhs src.toks site.decl name site.line
    let viaFor := forBinding src.toks site.decl name site.line
    match viaLet, viaFor with
    | some (l, rhs), some (f, lits) => if f > l then lits else resultLiterals rhs
    | some (_, rhs), none => resultLiterals rhs
    | none, some (_, lits) => lits
    | none, none => constLiterals files src name
  match expr.toList with
  | [x] =>
    if !whole then (byName x).map (·.toList)
    else
      match bindingRhs src.toks site.decl x.text site.line with
      | some (_, rhs) =>
        if (rhs[0]?.map (·.text)) != some "{" then none else
        (cmdField rhs).bind fun field =>
          match field.toList with
          | [y] => if y.kind == .str then some [y.text] else (byName y).map (·.toList)
          | _ => (resultLiteral field).map ([·])
      | none => none
  | _ => if whole then none else (resultLiteral expr).map ([·])

/-- The modules that reach `home`'s module through their imports, however
far, `home`'s own included: read off the scanned sources' headers and, for
the engine modules not lexed, the engine's import graph. -/
def reachers (inp : Inputs) (home : String) : Std.HashSet String := Id.run do
  let mut imports : Std.HashMap String (Array String) := inp.graph
  for src in inp.files do
    imports := imports.insert (moduleOf src.path) src.imports
  let mut importers : Std.HashMap String (Array String) := {}
  for (n, is) in imports.toList do
    for i in is do
      importers := importers.alter i fun seen => some ((seen.getD #[]).push n)
  let mut seen : Std.HashSet String := {}
  let mut todo := #[moduleOf home]
  for _ in [0:imports.size + 2] do
    if todo.isEmpty then break
    let mut next := #[]
    for n in todo do
      unless seen.contains n do
        seen := seen.insert n
        next := next ++ importers.getD n #[]
    todo := next
  return seen

/-- Whether `src` can ask the host to run a tool: it reaches `home` through
its imports however far, a re-export or a Core module among them, or names
the run question outright. -/
def asksHost (reach : Std.HashSet String) (src : Source) : Bool :=
  reach.contains (moduleOf src.path) ||
    src.toks.any fun t => t.kind == .ident && (t.text == "Ask.run" || t.text.endsWith ".Ask.run")

/-- The tokens at which `src` asks the host to run a tool, outside a proof:
`Ask.run` spelled as a name, a bare `run` inside the namespace `Ask`, or
`.run` where a term begins, rather than a projection after a term or a
pattern after a match arm's `|` or a `let`; the `|` of `<|` or `||` opens no
arm. -/
def runAsks (src : Source) : Array Nat := Id.run do
  let ts := src.toks
  let mut out := #[]
  for k in [0:ts.size] do
    let t := ts[k]!
    if t.proof then continue
    if t.kind == .ident && (t.text == "Ask.run" || t.text.endsWith ".Ask.run") then
      out := out.push k
    else if t.kind == .ident && t.text == "run" && !t.declares && (t.ns == "Ask" || t.ns.endsWith ".Ask") then
      out := out.push k
    else if t.kind == .sym && t.text == "." then
      if let some nx := ts[k + 1]? then
        if nx.kind == .ident && nx.text == "run" && nx.line == t.line && nx.col == t.col + 1 then
          let arm := k > 0 && ts[k - 1]!.text == "|" &&
            !(k > 1 && touches ts (k - 1) && ["<", "|"].contains ts[k - 2]!.text)
          let pattern := k > 0 && (let p := ts[k - 1]!
            p.kind == .str || p.kind == .num || closing p || arm || p.text == "let")
          unless pattern do out := out.push k
  return out

/-- A run asked outside the declared askers, an asker called from outside
the spawner and the askers, or an `open` or `export` that lets the run
question or an asker be named bare, where the scan does not read it: what
an `asked` route's reading rests on. -/
def askFaults (inp : Inputs) (spawner home : String) (askers : List String) : Array String := Id.run do
  let parent := ".".intercalate (spawner.splitOn ".").dropLast
  let reach := reachers inp home
  let mut out := #[]
  for src in inp.files do
    unless src.strict do continue
    if asksHost reach src then
      for k in runAsks src do
        let t := src.toks[k]!
        unless src.path == home && askers.contains t.decl do
          out := out.push s!"{src.path}:{t.line}: {t.decl} asks the host to run a tool outside {spawner}, whose calls are where the scan reads tools"
    for a in askers do
      let asker : Spawner := { full := parent ++ "." ++ a, home, arg := .pos 0 }
      for k in src.named a do
        let t := src.toks[k]!
        if t.declares || t.proof || !asker.sees src t then continue
        unless src.path == home && (t.decl == lastName spawner || askers.contains t.decl) do
          out := out.push s!"{src.path}:{t.line}: {t.decl} calls {a}, which only {spawner} may call"
    for k in src.named "open" ++ src.named "export" do
      let t := src.toks[k]!
      unless t.kind == .ident && (t.text == "open" || t.text == "export") do continue
      let clause := openClause src.toks k
      for n in clause.names do
        let n := if n.startsWith "_root_." then (n.drop 7).toString else n
        if (n == "Ask" || n.endsWith ".Ask") && clause.exposes "run" then
          out := out.push
            s!"{src.path}:{t.line}: `{t.text} {n}` lets the host's run question be asked by a bare name the scan does not read; spell it `.run` or `Ask.run`"
        let exposed := askers.filter fun a => (parent == n || parent.endsWith ("." ++ n)) && clause.exposes a
        unless exposed.isEmpty do
          let names := ", ".intercalate (exposed.map (parent ++ "." ++ ·))
          out := out.push
            s!"{src.path}:{t.line}: `{t.text} {n}` lets {names}, which only {spawner} may call, be called by a bare name the scan does not follow; qualify the call"
  return out

/-- Every spawn site, closed under forwarding: each wrapper a route makes of
an engine declaration, and each a suite or script declaration makes by
handing its own parameter on, is itself a spawner, until none is added. An
`open` or `export` that lets an engine spawner be called by a bare name the
scan does not follow is a fault. -/
def scan (inp : Inputs) (rs : List Route) : Scan := Id.run do
  let mut spawners := primitives
  let mut fresh := primitives
  let mut sites : Array Site := #[]
  let mut suite : Array Site := #[]
  let mut blind : Array Site := #[]
  let mut faults : Array String := #[]
  let mut used : Array String := #[]
  for _ in [0:64] do
    if fresh.isEmpty then break
    let mut next : Array Spawner := #[]
    for src in inp.files do
      let ts := src.toks
      for s in fresh do
        for k in src.named s.bare do
          let t := ts[k]!
          if t.declares || t.proof || !s.sees src t then continue
          -- A spawner's bare name can be a parameter that shadows it.
          if !s.alias && !t.text.contains '.' && (binders src t.decl).contains s.bare then continue
          let (expr, text, whole) := exprAt ts k s
          if s.alias && text == "_" then continue
          let site : Site :=
            { file := src.path, line := t.line, decl := t.decl, spawner := s.full, expr := text, tools := [] }
          if let some tools := literalTools expr then
            if src.strict then sites := sites.push { site with tools }
            else suite := suite.push { site with tools := tools.filter (!·.startsWith selfBin) }
            continue
          if !src.strict then
            match forwarded src site expr whole with
            | .ok w => if !(spawners.any w.same) && !(next.any w.same) then next := next.push w
            | .error _ =>
              match boundTools inp.files src site expr whole with
              | some tools => suite := suite.push { site with tools := tools.filter (!·.startsWith selfBin) }
              | none => blind := blind.push site
            continue
          let route := rs.find? fun r => r.file == src.path && r.spawner == s.full && r.expr == text
          match route with
          | none =>
            faults := faults.push
              s!"{src.path}:{t.line}: {s.full} runs '{text}', which no route in Tests/Premises.lean reads"
          | some r =>
            used := used.push r.key
            let made : Option (Except String Spawner) := match r.via with
              | .forwards => some (forwarded src site expr whole)
              | .derives p => some (derived src site expr p)
              | .alias name => some (.ok { full := name, home := src.path, arg := s.arg, alias := true })
              | .asked name home _ => some (.ok { full := name, home, arg := .pos 0 })
              | _ => none
            match made with
            | some (.ok w) =>
              if !(spawners.any w.same) && !(next.any w.same) then next := next.push w
              sites := sites.push site
            | some (.error why) => faults := faults.push s!"{src.path}:{t.line}: {why}"
            | none =>
              match derive inp src r.via with
              | .ok tools => sites := sites.push { site with tools }
              | .error why => faults := faults.push s!"{src.path}:{t.line}: {why}"
    spawners := spawners ++ next
    fresh := next
  unless fresh.isEmpty do faults := faults.push "the forwarding closure did not settle"
  for r in rs do
    unless used.contains r.key do
      faults := faults.push s!"route '{r.key}' reads no spawn site; delete it"
    if let .asked name home askers := r.via then
      faults := faults ++ askFaults inp name home askers
  -- A suite or script run asked of the host names its tool where the scan does not read it.
  for src in inp.files do
    unless !src.strict && src.imports.any (fun m => m.endsWith ".World" || m.endsWith ".Host") do continue
    for k in runAsks src do
      let t := src.toks[k]!
      let site : Site :=
        { file := src.path, line := t.line, decl := t.decl, spawner := "World.Ask.run", expr := "_", tools := [] }
      blind := blind.push site
  let engine := spawners.filter fun s => s.home.isEmpty || inp.files.any (fun f => f.strict && f.path == s.home)
  for src in inp.files do
    let opens := src.named "open"
    let exports := src.named "export"
    let commands := opens ++ exports
    for k in commands do
      let t := src.toks[k]!
      unless t.kind == .ident && (t.text == "open" || t.text == "export") do continue
      let clause := openClause src.toks k
      for n in clause.names do
        let n := if n.startsWith "_root_." then (n.drop 7).toString else n
        let exposed := engine.filter fun s =>
          !s.alias && !s.parent.isEmpty && (!s.hidden || s.home == src.path) &&
            (s.parent == n || s.parent.endsWith ("." ++ n)) && clause.exposes s.bare
        unless exposed.isEmpty do
          let names := ", ".intercalate (exposed.toList.map (·.full))
          faults := faults.push
            s!"{src.path}:{t.line}: `{t.text} {n}` lets {names} be called by a bare name the scan does not follow; qualify the call"
    if src.strict then
      for k in src.named "extern" do
        if k ≥ 2 && (src.toks[k - 1]!.text, src.toks[k - 2]!.text) == ("[", "@") then
          faults := faults.push
            s!"{src.path}:{src.toks[k]!.line}: an extern declaration runs code outside Lean that no row names"
  return { sites, suite, blind, spawners, faults }

/-- The engine's spawn sites whose wait has no time limit, by file and
declaration: every primitive spawn but the budget's own. -/
def Scan.unbudgeted (sc : Scan) (budget : List (String × String)) : List (String × String) :=
  (sc.sites.toList.filter fun s => s.spawner.startsWith "IO.Process." && !budget.contains (s.file, s.decl))
    |>.map (fun s => (s.file, s.decl)) |>.eraseDups

/-- Each tool spelling among `sites`, with one site that spawns it. -/
def spellings (sites : Array Site) : List (String × Site) := Id.run do
  let mut out : List (String × Site) := []
  for s in sites do
    for tool in s.tools do
      unless out.any (·.1 == tool) do out := out ++ [(tool, s)]
  return out

def Scan.tools (sc : Scan) : List (String × Site) := spellings sc.sites

def Scan.suiteTools (sc : Scan) : List (String × Site) := spellings sc.suite

/-- Every word a scanned string spells, by its last path component: what a
row's further tools must each be one of. -/
def mentioned (inp : Inputs) : Std.HashSet String := Id.run do
  let mut out : Std.HashSet String := {}
  for src in inp.files do
    for t in src.toks do
      if t.kind == .str then
        let mut word := ""
        for c in t.text.toList ++ [' '] do
          if c.isAlphanum || c == '.' || c == '_' || c == '/' || c == '-' || c == '+' then word := word.push c
          else
            unless word.isEmpty do out := out.insert (basename word)
            word := ""
  return out

/-! ## The toolchain the engine's imports reach

The scan reads IO.Process's three spawners as its primitives, which holds
only while nothing the engine can call starts a process another way. That
is a fact of the toolchain's library, read here off its shipped sources. -/

/-- The modules a source imports, read off its header: each `import`,
`public import`, `meta import` and `import all` before the first command
that is none of them, comments, `module` and `prelude` skipped. -/
def headerImports (text : String) : Array String :=
  let read (lines : List String) : Array String × Bool := Id.run do
    let mut out := #[]
    let mut depth := 0
    for raw in lines do
      let line := raw.trimAscii.toString
      if depth > 0 || line.startsWith "/-" then
        depth := depth + ((line.splitOn "/-").length - 1)
        depth := depth - min depth ((line.splitOn "-/").length - 1)
        continue
      if line.isEmpty || line.startsWith "--" || line == "module" || line == "prelude" then continue
      let words := ((line.splitOn " ").filter (!·.isEmpty)).dropWhile
        fun w => w == "public" || w == "meta" || w == "private"
      match words with
      | "import" :: "all" :: m :: _ => out := out.push m
      | "import" :: m :: _ => out := out.push m
      | _ => return (out, true)
    return (out, false)
  -- A header is short: read a prefix, and more only when the header runs
  -- past it.
  let (head, ended) := read ((text.take 2048).toString.splitOn "\n")
  if ended then head else (read (text.splitOn "\n")).1

/-- Where the toolchain keeps its sources: `$LEAN_SYSROOT/src/lean`, with
Lake's tree beside it. -/
def toolchainRoots : IO (Except String (Array System.FilePath)) := do
  let some root ← IO.getEnv "LEAN_SYSROOT" |
    return .error "LEAN_SYSROOT names no toolchain; run the suite through lake test"
  let src : System.FilePath := System.FilePath.mk root / "src" / "lean"
  unless ← (src / "Init.lean").pathExists do
    return .error s!"{src} holds no toolchain source"
  return .ok #[src, src / "lake"]

/-- Every toolchain module `seeds` reach through imports and `known` does
not already hold, with its text, or the first module whose source the
toolchain does not ship. -/
def toolchainClosure (roots : Array System.FilePath) (seeds : Array String)
    (known : Std.HashSet String := {}) : IO (Except String (Array (String × String))) := do
  let mut seen := known
  let mut todo := seeds.toList
  let mut out : Array (String × String) := #[]
  for _ in [0:200000] do
    match todo with
    | [] => break
    | m :: rest =>
      todo := rest
      if seen.contains m || m == "LeanTex" || m.startsWith "LeanTex." then continue
      seen := seen.insert m
      let rel := (m.replace "." "/") ++ ".lean"
      let mut text : Option String := none
      for r in roots do
        if text.isNone && (← (r / rel).pathExists) then text := some (← IO.FS.readFile (r / rel))
      let some body := text | return .error s!"the toolchain ships no source for {m}"
      out := out.push (m, body)
      todo := (headerImports body).toList ++ todo
  unless todo.isEmpty do return .error "the toolchain import closure did not settle"
  return .ok out

/-- IO.Process's spawners, the scan's primitives, and the module they live in. -/
def spawnerNames : List String := ["spawn", "output", "run"]

def spawnerHome : String := "Init.System.IO"

/-- Does the code token `t` call one of IO.Process's spawners: by a name
ending in `Process.` and the spawner, or by the bare name inside
`IO.Process`? -/
def namesSpawner (t : Tok) : Bool :=
  t.kind == .ident && !t.declares && spawnerNames.any fun s =>
    t.text.endsWith ("Process." ++ s) ||
      (t.text == s && (t.ns == "IO.Process" || t.ns.startsWith "IO.Process."))

/-- The symbols the `@[extern]` attributes of `ts` bind, each with the
declaration that follows it. -/
def externs (ts : Array Tok) : Array (String × String) := Id.run do
  let mut out := #[]
  for k in [0:ts.size] do
    let t := ts[k]!
    if t.kind == .ident && t.text == "extern" && k ≥ 2 && ts[k - 1]!.text == "[" && ts[k - 2]!.text == "@" then
      if let some sym := ts[k + 1]? then
        if sym.kind == .str then
          let mut decl := ""
          for m in [k + 2:ts.size] do
            if ts[m]!.declares then
              decl := ts[m]!.text
              break
          out := out.push (sym.text, decl)
  return out

/-- An extern symbol that can start a process. -/
def startsProcess (sym : String) : Bool :=
  ["spawn", "exec", "fork"].any (hasStr sym ·)

/-- Whether the `open` or `export` at `k` lets IO.Process's spawners be
called by a bare name outside their namespace: it names `IO.Process`, or
`Process` where IO's namespace is open around it, and does not hide them. -/
def opensSpawners (ts : Array Tok) (k : Nat) : Bool :=
  let t := ts[k]!
  let clause := openClause ts k
  let insideIO := t.ns == "IO" || t.ns.startsWith "IO."
  clause.names.any (fun n =>
    let n := if n.startsWith "_root_." then (n.drop 7).toString else n
    n == "IO.Process" || n.endsWith ".IO.Process" || (n == "Process" && insideIO)) &&
    spawnerNames.any clause.exposes

/-- Why a toolchain module can start a process the scan does not read: its
code calls an IO.Process spawner outside their home, which is read
declaration by declaration so that only `output` and `run` call one; it
opens or exports IO.Process, so a bare call the scan does not follow could
reach one; or it declares an extern whose symbol spawns, execs or forks
other than `spawn`'s own. -/
def toolchainSpawnFaults (closure : Array (String × String)) : Array String := Id.run do
  let mut out := #[]
  for (m, text) in closure do
    let suspect := m == spawnerHome || hasStr text "Process" ||
      (hasStr text "extern" && ["spawn", "exec", "fork"].any (hasStr text ·))
    unless suspect do continue
    let ts := lex text
    for k in [0:ts.size] do
      let t := ts[k]!
      if t.kind == .ident && (t.text == "open" || t.text == "export") && opensSpawners ts k then
        out := out.push s!"{m}:{t.line}: `{t.text}` brings IO.Process's spawners into scope, so a bare call the scan does not read could start a process"
    for (sym, decl) in externs ts do
      if startsProcess sym && !(m == spawnerHome && decl == "spawn" && sym == "lean_io_process_spawn") then
        out := out.push s!"{m}: {decl} binds the extern '{sym}', which starts a process the scan does not read"
    let callers := ((ts.toList.filter namesSpawner).map (·.decl)).eraseDups
    for d in callers do
      unless m == spawnerHome && spawnerNames.contains d do
        out := out.push s!"{m}: {d} calls an IO.Process spawner, so the scan must read it as one"
  return out

/-- The toolchain modules the engine imports: every module an engine
source's header names outside the engine, and `Init`, which every module
but a prelude imports. -/
def engineImports : IO (Array String) := do
  let files := ((← System.FilePath.walkDir "LeanTex").filter (·.toString.endsWith ".lean")).push
    "Main.lean" |>.push "LeanTex.lean"
  let mut out : Array String := #["Init"]
  for f in files.qsort (·.toString < ·.toString) do
    for m in headerImports (← IO.FS.readFile f) do
      unless m == "LeanTex" || m.startsWith "LeanTex." || out.contains m do out := out.push m
  return out

end Premises

open Premises in
/-- **The toolchain starts a process only where the scan reads one.** Every
toolchain module the engine's imports reach calls IO.Process's spawners
only in their home, where `output` and `run` alone call one, and declares
no extern that spawns, execs or forks but `spawn`'s own. An engine module
importing Lake or a Lean module that starts a process fires, as do a
spawner planted in the home and a forking extern. -/
def toolchainSpawnChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let start ← IO.monoMsNow
  match ← toolchainRoots with
  | .error why => t s!"toolchain spawns: {why}" false
  | .ok roots =>
    let seeds ← engineImports
    match ← toolchainClosure roots seeds with
    | .error why => t s!"toolchain spawns: {why}" false
    | .ok closure =>
      let faults := toolchainSpawnFaults closure
      t s!"toolchain spawns: the engine's imports reach no process start the scan does not read ({faults})"
        faults.isEmpty
      t "toolchain spawns: the closure holds the spawners' home"
        (closure.any (·.1 == spawnerHome))
      let known := closure.foldl (fun acc (m, _) => acc.insert m) ({} : Std.HashSet String)
      for (planted, needle) in [("import Lake", "Lake.Util.Proc"), ("public import Lean.Util.Path", "Lean.Util.Path")] do
        let more := headerImports ("module\n\npublic import LeanTex.Cli.RunBounded\n" ++ planted ++ "\n")
        let fired := match ← toolchainClosure roots more known with
          | .ok reached => (toolchainSpawnFaults reached).any (hasStr · needle)
          | .error _ => false
        t s!"toolchain spawns selftest: an engine module's `{planted}` fires" fired
      let home := ((closure.find? (·.1 == spawnerHome)).map (·.2)).getD ""
      t "toolchain spawns selftest: a spawner planted in the home fires"
        ((toolchainSpawnFaults #[(spawnerHome, home ++
          "\nnamespace IO.Process\ndef zzShell (c : String) : IO Unit := discard <| output { cmd := c }\nend IO.Process\n")]).any
          (hasStr · "zzShell"))
      t "toolchain spawns selftest: a forking extern fires"
        ((toolchainSpawnFaults #[("Std.Zz", "@[extern \"zz_fork\"] opaque zzFork : IO Unit\n")]).any
          (hasStr · "zz_fork"))
      t "toolchain spawns selftest: opening IO.Process, or Process inside IO, fires, and hiding its spawners does not"
        ((toolchainSpawnFaults #[("Std.ZzOpen", "open IO.Process\n")]).any (hasStr · "Std.ZzOpen:1") &&
          (toolchainSpawnFaults #[("Std.ZzIn", "namespace IO\nopen Process in\ndef zz := 1\nend IO\n")]).any
            (hasStr · "Std.ZzIn:2") &&
          (toolchainSpawnFaults #[("Std.ZzHide", "open IO.Process hiding spawn output run\n")]).isEmpty &&
          (toolchainSpawnFaults #[("Std.ZzOther", "open IO.Process (SpawnArgs)\n")]).isEmpty)
      t "toolchain spawns selftest: the header reader skips comments and reads every import form"
        (headerImports "/- c -/\nmodule\n\nprelude\n-- x\npublic import A.B\nmeta import C\nimport all D\npublic meta import E\n\nnamespace X\nimport F"
          == #["A.B", "C", "D", "E"])
      IO.println s!"toolchain spawns: the engine's {seeds.size} toolchain imports reach {closure.size} modules; {(← IO.monoMsNow) - start} ms"
