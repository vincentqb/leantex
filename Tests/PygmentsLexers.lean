module

public import Tests.Support
public import LeanTex.Core.Highlight
import LeanTex.Core.Highlight.Bash
public import LeanTex.Core.Highlight.Console
import LeanTex.Core.PygmentsLexData
import LeanTex.Core.ListingReply
public import Lean.Data.Json

public section

open LeanTex.Core LeanTex.Core.Highlight
open Lean (Json)

namespace Tests

namespace PygmentsLexers

def root : System.FilePath := "testdata/highlight/snippets"
def recorded : System.FilePath := "testdata/highlight/pygments-tokens.json"
def departures : System.FilePath := "testdata/highlight/pygments-departures.json"

/-- A stream as the record spells it: start, type, text. -/
abbrev Spelled := Array (Nat × String × String)

def native (lexer : Lexer) (source : String) : Spelled :=
  let src := Src.ofString (source ++ "\n")
  (lex lexer src).map fun r =>
    (r.start, r.kind, String.ofList (src.chars.extract r.start r.stop).toList)

def spelled (tokens : Json) : Option Spelled := do
  let items ← tokens.getArr?.toOption
  items.mapM fun item => do
    let parts ← item.getArr?.toOption
    return (← (parts.getD 0 .null).getNat?.toOption, ← (parts.getD 1 .null).getStr?.toOption,
      ← (parts.getD 2 .null).getStr?.toOption)

/-- The snippet files, as the record names them. -/
def snippetPaths : IO (Array String) := do
  let mut out := #[]
  for d in (← root.readDir).qsort (·.fileName < ·.fileName) do
    for f in (← d.path.readDir).qsort (·.fileName < ·.fileName) do
      out := out.push f.path.toString
  return out

/-- The listing language a snippet's directory names. -/
def aliasOf (path : String) : String :=
  ((path.splitOn "/").reverse.drop 1).headD ""

/-- Python `re`'s answer found by backtracking, the reference the session lexer's simulation is held
to. -/
def backtrack (s : Src) (lim : Nat) : Console.Re → Nat → (Nat → Option Nat) → Option Nat
  | .empty, i, k => k i
  | .cls p, i, k => if i < lim && s.sat i p then k (i + 1) else none
  | .seq a b, i, k => backtrack s lim a i fun j => backtrack s lim b j k
  | .alt a b, i, k => (backtrack s lim a i k).orElse fun _ => backtrack s lim b i k
  | .star p true, i, k =>
    (if _h : i < lim ∧ s.sat i p = true then backtrack s lim (.star p true) (i + 1) k
     else none).orElse fun _ => k i
  | .star p false, i, k =>
    (k i).orElse fun _ =>
      if _h : i < lim ∧ s.sat i p = true then backtrack s lim (.star p false) (i + 1) k else none
termination_by re i => (sizeOf re, lim + 1 - i)
decreasing_by
  all_goals simp_wf
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right; omega)

/-- Every string of at most `n` scalars drawn from `alphabet`. -/
def strings (alphabet : Array Char) (n : Nat) : Array String := Id.run do
  let mut level : Array String := #[""]
  let mut out : Array String := #[""]
  for _ in [0:n] do
    let mut grown : Array String := #[]
    for w in level do
      for c in alphabet do
        grown := grown.push (w.push c)
    out := out ++ grown
    level := grown
  return out

/-- A string of up to `n` scalars from `alphabet`, threading the seed. -/
def randomString (alphabet : Array Char) (n : Nat) (seed : UInt64) : String × UInt64 := Id.run do
  let (len, s0) := rand seed (n + 1)
  let mut s := s0
  let mut out := ""
  for _ in [0:len] do
    let (i, s1) := rand s alphabet.size
    s := s1
    out := out.push (alphabet.getD i 'a')
  return (out, s)

/-- A pattern of the session lexer's shape, at most `depth` deep. -/
def randomRe (depth : Nat) (seed : UInt64) : Console.Re × UInt64 :=
  let classes : Array (Char → Bool) :=
    #[(· == 'a'), (· == 'b'), (fun c => c == 'a' || c == 'b'), (· != '\n')]
  let (k, s) := rand seed (if depth == 0 then 3 else 6)
  match depth, k with
  | _, 0 => (.empty, s)
  | _, 1 => let (i, s) := rand s classes.size; (.cls (classes.getD i (fun _ => false)), s)
  | _, 2 =>
    let (i, s) := rand s classes.size
    let (g, s) := rand s 2
    (.star (classes.getD i (fun _ => false)) (g == 0), s)
  | d + 1, 3 | d + 1, 4 =>
    let (a, s) := randomRe d s
    let (b, s) := randomRe d s
    (.seq a b, s)
  | d + 1, _ =>
    let (a, s) := randomRe d s
    let (b, s) := randomRe d s
    (.alt a b, s)
  | 0, _ => (.empty, s)

/-- The first occurrence of `w`'s first `k` scalars at or after `fromPos`. -/
def findPrefix (s : Src) (fromPos : Nat) (w : Array Char) (k : Nat) : Option Nat := Id.run do
  if k == 0 then return some fromPos
  if k > w.size then return none
  for j in [fromPos:s.size + 1 - min k (s.size + 1)] do
    let mut hit := true
    for h : t in [0:min k w.size] do
      have : t < w.size := Nat.lt_of_lt_of_le h.upper (Nat.min_le_right _ _)
      if j + t ≥ s.size || s.chars.getD (j + t) w[t] != w[t] then
        hit := false
        break
    if hit then return some j
  return none

/-- The heredoc search as the regex reads it: delimiter prefixes, longest first. -/
def heredocByPrefixes (s : Src) (p : Nat) : Option Nat := Id.run do
  if !(s.is p '<' && s.is (p + 1) '<') then return none
  let mut a := p + 2
  if s.is a '-' then a := a + 1
  a := s.run a spaceChar
  if s.is a '\'' then a := a + 1
  if s.is a '\\' then a := a + 1
  let len := s.run a wordChar - a
  let word := s.chars.extract a (a + len)
  for i in [0:len] do
    let k := len - i
    if let some q := findPrefix s (a + k + 1) word k then return some (q + k)
  return none

end PygmentsLexers

/-- The native lexers match Pygments' recorded streams for the invented snippets, under the declared
departures, token for token. -/
def pygmentsLexerChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let declared ← match Json.parse (← IO.FS.readFile PygmentsLexers.departures) with
    | .ok j => pure j
    | .error e => do t s!"pygments lexers: the departures do not parse: {e}" false; return
  t "pygments lexers: the lexer data were generated under the declared departures"
    (declared.compress == PygmentsLexData.departures)
  let suite ← IO.FS.readFile "Tests.lean"
  let held := match declared with
    | .obj lexers => lexers.toArray.all fun (_, states) => match states with
      | .obj states => states.toArray.all fun (_, d) =>
        let sides := ["fires", "holds"].all fun k =>
          !((d.getObjValAs? (Array String) k).toOption.getD #[]).isEmpty
        match d.getObjValAs? String "check" with
        | .ok name => sides && !name.isEmpty && hasStr suite s!"  {name} ref\n"
        | .error _ => false
      | _ => false
    | _ => false
  t "pygments lexers: every departure names a check the suite runs and texts on each side of it" held
  let json ← match Json.parse (← IO.FS.readFile PygmentsLexers.recorded) with
    | .ok j => pure j
    | .error e => do t s!"pygments lexers: the record does not parse: {e}" false; return
  let version := (json.getObjValAs? String "pygments").toOption.getD ""
  let python := (json.getObjValAs? String "python").toOption.getD ""
  t "pygments lexers: the record and the lexer data come from one Pygments under one Python"
    (version == PygmentsLexData.pygmentsVersion && python == PygmentsLexData.pythonVersion)
  t "pygments lexers: the mirror implements the generated rule structure"
    (mirrorsRules == PygmentsLexData.rulesDigest)
  let cases := ((json.getObjVal? "cases").toOption.bind (·.getArr?.toOption)).getD #[]
  let mut seen : Array String := #[]
  let mut lexers : Array Lexer := #[]
  for c in cases do
    let path := (c.getObjValAs? String "path").toOption.getD ""
    seen := seen.push path
    let alias := PygmentsLexers.aliasOf path
    let some lexer := Lexer.ofName? alias
      | do t s!"pygments lexers: {path} stands under no native lexer's name" false; continue
    unless lexers.contains lexer do lexers := lexers.push lexer
    let some want := (c.getObjVal? "tokens").toOption.bind PygmentsLexers.spelled
      | do t s!"pygments lexers: {path} has a malformed record" false; continue
    let raw ← try IO.FS.readFile path catch _ => pure ""
    t s!"pygments lexers: {path} is a snippet file" (← System.FilePath.pathExists path)
    let source := (ListingReply.Request.ofSource alias raw).source
    let got := PygmentsLexers.native lexer source
    let first := (List.range (max got.size want.size)).find? fun i => got[i]? != want[i]?
    t s!"pygments lexers: {path} reproduces its recorded stream (first difference: token {first})"
      (!want.isEmpty && first.isNone)
  let files ← PygmentsLexers.snippetPaths
  t "pygments lexers: every snippet is recorded, and only snippets are"
    (files.all seen.contains && seen.all files.contains)
  t "pygments lexers: every native lexer has a recorded snippet"
    (Lexer.all.all lexers.contains)
  t "pygments lexers: a Lean proof hole is Generic.Error"
    ((PygmentsLexers.native .lean4 "theorem t : p := sorry").any fun (_, k, text) =>
      k == Ty.genericError && text == "sorry")
  t "pygments lexers: a step reading and popping nothing ends, the fallback taking each scalar"
    (drive () (fun _ m => m) (Src.ofString "a\nb") ==
        #[⟨0, 1, Ty.error⟩, ⟨1, 2, Ty.whitespace⟩, ⟨2, 3, Ty.error⟩] &&
      drive () (fun _ m => m.push ()) (Src.ofString "ab") == #[⟨0, 1, Ty.error⟩, ⟨1, 2, Ty.error⟩])
  t "pygments lexers: the ASCII fast paths answer as the class tables do"
    ((List.range 128).all fun n => asciiAgrees (Char.ofNat n))
  t "pygments lexers: every alias selects its lexer, in any case, and no other"
    (Lexer.all.all fun l => l.aliases.all fun a =>
      Lexer.ofName? a == some l && Lexer.ofName? a.toUpper == some l &&
        Lexer.all.all fun l' => l' == l || !l'.aliases.contains a)
  t "pygments lexers: `lean` names Lean 4"
    (Lexer.ofName? "lean" == some .lean4 && Lexer.ofName? " Lean4 " == some .lean4)
  t "pygments lexers: a language with no native lexer selects none"
    ((["ruby", "c", "lean3", "pycon", "", "py thon"] : List String).all
      fun n => (Lexer.ofName? n).isNone)

/-- The session lexer's prompt match and the Bash heredoc search answer what Python's backtracking
answers, without backtracking. -/
def pygmentsLinearChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let promptAnswer (line : String) : Option Nat × Option Nat :=
    let s := Src.ofString (line ++ "\n")
    (Console.promptEnd s 0 s.size, PygmentsLexers.backtrack s s.size Console.ps1 0 some)
  let short := PygmentsLexers.strings #['[', ']', '(', ')', '@', '$', 's', 'h', 'a', '-', ' '] 5
  let shortMiss := short.find? fun l => let (a, b) := promptAnswer l; a != b
  t s!"pygments lexers: the prompt match is the backtracking one on every short line (first miss: {shortMiss.map repr})"
    shortMiss.isNone
  let wide := #['[', ']', '(', ')', '@', ':', '$', '#', '%', '❯', 's', 'h', 'a', 'é', '_', '-',
    ' ', '\t', '\u00a0', '\u2028', '/', '~', '1']
  let mut seed : UInt64 := 0x5eed0f1a
  let mut longMiss : Option String := none
  let mut prompted := 0
  for _ in [0:20000] do
    let (line, s1) := PygmentsLexers.randomString wide 40 seed
    seed := s1
    let (a, b) := promptAnswer line
    if a.isSome then prompted := prompted + 1
    if a != b && longMiss.isNone then longMiss := some line
  t s!"pygments lexers: the prompt match is the backtracking one on random lines (first miss: {longMiss.map repr})"
    (longMiss.isNone && prompted > 1000)
  let mut reMiss : Option Nat := none
  for n in [0:400] do
    let (re, s1) := PygmentsLexers.randomRe 4 seed
    seed := s1
    let matcher := re.matcher
    for _ in [0:60] do
      let (text, s2) := PygmentsLexers.randomString #['a', 'b', 'c', '\n'] 9 seed
      seed := s2
      let s := Src.ofString text
      for start in [0:s.size + 1] do
        if matcher s start s.size != PygmentsLexers.backtrack s s.size re start some then
          if reMiss.isNone then reMiss := some n
  t s!"pygments lexers: a compiled pattern matches as backtracking does (first miss: pattern {reMiss})"
    reMiss.isNone
  let heads := #["<<", "<<-", "<< ", "<<'", "<<\\", "<<- '\\"]
  let words := PygmentsLexers.strings #['a', 'b'] 3
  let bodies := PygmentsLexers.strings #['a', 'b', 'x', '\n'] 6
  let mut docMiss : Option String := none
  let mut docHits := 0
  for h in heads do
    for w in words do
      for b in bodies do
        let s := Src.ofString (h ++ w ++ b)
        let got := Bash.heredocEnd s 0
        if got.isSome then docHits := docHits + 1
        if got != PygmentsLexers.heredocByPrefixes s 0 && docMiss.isNone then
          docMiss := some (h ++ w ++ b)
  t s!"pygments lexers: the heredoc search is the delimiter-prefix one (first miss: {docMiss.map repr})"
    (docMiss.isNone && docHits > 10000)

end Tests
