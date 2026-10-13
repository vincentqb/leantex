/-
The native listing lexers against the installed Pygments release they mirror, over the snippets,
seeded fuzz and `--docs` listings, by token stream, scalar type and colour.
Usage: lake env lean --run scripts/highlight-diff.lean [--fuzz N] [--seed S] [--lexer NAME] [--python P] [--any-version] [--docs FILE...] | --record [--python P] | --selftest
-/
import LeanTex
import LeanTex.Core.Highlight
import Lean.Data.Json

open LeanTex.Core
open LeanTex.Core.Highlight
open Lean (Json)

def die (msg : String) : IO α := do
  IO.eprintln s!"highlight-diff: {msg}"
  IO.Process.exit 2

/-- The constant bridge program, run isolated (`-I`): the batch names registry aliases and
sources, and the reply is each source's token stream and every type's colour per style. -/
def bridge : String := r#"import importlib
import json
import pathlib
import shutil
import sys
import unicodedata

try:
    import pygments
except ModuleNotFoundError as error:
    if error.name != 'pygments':
        raise
    launcher = shutil.which('latexminted')
    if launcher is None:
        raise SystemExit('no Pygments: no installed module and no latexminted launcher')
    wheels = sorted(pathlib.Path(launcher).resolve().parent.glob('pygments-*.whl'))
    if len(wheels) != 1:
        raise SystemExit('no Pygments: expected one wheel beside latexminted')
    sys.path.insert(0, str(wheels[0]))
    import pygments
import pygments.plugin
pygments.plugin.iter_entry_points = lambda group: ()
from pygments.lexers._mapping import LEXERS
from pygments.styles import get_style_by_name
from pygments.token import STANDARD_TYPES, string_to_tokentype

with open(sys.argv[1], encoding='utf-8') as stream:
    batch = json.load(stream)
lexers = {}


def lexer_for(alias):
    if alias not in lexers:
        selected = next(((name, entry) for name, entry in LEXERS.items() if alias in entry[2]), None)
        if selected is None:
            raise SystemExit(f'no lexer for {alias!r}')
        name, entry = selected
        lexers[alias] = getattr(importlib.import_module(entry[0]), name)(
            stripnl=False, stripall=False, ensurenl=False, tabsize=0)
    return lexers[alias]


seen = {str(t) for t in STANDARD_TYPES} | set(batch['types'])
answers = []
for request in batch['requests']:
    tokens = []
    for offset, kind, text in lexer_for(request['alias']).get_tokens_unprocessed(request['source'] + '\n'):
        tokens.append([offset, str(kind), text])
        seen.add(str(kind))
    answers.append(tokens)


def colour(style, name):
    # A type the style table lacks reads as its nearest ancestor, as the
    # formatters walk `ttype.parent` (pygments/formatters/latex.py).
    ttype = string_to_tokentype(name)
    while not style.styles_token(ttype) and ttype.parent is not None:
        ttype = ttype.parent
    return style.style_for_token(ttype)['color'] or ''


colours = {}
for name in batch['styles']:
    style = get_style_by_name(name)
    colours[name] = {t: colour(style, t) for t in sorted(seen)}
json.dump({'pygments': pygments.__version__, 'python': sys.version.split()[0],
           'unicode': unicodedata.unidata_version,
           'answers': answers, 'colours': colours}, sys.stdout, ensure_ascii=True)
"#

def styles : List String := ["default", "friendly"]

/-- Every type a native lexer writes, so the reply colours them too. -/
def nativeTypes : List String :=
  [Ty.text, Ty.whitespace, Ty.error, Ty.keyword, Ty.keywordConstant, Ty.keywordDeclaration,
   Ty.keywordNamespace, Ty.keywordType, Ty.name, Ty.nameBuiltin, Ty.nameBuiltinPseudo,
   Ty.nameClass, Ty.nameDecorator, Ty.nameException, Ty.nameFunction, Ty.nameFunctionMagic,
   Ty.nameNamespace, Ty.nameVariable, Ty.nameVariableMagic, Ty.string, Ty.stringAffix,
   Ty.stringBacktick, Ty.stringDoc, Ty.stringDouble, Ty.stringEscape, Ty.stringInterpol,
   Ty.stringSingle, Ty.stringSymbol, Ty.number, Ty.numberBin, Ty.numberFloat, Ty.numberHex,
   Ty.numberInteger, Ty.numberOct, Ty.operator, Ty.operatorWord, Ty.punctuation, Ty.comment,
   Ty.commentHashbang, Ty.commentMultiline, Ty.commentSingle, Ty.genericError,
   Ty.genericOutput, Ty.genericPrompt, Ty.genericPromptVirtualEnv].map ("Token." ++ ·)

structure Case where
  corpus : String
  label : String
  alias : String
  lexer : Lexer
  source : String

/-- A token as the comparison reads it: start, end, full type name. -/
abbrev Tok := Nat × Nat × String

def nativeTokens (c : Case) : Array Tok :=
  (lex c.lexer (Src.ofString (c.source ++ "\n"))).map fun r => (r.start, r.stop, "Token." ++ r.kind)

/-- Pygments' stream at the positions of the text it writes, empty tokens dropped, and
whether every reported offset was that position. -/
def theirTokens (answer : Json) : Except String (Array Tok × Bool) := do
  let items ← answer.getArr?
  let mut out := #[]
  let mut at_ := 0
  let mut faithful := true
  for item in items do
    let parts ← item.getArr?
    let offset ← (parts.getD 0 .null).getNat?
    let kind ← (parts.getD 1 .null).getStr?
    let text ← (parts.getD 2 .null).getStr?
    if offset != at_ then faithful := false
    if !text.isEmpty then out := out.push (at_, at_ + text.length, kind)
    at_ := at_ + text.length
  return (out, faithful)

/-- Each scalar's type, `Token.Text` where no token covers it. -/
def scalarTypes (n : Nat) (ts : Array Tok) : Array String := Id.run do
  let mut out := Array.replicate n "Token.Text"
  for (a, b, k) in ts do
    for i in [a:min b n] do
      out := out.setIfInBounds i k
  return out

inductive Level where
  | raw | scalar | colour
  deriving BEq, Repr

def Level.name : Level → String
  | .raw => "raw"
  | .scalar => "scalar"
  | .colour => "colour"

/-- The strongest level at which two streams over `n` scalars differ, and
its first differing scalar. -/
def compare (n : Nat) (colourOf : String → String → String) (ours theirs : Array Tok) :
    Option (Level × Nat) :=
  if ours == theirs then none else
  let a := scalarTypes n ours
  let b := scalarTypes n theirs
  let typeAt := fun (xs : Array String) (j : Nat) => xs[j]?.getD ""
  match (List.range n).find? fun j => typeAt a j != typeAt b j with
  | none =>
    let i := ((List.range (max ours.size theirs.size)).find? fun i => ours[i]? != theirs[i]?).getD 0
    some (.raw, (ours[i]?.map (·.1)).getD ((theirs[i]?.map (·.1)).getD 0))
  | some j =>
    match (List.range n).find? (fun k => styles.any fun st =>
        colourOf st (typeAt a k) != colourOf st (typeAt b k)) with
    | some k => some (.colour, k)
    | none => some (.scalar, j)

def escape (s : String) : String := Id.run do
  let mut out := ""
  for c in s.toList do
    match c with
    | '\n' => out := out ++ "\\n"
    | '\t' => out := out ++ "\\t"
    | '\\' => out := out ++ "\\\\"
    | c => out := out.push c
  return out

def showToks (src : Array Char) (ts : Array Tok) (around : Nat) : String := Id.run do
  let mut out := ""
  for (a, b, k) in ts do
    if b + 12 ≥ around && a ≤ around + 12 then
      let text := String.ofList (src.extract a b).toList
      out := out ++ s!"    {a}-{b} {k} \"{escape text}\"\n"
  return out

def nextRand (s : UInt64) : UInt64 × UInt64 :=
  let x := s ^^^ (s >>> 12)
  let x := x ^^^ (x <<< 25)
  let x := x ^^^ (x >>> 27)
  (x, x * 2685821657736338717)

def pick (seed : UInt64) (bound : Nat) : Nat × UInt64 :=
  let (s, v) := nextRand seed
  ((v % UInt64.ofNat (max bound 1)).toNat, s)

def fragments : Lexer → Array String
  | .lean4 =>
    #["def", "theorem", "lemma", "#eval", "#check", "x#eval", "fun", "λ", "Π", "Σ", "α", "x",
      "y'", "h₁", "Nat.succ", "`foo", "``Bar.baz", "`", "``", "Type", "Prop", "Sort", "Type*",
      "sorry", "admit", "sorryx", ":=", ":", "::", "->", "→", "←", "↔", "⟨", "⟩", "(", ")",
      "[", "]", "{", "}", "@[", "@[simp]", "@", "_", "_x", "x_y", "!", "?", "?x:", "~a:",
      "?A:", "1", "42", "3.14", "1.5e10", "2.", ".5", "x.1", "0x1F", "1e5", "1.e+", "\"",
      "\"str\"", "\"a\\nb\"", "\"\\t\"", "\\", "--", "-- comment", "/-", "-/", "/--", "/-!",
      "/- nested /- x -/ -/", " ", "  ", "\n", "\n", "\t", "·", "∀", "∃", "∧", "∨", "¬",
      "≠", "≤", "≥", "×", "∘", "∈", "ℕ", "ℝ", "𝒜", "₀", "ⁿ", "é", "😀", "'", "'a'", ",",
      ";", ".", "..", "...", "<|>", "|>.", "$", "%", "^", "&&", "||", "=>", "<=", ">=", "==",
      "!=", "=", "+", "-", "*", "/", "#", "#print", "attribute", "where", "in", "with",
      "match", "do", "let", "if", "then", "else", "by", "at", "calc", "show", "from",
      "obtain", "namespace", "end", "open", "instance", "structure", "inductive", "xs[i]!",
      "⁻¹", "▸", "⦃", "⦄", "↦", "⌞", "⬝", "٣", "x.٣", "]!", "]?", "]'", "xs[0]?", "a[i]'h",
      "]'h", "] !", "]]!"]
  | .python =>
    #["def ", "class ", "import ", "from ", " as ", "@decorator", "@", "#", "# comment",
      "#!/usr/bin/env python", "#!", "\\", "\\\n", "\n", "\n", "    ", " ", "\t", "r", "R",
      "b", "B", "u", "U", "f", "F", "rb", "Rb", "br", "fr", "rf", "Fr", "ub", "'", "\"",
      "'''", "\"\"\"", "\\n", "\\\\", "\\'", "\\\"", "\\N{DASH}", "\\N{", "\\u1234",
      "\\U0001F600", "\\x41", "\\x4", "\\123", "\\9", "%s", "%(name)d", "%-5.2f", "%%", "%",
      "{", "}", "{{", "}}", "{0}", "{name!r}", "{x:>10}", "{:}>}", "{a.b[c]}", "{x=}",
      "{x!r:^5}", "{x = }", "0", "1", "1_000", "1.", ".5", "1e5", "1E-5", "1j", "0x1F",
      "0o17", "0b101", "0x", "1__2", "١٢", "+", "-", "*", "**", "/", "//", "%", "==", "!=",
      "<", "<=", "<<", ">>", ":=", "->", "~", "^", "|", "&", ".", "!", "$", "?", "`", "(",
      ")", "[", "]", ":", ",", ";", "x", "_", "_x", "self", "cls", "print", "len",
      "Exception", "ValueError", "__init__", "__name__", "match", "case", "type", "async",
      "await", "lambda", "yield", "yield from", "async for", "None", "True", "False", "in",
      "is", "not", "and", "or", "éa", "α", "x1", "def", "class", "import", "from", "if",
      "else", "elif", "while", "for", "return", "pass", "with", "try", "except", "raise",
      "global", "nonlocal", "del", "assert", "match x:", "case _:", "case 1 | _:",
      "match = 1", "obj.print", ".len", "self.x", "__import__", "Ellipsis", "x.self", "t", "T",
      "rt", "tr", "Rt", "tR", "lazy import ", "lazy from ", "lazy", "frozendict", "sentinel"]
  | .bash =>
    #["if", "then", "else", "elif", "fi", "for", "in", "do", "done", "while", "until",
      "case", "esac", "function", "select", "break", "continue", "return", "echo", "cd",
      "export", "local", "true", "false", "type", "typeset", "test", "read", "x=1", "x+=2",
      "y =", "$", "$x", "$1", "$#", "$?", "$@", "$-", "$_", "$$", "${", "${x}", "${#x}",
      "${x:-y}", "$(", "$((", "))", ")", "(", "`", "\"", "'", "$'", "$\"", "\\", "\\n", "#",
      "# comment", "#!/bin/bash", "<<EOF", "<<-'EOF'", "<<\\EOF", "EOF", "<<<", "<", ">",
      ">>", "&&", "||", "|", "&", ";", ";;", "[", "]", "[[", "]]", "{", "}", "=", "1", "42",
      "2#101", "16#ff", "3# ", "0x1F", "x", "-n", "--flag", "file.txt", "*", "**", "+", "-",
      "/", "%", "^", " ", "  ", "\n", "\n", "\t", "a\\ b", "\"$x\"", "'a b'", "\"a\\\"b\"",
      "$'a\\'b'", ":-", ":", "é", "x1", "_y", "done2", "ifx", "echo2", "if;", "do\n", "do-",
      "fi#", "in$x", "then?", "done!", "else*", "esac@", "for-each", "if é"]
  | .console =>
    #["$ ", "# ", "% ", "> ", "user@host:~$ ", "[user@host dir]$ ", "(venv) $ ", "(venv) ",
      "(venv)", "sh-5.1$ ", "root@box:/# ", "ls -la", "echo hi", "cat <<EOF", "EOF", "\\",
      "output text", "error: x", "  indented", "\n", "\n", "\n", " ", "x=1", "$x", "| grep a",
      "&& make", "# comment", "[1] done", "user@host ~ % ", "$", "#", "%", "❯ ", "❯", "~ ❯ ",
      "(venv) ❯ "]
  | .text => #["plain", " ", "\n", "\t", "é", "{}", "\\"]

/-- The scalars a language's patterns divide on, for texts drawn scalar by scalar. -/
def alphabet : Lexer → String
  | .lean4 => "abxyzT_'!?.0123456789eE+-\"\\n/-`@[]{}()~:=<>|&λΠΣα₁ℕ→⟨⟩ \n\t"
  | .python => "\"'{}%:!.[]()<>=^,-+ #0123456789xXeEjoObBrRfFtTuUNsadgn_\\\n\t@*hlL"
  | .bash => "$\"'`(){}[]<>|&;=#:-+*/\\\nabefinortuxEOF019_ \t!?@"
  | .console => "$#%> ()[]@:~/\\\nabuserhost019 \t-|❯"
  | .text => "ab \n\t"

/-- A seeded draw: the state threads through every choice. -/
structure Draw where
  seed : UInt64
  out : String := ""

def Draw.nat (d : Draw) (bound : Nat) : Nat × Draw :=
  let (n, s) := pick d.seed bound
  (n, { d with seed := s })

def Draw.add (d : Draw) (s : String) : Draw := { d with out := d.out ++ s }

def Draw.oneOf (d : Draw) (xs : Array String) : Draw :=
  let (i, d) := d.nat xs.size
  d.add (xs[i]?.getD "")

/-- With probability one in `n`, run `f`. -/
def Draw.maybe (d : Draw) (n : Nat) (f : Draw → Draw) : Draw :=
  let (i, d) := d.nat n
  if i == 0 then f d else d

/-- `f`, between none and `n` times. -/
def Draw.times (d : Draw) (n : Nat) (f : Draw → Draw) : Draw := Id.run do
  let (k, d0) := d.nat (n + 1)
  let mut d := d0
  for _ in [0:k] do
    d := f d
  return d

/-- Python's formatting mini-languages and escapes, with their near misses. -/
def pyStringPart (d : Draw) : Draw :=
  let (k, d) := d.nat 6
  match k with
  | 0 =>
    let d := d.add "{"
    let d := d.maybe 2 fun d => (d.oneOf #["x", "name", "0", "_a", "é"]).times 2 fun d =>
      d.oneOf #[".attr", "[0]", "[key]", "[", ".", "[]"]
    let d := d.maybe 3 fun d => d.oneOf #["!r", "!s", "!a", "!x", "!"]
    let d := d.maybe 2 fun d =>
      let d := d.add ":"
      let d := d.maybe 2 fun d => d.oneOf #["<", ">", "=", "^", "*<", "}>", "x^", "\n<"]
      let d := d.maybe 3 fun d => d.oneOf #["+", "-", " "]
      let d := d.maybe 3 fun d => d.add "#"
      let d := d.maybe 3 fun d => d.add "0"
      let d := d.maybe 2 fun d => d.oneOf #["5", "10", "٣"]
      let d := d.maybe 3 fun d => d.add ","
      let d := d.maybe 3 fun d => d.oneOf #[".2", ".", ".٣"]
      d.maybe 2 fun d => d.oneOf #["E", "F", "G", "X", "b", "c", "d", "e", "f", "g", "n", "o",
        "s", "x", "%", "z", "i"]
    d.oneOf #["}", "}", "}", "", "}}"]
  | 1 =>
    let d := d.add "%"
    let d := d.maybe 3 fun d => d.oneOf #["(key)", "()", "(k", "(é)"]
    let d := d.times 2 fun d => d.oneOf #["-", "#", "0", " ", "+"]
    let d := d.maybe 2 fun d => d.oneOf #["5", "*", "12"]
    let d := d.maybe 3 fun d => d.oneOf #[".3", ".*", "."]
    let d := d.maybe 3 fun d => d.oneOf #["h", "l", "L"]
    d.oneOf #["d", "s", "r", "a", "x", "X", "e", "E", "f", "F", "g", "G", "c", "i", "o", "u", "%",
      "y", "z", ""]
  | 2 =>
    d.oneOf #["\\n", "\\\\", "\\'", "\\\"", "\\N{DASH}", "\\N{", "\\N{x\n}", "\\u12ab", "\\u12",
      "\\U0001f600", "\\U0001f6", "\\x4f", "\\x4", "\\0", "\\12", "\\123", "\\1234", "\\8",
      "\\\n", "\\q"]
  | 3 => d.oneOf #["{{", "}}", "{", "}", "%", "%%"]
  | 4 => d.oneOf #["text", " ", "é", "'", "\"", "\n", "\t"]
  | _ => d.oneOf #["{x}", "{x!r}", "{x=}", "{ x = }", "{x:{w}}", "{a[b]}", "{f(x)}", "{'q'}"]

def pyQuotes : Array String := #["'", "\"", "'''", "\"\"\""]

def pyString (d : Draw) : Draw :=
  let d := d.oneOf #["", "", "r", "R", "u", "U", "b", "B", "f", "F", "rb", "bR", "Rb", "fr",
    "rF", "ur", "bu", "t", "T", "rt", "tR", "Rt", "tr", "bt", "ft"]
  let (q, d) := d.nat pyQuotes.size
  let quote := pyQuotes[q]?.getD "'"
  let d := (d.add quote).times 6 pyStringPart
  d.maybe 5 (fun d => d.add "\n") |>.add quote

def pyNumber (d : Draw) : Draw :=
  d.oneOf #["0", "7", "1_000", "1__0", "1_", "12.", ".5", "1.5", "1._5", "1.e5", "1e+5", "1e-",
    "1E5j", "3j", "0x_1f", "0xg", "0o17", "0o8", "0b10", "0b2", "0X", "٣.٤", "١e٢", "0_0", "00"]

def pyLine (d : Draw) : Draw :=
  let d := d.maybe 2 fun d => d.oneOf #["    ", "\t", "  ", ""]
  let (k, d) := d.nat 10
  let d := match k with
    | 0 => (d.oneOf #["match ", "case ", "match", "case\t"]).times 3 fun d =>
        d.oneOf #["x", "_", " ", "(", "[a, _]", ":", "=", ".y", "if", "_x", "a_", "None", "|", ")"]
    | 1 => (d.oneOf #["def ", "def\\\n ", "class ", "class\t"]).oneOf #["f", "__init__", "1x", "é", "(", ""]
    | 2 => (d.oneOf #["import ", "from ", "lazy import ", "lazy from ", "lazy\\\n import ",
        "lazy  from\t", "lazy import", "lazyimport ", "lazy  x"]).times 5 fun d =>
        d.oneOf #["os", ".", " ", "as", " as ", " as", " asx", " as\n", ",", " , ", "import",
          " import ", " importx", "None", " None", "x.y", "\n"]
    | 3 => d.oneOf #["\"\"\"doc\"\"\"", "r'''doc'''", "\"\"\"open", "ub\"\"\"x\"\"\"", "  \n  \"\"\"x\"\"\""]
    | 4 => d.times 4 pyString
    | 5 => d.times 4 fun d => (pyNumber d).oneOf #["", " ", "+", ".", "x", "j"]
    | 6 => d.times 5 fun d => d.oneOf #["self", "cls", ".self", "print", ".len", "x", "__name__",
        "__init__", "ValueError", "async for", "yield from", "yield", "await", "not", "in", "is",
        "isinstance", "True", "None", "lambda", "@", "@deco", "!=", ":=", "**", "->", "$", "?"]
    | 7 => d.oneOf #["#!/usr/bin/env python", "# note", "\\", "\\\n", "#", "#!"]
    | 8 => (d.oneOf #["f\"", "t\"", "rt\"", "T\""]).times 3 (fun d => d.oneOf #["{", "}", "{x", "{x!r}", "{x!f}", "{x!z}",
        "{x!}", "{x=!s}", "{x = !a:>3}", "{x:>{y}}", "{(a, b)}", "{[1]}", "{ {1} }", "{x = }",
        "{'s'}", "{\"d\"}", "text", "\n"]) |>.add "\""
    | _ => d.times 3 fun d => d.oneOf #["x", " ", "(", ")", "[", "]", "{", "}", ",", ":", ";"]
  d.add "\n"

def bashPart (d : Draw) : Draw :=
  let (k, d) := d.nat 9
  match k with
  | 0 => ((d.oneOf #["<<", "<<-", "<< ", "<<'", "<<\\", "<<-'"]).oneOf #["EOF", "END", "E", "x1",
      "ABAB", "AAB", "MARKER"]).times 3
      (fun d => d.oneOf #["\nline", "\nEOF", "EOF", "\nEO", "\nE", " x", "'", "\nEND\n", "AB",
        "ABA", "AAAB", "MARK", "\nMARKER", "A"])
  | 1 => ((d.oneOf #["${", "${#"]).times 2 (fun d => d.oneOf #["x", ":-", "-", "y", "'a'", "\"b\"",
      "$z", "`c`", ":", "#", "/", "}"])).oneOf #["}", ""]
  | 2 => ((d.add "$((").times 4 (fun d => d.oneOf #["1", "2#101", "16#ff", "8# ", "8#", "0x1F",
      "x", "_y", "+", "**", "<<", "||", " ", "(", ")", "$z"])).oneOf #["))", ")", ""]
  | 3 => ((d.oneOf #["$'", "$\"", "'", "\""]).times 3 (fun d => d.oneOf #["a", "\\'", "\\\\",
      "\\\"", "\\0", "\\12", "$x", "$(y)", "\n", " "])).oneOf #["'", "\"", ""]
  | 4 => (d.oneOf #["if", "fi", "then", "done", "do", "in", "case", "esac", "elif", "function",
      "until", "select", "for", "while", "return", "break", "continue"]).oneOf #["", " ", "  x",
      ";", "\n", "x", "2", "-", "#", "$", ")", "  ;", " \n", "!", "?", "*", "@", "#x", "=1", "é"]
  | 5 => (d.oneOf #["echo", "cd", "type", "typeset", "test", "time", "times", "true", "exit",
      "read", "readonly", "export", "local", "set", "unset"]).oneOf #["", " ", ")", "`", "x", "2",
      "\n", "-", "("]
  | 6 => (d.oneOf #["x", "x1", "_", "a_b", "é"]).oneOf #["=", "+=", " =", " += ", "\n=", "=x", "+"]
  | 7 => ((d.oneOf #["$(", "`", "$((", "(", "[[", "{"]).times 3 (fun d =>
      d.oneOf #["ls", " ", "-l", "$x", "1"])).oneOf #[")", "`", "))", "]]", "}", ""]
  | _ => d.oneOf #["#!/bin/sh\n", "# c\n", "#", "\\", "\\x", "\\\n", "&&", "||", "|", "&", ";",
      ";;", "<", "<<<", ">", ">>", "2>&1", "42", "4x", "$1", "$#", "$$", "$@", "$-", "$_", "$!",
      "$?", "$*", "$"]

def consoleLine (d : Draw) : Draw :=
  let d := d.maybe 3 fun d => d.oneOf #["(venv) ", "(env)", "(a b) ", "()"]
  let (k, d) := d.nat 5
  let d := match k with
    | 0 => (d.oneOf #["$ ", "# ", "% ", "$", "user@host:~$ ", "[user@host dir]$ ", "sh-5.1$ ",
        "root@box:/# ", "(x) $ ", "[a]$", "u@h ~ % ", "a@b:c d $ ", "sh$x@y:z # ", "sh$ ",
        "shell@h:~% ", "sh@x $ ", "[a@b c]d]$ ", "[x]y$ ", "(v)sh$ ", "(v)u@h:~# ", "❯ ", "~ ❯ ",
        "(v) ❯ ", "u@h:~❯ "]).times 4 bashPart
    | 1 => (d.oneOf #["> ", ">", "> x"]).times 2 bashPart
    | 2 => d.oneOf #["output", "  out", "", "error: $x", "100%", "a # b", "x $ y"]
    | 3 => d.times 24 fun d => d.oneOf #["a", "aa", "@", ":", "@a", ":a", " ", "[", "]", "(", ")",
        "sh", "x$", "$", "-", "[a@b", "]x", "\t", "#", "❯"]
    | _ => ((d.oneOf #["$ ", "# "]).times 2 bashPart).add "\\"
  d.add "\n"

def leanPart (d : Draw) : Draw :=
  let (k, d) := d.nat 7
  match k with
  | 0 => d.oneOf #["1", "12", "1.", "1.5", "1.5e3", "1.5E-2", "1.e", "1.5e+", "x.1", "٣", "٣.٤", "0x1"]
  | 1 => (d.oneOf #["`", "``"]).oneOf #["a", "A.b", "a.b.c", "a.", "λ", "x'.y", "1", ""]
  | 2 => d.oneOf #["?", "~", "?x", "?a:", "?ab'c:", "?A:", "?a :", "~a:"]
  | 3 => ((d.add "\"").times 3 (fun d => d.oneOf #["a", "\\n", "\\\"", "\\\\", "\\t", "\\x",
      "\\\n", "\n", "λ"])).oneOf #["\"", ""]
  | 4 => ((d.oneOf #["/-", "/--", "/-!"]).times 3 (fun d => d.oneOf #["x", "/", "-", "/-", "-/",
      "\n", "--"])).oneOf #["-/", ""]
  | 5 => (d.oneOf #["@[", "@[simp", "@[inline]"]).times 2 (fun d =>
      d.oneOf #["x", ",", "]", " ", "def", "inline"])
  | _ => d.oneOf #["#eval", "x#eval", "#check", "sorry", "sorry'", "admit", "Type", "Typeα",
      "xs[i]!", "xs[i]?", "xs[i]'h", "]!", "]?", "]'", "@[a]!",
      "Sort*", "λ", "Π", "Σ", "α", "πx", "ℕ", "𝒜x", "x₁", "aⁿ", "_x", "x!", "x?", "def", "fun",
      "at", "in"]

def grammarCase (lexer : Lexer) (d : Draw) : Draw :=
  match lexer with
  | .python => d.times 6 pyLine
  | .bash => d.times 10 fun d => (bashPart d).oneOf #["", " ", "\n"]
  | .console => d.times 6 consoleLine
  | .lean4 => d.times 10 fun d => (leanPart d).oneOf #["", " ", "\n"]
  | .text => d.oneOf #["a", "\n"]

/-- A third of the texts concatenate fragments, a third draw scalars, a
third follow each language's grammar of near misses. -/
def fuzzCases (lexer : Lexer) (count : Nat) (seed : UInt64) : Array Case := Id.run do
  let frags := fragments lexer
  let chars := (Src.ofString (alphabet lexer)).chars
  let seps := #["", "", " ", "\n"]
  let mut s := seed ^^^ UInt64.ofNat (lexer.pygmentsAlias.length * 7919 + 1)
  let mut out := #[]
  for k in [0:count] do
    let mut text := ""
    if k % 3 == 0 then
      let (n, s1) := pick s 30
      s := s1
      for _ in [0:n + 1] do
        let (f, s2) := pick s frags.size
        let (sep, s3) := pick s2 seps.size
        s := s3
        text := text ++ frags[f]?.getD "" ++ seps[sep]?.getD ""
    else if k % 3 == 1 then
      let (n, s1) := pick s 60
      s := s1
      for _ in [0:n + 1] do
        let (c, s2) := pick s chars.size
        s := s2
        text := text.push (chars[c]?.getD ' ')
    else
      let d := grammarCase lexer { seed := s }
      s := d.seed
      text := d.out
    out := out.push { corpus := "fuzz", label := s!"{lexer.pygmentsAlias}#{k}",
                      alias := lexer.pygmentsAlias, lexer, source := text }
  return out

def snippetRoot : System.FilePath := "testdata/highlight/snippets"
def recordPath : System.FilePath := "testdata/highlight/pygments-tokens.json"

def snippetCases : IO (Array Case) := do
  let mut out := #[]
  let dirs := (← snippetRoot.readDir).qsort (·.fileName < ·.fileName)
  for d in dirs do
    let some lexer := Lexer.ofName? d.fileName | die s!"{d.path}: no native lexer is named {d.fileName}"
    for f in (← d.path.readDir).qsort (·.fileName < ·.fileName) do
      let raw ← IO.FS.readFile f.path
      let req := ListingReply.Request.ofSource d.fileName raw
      out := out.push { corpus := "snippets", label := f.path.toString, alias := d.fileName,
                        lexer, source := req.source }
  return out

def between (s : String) (start stop : String) : Option (String × String) :=
  match s.splitOn start with
  | _ :: rest@(_ :: _) =>
    let after := start.intercalate rest
    match after.splitOn stop with
    | body :: tail@(_ :: _) => some (body, stop.intercalate tail)
    | _ => none
  | _ => none

/-- minted's `{lang}`, after its options. -/
def mintedListings (path : String) (text : String) : Array Case := Id.run do
  let mut out := #[]
  let mut rest := text
  for k in [0:text.length] do
    match between rest "\\begin{minted}" "\\end{minted}" with
    | none => break
    | some (body, tail) =>
      rest := tail
      let body := if body.startsWith "[" then
          match body.splitOn "]" with
          | _ :: more => "]".intercalate more
          | [] => body
        else body
      if body.startsWith "{" then
        match body.drop 1 |>.toString.splitOn "}" with
        | lang :: more =>
          let src := "}".intercalate more
          let req := ListingReply.Request.ofSource lang src
          if let some lexer := Lexer.ofName? req.language then
            out := out.push { corpus := "docs", label := s!"{path}#{k}", alias := req.language,
                              lexer, source := req.source }
        | [] => pure ()
  return out

/-- The value a listings option list gives `key`, its braces dropped. -/
def optionValue (opts key : String) : Option String :=
  (opts.splitOn ",").findSome? fun entry =>
    match entry.splitOn "=" with
    | k :: v :: more =>
      if k.trimAscii.toString != key then none
      else
        let v := ("=".intercalate (v :: more)).trimAscii.toString
        some (if v.startsWith "{" && v.endsWith "}" then ((v.drop 1).dropEnd 1).toString else v)
    | _ => none

/-- The language `\lstset` lists last in `text`, if any. -/
def lstsetLanguage (text : String) (current : Option String) : Option String :=
  ((text.splitOn "\\lstset{").drop 1).foldl (fun lang setting =>
    (optionValue ((setting.splitOn "}").headD "") "language").orElse fun _ => lang) current

/-- lstlisting's `language=`, from its own options or the `\lstset` in
force where it stands. -/
def lstListings (path : String) (text : String) : Array Case := Id.run do
  let mut out := #[]
  let pieces := text.splitOn "\\begin{lstlisting}"
  let mut lang := lstsetLanguage (pieces.headD "") none
  for (piece, k) in pieces.drop 1 |>.zipIdx do
    match piece.splitOn "\\end{lstlisting}" with
    | body :: after@(_ :: _) =>
      let (opts, src) := if body.startsWith "[" then
          match body.splitOn "]" with
          | o :: more => ((o.drop 1).toString, "]".intercalate more)
          | [] => ("", body)
        else ("", body)
      if let some l := (optionValue opts "language").orElse fun _ => lang then
        let req := ListingReply.Request.ofSource l src
        if let some lexer := Lexer.ofName? req.language then
          out := out.push { corpus := "docs", label := s!"{path}#lst{k}", alias := req.language,
                            lexer, source := req.source }
      lang := lstsetLanguage ("\\end{lstlisting}".intercalate after) lang
    | _ => pure ()
  return out

def texListings (path : String) (text : String) : Array Case :=
  let minted := mintedListings path text
  let lst := lstListings path text
  minted ++ lst

def mdListings (path : String) (text : String) : Array Case := Id.run do
  let mut out := #[]
  let mut lang : Option String := none
  let mut body : Array String := #[]
  let mut k := 0
  for line in text.splitOn "\n" do
    match lang with
    | none =>
      if line.startsWith "```" then
        lang := some (line.drop 3).toString.trimAscii.toString
        body := #[]
    | some l =>
      if line.trimAscii.toString == "```" then
        let req := ListingReply.Request.ofSource l ("\n".intercalate body.toList)
        if let some lexer := Lexer.ofName? req.language then
          out := out.push { corpus := "docs", label := s!"{path}#{k}", alias := req.language,
                            lexer, source := req.source }
        k := k + 1
        lang := none
      else body := body.push line
  return out

def docCases (paths : List String) : IO (Array Case) := do
  let mut out := #[]
  for p in paths do
    let text ← IO.FS.readFile p
    out := out ++ (if p.endsWith ".md" then mdListings p text else texListings p text)
  return out

/-- The alias Pygments is asked for: the listing's own, but `lean`'s Lean 4. -/
def pygmentsName (c : Case) : String :=
  if c.alias == leanIsLean4 then c.lexer.pygmentsAlias else c.alias

structure Reply where
  version : String
  python : String
  unicode : String
  answers : Array (Array Tok × Bool)
  colours : Std.HashMap (String × String) String

def runPygments (python : String) (cases : Array Case) : IO Reply := do
  let batch := Json.mkObj [
    ("requests", Json.arr (cases.map fun c =>
      Json.mkObj [("alias", Json.str (pygmentsName c)), ("source", Json.str c.source)])),
    ("styles", Json.arr (styles.toArray.map Json.str)),
    ("types", Json.arr (nativeTypes.toArray.map Json.str))]
  IO.FS.withTempDir fun dir => do
    let input := dir / "batch.json"
    IO.FS.writeFile input batch.compress
    let out ← IO.Process.output { cmd := python, args := #["-I", "-B", "-c", bridge, input.toString] }
    if out.exitCode != 0 then die s!"Pygments failed:\n{out.stderr}"
    let json ← match Json.parse out.stdout with
      | .ok j => pure j
      | .error e => die s!"the Pygments reply is not JSON: {e}"
    let version := (json.getObjValAs? String "pygments").toOption.getD "?"
    let py := (json.getObjValAs? String "python").toOption.getD "?"
    let unicode := (json.getObjValAs? String "unicode").toOption.getD "?"
    let some answers := (json.getObjVal? "answers").toOption.bind (·.getArr?.toOption)
      | die "the reply has no answers"
    let answers ← answers.mapM fun a => match theirTokens a with
      | .ok ts => pure ts
      | .error e => die s!"a malformed answer: {e}"
    let mut colours : Std.HashMap (String × String) String := {}
    for st in styles do
      let some table := ((json.getObjVal? "colours").toOption.bind (·.getObjVal? st |>.toOption))
        | die s!"the reply has no colours for {st}"
      let .obj kvs := table | die s!"the {st} colours are not an object"
      for (k, v) in kvs.toArray do
        colours := colours.insert (st, k) ((v.getStr?).toOption.getD "")
    return { version, python := py, unicode, answers, colours }

def selftest : IO UInt32 := do
  let mut fails : Array String := #[]
  let colourOf := fun (_ k : String) => if k == "Token.Name" || k == "Token.Text" then "" else k
  let base : Array Tok := #[(0, 3, "Token.Keyword"), (3, 4, "Token.Text"), (4, 6, "Token.Name")]
  if compare 6 colourOf base base != none then fails := fails.push "identical streams differ"
  let split : Array Tok := #[(0, 2, "Token.Keyword"), (2, 3, "Token.Keyword"), (3, 4, "Token.Text"),
    (4, 6, "Token.Name")]
  if (compare 6 colourOf base split).map (·.1) != some .raw then
    fails := fails.push "a split run is not raw-only: the scalar level must be blind to it"
  let renamed : Array Tok := #[(0, 3, "Token.Keyword"), (3, 4, "Token.Name"), (4, 6, "Token.Name")]
  if (compare 6 colourOf base renamed).map (·.1) != some .scalar then
    fails := fails.push "an alike-painted retype is not scalar-only: the colour level must be blind to it"
  let retyped : Array Tok := #[(0, 3, "Token.Operator"), (3, 4, "Token.Text"), (4, 6, "Token.Name")]
  if (compare 6 colourOf base retyped).map (·.1) != some .colour then
    fails := fails.push "a repainted retype is not a colour difference"
  for f in fails do IO.eprintln s!"highlight-diff --selftest: {f}"
  if fails.isEmpty then
    IO.println "highlight-diff --selftest: ok (4 cases)"
    return 0
  return 1

def jsonStr (s : String) : String := (Json.str s).compress

def record (python : String) : IO UInt32 := do
  let cases ← snippetCases
  let reply ← runPygments python cases
  if reply.version != PygmentsLexData.pygmentsVersion then
    die s!"Pygments {reply.version} answers, but the lexers mirror {PygmentsLexData.pygmentsVersion}: record with --python naming an interpreter that imports it"
  let mut out := "{\n  \"pygments\": " ++ jsonStr reply.version ++ ",\n  \"python\": " ++
    jsonStr reply.python ++ ",\n  \"cases\": ["
  for (c, k) in cases.zipIdx do
    let ts := (reply.answers[k]?.getD (#[], true)).1
    let src := (Src.ofString (c.source ++ "\n")).chars
    out := out ++ (if k == 0 then "" else ",") ++ "\n    {\"path\": " ++ jsonStr c.label ++
      ", \"tokens\": ["
    for ((a, b, kind), j) in ts.zipIdx do
      let text := String.ofList (src.extract a b).toList
      out := out ++ (if j == 0 then "" else ",") ++ "\n      [" ++ toString a ++ ", " ++
        jsonStr ((kind.drop 6).toString) ++ ", " ++ jsonStr text ++ "]"
    out := out ++ "]}"
  out := out ++ "\n  ]\n}\n"
  IO.FS.writeFile recordPath out
  IO.println s!"highlight-diff --record: wrote {recordPath} ({cases.size} snippets, Pygments {reply.version})"
  return 0

structure Opts where
  fuzz : Nat := 2000
  seed : UInt64 := 20261008
  lexers : List Lexer := Lexer.all
  python : String := "python3"
  anyVersion : Bool := false
  docs : List String := []
  shown : Nat := 3

def parse : List String → Opts → Except String Opts
  | [], o => .ok o
  | "--fuzz" :: n :: rest, o => match n.toNat? with
    | some k => parse rest { o with fuzz := k }
    | none => .error s!"--fuzz takes a count, not {n}"
  | "--seed" :: n :: rest, o => match n.toNat? with
    | some k => parse rest { o with seed := UInt64.ofNat k }
    | none => .error s!"--seed takes a number, not {n}"
  | "--lexer" :: n :: rest, o => match Lexer.ofName? n with
    | some l => parse rest { o with lexers := [l] }
    | none => .error s!"no native lexer is named {n}"
  | "--python" :: p :: rest, o => parse rest { o with python := p }
  | "--any-version" :: rest, o => parse rest { o with anyVersion := true }
  | "--docs" :: rest, o => .ok { o with docs := o.docs ++ rest }
  | a :: _, _ => .error s!"unknown argument {a}"

def main (args : List String) : IO UInt32 := do
  if args == ["--selftest"] then return ← selftest
  if args.head? == some "--record" then
    return ← record (match args with | [_, "--python", p] => p | _ => "python3")
  let o ← match parse args {} with
    | .ok o => pure o
    | .error e => die e
  let mut cases := (← snippetCases).filter fun c => o.lexers.contains c.lexer
  for l in o.lexers do
    cases := cases ++ fuzzCases l o.fuzz o.seed
  cases := cases ++ (← docCases o.docs).filter fun c => o.lexers.contains c.lexer
  let reply ← runPygments o.python cases
  if reply.version != PygmentsLexData.pygmentsVersion then
    if o.anyVersion then
      IO.println s!"highlight-diff: Pygments {reply.version} answers and the lexers mirror {PygmentsLexData.pygmentsVersion}: the differences below are a drift report"
    else
      die s!"Pygments {reply.version} answers, but the lexers mirror {PygmentsLexData.pygmentsVersion}: pass --python with an interpreter that imports {PygmentsLexData.pygmentsVersion}, or --any-version for a drift report"
  if reply.unicode != PygmentsLexData.unicodeVersion then
    IO.println s!"highlight-diff: this Python's Unicode is {reply.unicode} and the class tables' {PygmentsLexData.unicodeVersion}: scalars either version alone assigns may differ"
  let colourOf := fun (st k : String) => reply.colours.getD (st, k) "?"
  let mut tally : Std.HashMap (String × Lexer) (Nat × Nat × Nat × Nat) := {}
  let mut shown := 0
  let mut drift : Std.HashMap Lexer Nat := {}
  for (c, k) in cases.zipIdx do
    let n := c.source.length + 1
    let ours := nativeTokens c
    let (theirs, faithful) := reply.answers[k]?.getD (#[], true)
    if !faithful then drift := drift.insert c.lexer (drift.getD c.lexer 0 + 1)
    let verdict := compare n colourOf ours theirs
    let (cs, r, s, col) := tally.getD (c.corpus, c.lexer) (0, 0, 0, 0)
    let entry := match verdict with
      | none => (cs + 1, r, s, col)
      | some (.raw, _) => (cs + 1, r + 1, s, col)
      | some (.scalar, _) => (cs + 1, r + 1, s + 1, col)
      | some (.colour, _) => (cs + 1, r + 1, s + 1, col + 1)
    tally := tally.insert (c.corpus, c.lexer) entry
    if let some (level, at_) := verdict then
      if shown < o.shown then
        shown := shown + 1
        let src := (Src.ofString (c.source ++ "\n")).chars
        let ctx := String.ofList (src.extract (at_ - min at_ 20) (at_ + 20)).toList
        IO.println s!"highlight-diff: {c.label} ({c.alias}) differs at {level.name} level, scalar {at_}: \"{escape ctx}\"\n  ours:\n{showToks src ours at_}  Pygments:\n{showToks src theirs at_}"
  let mut failed := false
  for corpus in ["snippets", "fuzz", "docs"] do
    for l in o.lexers do
      if let some (cs, r, s, col) := tally.get? (corpus, l) then
        if r > 0 then failed := true
        IO.println s!"highlight-diff: corpus={corpus} lexer={l.pygmentsAlias} cases={cs} raw-diffs={r} scalar-diffs={s} colour-diffs={col}"
  for l in o.lexers do
    if let some d := drift.get? l then
      IO.println s!"highlight-diff: lexer={l.pygmentsAlias} pygments-offset-drift={d} (compared at the text's positions; the provider refuses these replies)"
  IO.println s!"highlight-diff: Pygments {reply.version}, Python {reply.python}: {if failed then "FAIL" else "ok"}"
  return if failed then 1 else 0
