/-
Regenerate LeanTex/Core/PygmentsLexData.lean and testdata/highlight's rules and licence from an
installed Pygments: the native lexers' data and their rules' digest.
Usage: lake env lean --run scripts/gen-pygments-lex-data.lean [--python <interpreter>]
-/
import Lean.Data.Json

open Lean (Json)

def die (msg : String) : IO α := do
  IO.eprintln msg
  IO.Process.exit 1

/-- The constant bridge program, run isolated (`-I`) so no working directory, user site or
PYTHONPATH reaches the import. -/
def bridge : String := r#"import hashlib
import json
import keyword
import pathlib
import re
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
from pygments.lexer import combined, default, include, words
from pygments.lexers._mapping import LEXERS
from pygments.lexers.lean import Lean4Lexer
from pygments.lexers.python import PythonLexer
from pygments.lexers.shell import BashLexer, BashSessionLexer
from pygments.token import _TokenType


def ranges(pred):
    out, start = [], None
    for c in range(0x110000):
        ok = pred(chr(c))
        if ok and start is None:
            start = c
        elif not ok and start is not None:
            out.append([start, c - 1])
            start = None
    if start is not None:
        out.append([start, 0x10FFFF])
    return out


def single(pattern):
    rx = re.compile(pattern)
    return ranges(lambda ch: rx.fullmatch(ch) is not None)


def continuing(pattern):
    rx = re.compile(pattern)
    return ranges(lambda ch: rx.fullmatch('a' + ch) is not None)


segment = Lean4Lexer._name_segment
pyname = PythonLexer.uni_name
classes = {
    'word': single(r'\w'), 'space': single(r'\s'), 'digit': single(r'\d'),
    'leanNameStart': single(segment), 'leanNameRest': continuing(segment),
    'pyNameStart': single(pyname), 'pyNameRest': continuing(pyname),
}


def ascii_members(name):
    return {c for lo, hi in classes[name] for c in range(lo, hi + 1) if c < 128}


# The lexers' ASCII fast paths read these sets by name; the tables decide
# every other scalar.
letters = set(range(65, 91)) | set(range(97, 123))
digits = set(range(48, 58))
expected_ascii = {
    'word': letters | digits | {95},
    'space': set(range(9, 14)) | set(range(28, 33)),
    'digit': digits,
    'leanNameStart': letters | {95},
    'leanNameRest': letters | digits | {95, 39, 33, 63},
    'pyNameStart': letters | {95},
    'pyNameRest': letters | digits | {95},
}
for name, want in expected_ascii.items():
    if ascii_members(name) != want:
        raise SystemExit(f'the ASCII members of \\{name} are not the fast path\'s')
for letter in 'rfbtu':
    folded = {chr(c) for c in range(0x110000) if re.fullmatch('(?i)' + letter, chr(c))}
    if folded != {letter, letter.upper()}:
        raise SystemExit(f'(?i){letter} matches more than its two ASCII cases')

lists = {}
kwstops = [k for k in keyword.kwlist if k[0].islower()]
abbrev = [(pyname, '<py-name>'), (segment, '<lean-segment>'), ('|'.join(kwstops), '<pythonSoftStops>')]


def alternation(state_rules, index, shape, key):
    """A regex rule whose alternation the mirror reads as a list."""
    rx = state_rules[index][0]
    found = re.fullmatch(shape, rx)
    if found is None:
        raise SystemExit(f'{key}: the rule is not the shape the mirror reads: {rx!r}')
    lists[key] = found.group(1).split('|')
    abbrev.append((found.group(1), f'<{key}>'))


bash = BashLexer.tokens
alternation(bash['basic'], 0, r'\\b\(([a-z|]+)\)\(\?!\[\\w#\$\?!\*@-\]\)\(\\s\*\)', 'bashKeywords')
alternation(bash['basic'], 1, r'\\b\(([a-z|]+)\)\(\?=\[\\s\)`\]\)', 'bashBuiltins')
py = PythonLexer.tokens
alternation(py['builtins'], 1, r'\(\?<!\\\.\)\(([A-Za-z|]+)\)\\b', 'pythonPseudo')
alternation(py['expr'], 24, r'\(([a-z|]+)\)\\b', 'pythonOperatorWords')
lists['pythonSoftStops'] = kwstops


def regex_text(rx):
    for full, short in abbrev:
        rx = rx.replace(full, short)
    return rx


def action(a):
    if a is None:
        return 'none'
    if type(a) is _TokenType:
        return str(a)
    names = a.__code__.co_freevars
    cells = dict(zip(names, (c.cell_contents for c in a.__closure__)))
    if names == ('args',):
        return 'bygroups(' + ', '.join(action(x) for x in cells['args']) + ')'
    if names == ('gt_kwargs', 'kwargs') and not cells['gt_kwargs'] and not cells['kwargs']:
        return 'using(this)'
    raise SystemExit(f'an action the mirror does not read: {a!r}')


def transition(s):
    if s is None:
        return ''
    if isinstance(s, combined):
        return ' -> combined(' + ', '.join(s) + ')'
    if isinstance(s, tuple):
        return ' -> (' + ', '.join(s) + ')'
    return ' -> ' + s


def longest_semantics(key, rx, ws):
    """words() compiles to an optimized regex; the mirror reads it as its
    prefix assertion, then the longest listed word its suffix admits. Check
    that reading on every word, between every lead and tail the assertions
    distinguish."""
    compiled = re.compile(rx.get())
    prefix = re.compile(rx.prefix) if rx.prefix else None
    suffix = re.compile(rx.suffix) if rx.suffix else None
    probes = ['', ' ', 'a', '_', '0', '.', '(', '\n', '\u00e9', '-', ':', '!', '?', "'"]
    for lead in probes:
        for w in ws:
            for tail in probes:
                text = lead + w + tail
                at = len(lead)
                m = compiled.match(text, at)
                want = None
                if prefix is None or prefix.match(text, at):
                    for cand in sorted(ws, key=len, reverse=True):
                        if text.startswith(cand, at) and (suffix is None or suffix.match(text, at + len(cand))):
                            want = cand
                            break
                got = m.group() if m else None
                if got != want:
                    raise SystemExit(f'{key}: {text!r} at {at} matches {got!r}, not the longest admitted {want!r}')


def structure(cls, names):
    out = [f'lexer {cls.__name__}']
    for state, rules in cls.tokens.items():
        out.append(f'  state {state}')
        for i, r in enumerate(rules):
            if isinstance(r, include):
                out.append(f'    include {r}')
            elif isinstance(r, default):
                if not (isinstance(r.state, str) and r.state.startswith('#pop')):
                    raise SystemExit(f'{cls.__name__} {state}: default({r.state!r}) pushes without '
                                     'reading, which the native drive reads as no match')
                out.append(f'    default{transition(r.state)}')
            else:
                rx, act = r[0], r[1]
                if isinstance(rx, words):
                    key = names.get((state, i))
                    if key is None:
                        raise SystemExit(f'{cls.__name__} {state} rule {i}: a word list the mirror does not read')
                    if key in lists and lists[key] != list(rx.words):
                        raise SystemExit(f'{key}: two rules disagree on the list')
                    lists[key] = list(rx.words)
                    longest_semantics(key, rx, list(rx.words))
                    shown = f'words({key}, prefix={rx.prefix!r}, suffix={rx.suffix!r})'
                else:
                    shown = repr(regex_text(rx))
                out.append(f'    {shown} {action(act)}{transition(r[2] if len(r) > 2 else None)}')
    return out


text = []
text += structure(Lean4Lexer, {
    ('expression', 4): 'lean4KeywordType', ('expression', 5): 'lean4ErrorWords',
    ('expression', 6): 'lean4Operators', ('expression', 7): 'lean4Punctuation',
    ('root', 0): 'lean4KeywordNamespace', ('root', 1): 'lean4Keyword'})
text += structure(PythonLexer, {
    ('expr-keywords', 0): 'pythonExprKeywords', ('expr-keywords', 1): 'pythonConstants',
    ('keywords', 0): 'pythonKeywords', ('keywords', 1): 'pythonConstants',
    ('builtins', 0): 'pythonBuiltins', ('builtins', 2): 'pythonExceptions',
    ('magicfuncs', 0): 'pythonMagicFuncs', ('magicvars', 0): 'pythonMagicVars'})
text += structure(BashLexer, {})
text.append('lexer BashSessionLexer')
text.append(f'  ps1 {BashSessionLexer._ps1rgx.pattern!r}')
text.append(f'  ps2 {BashSessionLexer._ps2!r}')
text.append(f'  venv {BashSessionLexer._venv.pattern!r}')
text.append(f'  bare-continuation {BashSessionLexer._bare_continuation!r}')
rules = '\n'.join(text) + '\n'

aliases = {}
for lexer in ('Lean4Lexer', 'PythonLexer', 'BashLexer', 'BashSessionLexer', 'TextLexer'):
    aliases[lexer] = list(LEXERS[lexer][2])

# Every alias the registry selects a lexer by, the names a minted language
# argument may spell: one word each, as the data spells them space-separated.
registry = sorted({alias for entry in LEXERS.values() for alias in entry[2]})
for alias in registry:
    if not alias or alias != alias.lower() or any(c.isspace() for c in alias):
        raise SystemExit(f'the registry alias {alias!r} is not one lowercase word')

import importlib.metadata
dist = importlib.metadata.distribution('Pygments')
licence = dist.read_text('licenses/LICENSE') or dist.read_text('LICENSE')
if not licence:
    raise SystemExit('the installed Pygments carries no LICENSE')

json.dump({
    'licence': licence,
    'pygments': pygments.__version__,
    'python': sys.version.split()[0],
    'unicode': unicodedata.unidata_version,
    'rules': rules,
    'digest': hashlib.sha256(rules.encode('utf-8')).hexdigest(),
    'classes': classes,
    'lists': lists,
    'aliases': aliases,
    'registry': registry,
}, sys.stdout)
"#

def strLit (s : String) : String := Id.run do
  let mut out := "\""
  for c in s.toList do
    if c == '\\' then out := out ++ "\\\\"
    else if c == '"' then out := out ++ "\\\""
    else if c == '\n' then out := out ++ "\\n"
    else if c == '\t' then out := out ++ "\\t"
    else if c.toNat < 0x20 || c.toNat == 0x7f then out := out ++ s!"\\x{String.ofList (Nat.toDigits 16 c.toNat)}"
    else out := out.push c
  return out.push '"'

def hex6 (n : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 n)
  String.ofList (List.replicate (6 - s.length) '0') ++ s

def field (j : Json) (key : String) : IO Json := do
  match j.getObjVal? key with
  | .ok v => pure v
  | .error _ => die s!"the Pygments answer has no '{key}'"

def str (j : Json) (key : String) : IO String := do
  match ← field j key with
  | .str s => pure s
  | _ => die s!"the Pygments answer's '{key}' is not a string"

def strings (j : Json) : IO (Array String) := do
  let some xs := j.getArr?.toOption | die s!"not a list: {j.compress}"
  xs.mapM fun x => match x with
    | .str s => pure s
    | _ => die s!"not a string: {x.compress}"

def nat (j : Json) : IO Nat := do
  match j.getNat? with
  | .ok n => pure n
  | .error _ => die s!"not a natural number: {j.compress}"

/-- The ranges of one class as fixed-width hex: 6 digits for the low
scalar, 6 for the high, inclusive, ascending and disjoint. -/
def rangeHex (j : Json) (name : String) : IO String := do
  let some rs := j.getArr?.toOption | die s!"class {name} is not a list"
  let mut out := ""
  let mut last : Option Nat := none
  for r in rs do
    let some pair := r.getArr?.toOption | die s!"class {name}: a malformed range"
    let lo ← nat (pair.getD 0 .null)
    let hi ← nat (pair.getD 1 .null)
    if hi < lo || hi > 0x10FFFF || (last.map (fun l => decide (l + 1 ≥ lo))).getD false then
      die s!"class {name}: ranges must ascend, stay disjoint and apart"
    last := some hi
    out := out ++ hex6 lo
    out := out ++ hex6 hi
  return out

def classDocs : List (String × String) :=
  [("word", "`\\w`: Python's `re` word characters, what `\\b` divides on."),
   ("space", "`\\s`: Python's `re` whitespace."),
   ("digit", "`\\d`: Python's `re` decimal digits."),
   ("leanNameStart", "The first scalar of a Lean 4 name segment."),
   ("leanNameRest", "A later scalar of a Lean 4 name segment."),
   ("pyNameStart", "The first scalar of a name, by the Python lexer's name pattern."),
   ("pyNameRest", "A later scalar of a name, by the Python lexer's name pattern.")]

def listDocs : List (String × String) :=
  [("lean4KeywordNamespace", "Lean 4 `root`: `Keyword.Namespace` words."),
   ("lean4Keyword", "Lean 4 `root`: `Keyword` words."),
   ("lean4KeywordType", "Lean 4 `expression`: `Keyword.Type` words."),
   ("lean4ErrorWords", "Lean 4 `expression`: `Generic.Error` words."),
   ("lean4Operators", "Lean 4 `expression`: `Name.Builtin.Pseudo` operators."),
   ("lean4Punctuation", "Lean 4 `expression`: punctuation, typed `Operator`."),
   ("pythonKeywords", "Python `keywords`: `Keyword` words."),
   ("pythonConstants", "Python `keywords` and `expr-keywords`: `Keyword.Constant` words."),
   ("pythonExprKeywords", "Python `expr-keywords`: `Keyword` words."),
   ("pythonBuiltins", "Python `builtins`: `Name.Builtin` words."),
   ("pythonPseudo", "Python `builtins`: the `Name.Builtin.Pseudo` alternation."),
   ("pythonExceptions", "Python `builtins`: `Name.Exception` words."),
   ("pythonMagicFuncs", "Python `magicfuncs`: `Name.Function.Magic` words."),
   ("pythonMagicVars", "Python `magicvars`: `Name.Variable.Magic` words."),
   ("pythonOperatorWords", "Python `expr`: the `Operator.Word` alternation."),
   ("pythonSoftStops", "Python `soft-keywords`: the keywords whose arrival means `match`/`case` is a name."),
   ("bashKeywords", "Bash `basic`: the `Keyword` alternation, in its order."),
   ("bashBuiltins", "Bash `basic`: the `Name.Builtin` alternation, in its order.")]

def aliasDocs : List (String × String) :=
  [("Lean4Lexer", "lean4Aliases"), ("PythonLexer", "pythonAliases"), ("BashLexer", "bashAliases"),
   ("BashSessionLexer", "consoleAliases"), ("TextLexer", "textAliases")]

def arrayLit (xs : Array String) : String :=
  "#[" ++ ", ".intercalate (xs.toList.map strLit) ++ "]"

def main (args : List String) : IO UInt32 := do
  let python := match args with
    | ["--python", p] => p
    | _ => "python3"
  let out ← try
    IO.Process.output { cmd := python, args := #["-I", "-B", "-c", bridge] }
  catch e => die s!"{python} did not start: {e}"
  if out.exitCode != 0 then
    die s!"{python} could not read Pygments' lexers:\n{out.stderr}"
  let json ← match Json.parse out.stdout with
    | .ok j => pure j
    | .error e => die s!"the Pygments answer is not JSON: {e}"
  let version ← str json "pygments"
  let pyVersion ← str json "python"
  let uniVersion ← str json "unicode"
  let rules ← str json "rules"
  let digest ← str json "digest"
  let licence ← str json "licence"
  let classes ← field json "classes"
  let lists ← field json "lists"
  let aliases ← field json "aliases"
  let registry ← strings (← field json "registry")
  let mut data := "module\n\n/-\nGenerated by scripts/gen-pygments-lex-data.lean; do not edit by hand. \
Regenerate with:\n  lake env lean --run scripts/gen-pygments-lex-data.lean\n\n\
Source: Pygments " ++ version ++ " under Python " ++ pyVersion ++ " (Unicode " ++ uniVersion ++ "):\n\
the word lists its Lean 4, Python and Bash lexers match, the character\n\
classes their patterns name, and the registry aliases that select them.\n\
This module carries only data: the native lexers in LeanTex/Core/Highlight/\n\
read it, and the suite holds them to Pygments' own token streams in\n\
testdata/highlight/pygments-tokens.json. Pygments is BSD-licensed; its\n\
licence is testdata/highlight/LICENSE-Pygments.\n-/\n\n\
namespace LeanTex.Core.PygmentsLexData\n\n"
  data := data ++ s!"public def pygmentsVersion : String := {strLit version}\n\n"
  data := data ++ s!"public def pythonVersion : String := {strLit pyVersion}\n\n"
  data := data ++ s!"public def unicodeVersion : String := {strLit uniVersion}\n\n"
  data := data ++ "/-- SHA-256 of the rule structure in testdata/highlight/pygments-rules.txt. -/\n" ++
    s!"public def rulesDigest : String := {strLit digest}\n"
  for (name, doc) in classDocs do
    let hex ← rangeHex (← field classes name) name
    data := data ++ s!"\n/-- {doc}\nRanges in 12 hex digits each, low then high, inclusive, ascending. -/\n" ++
      s!"public def {name} : String := {strLit hex}\n"
  for (name, doc) in listDocs do
    let xs ← strings (← field lists name)
    data := data ++ s!"\n/-- {doc} -/\npublic def {name} : Array String :=\n  {arrayLit xs}\n"
  for (lexer, name) in aliasDocs do
    let xs ← strings (← field aliases lexer)
    data := data ++ s!"\n/-- The registry aliases of `{lexer}`. -/\npublic def {name} : Array String := {arrayLit xs}\n"
  data := data ++ "\n/-- Every alias Pygments' registry selects a lexer by, ascending, one space\n" ++
    "between each: the lexer names a listing's language may spell. -/\n" ++
    s!"public def registryAliases : String :=\n  {strLit (" ".intercalate registry.toList)}\n"
  data := data ++ "\nend LeanTex.Core.PygmentsLexData\n"
  IO.FS.writeFile "LeanTex/Core/PygmentsLexData.lean" data
  IO.FS.writeFile "testdata/highlight/LICENSE-Pygments" licence
  IO.FS.writeFile "testdata/highlight/pygments-rules.txt"
    ("# generated by scripts/gen-pygments-lex-data.lean — do not hand-edit\n# Pygments " ++
      version ++ ": the rules the native lexers mirror, word lists and large classes named.\n" ++ rules)
  IO.println s!"wrote LeanTex/Core/PygmentsLexData.lean, testdata/highlight/pygments-rules.txt and its licence from Pygments {version} (rules {digest})"
  return 0
