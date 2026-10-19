/-
Regenerate LeanTex/Core/PygmentsLexData.lean (with each code row's unmirrored lexer's rule table) and testdata/highlight's rules and licence
from Pygments `GenData.pygmentsRelease` under `GenData.pygmentsPython` and the departures testdata/highlight/pygments-departures.json declares.
Usage: lake build scripts.GenData LeanTex.Core.SurfaceKind && lake env lean --run scripts/gen-pygments-lex-data.lean [--python <interpreter>] | --selftest
-/
import scripts.GenData
import Lean.Data.Json
import LeanTex.Core.SurfaceKind

open GenData
open Lean (Json)

/-- The constant bridge program, run isolated (`-I`) so no working directory, user site or
PYTHONPATH reaches the import. -/
def bridge : String := r#"import hashlib
import importlib
import json
import keyword
import pathlib
import re
import shutil
import sys
import unicodedata

"# ++ GenData.pinnedLoader (some GenData.pygmentsPython) ++ r#"from pygments.lexer import RegexLexer, _TokenType, bygroups, combined, default, include, words
from pygments.lexers._mapping import LEXERS
from pygments.lexers.c_cpp import CFamilyLexer
from pygments.lexers.lean import Lean4Lexer
from pygments.lexers.python import PythonLexer
from pygments.lexers.shell import BashLexer, BashSessionLexer
from pygments.token import STANDARD_TYPES, _TokenType, string_to_tokentype

departures = json.loads(sys.argv[1])
table_aliases = json.loads(sys.argv[2])


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


def departure_rule(rx, *kinds):
    """A declared rule as Pygments reads it: `<lean-segment>` expanded, one standard type for the
    match or one per group."""
    if any(short in rx for _, short in abbrev if short != '<lean-segment>'):
        raise SystemExit(f'a departure from {rx!r} abbreviates more than <lean-segment>')
    rx = rx.replace('<lean-segment>', segment)
    types = [string_to_tokentype(k) for k in kinds]
    if not types or any(t not in STANDARD_TYPES for t in types):
        raise SystemExit(f'a departure from {rx!r} names no standard token type: {kinds!r}')
    if len(types) > 1 and re.compile(rx).groups != len(types):
        raise SystemExit(f'a departure from {rx!r} types {len(types)} groups it does not have')
    return rx, types[0] if len(types) == 1 else bygroups(*types)


def unreached(rx, declared):
    """The words a `\\b`-prefixed list holds that start on a non-word scalar, so that its prefix
    holds only after a word, and no declared rule of their state reads whole opening a text and
    after a line break."""
    if not isinstance(rx, words) or rx.prefix != r'\b':
        return []
    reads = [re.compile(departure_rule(*r)[0]) for r in declared['rules']] if declared else []
    whole = lambda d, t: (m := d.match(t)) is not None and m.end() == len(t)
    return [w for w in rx.words if not re.match(r'\w', w)
            and not any(whole(d, w) and whole(d, '\n' + w) for d in reads)]


departed = set()


def structure(cls, names):
    out = [f'lexer {cls.__name__}']
    for state, rules in cls.tokens.items():
        out.append(f'  state {state}')
        declared = departures.get(cls.__name__, {}).get(state)
        if declared is not None:
            because, check = declared['because'], declared['check']
            if not because or '\n' in because or not check.isidentifier():
                raise SystemExit(f'{cls.__name__} {state}: a departure names its reason in one '
                                 'line and the check holding it')
            if not declared['fires'] or not declared['holds']:
                raise SystemExit(f'{cls.__name__} {state}: a departure names texts it changes and '
                                 'texts it leaves')
            out.append(f'    departure held by {check} because {because}')
            for r in declared['rules']:
                rx, act = departure_rule(*r)
                out.append(f'    departure {regex_text(rx)!r} {action(act)}')
            departed.add((cls.__name__, state))
        for i, r in enumerate(rules):
            if not isinstance(r, (include, default)) and (lost := unreached(r[0], declared)):
                raise SystemExit(f'{cls.__name__} {state} rule {i}: {lost!r} follow a \\b their '
                                 'first scalar meets only after a word: declare a departure that reads them')
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
stray = {(lexer, state) for lexer, states in departures.items() for state in states} - departed
if stray:
    raise SystemExit(f'departures name states no mirrored lexer has: {sorted(stray)!r}')

aliases = {}
for lexer in ('Lean4Lexer', 'PythonLexer', 'BashLexer', 'BashSessionLexer', 'TextLexer'):
    aliases[lexer] = list(LEXERS[lexer][2])

# Every alias the registry selects a lexer by, the names a minted language
# argument may spell: one word each, as the data spells them space-separated.
registry = sorted({alias for entry in LEXERS.values() for alias in entry[2]})
for alias in registry:
    if not alias or alias != alias.lower() or any(c.isspace() for c in alias):
        raise SystemExit(f'the registry alias {alias!r} is not one lowercase word')


# A table lexer: its rules exported whole, each pattern as Python's `re` parser reads it, in postfix.
import re._parser as sre_parse
import re._constants as sre_c

CATEGORIES = {'CATEGORY_WORD': 'w', 'CATEGORY_NOT_WORD': 'W', 'CATEGORY_DIGIT': 'd',
              'CATEGORY_NOT_DIGIT': 'D', 'CATEGORY_SPACE': 's', 'CATEGORY_NOT_SPACE': 'S'}


def hexed(c):
    return format(c, 'x')


def postfix(p, flags, out):
    """A sequence's items, each run of literals one string, joined by `+`; `e` for none."""
    items, n, i = list(p), 0, 0
    while i < len(items):
        j = i
        while j < len(items) and str(items[j][0]) == 'LITERAL':
            j += 1
        if j - i >= 2:
            out.append('l' + '.'.join(hexed(a) for _, a in items[i:j]))
            i = j
        else:
            postfix_item(items[i][0], items[i][1], flags, out)
            i += 1
        n += 1
        if n > 1:
            out.append('+')
    if n == 0:
        out.append('e')


def postfix_item(op, av, flags, out):
    name, multiline = str(op), flags & re.MULTILINE
    if name == 'LITERAL':
        out.append('c' + hexed(av))
    elif name == 'NOT_LITERAL':
        out.append('n' + hexed(av))
    elif name == 'ANY':
        out.append(',' if flags & re.DOTALL else '.')
    elif name == 'IN':
        neg, parts = '', []
        for o, a in av:
            o = str(o)
            if o == 'NEGATE':
                neg = '^'
            elif o == 'LITERAL':
                parts.append(hexed(a))
            elif o == 'RANGE':
                parts.append(hexed(a[0]) + '-' + hexed(a[1]))
            elif o == 'CATEGORY' and str(a) in CATEGORIES:
                parts.append(CATEGORIES[str(a)])
            else:
                raise SystemExit(f'a set member the table lexer does not read: {o}')
        out.append('[' + neg + ','.join(parts))
    elif name == 'AT':
        code = {'AT_BEGINNING': '^' if multiline else 'A', 'AT_BEGINNING_STRING': 'A',
                'AT_END': '$' if multiline else 'z', 'AT_END_STRING': 'Z',
                'AT_BOUNDARY': 'b', 'AT_NON_BOUNDARY': 'B'}.get(str(av))
        if code is None:
            raise SystemExit(f'an anchor the table lexer does not read: {av}')
        out.append(code)
    elif name == 'SUBPATTERN':
        group, add, drop, body = av
        if (add | drop) & ~(re.DOTALL | re.MULTILINE):
            raise SystemExit('a scoped flag the table lexer does not read')
        postfix(body, (flags | add) & ~drop, out)
        if group is not None:
            out.append('g' + str(group))
    elif name == 'BRANCH':
        for b in av[1]:
            postfix(b, flags, out)
        out.extend(['|'] * (len(av[1]) - 1))
    elif name in ('MAX_REPEAT', 'MIN_REPEAT'):
        lo, hi, body = av
        postfix(body, flags, out)
        out.append(('*' if name == 'MAX_REPEAT' else '?') + str(lo) + ':' +
                   ('-' if hi == sre_c.MAXREPEAT else str(hi)))
    elif name in ('ASSERT', 'ASSERT_NOT'):
        direction, body = av
        postfix(body, flags, out)
        if direction == 1:
            out.append('>' if name == 'ASSERT' else '!')
        else:
            lo, hi = body.getwidth()
            if lo != hi:
                raise SystemExit('a lookbehind of no fixed width')
            out.append(('<' if name == 'ASSERT' else '~') + str(lo))
    elif name == 'GROUPREF':
        out.append('r' + str(av))
    else:
        raise SystemExit(f'a pattern operation the table lexer does not read: {name}')


def pattern_code(pattern, flags):
    p = sre_parse.parse(pattern, flags)
    if p.state.flags & (re.IGNORECASE | re.LOCALE | re.ASCII):
        raise SystemExit(f'a flag the table lexer does not read in {pattern!r}')
    out = []
    postfix(p, p.state.flags, out)
    return ' '.join(out), p.state.groups - 1


def token_name(t):
    s = str(t)
    if not s.startswith('Token.'):
        raise SystemExit(f'not a token type below Token: {s}')
    return s[len('Token.'):]


def rule_table(cls):
    cls(stripnl=False, stripall=False, ensurenl=False, tabsize=0)
    tokens = cls._tokens
    names = list(tokens)
    index = {n: i for i, n in enumerate(names)}

    def relex(a):
        cells = dict(zip(a.__code__.co_freevars, (c.cell_contents for c in a.__closure__)))
        if a.__code__.co_freevars != ('gt_kwargs', 'kwargs') or cells['kwargs'] or \
                set(cells['gt_kwargs']) - {'stack'}:
            raise SystemExit(f'{cls.__name__}: a callback the table lexer does not read: {a!r}')
        return 'u' + '/'.join(str(index[st]) for st in cells['gt_kwargs'].get('stack', ('root',)))

    def group_action(a):
        if a is None:
            return '-'
        if type(a) is _TokenType:
            return 't' + token_name(a)
        return relex(a)

    def action(a):
        if a is None:
            return '-'
        if type(a) is _TokenType:
            return 't' + token_name(a)
        if a.__code__.co_freevars == ('args',):
            return 'g' + ';'.join(group_action(x) for x in a.__closure__[0].cell_contents)
        return relex(a)

    def transition(ns):
        if ns is None:
            return '-'
        if isinstance(ns, int):
            return 'p' + str(-ns)
        if ns == '#push':
            return 'd'
        if isinstance(ns, tuple):
            return ','.join('p1' if st == '#pop' else 'd' if st == '#push' else 's' + str(index[st])
                            for st in ns)
        raise SystemExit(f'{cls.__name__}: a transition the table lexer does not read: {ns!r}')

    patterns, sources, rules = {}, [], []
    for n in names:
        rules.append('state ' + n)
        for rexmatch, act, ns in tokens[n]:
            compiled = rexmatch.__self__
            code = pattern_code(compiled.pattern, compiled.flags)
            if code not in patterns:
                patterns[code] = len(patterns)
                sources.append([compiled.pattern, compiled.flags])
            rules.append(f'r {patterns[code]} {action(act)} {transition(ns)}')
    head = [f'lexer {len(names)} {index["root"]} {len(patterns)}']
    return '\n'.join(head + [f'p {g} {c}' for (c, g) in patterns] + rules), sources


def retyped(cls):
    """The names a lexer's own lexing retypes from Name to Keyword.Type after its rules."""
    owner = next(k for k in cls.__mro__ if 'get_tokens_unprocessed' in k.__dict__)
    if owner is RegexLexer:
        return []
    if owner is CFamilyLexer:
        return sorted(set(cls.stdlib_types) | set(cls.c99_types) | set(cls.c11_atomic_types) |
                      set(cls.linux_types))
    raise SystemExit(f'{cls.__name__} lexes past its rules, in {owner.__name__}')


mirrored = {'Lean4Lexer', 'PythonLexer', 'BashLexer', 'BashSessionLexer', 'TextLexer'}
tables = []
for alias in table_aliases:
    found = next(((n, e) for n, e in LEXERS.items() if alias in e[2]), None)
    if found is None:
        raise SystemExit(f'no Pygments lexer is named {alias!r}')
    name, entry = found
    if name in mirrored or any(t['class'] == name for t in tables):
        continue
    cls = getattr(importlib.import_module(entry[0]), name)
    if not issubclass(cls, RegexLexer) or getattr(cls, 'flags', re.MULTILINE) & re.IGNORECASE:
        raise SystemExit(f'{name} is no RegexLexer the table lexer reads')
    table_rules, sources = rule_table(cls)
    tables.append({'class': name, 'aliases': list(entry[2]), 'rules': table_rules,
                   'sources': sources, 'retype': retyped(cls)})

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
    'tables': tables,
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

def departuresPath : System.FilePath := "testdata/highlight/pygments-departures.json"

/-- Each table lexer's patterns as Pygments compiles them, source and flags, in the table's order,
which highlight-diff's pattern comparison asks Python's `re` for. -/
def tablePatternsPath : System.FilePath := "testdata/highlight/table-patterns.json"

def main (args : List String) : IO UInt32 := do
  if args == ["--selftest"] then return ← pinSelftest "gen-pygments-lex-data" bridge (some pygmentsPython)
  let python ← match args with
    | [] => pure "python3"
    | ["--python", p] => pure p
    | _ => die "usage: gen-pygments-lex-data [--python <interpreter>] | --selftest"
  let departures ← match Json.parse (← IO.FS.readFile departuresPath) with
    | .ok j => pure j.compress
    | .error e => die s!"{departuresPath} is not JSON: {e}"
  let tableAliases := (Json.arr (LeanTex.Core.Ir.CodeLang.all.toArray.map (Json.str ·.listing))).compress
  let out ← try
    IO.Process.output { cmd := python, args := #["-I", "-B", "-c", bridge, departures, tableAliases] }
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
  let some tables := (← field json "tables").getArr?.toOption | die "the Pygments answer's tables are not a list"
  let mut data := "module\n\n/-\nGenerated by scripts/gen-pygments-lex-data.lean; do not edit by hand. \
Regenerate with:\n  lake env lean --run scripts/gen-pygments-lex-data.lean --python <Python " ++
    pygmentsPython ++ " importing Pygments " ++ pygmentsRelease ++ ">\n\n\
Source: Pygments " ++ version ++ " under Python " ++ pyVersion ++ " (Unicode " ++ uniVersion ++ "):\n\
the word lists its Lean 4, Python and Bash lexers match, the character\n\
classes their patterns name, the registry aliases that select them, and\n\
the rule tables of the lexers the table lexer drives.\n\
This module carries only data: the native lexers in LeanTex/Core/Highlight/\n\
read it, and the suite holds them to Pygments' token streams, under the\n\
departures testdata/highlight/pygments-departures.json declares, in\n\
testdata/highlight/pygments-tokens.json. Pygments is BSD-licensed; its\n\
licence is " ++ pygmentsLicence ++ ".\n-/\n\n\
namespace LeanTex.Core.PygmentsLexData\n\n"
  data := data ++ s!"public def pygmentsVersion : String := {strLit version}\n\n"
  data := data ++ s!"public def pythonVersion : String := {strLit pyVersion}\n\n"
  data := data ++ s!"public def unicodeVersion : String := {strLit uniVersion}\n\n"
  data := data ++ "/-- SHA-256 of the rule structure in testdata/highlight/pygments-rules.txt. -/\n" ++
    s!"public def rulesDigest : String := {strLit digest}\n"
  data := data ++ s!"\n/-- {departuresPath} as these data were generated under it, compressed. -/\n" ++
    s!"public def departures : String :=\n  {strLit departures}\n"
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
  let tableField (key : String) : IO (Array Json) := tables.mapM fun t => field t key
  let classNames ← (← tableField "class").mapM fun j => match j with
    | .str s => pure s
    | _ => die "a table's class is not a string"
  data := data ++ "\n/-- The Pygments lexers the table lexer drives, by class. -/\n" ++
    s!"public def tableClasses : Array String := {arrayLit classNames}\n"
  data := data ++ "\n/-- Each table lexer's registry aliases. -/\npublic def tableAliases : Array (Array String) :=\n  #[" ++
    ", ".intercalate ((← (← tableField "aliases").mapM strings).toList.map arrayLit) ++ "]\n"
  data := data ++ "\n/-- Each table lexer's names its own lexing retypes from `Name` to `Keyword.Type`. -/\n" ++
    "public def tableRetypes : Array (Array String) :=\n  #[" ++
    ", ".intercalate ((← (← tableField "retype").mapM strings).toList.map arrayLit) ++ "]\n"
  let ruleTexts ← (← tableField "rules").mapM fun j => match j with
    | .str s => pure s
    | _ => die "a table's rules are not a string"
  data := data ++ "\n/-- Each table lexer's rules: its patterns in postfix as Python's `re` parser reads them, its\n" ++
    "states and each rule's pattern, action and transition (`Highlight.Table.Decode`). -/\n" ++
    "public def tableRules : Array String :=\n  #[" ++
    ",\n    ".intercalate (ruleTexts.toList.map strLit) ++ "]\n"
  data := data ++ "\nend LeanTex.Core.PygmentsLexData\n"
  let sources ← tableField "sources"
  let patternsJson := Json.mkObj ((classNames.zip sources).toList.map fun (c, j) => (c, j))
  IO.FS.writeFile "LeanTex/Core/PygmentsLexData.lean" data
  IO.FS.writeFile tablePatternsPath (patternsJson.pretty ++ "\n")
  IO.FS.writeFile pygmentsLicence licence
  IO.FS.writeFile "testdata/highlight/pygments-rules.txt"
    ("# generated by scripts/gen-pygments-lex-data.lean — do not hand-edit\n# Pygments " ++
      version ++ ": the rules the native lexers mirror, word lists and large classes named;\n" ++
      "# a departure line is " ++ departuresPath.toString ++ "'s, tried before its state's own.\n" ++
      rules)
  IO.println s!"wrote LeanTex/Core/PygmentsLexData.lean, testdata/highlight/pygments-rules.txt and its licence from Pygments {version} (rules {digest})"
  return 0
