/-
Regenerate LeanTex/Core/PygmentsStyleData.lean and
testdata/oracles/pygments-styles.tsv from an installed Pygments. Run from
the repository root with:

  lake env lean --run scripts/gen-pygments-style-data.lean [--python <interpreter>]

The interpreter defaults to `python3`. Pygments is the module it imports,
or else the wheel TeX Live installs beside its `latexminted` launcher: the
two places the listing provider reads it from (LeanTex/Cli/ListingHighlight.lean),
and the second is the one a lualatex build's minted runs.

For each shipped style (`Ir.ListingStyle`):
- the data module receives the style's `styles` table, every non-empty
  declaration verbatim, in token order: what `PygmentsStyle` resolves;
- the oracle receives Pygments' own answers for every standard token type
  (`pygments.token.STANDARD_TYPES`): `style_for_token`, and what the LaTeX
  formatter minted runs ships for one token of the type, read off its
  `\PYG` chain and the chain's command definitions.

A declaration word the painter does not carry is refused, never dropped:
a font family (`roman`, `sans`, `mono`), `noinherit`, and a colour that is
not `#rgb` or `#rrggbb`.
-/
import Lean.Data.Json

open Lean (Json)

def die (msg : String) : IO α := do
  IO.eprintln msg
  IO.Process.exit 1

def styles : List String := ["default", "friendly"]

/-- Constant program, run isolated (`-I`): no working directory, user site
or PYTHONPATH reaches the import. -/
def bridge : String := r#"import io
import json
import pathlib
import re
import shutil
import sys

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
from pygments.formatters.latex import LatexFormatter
from pygments.styles import get_style_by_name
from pygments.token import STANDARD_TYPES

COLOR = re.compile(r'#(?:[0-9A-Fa-f]{3}|[0-9A-Fa-f]{6})$')
FLAGS = {'bold', 'nobold', 'italic', 'noitalic', 'underline', 'nounderline'}

def carried(word):
    for prefix in ('bg:', 'border:'):
        if word.startswith(prefix):
            rest = word[len(prefix):]
            return rest == '' or COLOR.match(rest) is not None
    return word in FLAGS or COLOR.match(word) is not None

def hexcolor(value):
    return value.upper() if value else '-'

def minted(formatter, ttype):
    out = io.StringIO()
    formatter.format([(ttype, 'x')], out)
    found = re.search(r'\\PYG\{([^}]*)\}\{x\}', out.getvalue())
    chain = found.group(1) if found else ''
    look = {'chain': chain or '-', 'color': '-', 'bold': 0, 'italic': 0,
            'underline': 0, 'box': '-'}
    for name in chain.split('+'):
        body = formatter.cmd2def.get(name, '')
        if '@ff=' in body:
            raise SystemExit(f'{ttype}: a font family the painter does not carry')
        if r'\let\PYG@bf=\textbf' in body:
            look['bold'] = 1
        if r'\let\PYG@it=\textit' in body:
            look['italic'] = 1
        if r'\let\PYG@ul=\underline' in body:
            look['underline'] = 1
        color = re.search(r'\\textcolor\[rgb\]\{([^}]*)\}', body)
        if color:
            look['color'] = color.group(1)
        frame = re.search(r'\\fcolorbox\[rgb\]\{([^}]*)\}\{([^}]*)\}', body)
        fill = re.search(r'\\colorbox\[rgb\]\{([^}]*)\}', body)
        if frame:
            look['box'] = f'frame:{frame.group(1)}/{frame.group(2)}'
        elif fill:
            look['box'] = f'fill:{fill.group(1)}'
    return look

answers = []
for name in sys.argv[1:]:
    style = get_style_by_name(name)
    declarations = []
    for ttype in sorted(style.styles, key=tuple):
        text = style.styles[ttype]
        if not text:
            continue
        for word in text.split():
            if not carried(word):
                raise SystemExit(f'{name} {ttype}: the painter does not carry {word!r}')
        declarations.append([str(ttype), text])
    formatter = LatexFormatter(style=name, commandprefix='PYG')
    rows = []
    for ttype in sorted(STANDARD_TYPES, key=tuple):
        resolved = style.style_for_token(ttype)
        rows.append({'type': str(ttype), 'color': hexcolor(resolved['color']),
                     'bold': int(resolved['bold']), 'italic': int(resolved['italic']),
                     'underline': int(resolved['underline']),
                     'bgcolor': hexcolor(resolved['bgcolor']),
                     'border': hexcolor(resolved['border']),
                     'minted': minted(formatter, ttype)})
    answers.append({'name': name, 'declarations': declarations, 'rows': rows})
json.dump({'version': pygments.__version__, 'styles': answers}, sys.stdout)
"#

def strLit (s : String) : String :=
  "\"" ++ (s.replace "\\" "\\\\").replace "\"" "\\\"" ++ "\""

def field (j : Json) (key : String) : IO String := do
  match j.getObjVal? key with
  | .ok (.str s) => pure s
  | .ok (.num n) => pure (toString n)
  | _ => die s!"the Pygments answer has no '{key}' in {j.compress}"

def main (args : List String) : IO UInt32 := do
  let python := match args with
    | ["--python", p] => p
    | _ => "python3"
  let out ← try
    IO.Process.output { cmd := python, args := #["-I", "-B", "-c", bridge] ++ styles.toArray }
  catch e => die s!"{python} did not start: {e}"
  if out.exitCode != 0 then
    die s!"{python} could not read Pygments' styles:\n{out.stderr}"
  let json ← match Json.parse out.stdout with
    | .ok j => pure j
    | .error e => die s!"the Pygments answer is not JSON: {e}"
  let version ← field json "version"
  let some answers := (json.getObjVal? "styles").toOption.bind (·.getArr?.toOption)
    | die "the Pygments answer has no styles"
  let mut data := "module\n\n/-\nGenerated by scripts/gen-pygments-style-data.lean; do not edit by hand. \
Regenerate with:\n  lake env lean --run scripts/gen-pygments-style-data.lean\n\n\
Source: Pygments " ++ version ++ ", each shipped style's `styles` table, every\n\
non-empty declaration verbatim and in token order. This module carries only\n\
data: `PygmentsStyle` resolves it, and the suite holds that resolution to\n\
Pygments' own answers in testdata/oracles/pygments-styles.tsv.\n-/\n\n\
namespace LeanTex.Core.PygmentsStyleData\n"
  let mut table := "# generated by scripts/gen-pygments-style-data.lean — do not hand-edit\n\
# Pygments " ++ version ++ ". For every standard token type: style_for_token's colour,\n\
# bold, italic, underline, bgcolor and border, then what the LaTeX formatter\n\
# minted runs ships for one token of the type: its \\PYG chain, and the colour\n\
# (two-decimal rgb), bold, italic, underline and box its definitions compose to.\n\
style\ttype\tcolor\tbold\titalic\tunderline\tbgcolor\tborder\
\tchain\ttex-color\ttex-bold\ttex-italic\ttex-underline\ttex-box\n"
  for (name, answer) in styles.zip answers.toList do
    if (← field answer "name") != name then die s!"the Pygments answer reordered '{name}'"
    let some decls := (answer.getObjVal? "declarations").toOption.bind (·.getArr?.toOption)
      | die s!"'{name}' has no declarations"
    let mut lines : Array String := #[]
    for d in decls do
      let some pair := d.getArr?.toOption | die s!"'{name}': a malformed declaration"
      let (.str ttype, .str text) := (pair.getD 0 .null, pair.getD 1 .null)
        | die s!"'{name}': a malformed declaration"
      lines := lines.push s!"({strLit ttype}, {strLit text})"
    data := data ++ s!"\n/-- `pygments.styles.{name}`'s declarations: (token type, declaration). -/\n\
public def {name}Style : List (String × String) :=\n  [" ++
      ",\n   ".intercalate lines.toList ++ "]\n"
    let some rows := (answer.getObjVal? "rows").toOption.bind (·.getArr?.toOption)
      | die s!"'{name}' has no rows"
    for row in rows do
      let some tex := (row.getObjVal? "minted").toOption | die s!"'{name}': a row has no minted look"
      let cells := #[name, ← field row "type", ← field row "color", ← field row "bold",
        ← field row "italic", ← field row "underline", ← field row "bgcolor", ← field row "border",
        ← field tex "chain", ← field tex "color", ← field tex "bold", ← field tex "italic",
        ← field tex "underline", ← field tex "box"]
      table := table ++ "\t".intercalate cells.toList ++ "\n"
  data := data ++ "\nend LeanTex.Core.PygmentsStyleData\n"
  IO.FS.writeFile "LeanTex/Core/PygmentsStyleData.lean" data
  IO.FS.writeFile "testdata/oracles/pygments-styles.tsv" table
  IO.println s!"wrote LeanTex/Core/PygmentsStyleData.lean and testdata/oracles/pygments-styles.tsv from Pygments {version}"
  return 0
