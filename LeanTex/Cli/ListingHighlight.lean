module

public import LeanTex.Core.ListingReply
public import LeanTex.Core.Diag
import LeanTex.Cli.DriverDiag
import LeanTex.Cli.Host
import LeanTex.Cli.RunBounded

/-!
The installed Pygments boundary. One isolated Python process classifies a
bounded batch; only built-in registry aliases select lexers. The document
supplies language and source data, never Python, options, filters or paths.
`ListingReply.decode` validates the entire response before any classification
can reach the IR. Provider failures retain the source and name its lost
highlighting through the driver's diagnostic builder.
-/
namespace LeanTex.Cli.ListingHighlight

open LeanTex.Core

/-- Constant program, not authored code. Python's isolated mode excludes the
working directory, user site and PYTHONPATH. A normal installation is preferred;
TeX Live also installs Pygments as a wheel beside its resolved latexminted
launcher. Only that installed directory is searched, and latexminted is never
executed. Neither provider discovery nor lexer selection reads a document path.

The raw-token API bypasses Pygments' newline, tab and filter preprocessing.
One lexer-only LF lets newline-terminated rules also classify the final line.
The pure decoder validates that boundary and removes only its empty last line.
Plugin discovery is disabled before importing lexer modules, including for
built-in lexers that delegate embedded languages. The registry supplies both
module and class names; no authored string becomes an import. -/
private def bridge : String := r#"import importlib
import json
import pathlib
import shutil
import sys

try:
    try:
        import pygments
    except ModuleNotFoundError as error:
        if error.name != 'pygments':
            raise
        launcher = shutil.which('latexminted')
        if launcher is None:
            raise SystemExit(3)
        wheels = sorted(pathlib.Path(launcher).resolve().parent.glob('pygments-*.whl'))
        if len(wheels) != 1:
            raise SystemExit(3)
        sys.path.insert(0, str(wheels[0]))
        import pygments
    import pygments.plugin
    pygments.plugin.iter_entry_points = lambda group: ()
    from pygments.lexers._mapping import LEXERS
except Exception:
    raise SystemExit(3)

with open(sys.argv[1], encoding='utf-8') as stream:
    batch = json.load(stream)
if batch['version'] != 1:
    raise SystemExit(2)
max_tokens = int(sys.argv[2])
token_count = 0
answers = []
for request in batch['requests']:
    language, source = request['language'], request['source']
    answer = {'language': language, 'source': source}
    selected = next(((name, entry) for name, entry in LEXERS.items()
                     if language.lower() in entry[2]), None)
    if selected is None:
        answer['error'] = 'unsupported'
    else:
        try:
            name, entry = selected
            lexer = getattr(importlib.import_module(entry[0]), name)(
                stripnl=False, stripall=False, ensurenl=False, tabsize=0)
            tokens = []
            for offset, kind, text in lexer.get_tokens_unprocessed(source + '\n'):
                token_count += 1
                if token_count > max_tokens:
                    raise SystemExit(4)
                tokens.append({'offset': offset, 'kind': str(kind), 'text': text})
            answer['tokens'] = tokens
        except Exception:
            answer['error'] = 'rejected'
    answers.append(answer)
json.dump({'version': 1, 'provider': 'Pygments',
           'providerVersion': pygments.__version__, 'answers': answers},
          sys.stdout, ensure_ascii=True, separators=(',', ':'))
"#

private def diagnostic (request : ListingReply.Request)
    (failure : ListingReply.Failure) : Diag :=
  DriverDiag.listingHighlightUnavailable request.language failure.reason

/-- Unfinished, absent or malformed batches produce no reusable answers.
Every affected request keeps the driver's named loss; completed per-request
refusals instead come from the decoder alongside source-valid plain answers. -/
private def failed (requests : Array ListingReply.Request)
    (failure : ListingReply.Failure) : Array ListingReply.Answer × Array Diag :=
  (#[], requests.map fun request => diagnostic request failure)

/-- Fulfil content-keyed requests through the installed provider — the first
python3 on PATH the OS starts, as execvp chooses it (`ToolPath.probeGo_exact`) —
in one bounded process. Its elapsed time and captured bytes are limited by `RunBounded`; source,
request and token ceilings are shared with the pure protocol validator. An empty
batch starts no tool. No external output becomes diagnostic prose or authored
code, and no answer is returned before exact reconstruction is checked. -/
public def fulfil (_file : String) (requests : Array ListingReply.Request) :
    IO (Array ListingReply.Answer × Array Diag) := do
  if requests.isEmpty then return (#[], #[])
  if !ListingReply.withinBudget requests then return failed requests .budget
  -- Python finds its virtual environment from the invocation spelling, which
  -- each candidate keeps: its PATH entry, anchored, joined to the name.
  let call (python : String) : World.ToolCall :=
    { tool := python
      args := #["-I", "-B", "-c", bridge, "requests.json", toString ListingReply.maxTokens]
      inputs := #[("requests.json", (ListingReply.encode requests).toUTF8)]
      budgetMs := RunBounded.convBudgetMs, graceMs := RunBounded.convGraceMs
      captureLimit := ListingReply.maxReplyBytes }
  let some (_, got) ← Host.runIO (World.ToolPath.probe "python3" call)
    | return failed requests .unavailable
  if !got.complete then
    return failed requests (match got.ran with
      | .unstarted _ => .unavailable
      | _ => .budget)
  match got.ran with
  | .exited 0 =>
    match ListingReply.decode requests got.out (terminalLf := true) with
    | .ok (answers, failures) =>
      return (answers, failures.map fun (request, failure) => diagnostic request failure)
    | .error _ => return failed requests .invalidReply
  | .exited 3 => return failed requests .unavailable
  | .exited 4 | .overran _ => return failed requests .budget
  | .exited _ => return failed requests .rejected
  | .unstarted _ => return failed requests .unavailable

end LeanTex.Cli.ListingHighlight
