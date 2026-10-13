module

public import LeanTex.Core.ListingReply
public import LeanTex.Core.Diag
import LeanTex.Core.LexerName
import LeanTex.Cli.DriverDiag
import LeanTex.Cli.Host
import LeanTex.Cli.RunBounded

/-! The installed Pygments boundary for listing languages no native lexer reads: one
isolated Python process classifies a bounded batch, and its reply is validated whole
before it reaches the IR. -/
namespace LeanTex.Cli.ListingHighlight

open LeanTex.Core

/-- The constant bridge program: isolated Python, built-in registry lexers only, plugin
discovery off, and no import named by a document. -/
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

/-- Whether the driver names a request's loss: a language outside the registry is named by
the elaborator instead. -/
public def driverNamed (request : ListingReply.Request) : Bool :=
  -- premise: Tests.inlineCodeRequestChecks — the elaborator names an unregistered language once
  LexerName.known request.language

/-- A decoded batch as the run keeps it: every answer and the driver's named refusals, but
neither answer nor line for a refused language outside the registry, which the elaborator
names. -/
public def settle (answers : Array ListingReply.Answer)
    (failures : Array (ListingReply.Request × ListingReply.Failure)) :
    Array ListingReply.Answer × Array Diag :=
  let unnamed := (failures.filter (!driverNamed ·.1)).map (·.1)
  (answers.filter (!unnamed.contains ·.request),
    (failures.filter (driverNamed ·.1)).map fun (request, failure) => diagnostic request failure)

/-- A batch that yields no reusable answer: every request keeps the driver's named
loss. -/
private def failed (requests : Array ListingReply.Request)
    (failure : ListingReply.Failure) : Array ListingReply.Answer × Array Diag :=
  (#[], (requests.filter driverNamed).map fun request => diagnostic request failure)

/-- Fulfil content-keyed requests in one bounded run of the first `python3` on PATH; an
empty batch starts no tool, and no answer returns before its reconstruction is checked. -/
public def fulfil (_file : String) (requests : Array ListingReply.Request) :
    IO (Array ListingReply.Answer × Array Diag) := do
  if requests.isEmpty then return (#[], #[])
  if !ListingReply.withinBudget requests then return failed requests .budget
  -- Python finds its virtual environment from the invocation spelling, so each candidate keeps it.
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
    | .ok (answers, failures) => return settle answers failures
    | .error _ => return failed requests .invalidReply
  | .exited 3 => return failed requests .unavailable
  | .exited 4 | .overran _ => return failed requests .budget
  | .exited _ => return failed requests .rejected
  | .unstarted _ => return failed requests .unavailable

end LeanTex.Cli.ListingHighlight
