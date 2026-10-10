/-
How much of TikZ the engine draws itself, committed as numbers. Run from
the repository root after `lake build TestsModules`:

  lake env lean --run scripts/tikz-native.lean              regenerate the baseline
  lake env lean --run scripts/tikz-native.lean --check      gate against the committed one
  lake env lean --run scripts/tikz-native.lean --selftest   break each verdict once

One item per construct: an invented probe exercising it, elaborated
in-process under the declared refusal (`\pictures{ tool = none }`), so what
the subset draws is all that ships. The value is the probe's verdict:

  2  drawn natively with no loss named;
  1  drawn natively with a named loss (W0334, E0333, W0012);
  0  refused: no engine picture ships, or only the placeholder (W0362).

The spec's 2 also asks that the drawing be structurally equal to its
lualatex reference as the PDF figure reader reads it. That reader has not
landed, so the structural half is not measured yet: when it lands, a probe
whose drawing differs falls from 2, and the fall is the finding. Positions
against lualatex are `scripts/tikz-diff.lean`'s report, never this gate.

Hermetic: the probes are in this file, the faces are the suite's, and no
tool runs.
-/
import Tests.Support
import scripts.Board
import scripts.TikzProbes

open LeanTex.Core Scoreboard

/-- A probe's verdict (the file header's 0/1/2). -/
def verdict (doc : Ir.Doc) (ds : Array Diag) : Int :=
  let drawn := Elab.enginePictures doc.body > 0 && !(ds.any (·.code == "W0362"))
  let lost := ds.any fun d => d.code == "W0334" || d.code == "E0333" || d.code == "W0012"
  if !drawn then 0 else if lost then 1 else 2

def measureTier : IO (Array String × Array Row) := do
  let rows := probes.map fun (item, kind, body) =>
    let (doc, ds) := elabStr (probeDoc kind body)
    ({ item, value := verdict doc ds } : Row)
  let count (v : Int) := (rows.filter (·.value == v)).size
  return (#[s!"# source: {probes.size} invented probes, elaborated in-process under tool = none; \
2 native and lossless {count 2}, 1 native with named losses {count 1}, 0 refused {count 0}; \
the structural half waits on the PDF figure reader"], rows)

def selftest : IO UInt32 := tierSelftest "tikz-native" fun no => do
  let (drawn, _) := elabStr (probeDoc .picture "\\draw (0,0) -- (1,0);")
  let (none', _) := elabStr (probeDoc .picture "")
  let named (c : DiagCode) : Diag := Diag.of c "a probe's loss" none
  no "verdict: an engine picture with no loss named is 2" (verdict drawn #[] == 2)
  no "verdict: a construct outside the subset makes it 1" (verdict drawn #[named .W0334] == 1)
  no "verdict: a document error makes it 1" (verdict drawn #[named .E0333] == 1)
  no "verdict: a formula floor makes it 1" (verdict drawn #[named .W0012] == 1)
  no "verdict: the placeholder is 0" (verdict drawn #[named .W0362] == 0)
  no "verdict: no engine picture is 0" (verdict none' #[] == 0)
  no "verdict: a note is no loss" (verdict drawn #[named .N0376] == 2)
  no "probes: items are unique" ((probes.map (·.1)).toList.eraseDups.length == probes.size)
  no "probes: items are tier item names"
    (probes.all fun (i, _, _) => !i.isEmpty && i.all fun c => c.isLower || c.isDigit || c == '-')

def main (args : List String) : IO UInt32 :=
  tierMain "tikz-native" .raw measureTier selftest args
