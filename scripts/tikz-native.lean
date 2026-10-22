/-
The tikz-native tier: per construct, an invented probe's verdict under `\pictures{ tool = none
}`: 2 drawn with no loss, 1 drawn with a named loss, 0 refused.
Usage: lake build TestsModules && lake env lean --run scripts/tikz-native.lean [--check | --selftest]
-/
import Tests.Support
import scripts.Board
import scripts.TikzProbes

open LeanTex.Core Scoreboard

/-- A probe's verdict (the file header's 0/1/2). -/
def verdict (doc : Ir.Doc) (ds : Array Diag) : Int :=
  let drawn := Elab.enginePictures doc.body > 0 && !(ds.any (·.code == "W0362"))
  let lost := ds.any fun d => d.code == "W0334" || d.code == "E0333" ||
    d.code == "W0012" && !d.subject.any fun s => s.startsWith "math:style:" || s == "ctrl:thanks"
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
