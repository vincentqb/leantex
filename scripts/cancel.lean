/-
The cancel tier: the oracle's cases within the stated tolerances, its key held to this tree.
Usage: lake build leantex && lake env lean --run scripts/cancel.lean [--check | --selftest]
-/
import scripts.CancelProbe

open Scoreboard CancelProbe

def measureTier : IO (Array String × Array Row) := do
  if !(← System.FilePath.pathExists oraclePath) then
    IO.eprintln s!"scoreboard: {oraclePath} is missing; regenerate it with \
lake env lean --run scripts/cancel-diff.lean"
    return (#[], #[])
  let text ← IO.FS.readFile oraclePath
  let leantex : System.FilePath := ".lake" / "build" / "bin" / "leantex"
  unless ← leantex.pathExists do
    IO.eprintln s!"scoreboard: {leantex} is missing; lake build leantex"
    return (#[], #[])
  let key ← match ← buildKey (← IO.FS.realPath leantex) with
    | .ok k => pure k
    | .error e => IO.eprintln s!"scoreboard: cannot build the cancellation probe: {e}"; return (#[], #[])
  let some recorded := oracleValue text "src-key"
    | IO.eprintln s!"scoreboard: {oraclePath} carries no unique `src-key:` line"; return (#[], #[])
  if recorded != key then
    IO.eprintln s!"scoreboard: {oraclePath} was measured on other output (src-key {recorded}, \
this tree builds {key}); rerun the oracle: lake env lean --run scripts/cancel-diff.lean"
    return (#[], #[])
  let rows := readOracle text
  let mut out : Array Row := #[]
  for (engine, against, tol) in judgements do
    let (pass, n) := judge rows engine against tol
    out := out.push { item := s!"{engine}-vs-{against}.pass", value := pass }
    out := out.push { item := s!"{engine}-vs-{against}.rows", value := n }
  return (#[s!"# source: {oraclePath}; tolerances: pdf {pdfTolerance}, html {htmlTolerance} \
thousandths of an em", s!"# src-key: {key} — this tree's probe, rebuilt and compared on every --check"],
    out)

def selftest : IO UInt32 := tierSelftest "cancel" fun no => do
  let a : Anchors :=
    { left := -10, bottom := 5, right := 20, top := 0, valueX := none, valueY := none }
  let text := s!"tools: invented\nsrc-key: abc\n# a comment\n{renderRow "x-mk" "pdf" a}\n\
{renderRow "x-mk" "lualatex" a}\n"
  no "oracle: the key reads back" (oracleValue text "src-key" == some "abc")
  no "oracle: header lines are not rows" ((readOracle text).size == 2)
  no "oracle: a case agreeing with itself passes" (judge (readOracle text) "pdf" "lualatex" 0 == (1, 1))
  no "oracle: a case missing an engine counts and fails"
    (judge (readOracle text) "chromium" "pdf" 100 == (0, 1))

def main (args : List String) : IO UInt32 :=
  tierMain "cancel" (.pairs "pass" "rows") measureTier selftest args
