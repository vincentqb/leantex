module

public meta import LeanTex.Core.SeedPalette
public meta import Lean.Data.Json

open LeanTex.Core

private meta def seedArgs (source : String) : Except String (List String) := do
  let value ← Lean.Json.parse source
  unless (← value.getObj?).size == 3 do
    throw "expected exactly three keys: ink, paper, accent"
  return [← value.getObjValAs? String "ink", ← value.getObjValAs? String "paper",
    ← value.getObjValAs? String "accent"]

#guard (seedArgs "{\"accent\":\"FA9D25\",\"paper\":\"FFFFFF\",\"ink\":\"192A3D\"}").toOption ==
  some ["192A3D", "FFFFFF", "FA9D25"]
#guard (seedArgs "{\"ink\":\"192A3D\",\"paper\":\"FFFFFF\"}").toOption == none
#guard (seedArgs "{\"ink\":\"192A3D\",\"paper\":\"FFFFFF\",\"accent\":\"FA9D25\",\"muted\":\"777777\"}").toOption == none
#guard (seedArgs "{\"ink\":\"192A3D\",\"paper\":\"FFFFFF\",\"accent\":42}").toOption == none
#guard (seedArgs "[\"192A3D\",\"FFFFFF\",\"FA9D25\"]").toOption == none

private meta def rgb (value : String) : Option Ir.Color := do
  let spec ← (Decl.parseColorSpec (some "HTML") value).toOption
  Ir.Palette.resolveSpec {} spec

/-- Export ordinary TeX colours from three RGB seeds:
`lake env lean --run scripts/palette.lean Prefix INK PAPER ACCENT`.
Use `Prefix --seeds colors.json` to read exactly `ink`, `paper` and `accent`
string fields instead of the three RGB arguments.
Add `--beamer-blocks` before the prefix for filled block bindings; load
the export after the Beamer theme's initialization.
Only declarations go to stdout, so the caller can save or compare them.
The script never rewrites a document or changes its permissions. -/
public meta def main (args : List String) : IO UInt32 := do
  let (blocks, args) := match args with
    | "--beamer-blocks" :: rest => (true, rest)
    | rest => (false, rest)
  let args ← match args with
    | [stem, "--seeds", path] =>
      try
        match seedArgs (← IO.FS.readFile path) with
        | .ok seeds => pure (stem :: seeds)
        | .error message =>
          IO.eprintln s!"invalid palette seeds in '{path}': {message}"
          return 2
      catch error =>
        IO.eprintln s!"cannot read palette seeds '{path}': {error}"
        return 2
    | _ => pure args
  let [stem, ink, paper, accent] := args
    | IO.eprintln "usage: palette.lean [--beamer-blocks] Prefix (INK PAPER ACCENT | --seeds colors.json)"
      return 2
  if stem.isEmpty || !(stem.toList.all fun c => c.isAlpha && c.toNat < 128) then
    IO.eprintln "palette prefix must contain ASCII letters only"
    return 2
  let some ink := rgb ink | IO.eprintln "invalid ink RGB"; return 2
  let some paper := rgb paper | IO.eprintln "invalid paper RGB"; return 2
  let some accent := rgb accent | IO.eprintln "invalid accent RGB"; return 2
  let seeds : SeedPalette.Seeds := ⟨ink, paper, accent⟩
  let some palette := SeedPalette.generate seeds
    | IO.eprintln "could not derive every role; use contrasting ink and paper with a distinct accent"
      return 1
  IO.print (if blocks then SeedPalette.beamerDeclarations stem seeds palette
    else SeedPalette.declarations stem seeds palette)
  return 0
