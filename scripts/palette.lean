module

public meta import LeanTex.Core.SeedPalette

open LeanTex.Core

private meta def rgb (value : String) : Option Ir.Color := do
  let spec ← (Decl.parseColorSpec (some "HTML") value).toOption
  Ir.Palette.resolveSpec {} spec

/-- Export ordinary TeX colours from three RGB seeds:
`lake env lean --run scripts/palette.lean Prefix INK PAPER ACCENT`.
Add `--beamer-blocks` before the prefix for filled block bindings; load
the export after the Beamer theme's initialization.
Only declarations go to stdout, so the caller can save or compare them.
The script never rewrites a document or changes its permissions. -/
public meta def main (args : List String) : IO UInt32 := do
  let (blocks, args) := match args with
    | "--beamer-blocks" :: rest => (true, rest)
    | rest => (false, rest)
  let [stem, ink, paper, accent] := args
    | IO.eprintln "usage: palette.lean [--beamer-blocks] Prefix INK PAPER ACCENT (six hex digits)"
      return 2
  if stem.isEmpty || !(stem.toList.all fun c => c.isAlpha && c.toNat < 128) then
    IO.eprintln "palette prefix must contain ASCII letters only"
    return 2
  let some ink := rgb ink | IO.eprintln "invalid ink RGB"; return 2
  let some paper := rgb paper | IO.eprintln "invalid paper RGB"; return 2
  let some accent := rgb accent | IO.eprintln "invalid accent RGB"; return 2
  let seeds : SeedPalette.Seeds := ⟨ink, paper, accent⟩
  let some palette := SeedPalette.generate seeds
    | IO.eprintln "could not derive every text and graphic role; choose stronger ink and accent against the paper and pale fills"
      return 1
  IO.print (if blocks then SeedPalette.beamerDeclarations stem seeds palette
    else SeedPalette.declarations stem seeds palette)
  return 0
