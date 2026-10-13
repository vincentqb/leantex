module

public meta import LeanTex.Core.SeedPalette
public meta import LeanTex.Core.SeedSeries
public meta import LeanTex.Core.CodeExport
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

/-- The flags before the prefix, in any order. -/
private structure Flags where
  blocks : Bool := false
  style : SeedPalette.Blocks := .tonal
  depth : Ir.GroundDepth := .decks
  pygments : Option String := none
  series : Option Nat := none
  check : Option String := none

private meta def flags : Flags → List String → Except String (Flags × List String)
  | f, "--beamer-blocks" :: rest => flags { f with blocks := true } rest
  | f, "--blocks" :: name :: rest =>
    match SeedPalette.Blocks.ofName? name with
    | some b => flags { f with style := b } rest
    | none => .error s!"unknown block style '{name}'; use tonal or strong"
  | f, "--depth" :: "documents" :: rest => flags { f with depth := .documents } rest
  | f, "--depth" :: "decks" :: rest => flags { f with depth := .decks } rest
  | _, "--depth" :: name :: _ => .error s!"unknown depth '{name}'; use documents or decks"
  | f, "--pygments" :: style :: rest => flags { f with pygments := some style } rest
  | f, "--series" :: n :: rest =>
    match n.toNat? with
    | some k =>
      if k == 0 || SeedSeries.maxCount < k then
        .error s!"a series count is a number from 1 to {SeedSeries.maxCount}, not '{n}'"
      else flags { f with series := some k } rest
    | none => .error s!"a series count is a number from 1 to {SeedSeries.maxCount}, not '{n}'"
  | f, "--check" :: path :: rest => flags { f with check := some path } rest
  | f, rest => .ok (f, rest)

/-- Export ordinary TeX colours from three RGB seeds:
`lake env lean --run scripts/palette.lean Prefix INK PAPER ACCENT`.
Use `Prefix --seeds colors.json` to read exactly `ink`, `paper` and `accent`
string fields instead of the three RGB arguments. Flags, before the prefix:
`--beamer-blocks` binds every beamer element the palette writes — the page's
text and ground, the footline, the alert, and the six block elements in the
style `--blocks tonal|strong` names (load the export after the Beamer theme's
initialization);
`--depth documents|decks` picks the class's ground depth (decks by default);
`--pygments STYLE` adds a listing's code colours as the engine derives them
from the generated palette (`CodeExport`), with STYLE's colours where the
palette leaves a role open, and a `\<Prefix>Pygments` command to name in
minted's `formatcom`; `--series N` adds N categorical series colours for a
chart, the colours `<Prefix>Series1` to `<Prefix>SeriesN` (`SeedSeries`), the
first the accent's text tone at the depth; `--check FILE` prints nothing and
exits 1 when FILE
is not what these seeds generate. Only declarations go to stdout, so the
caller can save or compare them. The script never rewrites a document or
changes its permissions. -/
public meta def main (args : List String) : IO UInt32 := do
  let (f, args) ← match flags {} args with
    | .ok r => pure r
    | .error message =>
      IO.eprintln message
      return 2
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
    | IO.eprintln ("usage: palette.lean [--beamer-blocks] [--blocks tonal|strong] " ++
        "[--depth documents|decks] [--pygments STYLE] [--series N] [--check FILE] Prefix " ++
        "(INK PAPER ACCENT | --seeds colors.json)")
      return 2
  if stem.isEmpty || !(stem.toList.all fun c => c.isAlpha && c.toNat < 128) then
    IO.eprintln "palette prefix must contain ASCII letters only"
    return 2
  let some ink := rgb ink | IO.eprintln "invalid ink RGB"; return 2
  let some paper := rgb paper | IO.eprintln "invalid paper RGB"; return 2
  let some accent := rgb accent | IO.eprintln "invalid accent RGB"; return 2
  let seeds : SeedPalette.Seeds := { ink, paper, accent }
  let targets := seeds.targets f.depth
  let palette ← match SeedPalette.generate seeds targets with
    | .ok p => pure p
    | .error failure =>
      IO.eprintln s!"could not derive {(Ir.ColorRef.role failure.role).key}: {failure.detail}; \
use contrasting ink and paper with a distinct accent"
      return 1
  let st : SeedPalette.SeedState := { seeds, targets, blocks := f.style, colors := palette.colors }
  let code ← match f.pygments with
    | none => pure ""
    | some name =>
      let some style := Ir.ListingStyle.ofName? name
        | IO.eprintln s!"unknown highlighting style '{name}'; use default or friendly"
          return 2
      pure (CodeExport.texDeclarations stem (({} : Ir.Palette).applySeeds st) style)
  let series ← match f.series with
    | none => pure ""
    | some n =>
      match SeedSeries.generate seeds targets palette n with
      | .ok g => pure (SeedSeries.declarations stem g.series)
      | .error message =>
        IO.eprintln s!"could not derive the series: {message}"
        return 1
  let out := (if f.blocks then SeedPalette.beamerDeclarations stem st
    else SeedPalette.declarations stem st) ++ code ++ series
  match f.check with
  | some path =>
    let current ← try IO.FS.readFile path catch error =>
      IO.eprintln s!"cannot read '{path}': {error}"
      return 2
    if current == out then return 0
    IO.eprintln s!"'{path}' is not what these seeds generate; regenerate it"
    return 1
  | none =>
    IO.print out
    return 0
