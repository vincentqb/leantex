module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests.ElementBoundaries

/-! The space between two elements is the space TeX sets there: each row holds the page to one
difference of two lualatex-measured distances on invented beamer and article probes, so what neither
boundary decides cancels. -/

private def preamble (cls : String) : String :=
  (if cls == "article" then "\\documentclass[10pt]{article}\n\\usepackage{amsmath}\n"
   else "\\documentclass[10pt,aspectratio=169]{beamer}\n\\usetheme{moloch}\n") ++
  "\\usepackage{minted}\n"

/-- The upper element, marked by its first word. -/
private def upper : String → String
  | "para" => "Alpha lead words."
  | "block" => "\\begin{block}{Alpha title}Alpha body words.\\end{block}"
  | "list" => "\\begin{itemize}\n\\item Alpha item words.\n\\end{itemize}"
  | "enum" => "\\begin{enumerate}\n\\item Alpha item words.\n\\end{enumerate}"
  | "centre" => "\\begin{center}\nAlpha centred words.\n\\end{center}"
  | "display" => "Alpha lead words.\n\\[ x = y \\]"
  | "minted" => "\\begin{minted}{text}\nalpha code\n\\end{minted}"
  | _ => "\\begin{verbatim}\nalpha code\n\\end{verbatim}"

/-- The lower element, marked by its first word. -/
private def lower : String → String
  | "para" => "Omega tail words."
  | "list" => "\\begin{itemize}\n\\item Omega item words.\n\\end{itemize}"
  | "enum" => "\\begin{enumerate}\n\\item Omega item words.\n\\end{enumerate}"
  | "centre" => "\\begin{center}\nOmega centred words.\n\\end{center}"
  | "display" => "\\[ \\text{Omega} = z \\]"
  | "minted" => "\\begin{minted}{text}\nomega code\n\\end{minted}"
  | _ => "\\begin{verbatim}\nomega code\n\\end{verbatim}"

/-- A probe's body: the upper element, a blank line, the lower, or the lower opening a block's body
(`bodytop`) or an item's second paragraph (`item`). -/
private def pairBody (x y : String) : String :=
  match x with
  | "bodytop" => "\\begin{block}{Alpha title}\n" ++ lower y ++ "\n\\end{block}"
  | "item" => "\\begin{itemize}\n\\item Alpha item words.\n\n" ++ lower y ++ "\n\\end{itemize}"
  | _ => s!"{upper x}\n\n{lower y}"

private def unit (cls body : String) : String :=
  if cls == "article" then body ++ "\n\\newpage\n"
  else "\\begin{frame}[fragile,t]{F}\n" ++ body ++ "\n\\end{frame}\n"

/-- One measured difference: the probe pair, the pair it is measured against (none: the distance
itself), and lualatex's difference in thousandths of a TeX point. -/
private structure Row where
  cls : String
  pair : String × String
  base : Option (String × String)
  lua : Int

private def opening (cls x y : String) (lua : Int) : Row :=
  { cls, pair := (x, y), base := some (x, "para"), lua }

private def closing (cls x : String) (lua : Int) : Row :=
  { cls, pair := (x, "para"), base := some ("para", "para"), lua }

private def distance (cls x y : String) (lua : Int) : Row :=
  { cls, pair := (x, y), base := none, lua }

/-- lualatex's differences (TeX Live 2026, the probes above). -/
private def measured : List Row :=
  -- beamer's lists: their `\topsep`, 3 pt, on top of whatever stands above.
  (["para", "block", "list", "enum", "centre", "display", "verbatim"].flatMap fun x =>
    [opening "beamer" x "list" 3000, opening "beamer" x "enum" 3000]) ++
  -- A centre: the size file's 8 pt `\topsep`, the larger of it and the space above.
  [opening "beamer" "para" "centre" 8000, opening "beamer" "block" "centre" 5001,
   opening "beamer" "list" "centre" 4999, opening "beamer" "enum" "centre" 4999,
   opening "beamer" "centre" "centre" 0, opening "beamer" "display" "centre" 2000,
   closing "beamer" "centre" 8000,
   opening "article" "list" "centre" 0, opening "article" "enum" "centre" 0,
   distance "article" "para" "list" 22001] ++
  -- A display after an environment and a blank line: the empty line first, as after a paragraph.
  [opening "beamer" "para" "display" 12000, opening "beamer" "list" "display" 11999,
   opening "beamer" "enum" "display" 11999, opening "beamer" "centre" "display" 12001,
   distance "article" "para" "display" 24000, opening "article" "list" "display" 11999,
   opening "article" "enum" "display" 11999] ++
  -- the listings: a trivlist, and fancyvrb's list.
  [opening "beamer" "para" "verbatim" 8000, opening "beamer" "block" "verbatim" 5001,
   opening "beamer" "list" "verbatim" 4999, opening "beamer" "centre" "verbatim" 0,
   opening "beamer" "display" "verbatim" 2000, opening "beamer" "verbatim" "verbatim" 0,
   closing "beamer" "verbatim" 8000,
   opening "beamer" "para" "minted" 3000, opening "beamer" "list" "minted" 0,
   opening "beamer" "verbatim" "minted" 0,
   opening "beamer" "bodytop" "verbatim" 8001, opening "beamer" "bodytop" "minted" 3000,
   opening "beamer" "item" "verbatim" 3001, opening "beamer" "item" "minted" 2000,
   distance "article" "para" "minted" 22000, opening "article" "list" "minted" 0]

/-- Each row's probe, then its base's. -/
private def probes (row : Row) : List (String × String) :=
  row.pair :: row.base.toList

private def frames (cls : String) (rows : List Row) : String :=
  preamble cls ++ "\\begin{document}\n" ++
    String.join (rows.flatMap fun row => (probes row).map fun (x, y) =>
      unit cls (pairBody x y)) ++
    "\\end{document}\n"

/-- A screen length in the sheet's spelling: thousandths of a rem. -/
private def rem (m : Nat) : String :=
  let r := toString (m % 1000)
  s!"{m / 1000}.{"".pushn '0' (3 - min 3 r.length) ++ r}rem"

/-- The browser's half: at the top list level, the last rule a pair of elements meets composes the
upper's space below with the lower's opening as the page does. -/
private def htmlPairChecks (ref : IO.Ref (List String)) : IO Unit := do
  let size := Dim.pt 10
  let rules := HtmlDoc.blockGapRules .beamer size (HtmlDoc.exAt none size) {}
  let bounds := (rules.filterMap fun
    | .boundary sel v => some (cssSelectorParts sel, v)
    | _ => none).toArray
  let top := ":not(li, dd, blockquote) > "
  -- The last rule with a top-level part naming the upper element and, after it, the lower.
  let lastFor (upper lower : String) : Option (Nat × String) :=
    (bounds.zipIdx.toList.filter fun ((parts, _), _) => parts.any fun p =>
      p.startsWith top && match (p.drop top.length).toString.splitOn " + " with
        | [u, l] => hasStr u upper && l.startsWith lower
        | _ => false).getLast?.map fun ((_, v), i) => (i, v)
  let below := rem (HtmlDoc.screenMilli size (Dim.pt 3))
  let opened := rem (HtmlDoc.screenMilli size (Dim.pt 3))
  let above := rem (HtmlDoc.screenMilli size (Dim.pt 6 + Ir.inkClearance))
  let par := "var(--parskip, 0rem)"
  let display := s!"var(--{Ir.displaySkipBelow}"
  let blockU := "section.block"
  let listL := "ul:not(.bibliography)"
  let triv := ".u-trivlist-env"
  let rows : List (String × String × String × (String → Bool)) :=
    [("a list under a block", blockU, s!":is({listL}", (· == s!"calc({below} + {opened} + {par})")),
     ("a list under a list", listL, s!":is({listL}", (· == s!"calc({opened} + {opened} + {par})")),
     ("a list under a centred block", triv, s!":is({listL}", fun v =>
        v.startsWith "calc(var(--topsep" && v.endsWith (" + " ++ opened ++ " + " ++ par ++ ")")),
     ("a list under a display", ".display", s!":is({listL}", fun v =>
        v.startsWith ("calc(" ++ display) && v.endsWith (" + " ++ opened ++ " + " ++ par ++ ")")),
     ("a block under a list", listL, "section.block:not(.block-shaped)", (· == s!"calc({opened} + {above})")),
     ("a block under a centred block", triv, "section.block:not(.block-shaped)", fun v =>
        v.startsWith "calc(var(--topsep" && v.endsWith (" + " ++ above ++ ")")),
     ("a block under a display", ".display", "section.block:not(.block-shaped)", fun v =>
        v.startsWith ("calc(" ++ display) && v.endsWith (" + " ++ above ++ ")")),
     ("a centred block under a block", blockU, triv, fun v =>
        v.startsWith ("calc(max(" ++ below ++ ", var(--topsep") && v.endsWith (") + " ++ par ++ ")")),
     ("a centred block under a list", listL, triv, fun v =>
        v.startsWith ("calc(max(" ++ opened ++ ", var(--topsep") && v.endsWith (") + " ++ par ++ ")")),
     ("a minted under a block", blockU, ".verbatim-list", (· == s!"calc(max({below}, {opened}) + {par})")),
     ("a minted under a centred block", triv, ".verbatim-list", fun v =>
        v.startsWith "calc(max(var(--topsep" && v.endsWith (", " ++ opened ++ ") + " ++ par ++ ")")),
     ("a minted under a display", ".display", ".verbatim-list", fun v =>
        v.startsWith ("calc(max(" ++ display) && v.endsWith (", " ++ opened ++ ") + " ++ par ++ ")")),
     ("a centred block under a display", ".display", triv, fun v =>
        v.startsWith ("calc(max(" ++ display) && v.endsWith (") + " ++ par ++ ")"))]
  -- every generic rule a pair's lower element meets stands before it
  let generic := (bounds.zipIdx.toList.filter fun ((parts, _), _) =>
    parts.any fun p => p == s!"* + {listL}" || p == s!"* + {triv}").map (·.2)
  for (name, upper, lower, ok) in rows do
    match lastFor upper lower with
    | some (i, v) =>
      check ref s!"element boundaries (beamer, browser): {name} composes both spaces, got {v}"
        (ok v && generic.all (· < i))
    | none => check ref s!"element boundaries (beamer, browser): {name} has its pair rule" false
  -- A slide's spacer after its body meets an element's own space below: no paragraph follows.
  for (name, sel) in [("a list", listL), ("a minted", ".verbatim-list"), ("a centred block", triv),
      ("a block", blockU), ("a display", ".display")] do
    let own := bounds.toList.filter fun (parts, _) => parts.any fun p =>
      p.startsWith (sel ++ " + :is(") && p.endsWith ", .fill, section.block-shaped)"
    check ref s!"element boundaries (beamer, browser): the slide's spacer after {name} meets its own space alone"
      (!own.isEmpty && own.all fun (_, v) => !hasStr v "parskip")
  -- A templated block's skips are its padding: the element above meets it on its own space.
  let shapedBounds := (HtmlDoc.blockGapRules .beamer size (HtmlDoc.exAt none size) {} (shaped := true)).filterMap fun
    | .boundary sel v => some (cssSelectorParts sel, v)
    | _ => none
  check ref "element boundaries (beamer, browser): a templated block meets the list above it on the list's own space"
    (shapedBounds.any fun (parts, v) => parts.any (fun p =>
      p.startsWith (listL ++ " + :is(") && p.endsWith "section.block-shaped)") && !hasStr v "parskip")
  -- The centred block's rules stand before the block's, so its pair is the last rule both meet.
  let lastShaped := (shapedBounds.filter fun (parts, _) =>
    parts.any (· == s!"{triv} + section.block-shaped")).getLast?
  check ref "element boundaries (beamer, browser): a templated block meets the centred block above it on its own space"
    ((lastShaped.map fun (_, v) => !hasStr v "parskip" && hasStr v "--topsep").getD false &&
      (shapedBounds.reverse.find? fun (parts, _) => parts.any fun p =>
        p == s!"{triv} + section.block-shaped" || p == "* + section.block-shaped").any fun (parts, _) =>
          parts.any (· == s!"{triv} + section.block-shaped"))
  check ref "element boundaries (beamer, browser): no adding pair reads a templated block"
    (shapedBounds.all fun (parts, _) => parts.all fun p =>
      !(p.startsWith top && hasStr p "section.block" && !hasStr p "section.block:not(.block-shaped)"))
  check ref "element boundaries (article, browser): the article's sheet owes no adding pair"
    ((HtmlDoc.blockGapRules .sizeFile size (HtmlDoc.exAt none size) {}).all fun
      | .boundary sel _ => !hasStr sel top
      | _ => true)

/-- A listing framed as a trivlist leaves `\@endpe`, so a display right after it opens on no empty
line. -/
private def framedEndPeChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let verbatim := "\\begin{verbatim}\nalpha code\n\\end{verbatim}"
  let display := "\\[ \\text{Omega} = z \\]"
  for cls in ["article", "resume", "webpage", "poster"] do
    let spanOf (sep : String) : Option Dim.Length :=
      let src := s!"\\documentclass\{{cls}}\n\\begin\{document}\n" ++ verbatim ++ sep ++ display ++
        "\n\\end{document}\n"
      let (doc, _) := Elab.run s!"element-boundaries-endpe-{cls}.tex" src
      ((Layout.run (Layout.Geom.ofPage doc.page) fonts none doc).pages[0]?).bind probeSpan
    check ref s!"element boundaries ({cls}): a display right after a framed verbatim opens on no empty line"
      (match spanOf "\n", spanOf "\n\n" with
       | some tight, some blank => tight < blank
       | _, _ => false)

def elementBoundaryChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  for cls in ["beamer", "article"] do
    let rows := measured.filter (·.cls == cls)
    if rows.isEmpty then continue
    let (doc, _) := Elab.run s!"element-boundaries-{cls}.tex" (frames cls rows)
    let pages := (Layout.run (Layout.Geom.ofPage doc.page) fonts none doc).pages
    check ref s!"element boundaries ({cls}): one page per probe"
      (pages.size == (rows.map (probes · |>.length)).sum)
    let mut idx := 0
    for row in rows do
      let (x, y) := row.pair
      let d := pages[idx]?.bind probeSpan
      let b : Option Dim.Length := if row.base.isSome then pages[idx + 1]?.bind probeSpan else some 0
      idx := idx + (probes row).length
      let against := match row.base with
        | some (bx, bz) => s!" beyond a {bz} under a {bx}"
        | none => ""
      match d, b with
      | some d, some b =>
        check ref s!"element boundaries ({cls}): a {y} under a {x} stands {row.lua}{against} (lualatex), got {spMilli (d - b)}"
          ((spMilli (d - b) - row.lua).natAbs ≤ probeTolerance.toNat)
      | _, _ => check ref s!"element boundaries ({cls}): the {x}/{y} probe ships its marks" false
  htmlPairChecks ref
  framedEndPeChecks ref fonts

end Tests.ElementBoundaries
