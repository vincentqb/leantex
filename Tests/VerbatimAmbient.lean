module

public import Tests.Support

public section

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-! ## The verbatim-ambient invariant

LaTeX's `verbatim` environment selects the normal monospaced family
(`\verbatim@font` is `\normalfont\ttfamily`) and changes **no** size: the
code sets at whatever size is in force where the environment stands. So a
bare `\begin{verbatim}` inherits the ambient font size and leading — the
document base at top level, `\small` inside a `\small` group, restored to
the base once the group closes — and never a fixed `footnotesize`.

The one resolving path is the size-in-force fold `listingBlock` already
uses for `minted`/`lstlisting` (`inherited`, folding `blockDecls`,
defaulting to `normalsize`): bare `verbatim`, `minted`, and `lstlisting`
share that one door. A package's own size option (`basicstyle`,
`fontsize`) stays separate — it overrides the ambient exactly where the
document declares it, and nowhere else.

The invariant, stated over the three surfaces the finding names:

  * **IR** — a bare `verbatim`'s `ListingSpec.fontSize` equals the ambient
    size the surrounding declarations resolve to (the `inherited` fold),
    never the constant `footnotesize`.
  * **Layout.Out** — the shipped code run sets at that ambient size and its
    `leadingFor` leading, in the mono slot (slot 2).
  * **HTML** — the `<pre>` carries the ambient `font-size` (`1.000em` at the
    base, `0.900em` under `\small`) and the mono family.

These checks fail before the fix (every bare verbatim reports
`footnotesize`) and pass after; the `basicstyle`/`fontsize` cases guard
that the package-specific path stays separate. -/

/-- The first verbatim/listing block of an elaborated source, if any. -/
private def firstListingSpec (src : String) : Option Ir.ListingSpec :=
  (elabStr src).1.body.findSome? fun b => match b with
    | .verbatim _ _ spec => some spec
    | _ => none

/-- The first glyph-setting run of a shipped body line whose text carries
`needle`: its face index, set size, and leading. What the ambient-size and
mono-slot claims read off `Layout.Out`. -/
private def runOf (out : Layout.Out) (needle : String) :
    Option (Nat × Dim.Sp × Option Dim.Sp) :=
  (bodyLines out).findSome? fun l =>
    if hasStr (lineText l) needle then
      l.segs.findSome? fun s => match s with
        | .run idx _ _ _ glyphs size metrics _ _ _ _ =>
          if glyphs.isEmpty then none else some (idx, size, metrics.leading)
        | _ => none
    else none

/-- The `style` attribute of the emitted `<pre>` block, if the page ships one. -/
private def preStyleOf (doc : Ir.Doc) : Option String :=
  let page := (HtmlDoc.emit {} doc).1
  match page.splitOn "<pre" with
  | _ :: rest :: _ =>
    match (rest.splitOn "style=\"") with
    | _ :: v :: _ => (v.splitOn "\"").head?
    | _ => none
  | _ => none

def verbatimAmbientChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let load (n : String) : IO (Option Font.Font) := do
    let p := testFonts ++ "/" ++ n
    unless ← System.FilePath.pathExists p do return none
    match Font.parse (← IO.FS.readBinFile p) with
    | .ok f => pure (some f)
    | .error _ => pure none
  -- A set that puts the mono slot (2) in its own face, so a run's face
  -- index says whether it set in the monospaced family.
  let some serif ← load "SourceSerifPro-Regular.otf"
    | failures ref "verbatim ambient: the shipped serif face did not load"
  let some mono ← load "SourceCodePro-Regular.otf"
    | failures ref "verbatim ambient: the shipped mono face did not load"
  let fs : Font.FontSet := {
    fonts := #[serif, mono]
    index := ((List.range 3).flatMap fun slot =>
      let f := if slot == 2 then 1 else 0
      [((slot, 400, false), f), ((slot, 700, false), f),
       ((slot, 400, true), f), ((slot, 700, true), f)]).toArray }
  let geom : Layout.Geom := {}
  let base := geom.fontSize
  let footStep := Ir.scaleStep base "footnotesize"
  let smallStep := Ir.scaleStep base "small"

  -- IR: the ambient size in force reaches the spec, never a fixed footnotesize.
  t "verbatim ambient: a top-level bare verbatim inherits normalsize"
    ((firstListingSpec (dvDoc "" "\\begin{verbatim}\nx\n\\end{verbatim}")).map (·.fontSize)
      == some (Ir.Style.size "normalsize"))
  t "verbatim ambient: a bare verbatim in a \\small group inherits small"
    ((firstListingSpec (dvDoc "" "{\\small\n\\begin{verbatim}\nx\n\\end{verbatim}\n}")).map
      (·.fontSize) == some (.size "small"))
  t "verbatim ambient: a bare verbatim in a \\Large group inherits Large"
    ((firstListingSpec (dvDoc "" "{\\Large\n\\begin{verbatim}\nx\n\\end{verbatim}\n}")).map
      (·.fontSize) == some (.size "Large"))
  t "verbatim ambient: after a \\small group closes, verbatim is back at normalsize"
    ((firstListingSpec (dvDoc "" "{\\small x}\n\\begin{verbatim}\nx\n\\end{verbatim}")).map
      (·.fontSize) == some (.size "normalsize"))
  t "verbatim ambient: a nested \\footnotesize group reaches verbatim as footnotesize"
    ((firstListingSpec
        (dvDoc "" "{\\Large {\\footnotesize\n\\begin{verbatim}\nx\n\\end{verbatim}\n}}")).map
      (·.fontSize) == some (.size "footnotesize"))

  -- Layout.Out: the code run sets at the ambient size and leading, in the mono slot.
  let outBase := layoutOf fs (elabStr
    (dvDoc "" "prose reading.\n\n\\begin{verbatim}\ncodeline\n\\end{verbatim}")).1 geom
  match runOf outBase "codeline", runOf outBase "prose" with
  | some (vIdx, vSize, vLead), some (pIdx, _, _) =>
    t "verbatim ambient: the shipped code sets at the ambient (normalsize) size"
      (vSize == base && vSize != footStep)
    t "verbatim ambient: the shipped code sets on the ambient leading"
      (vLead == some (Ir.leadingFor base geom.leading) &&
        vLead != some (Ir.leadingFor footStep geom.leading))
    t "verbatim ambient: the shipped code sets in the mono slot"
      (vIdx == 1 && pIdx == 0)
  | _, _ => failures ref "verbatim ambient: the code or prose line did not ship"

  let outSmall := layoutOf fs (elabStr
    (dvDoc "" "{\\small\n\\begin{verbatim}\ncodeline\n\\end{verbatim}\n}")).1 geom
  match runOf outSmall "codeline" with
  | some (_, vSize, _) =>
    t "verbatim ambient: a \\small group sets the code at the small step"
      (vSize == smallStep && vSize != footStep)
  | none => failures ref "verbatim ambient: the small-scoped code line did not ship"

  -- HTML: the <pre> carries the ambient font-size, never a forced 0.8em.
  let preBase := preStyleOf (elabStr (dvDoc "" "\\begin{verbatim}\nx\n\\end{verbatim}")).1
  t "verbatim ambient: the HTML pre carries the ambient font-size, not footnotesize"
    ((preBase.map fun s => hasStr s "font-size: 1em;" && !hasStr s "font-size: 0.8em;")
      == some true)
  let preSmall := preStyleOf
    (elabStr (dvDoc "" "{\\small\n\\begin{verbatim}\nx\n\\end{verbatim}\n}")).1
  t "verbatim ambient: a \\small group sets the HTML pre at 0.9em"
    ((preSmall.map fun s => hasStr s "font-size: 0.9em;") == some true)

  -- The package-specific size path stays separate: a declared basicstyle /
  -- fontsize overrides the ambient exactly where it is written, and a bare
  -- listing still inherits.
  t "verbatim ambient: lstlisting basicstyle sets its own size, separate from ambient"
    ((firstListingSpec
        (dvDoc "" "\\begin{lstlisting}[basicstyle=\\ttfamily\\footnotesize]\nx\n\\end{lstlisting}")).map
      (·.fontSize) == some (.size "footnotesize"))
  t "verbatim ambient: minted fontsize sets its own size, separate from ambient"
    ((firstListingSpec
        (dvDoc "" "\\begin{minted}[fontsize=\\small]{text}\nx\n\\end{minted}")).map
      (·.fontSize) == some (.size "small"))
  t "verbatim ambient: a bare lstlisting inherits the ambient size"
    ((firstListingSpec (dvDoc "" "{\\small\n\\begin{lstlisting}\nx\n\\end{lstlisting}\n}")).map
      (·.fontSize) == some (.size "small"))
