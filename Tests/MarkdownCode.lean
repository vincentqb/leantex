module

public import Tests.Support

public section

open LeanTex.Core

/-! **Code on paper: every character reaches the page.**

A markdown document can declare no listing keys, and its code set at the
body size in a measure-wide face ran past the page edge: hundreds of lines
of a long generated report lost their ends. A markdown fence now sets as
its surface sets code (`Ir.Surface.listing`) — `\footnotesize`, wrapping —
and wraps whitespace first: at the last space that fits, else at the last
fallback-token boundary that is a boundary of the highlighter's type runs,
a run wider than a line parted between its fallback tokens, so `:=`, `->`,
a hex byte and an identifier stay whole. A tex listing that declares
`breaklines` wraps at listings' own units, each line filled to the last that
fits, as a LuaLaTeX probe of listings fills it but for the white space a
wrap falls before, which listings carries onto the continuation and the
engine drops. Each continuation stands 20 pt past its own line's indentation
(`breakindent`, `breakautoindent`), so every declared line holds. The
invariants are over `Layout.Out` (where each line's first glyph stands,
what each line holds, that each fits) and over the IR's listing values the
two artifacts read. Every word here is invented. -/

namespace Tests.MarkdownCode

/-- The first listing a document's top-level body holds. -/
def firstListing (doc : Ir.Doc) : Option Ir.ListingSpec :=
  doc.body.findSome? fun b => match b with
    | .verbatim _ _ spec => some spec
    | _ => none

/-- Where a character first stands on a shipped line, walking every
segment's advance. -/
def glyphX (l : Layout.LineOut) (wanted : Char) : Option Dim.Sp := Id.run do
  let mut x := l.x
  for s in l.segs do
    match s with
    | .run _ _ _ w glyphs _ _ _ _ _ _ =>
      let mut pen := x
      for (_, c, advance) in glyphs do
        if c == wanted then return some pen
        pen := pen + advance
      x := x + w
    | .gap w _ | .decoratedGap w _ _ | .decoration _ w _ _ _
    | .rule w _ _ _ | .image _ w _ => x := x + w
    | .poly _ _ => pure ()
  return none

/-- Where a shipped line's first glyph other than a space stands. -/
def firstGlyphX (l : Layout.LineOut) : Option Dim.Sp := Id.run do
  let mut x := l.x
  for s in l.segs do
    match s with
    | .run _ _ _ w glyphs _ _ _ _ _ _ =>
      let mut pen := x
      for (_, c, advance) in glyphs do
        if c != '\u00a0' && c != ' ' then return some pen
        pen := pen + advance
      x := x + w
    | .gap w _ | .decoratedGap w _ _ | .decoration _ w _ _ _
    | .rule w _ _ _ | .image _ w _ => x := x + w
    | .poly _ _ => pure ()
  return none

/-- A line's text with every space and no-break space removed. -/
def bare (s : String) : String := (s.replace "\u00a0" "").replace " " ""

/-- **Inline code breaks where url.sty's `\path` breaks.** A markdown
document's code cannot declare a break, and set unbreakable in a justified
paragraph it ran past the page edge or opened gaps of hundreds of points
around itself. Its typewriter runs now end a line after url.sty's break
characters (`. @ \ / ! _ | ; > ] ) , ? & ' + = #` at `\binoppenalty`, `:`
at `\relpenalty`), never after a hyphen, never inside a run of letters or
digits and never drawing one, and only where a line needs it — the
penalties outbid any ordinary line. A tex document's `\texttt` keeps LaTeX's rule: it never
breaks, and an identifier wider than the line is TeX's overfull box. The
invariants are over `Layout.Out`. Every word here is invented. -/
def inlineCodeChecks (ref : IO.Ref (List String)) (text : Font.Font)
    (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let codes := ["alpha_beta_gamma_delta_epsilon_zeta_eta_theta_iota_kappa_lambda_mu",
    "Nu.xi_omicron.pi_rho.sigma_tau", "upsilon_phi.chi_psi_omega_alpha_beta_gamma_delta_epsilon",
    "zeta/eta/theta/iota/kappa/lambda/mu/nu/xi/omicron"]
  let words := ["the", "sorter", "reads", "every", "gadget", "and", "writes", "it", "back", "to",
    "a", "store", "where", "each", "label", "waits", "for", "its", "turn"]
  let prose (code : String → String) : String := String.intercalate " "
    ((List.range 60).map fun k =>
      if k % 7 == 3 then code (codes[(k / 7) % codes.length]!)
      else words[(k * 5) % words.length]!)
  let size := Dim.pt 10
  let space : Dim.Sp := size * text.spaceAdvance / text.unitsPerEm
  let md := prose fun c => "`" ++ c ++ "`"
  let doc := (elabMd (md ++ "\n")).1
  let out := layoutOf fonts doc
  let lines := bodyLines out
  let left := doc.page.hmargin
  let measure := doc.page.width - 2 * doc.page.hmargin
  -- A boundary glyph may hang into the margin (character protrusion), a
  -- few points at most; an overfull line runs tens of points past it.
  t s!"markdown inline code: every line fits the measure and none is overfull ({lines.size})"
    (lines.size ≥ 6 && lines.all (fun l => left - Dim.pt 3 ≤ l.x
        && l.x + l.setWidth ≤ left + measure + Dim.pt 3)
      && !out.diags.any (·.kind == .W0005))
  -- A line whose last run is code that no identifier ends with broke
  -- inside the identifier.
  let midCode (out : Layout.Out) : Array String := (bodyLines out).filterMap fun l =>
    (lineRuns l).back?.bind fun (f, s, _, _) =>
      if f == 1 && !codes.any (·.endsWith s) then some s else none
  let breakChars := ".@\\/!_|;>]),?&'+=#:-"
  t s!"markdown inline code: a line ends inside code only after a break character, drawing no hyphen ({midCode out})"
    (!(midCode out).isEmpty && (midCode out).all fun s => breakChars.contains s.back)
  t "markdown inline code: every character reaches the page, in order"
    (String.join (lines.toList.map (bare ∘ lineText)) == bare (md.replace "`" ""))
  t "markdown inline code: no justified line opens a word space three of its own wide"
    (lines.all fun l => l.segs.all fun s => match s with
      | .gap w _ => w ≤ 3 * space
      | _ => true)
  -- A kebab-case flag longer than the measure breaks after its hyphens,
  -- as url.sty's `hyphens` option and every browser break it: without a
  -- break of its own the justified paragraph around it had none either.
  let flag := "--rewrite-every-gadget-label-before-counting-them-and-writing-each-one-back-to-its-store"
  let kebab := "The sorter takes " ++ "`" ++ flag ++ "`" ++ " and " ++ "`" ++ flag ++ "`" ++
    " before it reads every gadget it is handed and writes each one back."
  let kdoc := (elabMd (kebab ++ "\n")).1
  let kout := layoutOf fonts kdoc
  let klines := bodyLines kout
  t s!"markdown inline code: a kebab-case flag wider than the measure breaks after its hyphens ({klines.size} lines)"
    (klines.size ≥ 3 && klines.all (fun l => left - Dim.pt 3 ≤ l.x
        && l.x + l.setWidth ≤ left + measure + Dim.pt 3)
      && !kout.diags.any (·.kind == .W0005)
      && String.join (klines.toList.map (bare ∘ lineText)) == bare (kebab.replace "`" ""))
  -- A paragraph with long unbreakable runs ships every character on the
  -- paper: the breaker once packed the text between two such runs onto
  -- one overfull line past the sheet to save a loose line.
  let glued := ["orderregistryvaluefactorysearchlimitxx", "policywidgetfactorysearchproxyxx",
    "valueregistryfactorytokenproxytallyxx"]
  let filler := "with now them and must if years after may has even many can made back her each"
  let gluedProse (code : String → String) : String := "Or with her that because of if our you " ++
    code glued[0]! ++ " if make for two may " ++ filler ++ " " ++ code glued[1]! ++ " " ++
    code glued[2]! ++ " or your man than well even for the back well you have such so."
  for (label, src, isMd) in [
      ("tex typewriter", gluedProse fun c => "\\texttt{" ++ c ++ "}", false),
      ("tex url", gluedProse fun c => "\\url{https://example.org/" ++ c ++ "/index.html}", false),
      ("markdown code", gluedProse fun c => "`" ++ c ++ "`", true)] do
    let gdoc := if isMd then (elabMd (src ++ "\n")).1 else (elabStr (dvDoc "" src)).1
    let gout := layoutOf fonts gdoc
    let glines := (bodyLines gout).filter hasGlyphRun
    let shipped := String.join (glines.toList.map (bare ∘ lineText))
    let want := bare ((((src.replace "\\texttt{" "").replace "\\url{" "").replace "}" "").replace "`" "")
    t s!"a paragraph with long unbreakable runs ships every character on the paper ({label})"
      (!glines.isEmpty && glines.all (fun l => 0 ≤ l.x && l.x + l.setWidth ≤ gdoc.page.width)
        && shipped == want)
  -- A tex document's typewriter run keeps LaTeX's rule.
  let tex := prose fun c => "\\texttt{" ++ c.replace "_" "\\_" ++ "}"
  let texOut := layoutOf fonts (elabStr (dvDoc "" tex)).1
  t s!"tex inline code: a typewriter run never breaks, and one wider than the line is overfull ({midCode texOut})"
    ((midCode texOut).isEmpty && texOut.diags.any (·.kind == .W0005))
  -- The screen: a browser breaks an inline identifier only where it would
  -- push the page sideways.
  let codeRule := ":where(:not(pre) > code) { overflow-wrap: break-word; }"
  t "a markdown page's stylesheet lets inline code break where it would overflow; a tex page's keeps it whole"
    (hasStr (HtmlDoc.baseCss {} doc) codeRule
      && !hasStr (HtmlDoc.baseCss {} (elabStr (dvDoc "" tex)).1) codeRule)

/-- The fallback lexer's class of a character: 0 a space, 1 a word
character, 2 an operator character, 3 any other, a token of its own — the
classes the layout's fallback lexer reads. A shipped code line spells its
spaces as no-break spaces, read here as spaces. -/
def fallbackClass (c : Char) : Nat :=
  if c == ' ' || c == '\t' || c == '\u00a0' then 0
  else if c.isAlphanum || c == '_' || c == '\'' || c.toNat > 127 then 1
  else if "!#$%&*+-./:<=>?@\\^|~".contains c then 2
  else 3

/-- The wraps of `lines`, read off `code` they ship, that fall inside one
fallback token of the source: between two of its characters with no space
between them in the source, of one class that runs on (word or operator). -/
def dividedTokens (code : String) (lines : Array String) : Array String := Id.run do
  let src := code.toList.toArray
  -- the source index of each character a shipped line holds
  let mut at_ : Array Nat := #[]
  for i in [0:src.size] do
    if fallbackClass (src[i]?.getD ' ') != 0 then at_ := at_.push i
  let mut out : Array String := #[]
  let mut k := 0
  for l in lines.pop do
    k := k + (bare l).length
    match at_[k - 1]?, at_[k]? with
    | some i, some j =>
      let a := src[i]?.getD ' '
      let b := src[j]?.getD ' '
      if j == i + 1 && fallbackClass a == fallbackClass b && fallbackClass a ≤ 2 then
        out := out.push (String.ofList [a, b])
    | _, _ => pure ()
  return out

/-- The fallback lexer's tokens of a line (spaces dropped): a run of word
characters, a run of operator characters, and any other character alone. -/
def fallbackTokens (s : String) : Array String := Id.run do
  let cls := fallbackClass
  let mut out : Array String := #[]
  let mut cur := ""
  let mut prev := 0
  for c in s.toList do
    let k := cls c
    if k == 0 then
      unless cur.isEmpty do out := out.push cur
      cur := ""
    else if cur.isEmpty || (k == prev && k != 3) then cur := cur.push c
    else
      out := out.push cur
      cur := String.singleton c
    prev := k
  unless cur.isEmpty do out := out.push cur
  return out

/-- **Overfull only where one fallback token is wider than its room.** A
shipped code line runs past the measure only when a fallback token on it is
wider than the room from its first glyph to the measure's edge, `cell` the
typewriter advance. -/
def overrunExplained (left measure cell : Dim.Sp) (l : Layout.LineOut) : Bool :=
  l.x + l.setWidth ≤ left + measure ||
    match firstGlyphX l with
    | some x => (fallbackTokens (lineText l)).any fun t => t.length * cell > left + measure - x
    | none => false

/-- **A code line wraps where its lexer separates tokens, whitespace first.**
A wrapped Lean line split `:=` across two lines (`… :` above `= by`): the
wrap fell between two output units of one operator. Swept so that each
operator stands at every column across the measure's end, in a Lean, a
Python and a plain fence, after a space and inside a run wider than the
line: no two consecutive shipped lines of one source line divide `:=`,
`->`, `==`, `<=`, `**`, `!=`, `::` or `=>`, every character ships in order,
and every line fits. A URL in a comment, a path in a string, a formatted
string and a console line wrap inside their tokens rather than run past the
measure, overfull only where one fallback token is wider than the line. A
line whose last fitting space stands before a run wider than the line breaks
at the space, and the run only then at its tokens. A tex listing that
declares `breaklines` breaks as listings does: a LuaLaTeX probe of the same
invented lines at the same measure and advance sets each line at the units
these assertions name. Every word here is invented. -/
def codeTokenWrapChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let linesOf := codeFenceLines fonts
  let doc := (elabMd "```\nx\n```\n").1
  let left := doc.page.hmargin
  let measure := doc.page.width - 2 * doc.page.hmargin
  let some mono := fonts.fonts[1]? | t "code wraps: the typewriter face loads" false
  let cell := Dim.pt 8 * mono.spaceAdvance / mono.unitsPerEm
  let ops := [":=", "->", "==", "<=", "**", "!=", "::", "=>"]
  let divides (a b : String) : Option String :=
    ops.find? fun op => (List.range (op.length - 1)).any fun k =>
      a.endsWith (String.ofList (op.toList.take (k + 1))) &&
        b.startsWith (String.ofList (op.toList.drop (k + 1)))
  let judge (label : String) (code : String) (ls : Array Layout.LineOut) : Array String := Id.run do
    let mut found : Array String := #[]
    for (a, b) in ls.zip (ls.extract 1 ls.size) do
      if let some op' := divides (bare (lineText a)) (bare (lineText b)) then
        found := found.push s!"{label}: {op'} divided"
    unless String.join (ls.toList.map (bare ∘ lineText)) == bare code do
      found := found.push s!"{label}: lost text"
    let parted := dividedTokens code (ls.map lineText)
    unless parted.isEmpty do
      found := found.push s!"{label}: a fallback token parted at {parted}"
    unless ls.all (overrunExplained left measure cell) do
      found := found.push s!"{label}: overfull past its tokens"
    return found
  let pairs := [("lean", ":=", " by exact rfl"), ("lean", "->", " Gadget"),
      ("lean", "::", " rest"), ("lean", "=>", " widget"), ("python", "==", " beta:"),
      ("python", "**", " 2"), ("python", "!=", " gamma"), ("python", "->", " int:"),
      ("python", "<=", " delta"), ("", ":=", " value"), ("", "==", " other")]
  let mut offences : Array String := #[]
  let mut swept := 0
  let mut unspaced := 0
  for (lang, op, tail) in pairs do
    for k in [0:24] do
      let words := String.intercalate " " (List.replicate 20 "wwwwwww")
      let head := (String.ofList (words.toList.take (60 + k))).trimAsciiEnd.toString
      let code := head ++ " " ++ op ++ tail
      let ls := linesOf lang code
      if ls.size ≥ 2 then swept := swept + 1
      offences := offences ++ judge s!"{lang}:{op}@{k}" code ls
      unless ls.all (·.setWidth ≤ measure) do
        offences := offences.push s!"{lang}:{op}@{k} overfull"
      -- The same operator inside one run wider than the line, no space
      -- near it: only a token break can take the wrap.
      let chain := String.intercalate "." ((List.range 40).map fun i => "".pushn 'z' (2 + i % 3))
      let glued := String.ofList (chain.toList.take (70 + k)) ++ op ++ "y.yy.yyy"
      let gs := linesOf lang ("value = " ++ glued)
      if gs.size ≥ 2 then unspaced := unspaced + 1
      offences := offences ++ judge s!"{lang}:{op}@{k} unspaced" ("value = " ++ glued) gs
  t s!"code wraps: no wrap divides an operator, every character ships, every line fits ({offences})"
    offences.isEmpty
  t s!"code wraps: the sweeps wrap their lines ({swept}, {unspaced})"
    (swept ≥ 130 && unspaced == 24 * pairs.length)
  -- A Lean line with an order relation: each glyph ships, whole, in order.
  let rel := "theorem gadget_le_widget (n m : Nat) (h : n ≤ m) (k : Nat) (hk : m ≤ k) : n ≤ k + 0 := Nat.le_trans h hk"
  let relLines := linesOf "lean" rel
  t s!"code wraps: a Lean line holding ≤ wraps and ships whole ({relLines.size} lines)"
    (relLines.size ≥ 2 && (judge "lean ≤" rel relLines).isEmpty)
  -- Long tokens: a typed comment, string or console line wider than the
  -- line parts between its fallback tokens rather than run past the page.
  let url := "https://example.org/some/rather/long/path/segments/that/never/end/and/keep/going/on/forever.html"
  let path := "/var/lib/example/aaaaaaaa/bbbbbbbbbb/cccccccccc/dddddddddd/eeeeeeeeee/ffffffffff/gggg.txt"
  let long := [("python", "# see " ++ url), ("python", "x = \"" ++ url ++ "\""),
    ("python", "open(\"" ++ path ++ "\")"),
    ("python", "label = f\"" ++ "".pushn 'a' 50 ++ "{name}" ++ "".pushn 'b' 40 ++ "\""),
    ("python", "message = (\"the-quick-brown-fox-jumps-over-the-lazy-dog-and-keeps-running-far-away\")"),
    ("lean", "-- see " ++ url), ("lean", "def url : String := \"" ++ url ++ "\""),
    ("rust", "let url = \"" ++ url ++ "\";"), ("console", "$ cat " ++ path),
    ("", "see " ++ url)]
  let mut longOffences : Array String := #[]
  for (lang, code) in long do
    let ls := linesOf lang code
    longOffences := longOffences ++ judge s!"{lang}: {code.take 12}" code ls
    unless ls.size ≥ 2 do longOffences := longOffences.push s!"{lang}: {code.take 12} did not wrap"
  t s!"code wraps: a long comment, string or console line parts inside its tokens, never past the page ({longOffences})"
    longOffences.isEmpty
  -- Literals a highlighter splits into several runs stay whole: a hex byte,
  -- a numeral with underscores, a character literal, each one fallback
  -- token however its runs fall, at every phase across the measure's end.
  let hex := String.intercalate "," ((List.range 40).map fun i =>
    "0x" ++ String.ofList ["0123456789abcdef".toList[i / 16 % 16]!, "0123456789abcdef".toList[i % 16]!])
  let nums := String.intercalate " + " ((List.range 12).map fun i => s!"{i + 1}_000_000_{i}00")
  let chars := String.intercalate "," ((List.range 30).map fun i =>
    "'" ++ String.singleton (Char.ofNat (97 + i % 26)) ++ "'")
  let mut literalOffences : Array String := #[]
  for phase in [0:10] do
    let pad := "".pushn 'v' phase
    for (lang, code) in [("lean", s!"def {pad}table : Array UInt8 := #[{hex}]"),
        ("lean", s!"def {pad}big : Nat := {nums}"), ("lean", s!"def {pad}cs : List Char := [{chars}]"),
        ("python", s!"{pad}table = [{hex}]"), ("", s!"{pad}{nums}")] do
      literalOffences := literalOffences ++ judge s!"{lang} literal @{phase}" code (linesOf lang code)
  t s!"code wraps: a literal the highlighter splits into runs never parts ({literalOffences})"
    literalOffences.isEmpty
  -- Whitespace first: the run after the last fitting space is wider than a
  -- line, so the wrap takes the space and the run breaks only at its dots.
  let chain := String.intercalate "." ((List.range 24).map fun i => "".pushn 'z' (2 + i % 3))
  for lang in ["python", ""] do
    let ls := linesOf lang ("value = " ++ chain)
    t s!"code wraps ({lang}): the last fitting space wins over a later token break \
({ls.map lineText})"
      (ls.size ≥ 3 && (ls[0]?.map (bare ∘ lineText)) == some "value=" &&
        String.join (ls.toList.map (bare ∘ lineText)) == bare ("value = " ++ chain) &&
        ls.all (·.setWidth ≤ measure))
  -- A tex listing keeps listings' units, each line filled: the lines a
  -- LuaLaTeX probe of listings set from the same source at 300 pt in this
  -- 0.6 em face at `\footnotesize`, its spaces dropped.
  let probe : List (String × List String) := [
    ("value = " ++ chain,
      ["value=zz.zzz.zzzz.zz.zzz.zzzz.zz.zzz.zzzz.zz.zzz.zzzz.zz.zzz",
       ".zzzz.zz.zzz.zzzz.zz.zzz.zzzz.zz.zzz.zzzz"]),
    ("x = \"https://example.org/some/rather/long/path/segments/that/never/end/and/keep/going/on.html\"",
      ["x=\"https://example.org/some/rather/long/path/segments/that/",
       "never/end/and/keep/going/on.html\""]),
    ("f(" ++ String.intercalate "," ((List.range 30).map fun k => s!"arg{k}") ++ ")",
      ["f(arg0,arg1,arg2,arg3,arg4,arg5,arg6,arg7,arg8,arg9,arg10,",
       "arg11,arg12,arg13,arg14,arg15,arg16,arg17,arg18,arg19,",
       "arg20,arg21,arg22,arg23,arg24,arg25,arg26,arg27,arg28,", "arg29)"]),
    ("total = 1234567890.1234567890 + 9876543210.98765 * 31415926535.8979 - 2718281828.459045 / 7",
      ["total=1234567890.1234567890+9876543210.98765*", "31415926535.8979-2718281828.459045/7"]),
    ("abc123def456ghi789 = jkl012mno345pqr678(stu901vwx234yz) + aaa111bbb222ccc333ddd444eee555fff",
      ["abc123def456ghi789=jkl012mno345pqr678(stu901vwx234yz)+", "aaa111bbb222ccc333ddd444eee555fff"]),
    ("gadget(widget(sprocket(flange(bracket(lever(spindle(axle(wheel(rim(spoke(hub(nut))))))))))))):=x",
      ["gadget(widget(sprocket(flange(bracket(lever(spindle(axle(wheel", "(rim(spoke(hub(nut))))))))))))):=x"]),
    ("".pushn 'w' 71 ++ "->" ++ "".pushn 'v' 20, ["".pushn 'w' 71, "->" ++ "".pushn 'v' 20]),
    ("a.b.c.d.e.f.g.h.i.j.k.l.m.n.o.p.q.r.s.t.u.v.w.x.y.z.a.b.c.d.e.f.g.h.i.j.k.l.m.n.o.p.q.r.s.t.u.v",
      ["a.b.c.d.e.f.g.h.i.j.k.l.m.n.o.p.q.r.s.t.u.v.w.x.y.z.a.b.c.d.e.", "f.g.h.i.j.k.l.m.n.o.p.q.r.s.t.u.v"]),
    ("x = [" ++ String.intercalate ", " ((List.range 25).map fun k => toString (k + 1)) ++ "]",
      ["x=[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,", "17,18,19,20,21,22,23,24,25]"]),
    ("f(x)(y)" ++ "".pushn 'z' 50 ++ "a)b1)2+)-))" ++ "".pushn 'q' 10,
      ["f(x)(y)" ++ "".pushn 'z' 50 ++ "a)b1)", "2+)-))" ++ "".pushn 'q' 10])]
  let lst := String.intercalate "\n" (probe.map (·.1))
  let texDoc := (elabStr (dvDoc "" ("\\noindent\\begin{minipage}{300pt}\n\\begin{lstlisting}" ++
    "[breaklines=true,basicstyle=\\ttfamily\\footnotesize]\n" ++ lst ++
    "\n\\end{lstlisting}\n\\end{minipage}"))).1
  let texLines := (bodyLines (layoutOf fonts texDoc)).map (bare ∘ lineText)
  let want := (probe.flatMap (·.2)).toArray
  t s!"tex listing: breaklines fills each line to listings' last unit that fits, as LuaLaTeX sets it \
({(texLines.zip want).filter (fun (a, b) => a != b)})"
    (texLines == want)
  -- The declared departure: listings carries the white space a wrap falls
  -- before onto the continuation — a space one column past the break
  -- indent, a tab its six, which the probe sets moving the next unit a line
  -- further — and the engine drops it, so every continuation stands at its
  -- declared indent.
  let carried := ("".pushn 'a' 62 ++ " " ++ "".pushn 'b' 58 ++ " c") ++ "\n" ++
    ("".pushn 'a' 58 ++ "\t" ++ "".pushn 'b' 50 ++ " cccc")
  let carryDoc := (elabStr (dvDoc "" ("\\noindent\\begin{minipage}{300pt}\n\\begin{lstlisting}" ++
    "[breaklines=true,basicstyle=\\ttfamily\\footnotesize]\n" ++ carried ++
    "\n\\end{lstlisting}\n\\end{minipage}"))).1
  let carryLines := bodyLines (layoutOf fonts carryDoc)
  let x0 := carryLines[0]?.bind firstGlyphX
  t s!"tex listing: the white space a wrap falls before is dropped, every continuation at its indent \
({carryLines.map (bare ∘ lineText)})"
    (carryLines.map (bare ∘ lineText) ==
        #["".pushn 'a' 62, "".pushn 'b' 58, "c", "".pushn 'a' 58, "".pushn 'b' 50 ++ "cccc"] &&
      [1, 2, 4].all fun k => (carryLines[k]?.bind firstGlyphX) == x0.map (· + Ir.listingBreakIndent))

mutual

/-- The atoms a code tree holds on one line (`HtmlDoc.codeTokClass`), in
order, by their text, and how many `<wbr>` it carries. -/
def heldAtomsOne (acc : Array String × Nat) : Html.Node → Array String × Nat
  | .elem "span" #[("class", c)] kids =>
    if c == HtmlDoc.codeTokClass then (acc.1.push (nodeTextList "" kids.toList), acc.2)
    else heldAtomsList acc kids.toList
  | .elem "wbr" _ _ => (acc.1, acc.2 + 1)
  | .elem _ _ kids => heldAtomsList acc kids.toList
  | .text _ | .style _ | .script _ _ => acc

def heldAtomsList (acc : Array String × Nat) : List Html.Node → Array String × Nat
  | [] => acc
  | k :: rest => heldAtomsList (heldAtomsOne acc k) rest

end

/-- The code elements of a document's HTML body, each its text and what it
holds (`heldAtomsOne`). -/
def codeAtomsOf (doc : Ir.Doc) : Array (String × Array String × Nat) :=
  (elemNodesList (· == "code") #[] (docNodesOf doc).toList).filterMap fun n =>
    match n with
    | .elem _ _ kids => some (nodeTextList "" kids.toList, heldAtomsList (#[], 0) kids.toList)
    | _ => none

/-- **The web page wraps a code line where the page may.** A code block's
line holds on one line every atom the page's wrap may not break inside
(`Listing.codeMarks`): under whitespace first each fallback token of two
characters or more — `:=`, `->`, `==`, a path's `://`, an identifier — in a
`tok` element the stylesheet sets `nowrap`, and the block's own wrap
declaration lets a browser part a run wider than its line only between them
(`overflow-wrap`); under listings' rule each unit of two characters or more,
and a `<wbr>` between two units, where listings may break. The code's text
is the source's, character for character, and inline code is untouched.
Read off the typed HTML tree, against the fallback lexer the layout's
checks read (`fallbackTokens`); the browser's own wraps are the oracle's
`code-wrap` row. Every word here is invented. -/
def htmlCodeAtomChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let lines := [
    "theorem add_zero_right (n : Nat) : n + 0 = n := by simp  -- every n",
    "def route : String → String := fun path => path ++ \"/usr/local/share/a/file.txt\"",
    "example : (1 : Nat) ≤ 2 ∧ 2 ≤ 3 := ⟨by decide, by decide⟩",
    "def handler(event, context) -> dict:",
    "    return fetch(\"https://example.org/some/path?q=1&r=2\") == expected",
    "alpha_beta->gamma_delta->epsilon_zeta==eta_theta<=iota"]
  for (lang, label) in [("", "plain"), ("python", "python"), ("lean", "lean")] do
    for line in lines do
      let (doc, _) := elabMd s!"```{lang}\n{line}\n```\n"
      match codeAtomsOf doc with
      | #[(text, held, wbrs)] =>
        t s!"{label} code holds each fallback token of its line on one line ({repr line}: {held})"
          (text == line && wbrs == 0 && held == (fallbackTokens line).filter (·.length ≥ 2)
            && held.all fun a => !a.any (· == ' '))
      | other => t s!"{label} code is one code element ({other.size})" false
  -- Listings' rule: its units held, a `<wbr>` between two.
  for (line, units, wbrs) in [("x:=y->z", #[":=", "->"], 4),
      ("f(a1)=b2", #["a1", "b2"], 5), ("p ->q", #["->"], 1)] do
    let (doc, _) := elabStr (dvDoc "\\usepackage{listings}\n"
      s!"\\begin\{lstlisting}[breaklines=true]\n{line}\n\\end\{lstlisting}")
    match codeAtomsOf doc with
    | #[(text, held, w)] =>
      t s!"a breaking lstlisting holds its units and parts them as listings may ({repr line}: {held}, {w})"
        (text == line && held == units && w == wbrs)
    | other => t s!"a breaking lstlisting is one code element ({other.size})" false
  -- The declarations a browser reads.
  let (doc, _) := elabMd "```\na->b\n```\n\nInline `c->d` code.\n"
  let css := HtmlDoc.baseCss {} doc
  t "the stylesheet holds a code atom on one line"
    (hasStr css s!"pre .{HtmlDoc.codeTokClass} \{ white-space: nowrap; }")
  let pres := elemNodesList (· == "pre") #[] (docNodesOf doc).toList
  t "a wrapping code block wraps a run wider than its line between its atoms"
    (pres.all fun n => match n with
      | .elem _ attrs _ => (attrs.find? (·.1 == "style")).any fun (_, v) =>
          hasStr v "white-space: pre-wrap;" && hasStr v "overflow-wrap: break-word;"
      | _ => false)
  t "inline code holds no atom"
    ((codeAtomsOf doc).map (·.2.1) == #[#["->"], #[]])

def markdownCodeChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- The surface: one decision, read by the reader choice and the document.
  t "the surface is the path's: a .md source is markdown, any other tex"
    (Ir.Surface.ofPath "notes.md" == .markdown && Ir.Surface.ofPath "notes.tex" == .tex
      && Ir.Surface.ofPath "notes" == .tex)
  t "the elaborated document records its surface"
    ((elabMd "Words.\n").1.surface == .markdown && (elabStr (dvDoc "" "Words.")).1.surface == .tex)
  -- The listing values both artifacts read.
  let mdSpec := firstListing (elabMd "```\nplain code\n```\n").1
  let mdLang := firstListing (elabMd "```python\nx = 1\n```\n").1
  t "a markdown fence sets as its surface's code: footnotesize, wrapping whitespace first with listings' continuation indent"
    ([mdSpec, mdLang].all fun s => s.any fun s =>
      s.fontSize == .size "footnotesize" && s.breakLines
        && s.breakIndent == some Ir.listingBreakIndent && s.wrapAt == .whitespaceFirst)
  let texPlain := firstListing (elabStr (dvDoc "" "\\begin{verbatim}\nx\n\\end{verbatim}")).1
  let texLst := firstListing (elabStr (dvDoc "" "\\begin{lstlisting}\nx\n\\end{lstlisting}")).1
  t "a tex listing keeps LaTeX's defaults: the ambient size, no wrapping"
    ([texPlain, texLst].all fun s => s.any fun s =>
      s.fontSize == .size "normalsize" && !s.breakLines)
  let lstWrap := firstListing (elabStr (dvDoc ""
    "\\begin{lstlisting}[breaklines=true]\nx\n\\end{lstlisting}")).1
  let mintedWrap := firstListing (elabStr (dvDoc ""
    "\\begin{minted}[breaklines]{text}\nx\n\\end{minted}")).1
  t "listings wraps at its own units with its own continuation indent; minted's fvextra wrap is not that"
    (lstWrap.any (fun s => s.breakLines && s.breakIndent == some Ir.listingBreakIndent
        && s.wrapAt == .units)
      && mintedWrap.any (fun s => s.breakLines && s.breakIndent.isNone))
  -- The page.
  let some text ← loadTestFont "OpenSans-Regular.ttf"
    | t "markdown code: the text face loads" false
  let some mono ← loadTestFont "SourceCodePro-Regular.otf"
    | t "markdown code: the typewriter face loads" false
  let fonts := monoSlotOf text mono
  let size := Dim.pt 8
  let cell := size * mono.spaceAdvance / mono.unitsPerEm
  let words := "alpha beta gamma delta epsilon zeta eta theta iota kappa lambda mu nu xi \
omicron pi rho sigma tau upsilon phi chi psi omega"
  let src := "```\n" ++ words ++ "\nshort line\n    indented " ++ words ++ "\n```\n"
  let doc := (elabMd src).1
  let out := layoutOf fonts doc
  let measure := doc.page.width - 2 * doc.page.hmargin
  let lines := bodyLines out
  t s!"markdown code: long lines wrap and every shipped line fits the measure ({lines.size})"
    (lines.size ≥ 5 && lines.all (·.setWidth ≤ measure))
  t "markdown code: every source character ships once, in order"
    (String.join (lines.toList.map (bare ∘ lineText)) ==
      bare (words ++ "short line" ++ "indented" ++ words))
  t "markdown code: no line re-flows and none runs past the measure"
    (!out.diags.any fun d => d.kind == .W0386 || d.kind == .W0005)
  let x0 := (lines[0]?.bind firstGlyphX)
  t "markdown code: a continuation stands 20 pt in"
    (lines[1]?.bind firstGlyphX == x0.map (· + Ir.listingBreakIndent))
  let indentedAt := lines.findIdx? fun l => hasStr (lineText l) "indented"
  t "markdown code: an indented line's continuation stands its own indentation and 20 pt in"
    (match indentedAt with
      | some k =>
        (lines[k]?.bind firstGlyphX) == x0.map (· + 4 * cell) &&
          (lines[k + 1]?.bind firstGlyphX) == x0.map (· + 4 * cell + Ir.listingBreakIndent)
      | none => false)
  -- The markdown measure holds 80 columns of this 0.6 em face at
  -- footnotesize: an 80-column line stays one line, an 81-column one wraps.
  let cols (n : Nat) : String :=
    String.ofList ((List.range n).map fun k => if k % 5 == 4 && k + 1 < n then ' ' else 'a')
  let linesOf := codeFenceLines fonts ""
  t "markdown code: an 80-column line fits the markdown measure whole"
    ((linesOf (cols 79)).size == 1 && (linesOf (cols 80)).size == 1
      && (linesOf (cols 81)).size == 2)
  -- Never inside an identifier: a word wider than the measure is TeX's
  -- overfull line, whole, and a run of output units breaks between units.
  let ident := String.ofList (List.replicate 100 'q')
  let identLines := linesOf ident
  t "markdown code: an identifier wider than the measure is never split"
    (identLines.size == 1 && identLines.all fun l => bare (lineText l) == ident)
  let units := "f(" ++ String.intercalate "," ((List.range 30).map fun k => s!"arg{k}") ++ ")"
  let unitLines := linesOf units
  let joins := (unitLines.zip (unitLines.extract 1 unitLines.size)).toList.map fun (a, b) =>
    ((bare (lineText a)).back, (bare (lineText b)).front)
  t "markdown code: a run of output units wraps between units, never inside one"
    (unitLines.size ≥ 2 && String.join (unitLines.toList.map (bare ∘ lineText)) == units
      && joins.all fun (a, b) => !(a.isAlphanum && b.isAlphanum))
  -- A tex listing that declares listings' wrapping wraps at its units,
  -- line numbers included: no re-flow named, continuations past the
  -- number column.
  let texSrc := dvDoc "" ("\\begin{minipage}{120pt}\n\\begin{lstlisting}[breaklines=true,\
numbers=left,basicstyle=\\ttfamily\\footnotesize]\n" ++ words ++ "\n\\end{lstlisting}\n\\end{minipage}")
  let texOut := layoutOf fonts (elabStr texSrc).1
  let texLines := bodyLines texOut
  t s!"tex listing: breaklines wraps inside the measure with no re-flow named ({texLines.size})"
    (texLines.size ≥ 3 && texLines.all (·.setWidth ≤ Dim.pt 120)
      && !texOut.diags.any (·.kind == .W0386))
  t "tex listing: a continuation stands past the line numbers and 20 pt in"
    (match texLines[0]?, texLines[1]? with
      | some a, some b => !(lineText b).any Char.isDigit &&
          firstGlyphX b == (glyphX a 'a').map (· + Ir.listingBreakIndent)
      | _, _ => false)
  inlineCodeChecks ref text fonts
  Tests.MarkdownCode.codeTokenWrapChecks ref fonts

end Tests.MarkdownCode
