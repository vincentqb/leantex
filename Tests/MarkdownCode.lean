module

public import Tests.Support

public section

open LeanTex.Core

/-! Code on paper: every character reaches the page, a markdown fence wrapping whitespace first and
a tex listing at listings' units. -/

namespace Tests.MarkdownCode

/-- Where a shipped line's first non-space glyph stands. -/
def firstGlyphX (l : Layout.LineOut) : Option Dim.Length := Id.run do
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
    | .rule w _ _ _ | .image _ w _ _ _ => x := x + w
    | .poly _ _ => pure ()
  return none

/-- A line's text with every space and no-break space removed. -/
def bare (s : String) : String := (s.replace "\u00a0" "").replace " " ""

/-- Inline code breaks where url.sty's `\path` breaks, and a tex `\texttt` never breaks. -/
def inlineCodeChecks (ref : IO.Ref (List String)) (text : Font)
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
  let space : Dim.Length := size * text.spaceAdvance / text.unitsPerEm
  let md := prose fun c => "`" ++ c ++ "`"
  let doc := (elabMd (md ++ "\n")).1
  let out := layoutOf fonts doc
  let lines := bodyLines out
  let left := doc.page.hmargin
  let measure := doc.page.width - 2 * doc.page.hmargin
  -- Protrusion hangs a glyph a few points into the margin; an overfull line runs tens past it.
  t s!"markdown inline code: every line fits the measure and none is overfull ({lines.size})"
    (lines.size ≥ 6 && lines.all (fun l => left - Dim.pt 3 ≤ l.x
        && l.x + l.setWidth ≤ left + measure + Dim.pt 3)
      && !out.diags.any (·.kind == .W0005))
  let midCode (out : Layout.Out) : Array String := (bodyLines out).filterMap fun l =>
    (lineRuns l).back?.bind fun (f, s, _, _) =>
      if f == 1 && !codes.any (·.endsWith s) then some s else none
  let breakChars := ".@\\/!_|;>]),?&'+=#:-"
  t s!"markdown inline code: code lines end only after a break character, unhyphenated ({midCode out})"
    (!(midCode out).isEmpty && (midCode out).all fun s => breakChars.contains s.back)
  t "markdown inline code: every character reaches the page, in order"
    (String.join (lines.toList.map (bare ∘ lineText)) == bare (md.replace "`" ""))
  t "markdown inline code: no justified line opens a word space three of its own wide"
    (lines.all fun l => l.segs.all fun s => match s with
      | .gap w _ => w ≤ 3 * space
      | _ => true)
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
    t s!"long unbreakable runs ship every character on the paper ({label})"
      (!glines.isEmpty && glines.all (fun l => 0 ≤ l.x && l.x + l.setWidth ≤ gdoc.page.width)
        && shipped == want)
  let tex := prose fun c => "\\texttt{" ++ c.replace "_" "\\_" ++ "}"
  let texOut := layoutOf fonts (elabStr (dvDoc "" tex)).1
  t s!"tex inline code: a typewriter run never breaks; a too-wide one is overfull ({midCode texOut})"
    ((midCode texOut).isEmpty && texOut.diags.any (·.kind == .W0005))
  let codeRule := ":where(:not(pre) > code) { overflow-wrap: break-word; }"
  t "markdown CSS breaks overflowing inline code; tex CSS keeps it whole"
    (hasStr (HtmlDoc.baseCss {} doc) codeRule
      && !hasStr (HtmlDoc.baseCss {} (elabStr (dvDoc "" tex)).1) codeRule)

/-- The fallback lexer's class of a character: 0 a space, 1 a word character, 2 an operator
character, 3 any other. -/
def fallbackClass (c : Char) : Nat :=
  if c == ' ' || c == '\t' || c == '\u00a0' then 0
  else if Listing.wrapsBetweenChars c then 3
  else if c.isAlphanum || c == '_' || c == '\'' || c.toNat > 127 then 1
  else if "!#$%&*+-./:<=>?@\\^|~".contains c then 2
  else 3

/-- The wraps of `lines` that fall inside one fallback token of `code`. -/
def dividedTokens (code : String) (lines : Array String) : Array String := Id.run do
  let src := code.toList.toArray
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

/-- The fallback lexer's tokens of a line, spaces dropped: word runs, operator runs, and any other
character alone. -/
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

/-- A shipped code line overruns the measure only where one fallback token is wider than its
room. -/
def overrunExplained (left measure cell : Dim.Length) (l : Layout.LineOut) : Bool :=
  l.x + l.setWidth ≤ left + measure ||
    match firstGlyphX l with
    | some x => (fallbackTokens (lineText l)).any fun t => t.length * cell > left + measure - x
    | none => false

/-- A code line wraps where its lexer separates tokens, whitespace first, and a tex `breaklines`
listing breaks as listings does. -/
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
      let chain := String.intercalate "." ((List.range 40).map fun i => "".pushn 'z' (2 + i % 3))
      let glued := String.ofList (chain.toList.take (70 + k)) ++ op ++ "y.yy.yyy"
      let gs := linesOf lang ("value = " ++ glued)
      if gs.size ≥ 2 then unspaced := unspaced + 1
      offences := offences ++ judge s!"{lang}:{op}@{k} unspaced" ("value = " ++ glued) gs
  t s!"code wraps: no wrap divides an operator, every character ships, every line fits ({offences})"
    offences.isEmpty
  t s!"code wraps: the sweeps wrap their lines ({swept}, {unspaced})"
    (swept ≥ 130 && unspaced == 24 * pairs.length)
  let rel := "theorem gadget_le_widget (n m : Nat) (h : n ≤ m) (k : Nat) (hk : m ≤ k) : n ≤ k + 0 := Nat.le_trans h hk"
  let relLines := linesOf "lean" rel
  t s!"code wraps: a Lean line holding ≤ wraps and ships whole ({relLines.size} lines)"
    (relLines.size ≥ 2 && (judge "lean ≤" rel relLines).isEmpty)
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
  t s!"code wraps: long comments, strings and console lines part inside tokens, never past the page ({longOffences})"
    longOffences.isEmpty
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
  let chain := String.intercalate "." ((List.range 24).map fun i => "".pushn 'z' (2 + i % 3))
  for lang in ["python", ""] do
    let ls := linesOf lang ("value = " ++ chain)
    t s!"code wraps ({lang}): the last fitting space wins over a later token break \
({ls.map lineText})"
      (ls.size ≥ 3 && (ls[0]?.map (bare ∘ lineText)) == some "value=" &&
        String.join (ls.toList.map (bare ∘ lineText)) == bare ("value = " ++ chain) &&
        ls.all (·.setWidth ≤ measure))
  -- Expected lines: a LuaLaTeX listings probe of the same source at 300 pt, spaces dropped.
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
  t s!"tex listing: breaklines fills each line to the last unit that fits ({(texLines.zip want).filter (fun (a, b) => a != b)})"
    (texLines == want)
  -- Declared departure: the engine drops the white space listings carries onto a continuation.
  let carried := ("".pushn 'a' 62 ++ " " ++ "".pushn 'b' 58 ++ " c") ++ "\n" ++
    ("".pushn 'a' 58 ++ "\t" ++ "".pushn 'b' 50 ++ " cccc")
  let carryDoc := (elabStr (dvDoc "" ("\\noindent\\begin{minipage}{300pt}\n\\begin{lstlisting}" ++
    "[breaklines=true,basicstyle=\\ttfamily\\footnotesize]\n" ++ carried ++
    "\n\\end{lstlisting}\n\\end{minipage}"))).1
  let carryLines := bodyLines (layoutOf fonts carryDoc)
  let x0 := carryLines[0]?.bind firstGlyphX
  t s!"tex listing: a wrap drops the white space before it, continuations at their indent ({carryLines.map (bare ∘ lineText)})"
    (carryLines.map (bare ∘ lineText) ==
        #["".pushn 'a' 62, "".pushn 'b' 58, "c", "".pushn 'a' 58, "".pushn 'b' 50 ++ "cccc"] &&
      [1, 2, 4].all fun k => (carryLines[k]?.bind firstGlyphX) == x0.map (· + Ir.listingBreakIndent))

mutual

/-- The atoms a code tree holds on one line (`HtmlDoc.codeTokClass`), in order, and its `<wbr>`
count. -/
def heldAtomsOne (acc : Array String × Nat) : Html.Node → Array String × Nat
  | .elem "wbr" _ _ => (acc.1, acc.2 + 1)
  | .elem _ attrs kids =>
    if attrs.any fun (k, v) => k == "class" && (v.splitOn " ").contains HtmlDoc.codeTokClass then
      (acc.1.push (nodeTextList "" kids.toList), acc.2)
    else heldAtomsList acc kids.toList
  | .text _ | .style _ | .script _ _ => acc

def heldAtomsList (acc : Array String × Nat) : List Html.Node → Array String × Nat
  | [] => acc
  | k :: rest => heldAtomsList (heldAtomsOne acc k) rest

end

/-- The code elements of a document's HTML body, each with its text and held atoms. -/
def codeAtomsOf (doc : Ir.Doc) : Array (String × Array String × Nat) :=
  (elemNodesList (· == "code") #[] (docNodesOf doc).toList).filterMap fun n =>
    match n with
    | .elem _ _ kids => some (nodeTextList "" kids.toList, heldAtomsList (#[], 0) kids.toList)
    | _ => none

/-- Each held unit of a document's code: its text, and whether a narrow box releases it
(`HtmlDoc.codeLongTokClass`). -/
def heldClassesOf (doc : Ir.Doc) : Array (String × Bool) :=
  (elemNodesList (fun _ => true) #[] (docNodesOf doc).toList).filterMap fun n => match n with
    | .elem _ attrs kids =>
      let cls := (((attrs.find? (·.1 == "class")).map (·.2)).getD "").splitOn " "
      if cls.contains HtmlDoc.codeTokClass then
        some (nodeTextList "" kids.toList, cls.contains HtmlDoc.codeLongTokClass)
      else none
    | _ => none

mutual

/-- A code element's characters and `<wbr>`s in order, `none` for a `<wbr>`. -/
def wbrMarksOne (acc : Array (Option Char)) : Html.Node → Array (Option Char)
  | .elem "wbr" _ _ => acc.push none
  | .elem _ _ kids => wbrMarksList acc kids.toList
  | .text s => s.toList.foldl (fun a c => a.push (some c)) acc
  | .style _ | .script _ _ => acc

def wbrMarksList (acc : Array (Option Char)) : List Html.Node → Array (Option Char)
  | [] => acc
  | k :: rest => wbrMarksList (wbrMarksOne acc k) rest

end

/-- The characters each `<wbr>` of a document's code stands between. -/
def codeWbrNeighbours (doc : Ir.Doc) : Array (Char × Char) :=
  let marks := wbrMarksList #[] (elemNodesList (· == "code") #[] (docNodesOf doc).toList).toList
  (Array.range marks.size).filterMap fun i =>
    match marks[i]?, marks[i - 1]?, marks[i + 1]? with
    | some none, some (some a), some (some b) => if 0 < i then some (a, b) else none
    | _, _, _ => none

/-- What a code line holds whole under whitespace first, as the web page reads it
(`HtmlDoc.codeLineNodes`). -/
def heldUnitsOf (line : String) : Array String :=
  let fits (u : String) : Bool :=
    2 ≤ u.length && u.length ≤ HtmlDoc.codeHoldColumns
  (line.splitOn " ").toArray.flatMap fun st =>
    if fits st then #[st] else (fallbackTokens st).filter fits

/-- The web page wraps a code line where the page may, holding whole what the page's wrap may not
break inside. -/
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
        t s!"{label} code holds each stretch, or each fallback token of a wide one, on one line ({repr line}: {held})"
          (text == line && wbrs == 0 && held == heldUnitsOf line
            && held.all fun a => !a.any (· == ' '))
      | other => t s!"{label} code is one code element ({other.size})" false
  for (line, units, wbrs) in [("x:=y->z", #[":=", "->"], 4),
      ("f(a1)=b2", #["a1", "b2"], 5), ("p ->q", #["->"], 1)] do
    let (doc, _) := elabStr (dvDoc "\\usepackage{listings}\n"
      s!"\\begin\{lstlisting}[breaklines=true]\n{line}\n\\end\{lstlisting}")
    match codeAtomsOf doc with
    | #[(text, held, w)] =>
      t s!"a breaking lstlisting holds its units and parts them as listings may ({repr line}: {held}, {w})"
        (text == line && held == units && w == wbrs)
    | other => t s!"a breaking lstlisting is one code element ({other.size})" false
  let (doc, _) := elabMd "```\na->b\n```\n\nInline `c->d` code.\n"
  let css := HtmlDoc.baseCss {} doc
  t "the stylesheet holds a code atom on one line"
    (hasStr css s!"pre .{HtmlDoc.codeTokClass} \{ white-space: nowrap; }")
  let (opDoc, _) := elabMd "```python\ndef handler(event) -> dict:\n```\n"
  t s!"an operator stays held in every box, a longer unit only where it fits ({heldClassesOf opDoc})"
    (heldClassesOf opDoc == #[("def", false), ("handler(event)", true), ("->", false), ("dict:", true)])
  t "a box too narrow for a held unit longer than an operator releases it"
    (hasStr css s!"@container (width < {HtmlDoc.codeReleaseWidth}) \{ pre .{HtmlDoc.codeLongTokClass} \{ white-space: inherit; } }")
  let pres := elemNodesList (· == "pre") #[] (docNodesOf doc).toList
  t "a wrapping code block parts an over-wide run between its atoms"
    (pres.all fun n => match n with
      | .elem _ attrs _ => (attrs.find? (·.1 == "style")).any fun (_, v) =>
          hasStr v "white-space: pre-wrap;" && hasStr v "overflow-wrap: break-word;"
      | _ => false)
  t "inline code holds no atom"
    ((codeAtomsOf doc).map (·.2.1) == #[#["a->b"], #[]])
  let long := "value = compute(" ++ "".pushn 'x' 140 ++ ")"
  let (longDoc, _) := elabMd s!"```python\n{long}\n```\n"
  t "a token wider than the narrowest line is not held"
    (match codeAtomsOf longDoc with
      | #[(text, held, _)] => text == long && held == #["value", "compute"]
      | _ => false)
  let (kwDoc, _) := elabMd "```python\ndef handler(event):\n```\n"
  let ownClass := (elemNodesList (fun _ => true) #[] (docNodesOf kwDoc).toList).any fun n =>
    match n with
    | .elem _ attrs _ =>
      let classes := ((attrs.find? (·.1 == "class")).map (·.2.splitOn " ")).getD []
      classes.contains HtmlDoc.codeTokClass &&
        (attrs.any (·.1 == "style") || classes.any (·.startsWith "tok-"))
    | _ => false
  t "a run held whole takes the class on its own element"
    (ownClass &&
      (codeAtomsOf kwDoc).all fun (text, held, _) => text != "def handler(event):" || held.contains "def")

/-- The typewriter face with invented advances for the Thai, CJK and Hangul characters a code line
here writes; it draws nothing. -/
def scriptMono (mono : Font) : Font := Id.run do
  let cell := mono.spaceAdvance
  let blocks : Array (Nat × Nat × Nat) :=
    #[(0x0E00, 0x0E7F, 1), (0x3000, 0x30FF, 2), (0x4E00, 0x9FFF, 2), (0xAC00, 0xD7A3, 2)]
  let mut widths := mono.widths
  let mut ranges : Array (UInt32 × UInt32 × UInt32) := #[]
  for (lo, hi, cells) in blocks do
    ranges := ranges.push (lo.toUInt32, hi.toUInt32, widths.size.toUInt32)
    widths := widths ++ Array.replicate (hi + 1 - lo) (cells * cell)
  let cmap := (mono.cmap ++ ranges).qsort (·.1 < ·.1)
  return { mono with cmap := cmap, widths := widths, numGlyphs := widths.size }

/-- A script that wraps between its characters wraps in code, holding only what holds together
(`Listing.holdsToPrevious`, `holdsToNext`). -/
def codeScriptWrapChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let some mono := fonts.fonts[1]? | t "code script wrap: the typewriter face loads" false
  let scripted := { fonts with fonts := fonts.fonts.set! 1 (scriptMono mono) }
  let lines := [
    ("Japanese comment", "# この行は折り返しを確かめるための架空のコメントで、句読点の前では改行しません。" ++
      "二行目に続く文も「括弧」の中で切れず、小さな「ッ」や長音の「ー」から行を始めません。"),
    ("Thai string", "th = \"ภาษาไทยไม่มีช่องว่างระหว่างคำจึงต้องตัดบรรทัดระหว่างพยางค์แทนการเว้นวรรค" ++
      "และเครื่องหมายสระที่อยู่บนหรือล่างตัวอักษรต้องอยู่กับพยัญชนะของมันเสมอ\""),
    ("Korean string", "ko = \"한국어문장을공백없이길게써서줄바꿈을확인합니다한국어문장을공백없이길게" ++
      "써서줄바꿈을확인합니다\"")]
  let joins (u : String) : Bool :=
    (u.toList.zip u.toList.tail).all fun (a, b) =>
      !(Listing.wrapsBetweenChars a && Listing.wrapsBetweenChars b) ||
        Listing.holdsToPrevious b || Listing.holdsToNext a
  for (label, line) in lines do
    for (surface, src) in [("markdown", s!"```python\n{line}\n```\n"),
        ("listings", dvDoc "" s!"\\begin\{lstlisting}[breaklines=true]\n{line}\n\\end\{lstlisting}")] do
      let doc := if surface == "markdown" then (elabMd src).1 else (elabStr src).1
      let out := layoutOf scripted doc
      let ls := bodyLines out
      let right := doc.page.width - doc.page.hmargin
      let texts := ls.map (bare ∘ lineText)
      t s!"code script wrap: a {surface} {label} wraps inside the measure ({ls.size} lines)"
        (ls.size ≥ 2 && ls.all (fun l => l.x + l.setWidth ≤ right) &&
          !out.diags.any (·.kind == .W0005) && String.join texts.toList == bare line)
      t s!"code script wrap: no {surface} {label} line splits what holds together ({texts})"
        ((texts.extract 1 texts.size).all (fun s => !Listing.holdsToPrevious s.front) &&
          texts.pop.all (fun s => !Listing.holdsToNext s.back))
      match codeAtomsOf doc with
      | #[(text, held, _)] =>
        t s!"code script wrap: a {surface} {label}'s characters stand apart on the web page ({held})"
          (text == line && held.all joins)
      | other => t s!"code script wrap: a {surface} {label} is one code element ({other.size})" false
      -- No `<wbr>` between its characters: a browser breaks there by its own dictionary.
      t s!"code script wrap: a {surface} {label} marks no break between two of its characters"
        ((codeWbrNeighbours doc).all fun (a, b) =>
          !(Listing.wrapsBetweenChars a && Listing.wrapsBetweenChars b))
  -- Thai's and Lao's digits are digits: a number is one unit, one token.
  let numbers := "year = 2567 # ๒๕๖๗ and ໒໕໖໗ ok"
  let numDoc := (elabStr (dvDoc "" s!"\\begin\{lstlisting}[breaklines=true]\n{numbers}\n\\end\{lstlisting}")).1
  match codeAtomsOf numDoc with
  | #[(text, held, _)] =>
    t s!"code script wrap: Thai and Lao numbers are held whole ({held})"
      (text == numbers && held.contains "๒๕๖๗" && held.contains "໒໕໖໗" &&
        (codeWbrNeighbours numDoc).all fun (a, b) =>
          !(Listing.wrapsAtWords a && Listing.wrapsAtWords b))
  | other => t s!"code script wrap: a numbered line is one code element ({other.size})" false

def markdownCodeChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  t "the surface is the path's: a .md source is markdown, any other tex"
    (Ir.Surface.ofPath "notes.md" == .markdown && Ir.Surface.ofPath "notes.tex" == .tex
      && Ir.Surface.ofPath "notes" == .tex)
  t "the elaborated document records its surface"
    ((elabMd "Words.\n").1.surface == .markdown && (elabStr (dvDoc "" "Words.")).1.surface == .tex)
  let mdSpec := firstListing (elabMd "```\nplain code\n```\n").1
  let mdLang := firstListing (elabMd "```python\nx = 1\n```\n").1
  t "a markdown fence sets as its surface's code: footnotesize, whitespace-first wrap, listings' indent"
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
  t "listings wraps at its units with its own indent, unlike fvextra"
    (lstWrap.any (fun s => s.breakLines && s.breakIndent == some Ir.listingBreakIndent
        && s.wrapAt == .units)
      && mintedWrap.any (fun s => s.breakLines && s.breakIndent.isNone))
  let some text ← loadTestFont "OpenSans-Regular.ttf"
    | t "markdown code: the text face loads" false
  let some mono ← loadTestFont "SourceCodePro-Regular.otf"
    | t "markdown code: the typewriter face loads" false
  let fonts := slotPairOf 2 text mono
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
  t "markdown code: a continuation stands at its line's indentation plus 20 pt"
    (match indentedAt with
      | some k =>
        (lines[k]?.bind firstGlyphX) == x0.map (· + 4 * cell) &&
          (lines[k + 1]?.bind firstGlyphX) == x0.map (· + 4 * cell + Ir.listingBreakIndent)
      | none => false)
  -- The markdown measure holds 80 columns of this face at footnotesize: 80 stay one line, 81 wrap.
  let cols (n : Nat) : String :=
    String.ofList ((List.range n).map fun k => if k % 5 == 4 && k + 1 < n then ' ' else 'a')
  let linesOf := codeFenceLines fonts ""
  t "markdown code: an 80-column line fits the markdown measure whole"
    ((linesOf (cols 79)).size == 1 && (linesOf (cols 80)).size == 1
      && (linesOf (cols 81)).size == 2)
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
  Tests.MarkdownCode.codeScriptWrapChecks ref fonts

end Tests.MarkdownCode
