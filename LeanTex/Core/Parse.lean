module

public import LeanTex.Core.Lex
public import LeanTex.Core.Heading
public import LeanTex.Core.ListingLang
public import LeanTex.Core.CiteDecl
import LeanTex.Core.Definer
import LeanTex.Core.KeyVal
import Std.Data.HashSet

namespace LeanTex.Core.Parse

open LeanTex.Core LeanTex.Core.Lex

/-- One option a listing's head carries: an item as the document spells it, or a value a surface
reader sets. -/
public inductive ListingOpt where
  | spelled (item : String)
  | language (lang : Ir.ListingLang)
  | breakLines
  deriving Repr, BEq, Inhabited

/-- A verbatim capture: a listing's head, read once where it is captured, and the text after it. -/
public structure Verbatim where
  /-- The defaults standing where the capture stands, which its own options override. -/
  defaults : Array String
  /-- The head's own options in the order they stack. -/
  opts : Array ListingOpt
  /-- minted's language argument as written. -/
  lang : Option String
  /-- The source the head took, empty where a surface reader builds the head. -/
  head : String
  text : String
  deriving Repr, BEq, Inhabited

/-- A capture with no head. -/
@[expose] public def Verbatim.plain (text : String) : Verbatim := ⟨#[], #[], none, "", text⟩

/-- The options a listing reads, its defaults first. -/
@[expose] public def Verbatim.stacked (v : Verbatim) : Array ListingOpt :=
  v.defaults.map .spelled ++ v.opts

/-- The capture's source: its head's and its text's. -/
@[expose] public def Verbatim.src (v : Verbatim) : String := v.head ++ v.text

/-- An option as a listing's head spells it. -/
@[expose] public def ListingOpt.spelling : ListingOpt → String
  | .spelled item => item
  | .language lang => "language=" ++ lang.val
  | .breakLines => "breaklines"

/-- The capture as TeX spells it, its defaults aside: its source, or a surface reader's head spelled
from its options and language. -/
@[expose] public def Verbatim.spelling (v : Verbatim) : String :=
  if !v.head.isEmpty then v.src else
  (if v.opts.isEmpty then "" else "[" ++ ",".intercalate (v.opts.map (·.spelling)).toList ++ "]") ++
    ((v.lang.map fun l => "{" ++ l ++ "}").getD "") ++ v.text

/-- The option head of a listing environment's captured body: spaces and tabs,
then `[...]` with nested braces. -/
def listingOptHead (s : String) : Option (String × Nat) := Id.run do
  let cs := s.toList.toArray
  let mut i := 0
  for _ in [0:cs.size] do
    if h : i < cs.size then
      if cs[i] == ' ' || cs[i] == '\t' then i := i + 1 else break
    else break
  if h : i < cs.size then
    if cs[i] != '[' then return none
    let mut depth : Nat := 0
    let mut j := i + 1
    let mut out := ""
    for _ in [0:cs.size] do
      if h2 : j < cs.size then
        let c := cs[j]
        if c == '{' then depth := depth + 1
        else if c == '}' then depth := depth - 1
        if c == ']' && depth == 0 then
          return some (out, j + 1)
        out := out.push c
        j := j + 1
      else break
    return none
  else return none

/-- The mandatory `{language}` head of a `{minted}` body after any option head, the groups it holds
nested in it. -/
def mintedLangHead (s : String) (start : Nat) : Option (String × Nat) := Id.run do
  let cs := s.toList.toArray
  let mut i := start
  for _ in [0:cs.size] do
    if h : i < cs.size then
      if cs[i] == ' ' || cs[i] == '\t' then i := i + 1 else break
    else break
  if h : i < cs.size then
    if cs[i] != '{' then return none
    let mut depth : Nat := 0
    let mut j := i + 1
    let mut out := ""
    for _ in [0:cs.size] do
      if h2 : j < cs.size then
        let c := cs[j]
        if c == '}' then
          if depth == 0 then return some (out, j + 1)
          depth := depth - 1
        else if c == '{' then depth := depth + 1
        out := out.push c
        j := j + 1
      else break
    return none
  else return none

/-- Whether a capture of `env` opens on minted's `{language}` argument. -/
@[expose] public def mintedEnv (env : String) : Bool :=
  env == "minted" || env == "mint" || env == "mintinline"

/-- A capture of `env` read into its head and the text after it: a listing's `[options]`, split
into items, and minted's `{language}` after them. -/
public def Verbatim.read (env s : String) : Verbatim :=
  let opt := if env == "lstlisting" || env == "lstinline" || mintedEnv env then listingOptHead s
    else none
  let afterOpt := (opt.map (·.2)).getD 0
  let lang := if mintedEnv env then mintedLangHead s afterOpt else none
  let n := (lang.map (·.2)).getD afterOpt
  { defaults := #[]
    opts := ((opt.map (KeyVal.items ·.1)).getD #[]).map .spelled
    lang := lang.map (·.1)
    head := String.ofList (s.toList.take n)
    text := String.ofList (s.toList.drop n) }

public theorem Verbatim.read_src (env s : String) : (Verbatim.read env s).src = s := by
  simp only [Verbatim.read, Verbatim.src, ← String.ofList_append, List.take_append_drop,
    String.ofList_toList]

public inductive Raw where
  | word (s : String) (pos : Pos)
  | space
  | par (pos : Pos)
  | ctrl (name : String) (pos : Pos)
  | sym (c : Char) (pos : Pos)
  | group (body : Array Raw) (pos : Pos)
  | math (display : Bool) (body : Array Raw) (pos : Pos)
  | env (name : String) (body : Array Raw) (pos : Pos)
  | verb (env : String) (v : Verbatim) (pos : Pos)
  deriving Repr, BEq, Inhabited

/-- Discharges a walk's termination goals: an array a constructor holds is smaller than it. -/
macro "raws_dec" : tactic =>
  `(tactic| (
    all_goals simp_wf
    all_goals try omega
    all_goals
      (have hb : ∀ {α : Type} [SizeOf α] (a : Array α), sizeOf a = 1 + sizeOf a.toList :=
        fun _ => rfl
       (try simp only [hb])
       omega)))

/-- The control name of a native heading for surface readers, unforgeable
because it holds a space. -/
public def headingControl : Ir.HeadingLevel → String
  | .title => "heading title"
  | .h1 => "heading 1"
  | .h2 => "heading 2"
  | .h3 => "heading 3"
  | .h4 => "heading 4"
  | .h5 => "heading 5"
  | .h6 => "heading 6"

/-- The native control a class's `\chapter` rewrites to; no source control word spells it. -/
@[expose] public def chapterControl : String := "heading chapter"

/-- The mark after a heading control that sets it unnumbered yet listed in the contents, as
KOMA-Script's `\addchap` and `\addsec`; no source word holds a space. -/
@[expose] public def listedUnnumbered : String := "* listed"

/-- Decode only the finite native heading vocabulary, a class's chapter its body h1. -/
public def headingControl? : String → Option Ir.HeadingLevel
  | "heading title" => some .title
  | "heading chapter" => some .h1
  | "heading 1" => some .h1
  | "heading 2" => some .h2
  | "heading 3" => some .h3
  | "heading 4" => some .h4
  | "heading 5" => some .h5
  | "heading 6" => some .h6
  | _ => none

/-- A surface reader's heading, always unnumbered, its title
the reader's own inline raws. -/
public def headingRaws (level : Ir.HeadingLevel) (body : Array Raw) (p : Pos) :
    Array Raw :=
  #[.ctrl (headingControl level) p, .word "*" p, .group body p]

public theorem headingControl_exact (level : Ir.HeadingLevel) :
    headingControl? (headingControl level) = some level := by
  cases level <;> rfl

public theorem headingRaws_contract (level : Ir.HeadingLevel)
    (body : Array Raw) (p : Pos) :
    headingRaws level body p =
      #[.ctrl (headingControl level) p, .word "*" p, .group body p] := by rfl

/-- A positioned raw's macro ancestry; `none` for a space. -/
@[expose] public def Raw.origins? : Raw → Option (List MacroOrigin)
  | .space => none
  | .word _ p | .par p | .ctrl _ p | .sym _ p
  | .group _ p | .math _ _ p | .env _ _ p | .verb _ _ p => some p.origins

mutual

/-- An enclosing invocation prepended to every position in an expanded raw. -/
public def markMacro (origin : MacroOrigin) : Raw → Raw
  | .word s p => .word s { p with origins := origin :: p.origins }
  | .space => .space
  | .par p => .par { p with origins := origin :: p.origins }
  | .ctrl n p => .ctrl n { p with origins := origin :: p.origins }
  | .sym c p => .sym c { p with origins := origin :: p.origins }
  | .group body p =>
    .group (markMacroList origin #[] body.toList) { p with origins := origin :: p.origins }
  | .math d body p =>
    .math d (markMacroList origin #[] body.toList) { p with origins := origin :: p.origins }
  | .env n body p =>
    .env n (markMacroList origin #[] body.toList) { p with origins := origin :: p.origins }
  | .verb env s p => .verb env s { p with origins := origin :: p.origins }

public def markMacroList (origin : MacroOrigin) (acc : Array Raw) : List Raw → Array Raw
  | [] => acc
  | r :: rest => markMacroList origin (acc.push (markMacro origin r)) rest

end

mutual

/-- A raw with every position moved by `f`. -/
@[expose] public def mapPos (f : Pos → Pos) : Raw → Raw
  | .word s p => .word s (f p)
  | .space => .space
  | .par p => .par (f p)
  | .ctrl n p => .ctrl n (f p)
  | .sym c p => .sym c (f p)
  | .group body p => .group (mapPosList f #[] body.toList) (f p)
  | .math d body p => .math d (mapPosList f #[] body.toList) (f p)
  | .env n body p => .env n (mapPosList f #[] body.toList) (f p)
  | .verb e s p => .verb e s (f p)

@[expose] public def mapPosList (f : Pos → Pos) (acc : Array Raw) : List Raw → Array Raw
  | [] => acc
  | r :: rest => mapPosList f (acc.push (mapPos f r)) rest

end

public theorem markMacro_origins_exact (origin : MacroOrigin) (r : Raw) :
    (markMacro origin r).origins? = r.origins?.map (origin :: ·) := by
  cases r <;> rfl

public theorem markMacroList_toList (origin : MacroOrigin) (acc : Array Raw) (rs : List Raw) :
    (markMacroList origin acc rs).toList = acc.toList ++ rs.map (markMacro origin) := by
  induction rs generalizing acc with
  | nil => simp [markMacroList]
  | cons r rs ih => simp [markMacroList, ih, List.append_assoc]

/-- What closes an open frame. -/
inductive Stop where
  | brace
  | math
  | dollarDisplay
  | parenMath
  | displayMath
  | env (name : String)
  deriving Repr, BEq, Inhabited

def Stop.name : Stop → String
  | .brace => "'}'"
  | .math => "closing '$'"
  | .dollarDisplay => "closing '$$'"
  | .parenMath => "'\\)'"
  | .displayMath => "'\\]'"
  | .env n => s!"'\\end\{{n}}'"

/-- An open delimiter with the items collected before it; `body` marks one of an
environment definer's two bodies. -/
private structure Frame where
  stop : Stop
  openPos : Pos
  outer : Array Raw
  body : Bool := false
  /-- The environment opened by its command, `\center` for `\begin{center}`. -/
  cmd : Bool := false

/-- The environments whose commands open and close them in the flow, as `\center` and `\endcenter`
do. -/
public def cmdEnvs : List String :=
  ["trivlist", "itemize", "enumerate", "description", "center", "flushleft", "flushright", "quote",
   "quotation", "verse"]

/-- The environment a command closes, `center` for `\endcenter`. -/
public def cmdEnvClose? (name : String) : Option String :=
  if name.startsWith "end" then
    let e := (name.drop 3).toString
    if cmdEnvs.contains e then some e else none
  else none

/-- A half's name for an environment its command opened or closed, unforgeable because it holds a
space. -/
public def cmdHalf (name : String) : String := "command " ++ name

/-- The command a half of a command-opened environment names, `center` for `\center`. -/
public def cmdHalf? (half : String) : Option String :=
  if half.startsWith "command " then some (half.drop "command ".length).toString else none

/-- The commands whose next control is an operand they read, not one they run: a definition's
name, a copy's source, a patch's target. -/
private def operandReaders : List String :=
  Definer.names (·.defines == .command) ++ ["patchcmd", "pretocmd", "apptocmd", "xpatchcmd",
    "xpretocmd", "xapptocmd", "show", "meaning", "ifx"]

/-- Whether a command standing next is an operand, as in `\let\keep\center` or
`\renewcommand\itemize`. -/
private def operandNext (acc : Array Raw) : Bool :=
  let rs := (acc.toList.reverse.filter fun r =>
    !(r matches .space) && !(r matches .word "=" _) && !(r matches .word "*" _)).take 2
  let reads (r : Raw) : Bool := match r with
    | .ctrl c _ => operandReaders.contains c
    | _ => false
  match rs with
  | r :: rest => reads r || ((r matches .ctrl ..) && (rest.head?.map reads).getD false)
  | [] => false

/-- The definers whose two body groups are token lists. -/
public def envDefiners : List String := Definer.tokenListEnvs

/-- The name of a definer body's half of a construct its other body completes,
unforgeable because it holds a space. -/
public def splitOpen (name : String) : String := "open " ++ name
public def splitClose (name : String) : String := "close " ++ name

public def splitOpen? (n : String) : Option String :=
  if n.startsWith "open " then some ((n.drop "open ".length).toString) else none

public def splitClose? (n : String) : Option String :=
  if n.startsWith "close " then some ((n.drop "close ".length).toString) else none

/-- The name a half of a frame carries: the environment's name, or the delimiter
that opened the math. -/
def Stop.halfName : Stop → String
  | .env n => n
  | .math => "$"
  | .dollarDisplay => "$$"
  | .parenMath => "\\("
  | .displayMath => "\\["
  | .brace => "{"

/-- The frame a half's name records. -/
def halfStop (name : String) : Stop :=
  if name == "$" then .math
  else if name == "$$" then .dollarDisplay
  else if name == "\\(" then .parenMath
  else if name == "\\[" then .displayMath
  else .env name

/-- The diagnostic an unclosed frame raises at a brace. -/
def unclosedAtBrace (file : String) (stop : Stop) (pos : Pos) : Diag :=
  Diag.of .E0201 s!"unclosed: expected {stop.name} before the group's '}'" (some ⟨file, pos⟩)

def unmatchedEnd (file name : String) (pos : Pos) : Diag :=
  Diag.of .E0205 s!"'\\end\{{name}}' without matching '\\begin\{{name}}'" (some ⟨file, pos⟩)

/-- The index past the last item before `j` that is not a space. -/
private def backSkip (acc : Array Raw) (j : Nat) : Nat := Id.run do
  let mut k := j
  for _ in [0:j] do
    if k == 0 then break
    match acc[k - 1]? with
    | some .space => k := k - 1
    | _ => break
  return k

private def before (acc : Array Raw) (k : Nat) : Option Raw :=
  if k == 0 then none else acc[k - 1]?

private def isSym (c : Char) : Option Raw → Bool
  | some (.sym d _) => d == c
  | _ => false

/-- Whether `acc` ends, before `k0`, with a definer's head. -/
private def definerHeadAt (acc : Array Raw) (k0 : Nat) : Bool := Id.run do
  let mut k := backSkip acc k0
  for _ in [0:acc.size] do
    let opener := if isSym ']' (before acc k) then '['
      else if isSym ')' (before acc k) then '(' else ' '
    if opener == ' ' then break
    let mut j := k - 1
    for _ in [0:k] do
      if j == 0 || isSym opener (before acc j) then break
      j := j - 1
    unless isSym opener (before acc j) do return false
    k := backSkip acc (j - 1)
  unless before acc k matches some (.group _ _) do return false
  k := backSkip acc (k - 1)
  if isSym '*' (before acc k) then k := backSkip acc (k - 1)
  match before acc k with
  | some (.ctrl d _) => return envDefiners.contains d
  | _ => return false

/-- How far back a definer head is sought from a body's `{`. -/
def definerReach : Nat := 128

/-- The items `envBodyNext` reads: the last `definerReach` of the level. -/
public def definerWindow (acc : Array Raw) : Array Raw :=
  acc.extract (acc.size - definerReach) acc.size

/-- Whether the group opening after `acc` is one of an
environment definer's two bodies. -/
private def envBodyNext (acc : Array Raw) : Bool :=
  let w := definerWindow acc
  let k := backSkip w w.size
  definerHeadAt w k ||
    (before w k matches some (.group _ _) && definerHeadAt w (k - 1))

public theorem definerWindow_fixed_point (acc : Array Raw) :
    definerWindow (definerWindow acc) = definerWindow acc := by
  unfold definerWindow
  rw [Array.extract_extract]
  simp only [Array.size_extract]
  have h1 : acc.size - definerReach
      + (min acc.size acc.size - (acc.size - definerReach) - definerReach)
      = acc.size - definerReach := by omega
  have h2 : min (acc.size - definerReach + (min acc.size acc.size - (acc.size - definerReach)))
      acc.size = acc.size := by omega
  rw [h1, h2]

private theorem envBodyNext_window_exact (acc : Array Raw) :
    envBodyNext acc = envBodyNext (definerWindow acc) := by
  simp only [envBodyNext, definerWindow_fixed_point]

/-- A closed frame's body wrapped into the node its delimiter denotes. -/
private def Frame.close (f : Frame) (body : Array Raw) : Array Raw :=
  match f.stop with
  | .brace => f.outer.push (.group body f.openPos)
  | .math => f.outer.push (.math false body f.openPos)
  | .dollarDisplay => f.outer.push (.math true body f.openPos)
  | .parenMath => f.outer.push (.math false body f.openPos)
  | .displayMath => f.outer.push (.math true body f.openPos)
  | .env n => f.outer.push (.env n body f.openPos)

private def err (file : String) (code : DiagCode) (msg : String) (pos : Pos) : Diag :=
  Diag.of code msg (some ⟨file, pos⟩)

/-- An open half settled to what a plain parse makes of it,
with that parse's diagnostic. -/
public def settleOpenHalf (file name : String) (body : Array Raw) (pos : Pos) : Array Raw × Diag :=
  let stop := halfStop name
  ((⟨stop, pos, #[], false, false⟩ : Frame).close body, unclosedAtBrace file stop pos)

/-- The diagnostic a plain parse raises at a close half. -/
public def closeHalfDiag (file name : String) (pos : Pos) : Diag :=
  match halfStop name with
  | .env n => unmatchedEnd file n pos
  | s => err file .E0202 s!"unexpected {s.name}" pos

/-- `{name}` after `\begin` or `\end`: the name and the next index. -/
private def envName (toks : Array Token) (file : String) (i : Nat) (pos : Pos) :
    String × Nat × Array Diag :=
  match toks[i]?, toks[i + 1]?, toks[i + 2]? with
  | some ⟨.lbrace, _⟩, some ⟨.word n, _⟩, some ⟨.rbrace, _⟩ => (n, i + 3, #[])
  | some ⟨.lbrace, _⟩, some ⟨.word n, _⟩, _ =>
    (n, i + 2, #[err file .E0205 "expected '}' after the environment name" pos])
  | some ⟨.lbrace, _⟩, _, _ =>
    ("", i + 1, #[err file .E0205 "expected an environment name" pos])
  | _, _, _ => ("", i, #[err file .E0205 "expected '{name}' here" pos])

/-- `\ifmmode`'s reading: its math branch as a formula first, then its text branch, each read in
its mode, unforgeable because its name holds a space. -/
@[expose] public def modeEnv : String := "ifmmode "

/-- The command a `modeEnv`'s math branch records, so its source reads back as
`\ifmmode <math>\else <text>\fi`, the conditional TeX reads the same. -/
@[expose] public def modeBranch : String := "\\ifmmode"

/-- TeX's conditional heads, TeX82's and e-TeX's, each closed by its own `\fi`. -/
public def condPrimitives : List String :=
  ["if", "ifcat", "ifnum", "ifdim", "ifodd", "ifvmode", "ifhmode", "ifmmode", "ifinner",
   "ifvoid", "ifhbox", "ifvbox", "ifx", "ifeof", "iftrue", "iffalse", "ifcase",
   "ifdefined", "ifcsname", "iffontchar"]

mutual

/-- The conditionals `\newif` declares in a text, by name, and whether it spells `\ifmmode`. -/
private def newifsIn (acc : Std.HashSet String × Bool) : List Raw → Std.HashSet String × Bool
  | [] => acc
  | .ctrl "newif" _ :: .ctrl n _ :: rest => newifsIn (acc.1.insert n, acc.2) rest
  | r :: rest => newifsIn (newifsOf acc r) rest

private def newifsOf (acc : Std.HashSet String × Bool) : Raw → Std.HashSet String × Bool
  | .group body _ | .env _ body _ | .math _ body _ => newifsIn acc body.toList
  | .ctrl n _ => (acc.1, acc.2 || n == "ifmmode")
  | .word .. | .space | .par _ | .sym .. | .verb .. => acc

end

/-- The engine-test conditionals packages define (ifpdf, iftex), each closed by its own `\fi`. -/
private def packageConds : List String :=
  ["ifpdf", "ifxetex", "ifluatex", "ifPDFTeX", "ifXeTeX", "ifLuaTeX", "ifpTeX", "ifupTeX", "iftutex"]

/-- An open `\ifmmode` while one list level is read: the output before it, its math branch once
`\else` is met, and how many other conditionals stand open inside it. -/
private structure ModeFrame where
  outer : Array Raw
  math : Option (Array Raw × Pos)
  depth : Nat
  pos : Pos

/-- One list level with each `\ifmmode … \else … \fi` it closes read as a `modeEnv`; one left
open stays as written. -/
private def modeLevel (conds : Std.HashSet String) (xs : Array Raw) : Array Raw := Id.run do
  let isCond (n : String) : Bool :=
    condPrimitives.contains n || packageConds.contains n || n.startsWith "if@" || conds.contains n
  let mut frames : Array ModeFrame := #[]
  let mut acc : Array Raw := #[]
  for r in xs do
    match r, frames.back? with
    | .ctrl "ifmmode" p, _ =>
      if acc.back? matches some (.ctrl "unless" _) then
        frames := frames.modify (frames.size - 1) fun f => { f with depth := f.depth + 1 }
        acc := acc.push r
      else
        frames := frames.push { outer := acc, math := none, depth := 0, pos := p }
        acc := #[]
    | .ctrl "else" p, some f =>
      if f.depth == 0 && f.math.isNone then
        frames := frames.pop.push { f with math := some (acc, p) }
        acc := #[]
      else acc := acc.push r
    | .ctrl "fi" _, some f =>
      if f.depth == 0 then
        let (math, text) := match f.math with
          | some (m, _) => (m, acc)
          | none => (acc, #[])
        frames := frames.pop
        acc := f.outer.push
          (.env modeEnv (#[Raw.math false math { f.pos with command := some modeBranch }] ++ text) f.pos)
      else
        frames := frames.pop.push { f with depth := f.depth - 1 }
        acc := acc.push r
    | .ctrl n _, some f =>
      if isCond n then frames := frames.pop.push { f with depth := f.depth + 1 }
      acc := acc.push r
    | _, _ => acc := acc.push r
  -- Each open frame's output precedes the one it holds, so the levels join outermost first.
  let mut out : Array Raw := #[]
  for f in frames do
    out := (out ++ f.outer).push (.ctrl "ifmmode" f.pos)
    if let some (m, ep) := f.math then out := (out ++ m).push (.ctrl "else" ep)
  return out ++ acc

/-- The picture environments, whose reader decides `\ifmmode` as pgf's horizontal box does. -/
private def pictureBodies : List String := ["tikzpicture", "picture", "tikzcd", "external"]

mutual

-- conserves: none — reads each closed `\ifmmode` as the mode reading it
private def modeList (conds : Std.HashSet String) (acc : Array Raw) : List Raw → Array Raw
  | [] => acc
  | r :: rest => modeList conds (acc.push (modeRaw conds r)) rest

private def modeRaw (conds : Std.HashSet String) : Raw → Raw
  | .group body p => .group (modeLevel conds (modeList conds #[] body.toList)) p
  | .env n body p =>
    if pictureBodies.contains n then .env n body p
    else .env n (modeLevel conds (modeList conds #[] body.toList)) p
  | .math d body p => .math d (modeLevel conds (modeList conds #[] body.toList)) p
  | .word w p => .word w p
  | .space => .space
  | .par p => .par p
  | .ctrl n p => .ctrl n p
  | .sym c p => .sym c p
  | .verb e v p => .verb e v p

end

/-- A parsed text with each `\ifmmode` it closes at one list level read as a `modeEnv`. -/
public def modeChoices (raws : Array Raw) : Array Raw :=
  let (conds, spelled) := newifsIn ({}, false) raws.toList
  if spelled then modeLevel conds (modeList conds #[] raws.toList) else raws

/-- Parses tokens into a `Raw` forest in one pass with an explicit frame stack;
strays are reported and skipped, unclosed delimiters close at end of input. -/
public def parse (file : String) (toks : Array Token) : Array Raw × Array Diag := Id.run do
  let mut frames : Array Frame := #[]
  let mut acc : Array Raw := #[]
  let mut diags : Array Diag := #[]
  let mut i := 0
  -- Every branch advances `i`, so the `i < toks.size` guard ends the loop.
  for _ in [0:toks.size + 1] do
    if h : i < toks.size then
      let ⟨tok, pos⟩ := toks[i]
      i := i + 1
      match tok with
      | .lbrace =>
        frames := frames.push ⟨.brace, pos, acc, envBodyNext acc, false⟩
        acc := #[]
      | .rbrace =>
        -- The group boundary wins: a delimiter still open at the `}` closes there, diagnosed.
        if frames.any (·.stop == .brace) then
          let body := (frames.findRev? (·.stop == .brace)).any (·.body)
          for _ in [0:frames.size] do
            match frames.back? with
            | some f =>
              if f.stop == .brace then break
              match body, f.stop with
              | true, s =>
                frames := frames.pop
                acc := f.outer.push
                  (.env (splitOpen (if f.cmd then cmdHalf s.halfName else s.halfName)) acc f.openPos)
              | _, s =>
                frames := frames.pop
                -- An environment's command a group closes over is the command alone.
                if f.cmd then acc := f.outer.push (.ctrl s.halfName f.openPos) ++ acc
                else
                  diags := diags.push (unclosedAtBrace file f.stop f.openPos)
                  acc := f.close acc
            | none => break
          match frames.back? with
          | some f =>
            frames := frames.pop
            acc := ({ f with openPos := { f.openPos with closeEol := pos.closeEol } } : Frame).close acc
          | none => pure ()
        else
          diags := diags.push (err file .E0202 "unexpected '}'" pos)
      | .math =>
        match frames.back? with
        | some f =>
          if f.stop == .math || f.stop == .dollarDisplay then
            if f.stop == .dollarDisplay then
              if toks[i]?.any (·.tok == .math) then i := i + 1
              else
                diags := diags.push
                  (err file .E0202 "expected a second '$' to close display math" pos)
            frames := frames.pop
            acc := f.close acc
            continue
        | none => pure ()
        -- Pair shifts only when opening display math.
        let display := toks[i]?.any (·.tok == .math)
        if display then i := i + 1
        frames := frames.push ⟨if display then .dollarDisplay else .math, pos, acc, false, false⟩
        acc := #[]
      | .ctrl "(" =>
        frames := frames.push ⟨.parenMath, pos, acc, false, false⟩
        acc := #[]
      | .ctrl ")" =>
        match frames.back? with
        | some f =>
          if f.stop == .parenMath then
            frames := frames.pop
            acc := f.close acc
          else if f.body then
            acc := acc.push (.env (splitClose Stop.parenMath.halfName) #[] pos)
          else
            diags := diags.push (err file .E0202 "unexpected '\\)'" pos)
        | none =>
          diags := diags.push (err file .E0202 "unexpected '\\)'" pos)
      | .ctrl "[" =>
        frames := frames.push ⟨.displayMath, pos, acc, false, false⟩
        acc := #[]
      | .ctrl "]" =>
        match frames.back? with
        | some f =>
          if f.stop == .displayMath then
            frames := frames.pop
            acc := f.close acc
          else if f.body then
            acc := acc.push (.env (splitClose Stop.displayMath.halfName) #[] pos)
          else
            diags := diags.push (err file .E0202 "unexpected '\\]'" pos)
        | none =>
          diags := diags.push (err file .E0202 "unexpected '\\]'" pos)
      | .ctrl "begin" =>
        let (name, j, ds) := envName toks file i pos
        diags := diags ++ ds
        i := j
        frames := frames.push ⟨.env name, pos, acc, false, false⟩
        acc := #[]
      | .ctrl "end" =>
        let (name, j, ds) := envName toks file i pos
        diags := diags ++ ds
        i := j
        -- An environment's command an `\end` of another, or of a `\begin` below it, closes over is
        -- the command alone.
        let begun := frames.any fun g => !g.cmd && g.stop == .env name
        for _ in [0:frames.size] do
          match frames.back? with
          | some f =>
            if f.cmd && (f.stop != .env name || begun) then
              frames := frames.pop
              acc := f.outer.push (.ctrl f.stop.halfName f.openPos) ++ acc
            else break
          | none => break
        match frames.back? with
        | some f =>
          match f.stop with
          | .env expected =>
            if name != expected then
              diags := diags.push
                (err file .E0205 s!"'\\end\{{name}}' closes '\\begin\{{expected}}'" pos)
            frames := frames.pop
            acc := f.close acc
          | .brace =>
            if f.body then acc := acc.push (.env (splitClose name) #[] pos)
            else diags := diags.push (unmatchedEnd file name pos)
          | _ =>
            diags := diags.push (unmatchedEnd file name pos)
        | none =>
          diags := diags.push (unmatchedEnd file name pos)
      | .ctrl name =>
        if cmdEnvs.contains name && !operandNext acc then
          frames := frames.push { stop := .env name, openPos := pos, outer := acc, cmd := true }
          acc := #[]
        else match cmdEnvClose? name, frames.back? with
          | some e, some f =>
            if f.cmd && f.stop == .env e then
              frames := frames.pop
              acc := f.close acc
            else if f.stop == .brace && f.body then
              acc := acc.push (.env (splitClose (cmdHalf e)) #[] pos)
            else acc := acc.push (.ctrl name pos)
          | _, _ => acc := acc.push (.ctrl name pos)
      | .word s => acc := acc.push (.word s pos)
      | .space => acc := acc.push .space
      | .par => acc := acc.push (.par pos)
      | .sym c => acc := acc.push (.sym c pos)
      | .verb env s => acc := acc.push (.verb env (Verbatim.read env s) pos)
  -- End of input: close what is still open, innermost first.
  for _ in [0:frames.size] do
    match frames.back? with
    | some f =>
      frames := frames.pop
      if f.cmd then acc := f.outer.push (.ctrl f.stop.halfName f.openPos) ++ acc
      else
        diags := diags.push
          (err file .E0201 s!"unclosed: expected {f.stop.name}" f.openPos)
        acc := f.close acc
    | none => pure ()
  return (modeChoices acc, diags)

/-- The code of a captured `\mintinline` or `\mint` call
from just past its `{language}`. -/
public def mintedCode (s : String) (start : Nat) : String := Id.run do
  let cs := s.toList.toArray
  let some opener := cs[start]? | return ""
  let mut out := ""
  let mut depth : Nat := 0
  let mut i := start + 1
  for _ in [start + 1:cs.size] do
    let some c := cs[i]? | break
    if opener == '{' then
      if c == '}' then
        if depth == 0 then break
        depth := depth - 1
      else if c == '{' then depth := depth + 1
    else if c == opener then break
    if c == '\r' && cs[i + 1]? == some '\n' then
      out := out.push ' '
      i := i + 2
    else
      out := out.push (if c == '\n' || c == '\r' then ' ' else c)
      i := i + 1
  return out

/-- The environment wrapping an `\input` file's content,
unforgeable because its name holds a space. -/
public def inputEnv (file : String) : String := "input " ++ file

/-- The environment wrapping an included markdown or code file's raws, which neither the
compatibility pass nor the document's own commands reach. -/
public def keptInputEnv (file : String) : String := "kept input " ++ file

/-- The environment wrapping a file a package, class or theme inputs, or a macro one defines,
whose declarations are that package's. -/
public def ownedInputEnv (file : String) : String := "owned input " ++ file

@[expose] public def inputEnvFile? (name : String) : Option String :=
  if name.startsWith "input " then some ((name.drop "input ".length).toString)
  else if name.startsWith "kept input " then some ((name.drop "kept input ".length).toString)
  else if name.startsWith "owned input " then some ((name.drop "owned input ".length).toString)
  else none

/-- Whether an input environment holds a file a package's code input. -/
@[expose] public def isOwnedInput (name : String) : Bool := name.startsWith "owned input "

/-- Whether an input environment holds an included markdown or code file's raws. -/
@[expose] public def isKeptInput (name : String) : Bool := name.startsWith "kept input "

/-- The environment of a generated declaration scope,
unforgeable because its name holds a space. -/
public def scopeEnv : String := "scope "

/-- Whether a raw is the empty generated scope an environment's rewrite leaves
where `\begin` stood. -/
@[expose] public def isPlaceKeeper : Raw → Bool
  | .env n body _ => n == scopeEnv && body.isEmpty
  | _ => false

/-- Whether a group standing next would read as an argument. -/
@[expose] public def endsInArgument (cur : Array Raw) : Bool := Id.run do
  let mut k := cur.size
  for _ in [0:cur.size] do
    match cur[k - 1]? with
    | some .space => k := k - 1
    | some (.group _ _) => k := k - 1
    | some (.ctrl _ _) => return true
    | some (.sym ']' _) => return true
    | _ => return false
  return false

/-- The environment a markdown pipe table desugars to. -/
public def markdownTableEnv : String := "markdown tabular"

/-- The environment a markdown disclosure desugars to. -/
public def markdownDisclosureEnv : String := "markdown details"

/-- The environment a Lean statement's words lay out in, one nested in it a block one step in. -/
public def linesEnv : String := "prose lines"

/-- The control a markdown reference list desugars to: `\bibliography` without LaTeX's `\refname`
heading, unforgeable because it holds a space. -/
public def markdownBibControl : String := "markdown bibliography"

/-- The control carrying a citation setup to the elaborator, unforgeable as it holds a space. -/
public def citeSetupMark : String := "citation setup"

/-- The control a markdown image whose alternative cites desugars to, then its alternative's group
and its file's, unforgeable because it holds a space. -/
public def markdownImageControl : String := "markdown image"

/-- A citation setup as the raws that carry it: its mark, then a group of a word per declaration. -/
public def citeSetupRaws (ds : Array CiteDecl) (pos : Pos) : Array Raw :=
  #[.ctrl citeSetupMark pos, .group (ds.map fun d => .word d.spelling pos) pos]

/-- The declarations a carried setup's group spells. -/
public def citeSetupOf (body : Array Raw) : Array CiteDecl :=
  body.filterMap fun
    | .word w _ => CiteDecl.ofSpelling? w
    | _ => none

/-- Whether an environment is one only the markdown reader writes. -/
@[expose] public def markdownEnv (name : String) : Bool :=
  name == markdownTableEnv || name == markdownDisclosureEnv

/-- The verbatim environment standing for raws the compatibility pass leaves alone until they return,
unforgeable because its name holds a space. -/
public def keptEnv : String := "kept raws"

/-- Where the `k`th raws the compatibility pass leaves alone return. -/
@[expose] public def keptRaw (k : Nat) (p : Pos) : Raw := .verb keptEnv (.plain (toString k)) p

/-- A raw under the macro invocations `os`, outermost first, before its own. -/
@[expose] public def withOrigins (os : List MacroOrigin) (r : Raw) : Raw := os.foldr markMacro r

mutual

/-- A raw with each place of raws the compatibility pass left alone replaced by those raws, under
the invocations enclosing the place. -/
@[expose] public def spliceKept (kept : Array (Array Raw)) : Raw → Array Raw
  | .verb e s p =>
    match if e == keptEnv then s.text.toNat?.bind (kept[·]?) else none with
    | some rs => rs.map (withOrigins p.origins)
    | none => #[.verb e s p]
  | .group body p => #[.group (spliceKeptList kept #[] body.toList) p]
  | .env n body p => #[.env n (spliceKeptList kept #[] body.toList) p]
  | .math d body p => #[.math d (spliceKeptList kept #[] body.toList) p]
  | .word s p => #[.word s p]
  | .space => #[.space]
  | .par p => #[.par p]
  | .ctrl n p => #[.ctrl n p]
  | .sym c p => #[.sym c p]

@[expose] public def spliceKeptList (kept : Array (Array Raw)) (acc : Array Raw) :
    List Raw → Array Raw
  | [] => acc
  | r :: rest => spliceKeptList kept (acc ++ spliceKept kept r) rest

end

/-- The index past the leading run of `.space` raws at `i`. -/
@[expose] public def skipSpaces (raws : Array Raw) (i : Nat) : Nat :=
  if h : i < raws.size then
    if raws[i] matches .space then skipSpaces raws (i + 1) else i
  else i
termination_by raws.size - i

public theorem skipSpaces_ge (raws : Array Raw) (i : Nat) : i ≤ skipSpaces raws i := by
  fun_induction skipSpaces raws i <;> omega

/-- A raw run without its leading and trailing spaces. -/
public def trimSpace (rs : Array Raw) : Array Raw :=
  ((rs.toList.dropWhile (· matches .space)).reverse.dropWhile (· matches .space)).reverse.toArray

/-- A run's raws with a space after `acc` as the lexer reads one: none after a control word but a
text symbol, or after another space. -/
private def pushSpelledSpace (acc : Array Raw) : Array Raw :=
  match acc.back? with
  | some (.ctrl n _) =>
    if (n.length == 1 && !Lex.nameChar n.front) || (Lex.textSymbols.lookup n).isSome then acc.push .space
    else acc
  | some .space => acc
  | _ => acc.push .space

/-- Raws as the lexer reads their spelling back: a paragraph break a space, a run of spaces one,
none after a control word, each body without spaces at its ends; a control space stands once. -/
public def asSpelled : List Raw → Array Raw → Array Raw
  | [], acc => acc
  | .par _ :: rest, acc | .space :: rest, acc => asSpelled rest (pushSpelledSpace acc)
  | .group b p :: rest, acc => asSpelled rest (acc.push (.group (trimSpace (asSpelled b.toList #[])) p))
  | .math d b p :: rest, acc =>
    asSpelled rest (acc.push (.math d (trimSpace (asSpelled b.toList #[])) p))
  | .env n b p :: rest, acc =>
    asSpelled rest (acc.push (.env n (trimSpace (asSpelled b.toList #[])) p))
  | r :: rest, acc => asSpelled rest (acc.push r)
termination_by l => sizeOf l
decreasing_by raws_dec

/-- A raw run cut at its commas outside groups, inside words and standing alone; each word piece
stands at its own column, and empty pieces are dropped. -/
public def rawEntries (rs : Array Raw) : Array (Array Raw) := Id.run do
  let mut out := #[]
  let mut current := #[]
  for r in rs do
    match r with
    | .word s p =>
      let mut p := p
      let mut first := true
      for part in s.splitOn "," do
        unless first do
          out := out.push current
          current := #[]
          p := p.next false
        unless part.isEmpty do current := current.push (.word part p)
        p := { p with col := p.col + part.length }
        first := false
    | .sym ',' _ =>
      out := out.push current
      current := #[]
    | _ => current := current.push r
  return out.push current

@[expose] public def isBlankRaw : Raw → Bool
  | .space | .par _ => true
  | _ => false

@[expose] public def isCtrlSpace : Raw → Bool
  | .ctrl n _ => n == " "
  | _ => false

/-- Whether a list's last token past its blanks is a control space, whose name a trim would cut. -/
@[expose] public def endsCtrlSpace : List Raw → Bool
  | [] => false
  | r :: rest => if rest.all isBlankRaw then isCtrlSpace r else endsCtrlSpace rest

mutual

@[expose] public def rawSrc (raws : Array Raw) : String :=
  (rawSrcList raws.toList).trimAscii.toString

@[expose] public def rawSrcList (rs : List Raw) : String :=
  match rs with
  | [] => ""
  | r :: rest => rawSrcOne r ++ rawSrcList rest

@[expose] public def rawSrcOne (r : Raw) : String :=
  match r with
  | .word s _ => s
  | .space => " "
  | .par _ => " "
  | .sym c _ => String.ofList [c]
  | .ctrl n _ =>
    if n.length == 1 && !Lex.nameChar n.front && n != " " then "\\" ++ n else "\\" ++ n ++ " "
  | .group body _ => "{" ++ rawSrc body ++ (if endsCtrlSpace body.toList then " " else "") ++ "}"
  | .math d body p =>
    let inner := rawSrc body
    if p.command == some modeBranch then inner ++ "\\else "
    else if d then s!"\\[{inner}\\]" else s!"${inner}$"
  | .env n body _ =>
    if n == scopeEnv then "{" ++ rawSrc body ++ (if endsCtrlSpace body.toList then " " else "") ++ "}"
    else if n == modeEnv then "\\ifmmode " ++ rawSrcList body.toList ++ "\\fi "
    else s!"\\begin\{{n}}" ++ rawSrc body ++ s!"\\end\{{n}}"
  | .verb env v _ =>
    let s := v.spelling
    if env == "verb" then
      let d := (['|', '!', '+', '=', '/', '"', '@'].find? (fun c => !s.contains c)).getD '|'
      s!"\\verb{d}{s}{d}"
    else if env == "mintinline" || env == "mint" || env == "lstinline" || Lex.urlCommands.contains env
      then "\\" ++ env ++ s
    else s!"\\begin\{{env}}{s}\\end\{{env}}"

end

mutual

/-- `rawSrc` onto an accumulator, in time linear in the source it spells. -/
public def rawSrcOnto (raws : Array Raw) : String :=
  (rawSrcOntoList "" raws.toList).trimAscii.toString

public def rawSrcOntoList (acc : String) (rs : List Raw) : String :=
  match rs with
  | [] => acc
  | r :: rest => rawSrcOntoList (acc ++ rawSrcOneOnto r) rest

public def rawSrcOneOnto (r : Raw) : String :=
  match r with
  | .word s _ => s
  | .space => " "
  | .par _ => " "
  | .sym c _ => String.ofList [c]
  | .ctrl n _ =>
    if n.length == 1 && !Lex.nameChar n.front && n != " " then "\\" ++ n else "\\" ++ n ++ " "
  | .group body _ =>
    "{" ++ rawSrcOnto body ++ (if endsCtrlSpace body.toList then " " else "") ++ "}"
  | .math d body _ =>
    let inner := rawSrcOnto body
    if d then s!"\\[{inner}\\]" else s!"${inner}$"
  | .env n body _ =>
    if n == scopeEnv then
      "{" ++ rawSrcOnto body ++ (if endsCtrlSpace body.toList then " " else "") ++ "}"
    else s!"\\begin\{{n}}" ++ rawSrcOnto body ++ s!"\\end\{{n}}"
  | .verb env v p => rawSrcOne (.verb env v p)

end

mutual

private theorem rawSrcOnto_eq (raws : Array Raw) : rawSrc raws = rawSrcOnto raws := by
  rw [rawSrc, rawSrcOnto, ← rawSrcOntoList_eq "" raws.toList, String.empty_append]

private theorem rawSrcOntoList_eq (acc : String) (rs : List Raw) :
    acc ++ rawSrcList rs = rawSrcOntoList acc rs := by
  match rs with
  | [] => simp [rawSrcList, rawSrcOntoList]
  | r :: rest =>
    rw [rawSrcList, rawSrcOntoList, ← rawSrcOntoList_eq _ rest, ← rawSrcOneOnto_eq r,
      String.append_assoc]

private theorem rawSrcOneOnto_eq (r : Raw) : rawSrcOne r = rawSrcOneOnto r := by
  match r with
  | .word s _ | .space | .par _ | .sym c _ | .ctrl n _ => rfl
  | .group body _ => simp only [rawSrcOne, rawSrcOneOnto, rawSrcOnto_eq body]
  | .math d body _ => simp only [rawSrcOne, rawSrcOneOnto, rawSrcOnto_eq body]
  | .env n body _ => simp only [rawSrcOne, rawSrcOneOnto, rawSrcOnto_eq body]
  | .verb env v _ => rfl

end

@[csimp] public theorem rawSrc_onto : @rawSrc = @rawSrcOnto := by
  funext raws; exact rawSrcOnto_eq raws

/-- `rawSrcList` as the compiled program runs it. -/
public def rawSrcListOnto (rs : List Raw) : String := rawSrcOntoList "" rs

@[csimp] public theorem rawSrcList_onto : @rawSrcList = @rawSrcListOnto := by
  funext rs; rw [rawSrcListOnto, ← rawSrcOntoList_eq, String.empty_append]

@[csimp] public theorem rawSrcOne_onto : @rawSrcOne = @rawSrcOneOnto := by
  funext r; exact rawSrcOneOnto_eq r

/-- A declaration's group as its reader reads it: one word as written, else its tokens' source. -/
@[expose] public def declSrc (raws : Array Raw) : String :=
  match raws.toList with
  | [] => ""
  | [.word w _] => w
  | _ => rawSrc raws

public theorem scopeEnv_source_exact (body : Array Raw) (p : Pos) :
    rawSrcOne (.env scopeEnv body p) = rawSrcOne (.group body p) := by
  simp only [rawSrcOne, BEq.rfl, ↓reduceIte]

private theorem endsCtrlSpace_map (origin : MacroOrigin) (rs : List Raw) :
    endsCtrlSpace (rs.map (markMacro origin)) = endsCtrlSpace rs := by
  induction rs with
  | nil => rfl
  | cons r rest ih =>
    have hb : isBlankRaw ∘ markMacro origin = isBlankRaw := by
      funext x; cases x <;> rfl
    have hr : isCtrlSpace (markMacro origin r) = isCtrlSpace r := by cases r <;> rfl
    simp only [List.map_cons, endsCtrlSpace, List.all_map, hb, hr, ih]

private theorem endsCtrlSpace_markMacro (origin : MacroOrigin) (rs : List Raw) :
    endsCtrlSpace (markMacroList origin #[] rs).toList = endsCtrlSpace rs := by
  rw [markMacroList_toList, Array.toList_empty, List.nil_append, endsCtrlSpace_map]

mutual

public theorem markMacroArray_source_exact (origin : MacroOrigin) (raws : Array Raw) :
    rawSrc (markMacroList origin #[] raws.toList) = rawSrc raws := by
  simp only [rawSrc, markMacroList_toList, List.nil_append]
  rw [markMacroList_source_exact]

public theorem markMacroList_source_exact (origin : MacroOrigin) (rs : List Raw) :
    rawSrcList (rs.map (markMacro origin)) = rawSrcList rs := by
  cases rs with
  | nil => rfl
  | cons r rest =>
    simp only [List.map_cons, rawSrcList]
    rw [markMacro_source_exact, markMacroList_source_exact]

public theorem markMacro_source_exact (origin : MacroOrigin) (r : Raw) :
    rawSrcOne (markMacro origin r) = rawSrcOne r := by
  cases r <;> simp only [markMacro, rawSrcOne, markMacroArray_source_exact, markMacroList_toList,
    List.nil_append, markMacroList_source_exact, endsCtrlSpace_map]

end

end LeanTex.Core.Parse
