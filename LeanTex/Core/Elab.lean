import LeanTex.Core.Lex
import LeanTex.Core.Parse
import LeanTex.Core.Ir
import LeanTex.Core.Dim
import LeanTex.Core.Decl
import LeanTex.Core.Compat

namespace LeanTex.Core.Elab

open LeanTex.Core LeanTex.Core.Parse LeanTex.Core.Ir LeanTex.Core.Dim

inductive ParamType where
  | text
  | content
  deriving Repr, BEq

structure Param where
  name : String
  type : ParamType
  optional : Bool
  deriving Repr, BEq

structure UserCmd where
  name : String
  params : Array Param
  body : Array Raw
  deriving Repr, BEq

/-- A user command sees only commands defined before it: `limit` bounds the
visible prefix of `user`. That rule is what makes expansion terminate. -/
structure Ctx where
  file : String
  user : Array UserCmd := #[]
  limit : Nat := 0
  args : Array (String × Option (Array Inline)) := #[]
  /-- Palette names usable as colour commands, from `\palette`. -/
  palette : Palette := {}
  /-- Named lengths from `\tokens`. -/
  tokens : Tokens := {}
  /-- Inside mono/verbatim content, where punctuation stays literal. -/
  literalText : Bool := false

structure ESt where
  diags : Array Diag := #[]
  /-- Unknown commands already warned about: a macro used forty times is one
  problem, not forty. -/
  warnedUnknown : Array String := #[]

abbrev EM := StateM ESt

private def diag (ctx : Ctx) (code msg : String) (pos : Option Pos)
    (help : Option String := none) (sev : Severity := .error) : EM Unit :=
  modify fun st => { st with diags := st.diags.push {
    severity := sev
    code := code
    message := msg
    span := pos.map (⟨ctx.file, ·⟩)
    help := help
  } }

def reservedCtrl : List (String × String) :=
  [("vspace", "M3"), ("noindent", "M3"),
   ("fontfallback", "M5"), ("figure", "M5"), ("note", "M5")]

/-- Declarations that take a `{...}` block and are handled in the preamble. -/
def declCtrl : List String :=
  ["page", "pdfmeta", "assert", "fonts", "palette", "tokens", "style", "output"]

/-- Preamble declarations that take one group of *inline content* rather than
a key/value block: running head and foot. -/
def runningCtrl : List String := ["runninghead", "runningfoot"]

def pageKeys : List String :=
  ["size", "width", "height", "margin", "vmargin", "hmargin", "leading"]

/-- Page keys that are declared but not implemented yet, with the milestone
that will land them. Reported as pending, never as a type error. -/
def pagePending : List (String × String) := []

def metaKeys : List String := ["title", "author", "subject", "keywords"]

def fontKeys : List String := ["body", "sans", "mono", "rm", "sf", "tt"]

/-- Named page sizes, in sp. -/
def pageSizes : List (String × (Sp × Sp)) :=
  [("letter", (pt 612, pt 792)),
   ("legal", (pt 612, pt 1008)),
   ("a4", (Dim.pt 595, Dim.pt 842)),
   ("a5", (Dim.pt 420, Dim.pt 595))]

def reservedEnv : List (String × String) :=
  [("frame", "M5"), ("verbatim", "M5"), ("external", "M5")]

def argStyles : List (String × Style) :=
  [("textbf", .bold), ("textit", .italic), ("texttt", .mono), ("emph", .emph)]

def declStyles : List (String × Style) :=
  [("bfseries", .bold), ("itshape", .italic), ("ttfamily", .mono),
   ("scshape", .smallcaps), ("sffamily", .sans), ("sans", .sans),
   ("normalfont", .normal)] ++
  (["tiny", "scriptsize", "footnotesize", "small", "normalsize", "large",
    "Large", "LARGE", "huge", "Huge"].map fun n => (n, Style.size n))

def escapes : List (String × String) :=
  [("%", "%"), ("{", "{"), ("}", "}"), ("$", "$"), ("&", "&"), ("#", "#"),
   ("_", "_"), ("~", "~"), (" ", " "),
   -- Control-symbol spaces, TeX's spelling. Fixed widths, so they are text.
   (",", "\u2009"), (":", "\u2005"), (";", "\u2004")]

def blockOnly : List String :=
  ["section", "subsection", "subsubsection", "item", "documentclass", "define",
   "block"]

def builtinNames : List String :=
  ["begin", "end", "par", "define", "ifgiven", "documentclass", "textcolor",
   -- Underline is native; a document's own \varul (soul-style) is ignored.
   "underline", "uline", "ul", "varul"] ++
  blockOnly ++ (escapes.map (·.1)) ++ (argStyles.map (·.1)) ++
  (declStyles.map (·.1)) ++ (reservedCtrl.map (·.1)) ++ declCtrl ++
  (Lex.textSymbols.map (·.1))

private def lookupUser (ctx : Ctx) (name : String) : Option (Nat × UserCmd) := Id.run do
  let mut k := ctx.limit
  for _ in [0:ctx.limit] do
    k := k - 1
    if h : k < ctx.user.size then
      if ctx.user[k].name == name then
        return some (k, ctx.user[k])
  return none

-- Best-effort source text of raw content (math bodies, class options).
-- Structural recursion through `List`; the outer call trims, and so does each
-- nested group, matching what the elaborator has always emitted.

private def isSpace : Raw → Bool
  | .space => true
  | _ => false

private def isSpaceOrPar : Raw → Bool
  | .space => true
  | .par _ => true
  | _ => false

private def skipSpaces (raws : Array Raw) (i : Nat) : Nat := Id.run do
  let mut j := i
  for _ in [i:raws.size] do
    if h : j < raws.size then
      if isSpace raws[j] then j := j + 1 else break
    else break
  return j

/-- Drop whitespace at both edges: a define body's braces delimit, the
padding inside them is not content. -/
private def trimRaws (raws : Array Raw) : Array Raw := Id.run do
  let mut a := 0
  for _ in [0:raws.size] do
    if h : a < raws.size then
      if isSpaceOrPar raws[a] then a := a + 1 else break
    else break
  let mut b := raws.size
  for _ in [0:raws.size] do
    if b > a && isSpaceOrPar raws[b - 1]! then b := b - 1 else break
  return raws.extract a b

private def allText (xs : Array Inline) : Bool :=
  xs.all fun x => match x with
    | .text _ => true
    | _ => false

/-- Typographic punctuation, applied to ordinary text. `--` and `---` are the
dashes an author means when they type them; `...` is an ellipsis; straight
quotes become the directional pair, chosen by what precedes them (so an
apostrophe in "don't" closes). Literal text (mono, verbatim) is exempt — that
is where a straight quote is the point. -/
def smartPunct (s : String) : String :=
  String.ofList (go s.toList [])
where
  /-- `prev` is the output so far, reversed: its head is the character just
  emitted, which is what decides quote direction. -/
  go : List Char → List Char → List Char
    | [], prev => prev.reverse
    | '-' :: '-' :: '-' :: rest, prev => go rest ('—' :: prev)
    | '-' :: '-' :: rest, prev => go rest ('–' :: prev)
    | '.' :: '.' :: '.' :: rest, prev => go rest ('…' :: prev)
    | '"' :: rest, prev =>
      let opening := match prev with
        | [] => true
        | c :: _ => c == ' ' || c == '(' || c == '[' || c == '—' || c == '–'
      go rest ((if opening then '“' else '”') :: prev)
    | '\'' :: rest, prev =>
      let opening := match prev with
        | [] => true
        | c :: _ => c == ' ' || c == '(' || c == '[' || c == '“'
      go rest ((if opening then '‘' else '’') :: prev)
    | c :: rest, prev => go rest (c :: prev)

private def flushText (acc : Array Inline) (sb : String) : Array Inline :=
  if sb == "" then acc else acc.push (.text sb)

private def mergeText (xs : Array Inline) : Array Inline := Id.run do
  let mut out : Array Inline := #[]
  for x in xs do
    match x, out.back? with
    | .text s, some (.text t) =>
      out := out.pop.push (.text (t ++ s))
    | _, _ => out := out.push x
  return out

/-- Skip `[...]` runs and at most one group: argument recovery after a
reserved (not yet implemented) command. -/
private def skipReservedArgs (raws : Array Raw) (i : Nat) : Nat := Id.run do
  let mut j := skipSpaces raws i
  if let some (.sym '[' _) := raws[j]? then
    for _ in [j:raws.size] do
      j := j + 1
      if let some (.sym ']' _) := raws[j - 1]? then
        break
    j := skipSpaces raws j
  if let some (.group _ _) := raws[j]? then
    j := j + 1
  return j

-- Inline elaboration and argument binding are mutually recursive: a call
-- site's arguments are themselves inline content. Nontermination is
-- impossible by design (a body sees only earlier definitions), but the
-- checker cannot see that yet: de-partialing is scheduled proof work.
mutual

/-- Bind a user command's declared parameters from the call site. Returns the
bindings and the index just past the consumed arguments. Shared by inline and
block expansion so both bind identically. -/
partial def takeArgs (ctx : Ctx) (cmd : UserCmd) (name : String)
    (raws : Array Raw) (start : Nat) (pos : Pos) :
    EM (Array (String × Option (Array Inline)) × Nat) := do
  let mut bindings : Array (String × Option (Array Inline)) := #[]
  let mut i := start
  for p in cmd.params do
    if p.optional then
      let j := skipSpaces raws i
      match raws[j]? with
      | some (.sym '[' _) =>
        let mut body : Array Raw := #[]
        let mut k' := j + 1
        let mut closed := false
        for _ in [j:raws.size] do
          match raws[k']? with
          | some (.sym ']' _) =>
            closed := true
            k' := k' + 1
            break
          | some r' =>
            body := body.push r'
            k' := k' + 1
          | none => break
        unless closed do
          diag ctx "E0316" s!"unclosed optional argument for '\\{name}'" pos
        i := k'
        let v ← elabInlines ctx body
        if p.type == .text && !allText v then
          diag ctx "E0305" s!"parameter '{p.name}' of '\\{name}' expects text" pos
        bindings := bindings.push (p.name, some v)
      | _ =>
        bindings := bindings.push (p.name, none)
    else
      let j := skipSpaces raws i
      match raws[j]? with
      | some (.group body _) =>
        i := j + 1
        let v ← elabInlines ctx body
        if p.type == .text && !allText v then
          diag ctx "E0305" s!"parameter '{p.name}' of '\\{name}' expects text" pos
        bindings := bindings.push (p.name, some v)
      | some (.word s _) =>
        i := j + 1
        bindings := bindings.push (p.name, some #[.text s])
      | _ =>
        diag ctx "E0304" s!"missing argument '{p.name}' for '\\{name}'" pos
        bindings := bindings.push (p.name, some #[])
  return (bindings, i)

/-- Elaborate raw items as inline content. -/
partial def elabInlines (ctx : Ctx) (raws : Array Raw) : EM (Array Inline) := do
  let mut acc : Array Inline := #[]
  let mut sb : String := ""
  let mut i := 0
  repeat
    if h : i < raws.size then
      let r := raws[i]
      match r with
      | .word s _ =>
        sb := sb ++ s
        i := i + 1
      | .space =>
        sb := sb.push ' '
        i := i + 1
      | .par _ =>
        sb := sb.push ' '
        i := i + 1
      | .sym '[' _ =>
        sb := sb.push '['
        i := i + 1
      | .sym ']' _ =>
        sb := sb.push ']'
        i := i + 1
      | .sym '~' _ =>
        -- Every LaTeX author means a non-breaking space by `~`, and reserving
        -- it buys nothing: there is no catcode machinery here to reserve it for.
        sb := sb.push '\u00a0'
        i := i + 1
      | .sym c pos =>
        diag ctx "E0311" s!"reserved character '{c}'" pos (help := s!"escape it as '\\{c}'")
        i := i + 1
      | .math d body _ =>
        acc := flushText acc sb
        sb := ""
        acc := acc.push (.math d (rawSrc body))
        i := i + 1
      | .group body _ =>
        acc := flushText acc sb
        sb := ""
        acc := acc ++ (← elabInlines ctx body)
        i := i + 1
      | .env name body pos =>
        i := i + 1
        match reservedEnv.lookup name with
        | some milestone =>
          diag ctx "E0307" s!"'\{{name}}' is not implemented yet" pos
            (help := s!"planned for {milestone}; see PLAN.md")
        | none =>
          diag ctx "E0302" s!"unknown environment '{name}'" pos
          acc := flushText acc sb
          sb := ""
          acc := acc ++ (← elabInlines ctx body)
      | .verb _ pos =>
        diag ctx "E0307" "'{verbatim}' is not implemented yet" pos
          (help := "planned for M5; see PLAN.md")
        i := i + 1
      | .ctrl name pos =>
        i := i + 1
        if name == "hfill" then
          acc := flushText acc sb
          sb := ""
          acc := acc.push .fill
        else if name == "\\" || name == "par" then
          -- `\\[len]` adds space after the break. The bracket must be
          -- adjacent: LaTeX skips spaces here and so swallows the `[` of a
          -- line that legitimately starts with one.
          let mut extra : SymGlue := {}
          if name == "\\" then
            if let some (.sym '[' _) := raws[i]? then
              let mut optSrc : Array Raw := #[]
              let mut k := i + 1
              for _ in [k:raws.size + 1] do
                match raws[k]? with
                | some (.sym ']' _) =>
                  k := k + 1
                  break
                | some r' =>
                  optSrc := optSrc.push r'
                  k := k + 1
                | none => break
              i := k
              let src := rawSrc optSrc
              match Decl.parseValue src ctx.tokens.entries with
              | some (.glue g) => extra := g
              | some (.dim d) => extra := { width := Dim.Length.ofSp d }
              | _ =>
                diag ctx "E0331" s!"cannot read a length from '{src}'" pos
                  (help := "lengths look like 10pt or 1.5ex, or name a token")
          acc := flushText acc sb
          sb := ""
          acc := acc.push (.linebreak extra)
          -- Whitespace after a break is the source's line ending, not content;
          -- keeping it would open the next line with a stray space.
          for _ in [i:raws.size] do
            if let some .space := raws[i]? then i := i + 1 else break
        else if let some lit := escapes.lookup name then
          sb := sb ++ lit
        else if (lookupUser ctx name).isNone && (Lex.textSymbols.lookup name).isSome then
          -- A document may define a symbol's name for itself; its definition
          -- wins, so the symbol only fires when nothing shadows it.
          sb := sb ++ (Lex.textSymbols.lookup name).getD ""
        else if let some style := argStyles.lookup name then
          let argCtx := if style == Style.mono then { ctx with literalText := true } else ctx
          let j := skipSpaces raws i
          match raws[j]? with
          | some (.group body _) =>
            acc := flushText acc sb
            sb := ""
            acc := acc.push (.styled style (← elabInlines argCtx body))
            i := j + 1
          | some (.word s _) =>
            acc := flushText acc sb
            sb := ""
            acc := acc.push (.styled style #[.text s])
            i := j + 1
          | _ =>
            diag ctx "E0304" s!"'\\{name}' needs an argument" pos
        else if name == "underline" || name == "uline" then
          -- Drawn, not a face change, so not a Style: one group, like \textbf.
          let j := skipSpaces raws i
          match raws[j]? with
          | some (.group body _) =>
            acc := flushText acc sb
            sb := ""
            acc := acc.push (.underline (← elabInlines ctx body))
            i := j + 1
          | some (.word s _) =>
            acc := flushText acc sb
            sb := ""
            acc := acc.push (.underline #[.text s])
            i := j + 1
          | _ =>
            diag ctx "E0304" s!"'\\{name}' needs an argument" pos
        else if name == "href" || name == "link" then
          let j := skipSpaces raws i
          let j2 := skipSpaces raws (j + 1)
          match raws[j]?, raws[j2]? with
          | some (.group urlRaw _), some (.group body _) =>
            i := j2 + 1
            acc := flushText acc sb
            sb := ""
            acc := acc.push (.link (rawSrc urlRaw) (← elabInlines ctx body))
          | some (.group urlRaw _), _ =>
            -- One argument: the URL is also the text, which is the common case
            -- for a bare link and saves writing it twice.
            i := j + 1
            let url := rawSrc urlRaw
            acc := flushText acc sb
            sb := ""
            acc := acc.push (.link url #[.text url])
          | _, _ =>
            diag ctx "E0304" s!"'\\{name}' needs a URL group, optionally followed by text" pos
        else if name == "pagenumber" then
          acc := flushText acc sb
          sb := ""
          acc := acc.push .pageNumber
        else if name == "pagecount" then
          acc := flushText acc sb
          sb := ""
          acc := acc.push .pageCount
        else if name == "textcolor" then
          let j := skipSpaces raws i
          let j2 := skipSpaces raws (j + 1)
          match raws[j]?, raws[j2]? with
          | some (.group cname _), some (.group body _) =>
            i := j2 + 1
            let key := (rawSrc cname).trimAscii.toString
            match ctx.palette.find? key with
            | some c =>
              acc := flushText acc sb
              sb := ""
              acc := acc.push (.colored c (some key) (← elabInlines ctx body))
            | none =>
              diag ctx "E0326" s!"'{key}' is not in the palette" pos
                (help := s!"declared: {String.intercalate ", "
                  (ctx.palette.entries.toList.map (·.1))}")
          | _, _ =>
            diag ctx "E0304" "'\\textcolor' needs {name} and {content}" pos
        else if let some c := ctx.palette.find? name then
          -- With a group, that group is the argument: `\primary{Alex}` means
          -- colour Alex, which is what it looks like. Without one it is a
          -- declaration colouring the rest of the group, as `\bfseries` does.
          let j := skipSpaces raws i
          match raws[j]? with
          | some (.group body _) =>
            acc := flushText acc sb
            sb := ""
            acc := acc.push (.colored c (some name) (← elabInlines ctx body))
            i := j + 1
          | _ =>
            let rest ← elabInlines ctx (raws.extract i raws.size)
            acc := flushText acc sb
            sb := ""
            acc := acc.push (.colored c (some name) rest)
            i := raws.size
        else if let some style := declStyles.lookup name then
          let declCtx := if style == Style.mono then { ctx with literalText := true } else ctx
          let rest ← elabInlines declCtx (raws.extract i raws.size)
          acc := flushText acc sb
          sb := ""
          acc := acc.push (.styled style rest)
          i := raws.size
        else if name == "ifgiven" then
          let j := skipSpaces raws i
          let j2 := skipSpaces raws (j + 1)
          match raws[j]?, raws[j2]? with
          | some (.group cond _), some (.group tmpl _) =>
            i := j2 + 1
            let refs := cond.filter (!isSpace ·)
            match refs.toList with
            | [.ctrl pname _] =>
              match ctx.args.find? (·.1 == pname) with
              | some (_, some _) => acc := acc ++ (← elabInlines ctx tmpl)
              | some (_, none) => pure ()
              | none => diag ctx "E0306" s!"unknown parameter '\\{pname}'" pos
            | _ =>
              diag ctx "E0306" "expected a parameter reference like {\\team}" pos
          | _, _ =>
            diag ctx "E0304" "'\\ifgiven' needs {\\param} and {content}" pos
        else if let some (_, binding) := ctx.args.find? (·.1 == name) then
          acc := flushText acc sb
          sb := ""
          if let some inlines := binding then
            acc := acc ++ inlines
        else if let some (k, cmd) := lookupUser ctx name then
          acc := flushText acc sb
          sb := ""
          let (bindings, j) ← takeArgs ctx cmd name raws i pos
          i := j
          let callCtx : Ctx := { ctx with limit := k, args := bindings }
          acc := acc ++ (← elabInlines callCtx cmd.body)
        else if let some milestone := reservedCtrl.lookup name then
          diag ctx "E0307" s!"'\\{name}' is not implemented yet" pos
            (help := s!"planned for {milestone}; see PLAN.md")
          i := skipReservedArgs raws i
        else if blockOnly.contains name then
          diag ctx "E0312" s!"'\\{name}' is not allowed here" pos
            (help := "it is a block-level command: use it between paragraphs, " ++
              "not inside inline content or a command body")
        else
          -- Best effort: the arguments are content, and content is never
          -- dropped for want of a command. Only the formatting is lost.
          unless (← get).warnedUnknown.contains name do
            modify fun st => { st with warnedUnknown := st.warnedUnknown.push name }
            modify fun st => { st with diags := st.diags.push {
              severity := .warning, code := "W0301"
              message := s!"unknown command '\\{name}'; its arguments were kept as text"
              span := some ⟨ctx.file, pos⟩
              help := some "define it with \\define, or see PLAN.md for planned commands" } }
          let mut j := skipSpaces raws i
          let mut kept := 0
          for _ in [0:9] do
            match raws[j]? with
            | some (.group body _) =>
              acc := flushText acc sb
              -- Whatever separated the arguments visually is gone with the
              -- command, so a space stands in; without one, `{a}{b}` runs
              -- together as `ab`.
              sb := if kept > 0 then " " else ""
              acc := flushText acc sb
              sb := ""
              acc := acc ++ (← elabInlines ctx body)
              kept := kept + 1
              j := skipSpaces raws (j + 1)
            | _ => break
          -- The control word swallowed the space after it; give one back so
          -- the kept text does not fuse with what follows.
          if kept > 0 && j < raws.size then
            sb := " "
          i := j
    else
      break
  let out := mergeText (flushText acc sb)
  return if ctx.literalText then out else out.map mapText
where
  /-- Applied to this level's own text only; nested bodies were processed by
  their own call, with their own literal-text setting. -/
  mapText (x : Inline) : Inline :=
    match x with
    | .text t => .text (smartPunct t)
    | other => other

end

/-- Block environments: those whose content is a block sequence. -/
def blockEnvs : List String := ["itemize", "enumerate", "center", "document"]

/-- Does this body produce block-level content? Decides whether a user command
called between paragraphs expands as blocks or as inline content. A purely
inline macro must stay inline, or `\role{Ada} and more text` would split the
paragraph. -/
def bodyIsBlock (raws : Array Raw) : Bool :=
  raws.any fun r =>
    match r with
    | .ctrl n _ => n == "block" || ["section", "subsection", "subsubsection"].contains n
    | .env n _ _ => blockEnvs.contains n
    | _ => false

private def sectionLevel : String → Option Nat
  | "section" => some 1
  | "subsection" => some 2
  | "subsubsection" => some 3
  | _ => none

private def mkPara (ctx : Ctx) (cur : Array Raw) : EM (Option Block) := do
  let mut cur := cur
  repeat
    match cur.back? with
    | some .space => cur := cur.pop
    | some (.par _) => cur := cur.pop
    | _ => break
  if cur.isEmpty then
    return none
  let inlines ← elabInlines ctx cur
  return if inlines.isEmpty then none else some (.para inlines)

/-- Elaborate raw items as a block sequence. -/
partial def elabBlocks (ctx : Ctx) (raws : Array Raw) : EM (Array Block) := do
  let mut blocks : Array Block := #[]
  let mut cur : Array Raw := #[]
  let mut i := 0
  repeat
    if h : i < raws.size then
      let r := raws[i]
      let isBoundary : Bool :=
        match r with
        | .par _ => true
        | .ctrl "par" _ => true
        | .ctrl "block" _ => true
        | .ctrl n _ =>
          (sectionLevel n).isSome ||
          -- A user command whose body produces blocks is itself a boundary.
          (match lookupUser ctx n with
           | some (_, cmd) => bodyIsBlock cmd.body
           | none => false)
        | .env n _ _ =>
          n == "itemize" || n == "enumerate" || n == "center" ||
          (reservedEnv.lookup n).isSome
        | _ => false
      if !isBoundary then
        unless cur.isEmpty && isSpaceOrPar r do
          cur := cur.push r
        i := i + 1
      else
        if !cur.isEmpty then
          if let some p ← mkPara ctx cur then
            blocks := blocks.push p
          cur := #[]
        match r with
        | .par _ =>
          i := i + 1
        | .ctrl "par" _ =>
          i := i + 1
        | .ctrl "block" pos =>
          i := i + 1
          -- \block[before = <len>]{content}
          let mut before : SymGlue := {}
          let mut j := skipSpaces raws i
          if let some (.sym '[' _) := raws[j]? then
            let mut optSrc : Array Raw := #[]
            j := j + 1
            for _ in [j:raws.size] do
              match raws[j]? with
              | some (.sym ']' _) =>
                j := j + 1
                break
              | some r' =>
                optSrc := optSrc.push r'
                j := j + 1
              | none => break
            let (opts, ds) := Decl.parseBlock ctx.file (rawSrc optSrc) pos "block"
              ctx.tokens.entries
            modify fun st => { st with diags := st.diags ++ ds }
            for e in opts do
              match e.key, e.value with
              | "before", .glue g => before := g
              | "before", .dim d => before := { width := Dim.Length.ofSp d }
              | key, v =>
                if key == "before" then
                  modify fun st => { st with
                    diags := st.diags.push (Decl.wrongType ctx.file "block" key
                      "a length" v pos) }
                else
                  modify fun st => { st with
                    diags := st.diags.push (Decl.unknownKey ctx.file "block" key
                      ["before"] pos) }
            j := skipSpaces raws j
          match raws[j]? with
          | some (.group body _) =>
            i := j + 1
            blocks := blocks.push (.spaced before (← elabBlocks ctx body))
          | _ =>
            diag ctx "E0304" "'\\block' needs a {body}" pos
        | .ctrl n pos =>
          i := i + 1
          match lookupUser ctx n with
          | some (k, cmd) =>
            -- Block-producing user command: bind its arguments, then
            -- elaborate the body as blocks so `\block` inside a definition
            -- works instead of reporting E0312.
            let (bindings, j) ← takeArgs ctx cmd n raws i pos
            i := j
            let callCtx : Ctx := { ctx with limit := k, args := bindings }
            blocks := blocks ++ (← elabBlocks callCtx cmd.body)
          | none =>
          let level := (sectionLevel n).getD 1
          let mut starred := false
          if let some (.word "*" _) := raws[i]? then
            starred := true
            i := i + 1
          let j := skipSpaces raws i
          match raws[j]? with
          | some (.group title _) =>
            i := j + 1
            blocks := blocks.push (.section level starred (← elabInlines ctx title))
          | _ =>
            diag ctx "E0304" s!"'\\{n}' needs a \{title}" pos
        | .env n body pos =>
          i := i + 1
          if n == "itemize" || n == "enumerate" then
            let mut items : Array (Array Raw) := #[]
            let mut curItem : Array Raw := #[]
            let mut seen := false
            let mut strayDiagged := false
            for item in body do
              match item with
              | .ctrl "item" _ =>
                if seen then
                  items := items.push curItem
                curItem := #[]
                seen := true
              | _ =>
                if seen then
                  curItem := curItem.push item
                else if !isSpaceOrPar item && !strayDiagged then
                  diag ctx "E0310" s!"content before the first '\\item'" pos
                  strayDiagged := true
            if seen then
              items := items.push curItem
            let mut elabItems : Array (Array Block) := #[]
            for it in items do
              elabItems := elabItems.push (← elabBlocks ctx it)
            blocks := blocks.push (.list (n == "enumerate") elabItems)
          else if n == "center" then
            blocks := blocks.push (.center (← elabBlocks ctx body))
          else
            diag ctx "E0307" s!"'\{{n}}' is not implemented yet" pos
              (help := s!"planned for {(reservedEnv.lookup n).getD "later"}; see PLAN.md")
        | _ =>
          i := i + 1
    else
      break
  if !cur.isEmpty then
    if let some p ← mkPara ctx cur then
      blocks := blocks.push p
  return blocks

private def parseSig (ctx : Ctx) (s : String) (pos : Pos) : EM (Array Param) := do
  let s := s.trimAscii.toString
  if s == "" || s == "()" then
    return #[]
  if !(s.startsWith "(" && s.endsWith ")") then
    diag ctx "E0303" s!"malformed signature '{s}'" pos
      (help := "expected (name: type, ..., opt?: type)")
    return #[]
  let inner := (String.ofList (s.toList.drop 1).dropLast).trimAscii.toString
  if inner == "" then
    return #[]
  let mut params : Array Param := #[]
  for entry in inner.splitOn "," do
    match entry.splitOn ":" with
    | [name, ty] =>
      let name := name.trimAscii.toString
      let ty := ty.trimAscii.toString
      let optional := name.endsWith "?"
      let name := if optional then (String.ofList name.toList.dropLast).trimAscii.toString else name
      let type? : Option ParamType :=
        if ty == "text" then some .text
        else if ty == "content" then some .content
        else none
      let wellFormed := match name.toList with
        | c :: rest => c.isAlpha && rest.all Char.isAlphanum
        | [] => false
      if !wellFormed then
        diag ctx "E0303" s!"invalid parameter name '{name}'" pos
          (help := "parameter names start with a letter")
      else
        match type? with
        | some t => params := params.push ⟨name, t, optional⟩
        | none =>
          diag ctx "E0303" s!"unknown parameter type '{ty}' for '{name}'" pos
            (help := "types: text | content")
    | _ =>
      diag ctx "E0303" s!"malformed parameter '{entry.trimAscii.toString}'" pos
        (help := "expected name: type")
  return params

/-- `\page{...}`: geometry. `size` names a standard page; `width`/`height`
override it; `margin` sets both axes, `vmargin`/`hmargin` one each. -/
private def applyPage (ctx : Ctx) (spec : PageSpec) (entries : Array Decl.Entry)
    (pos : Pos) : EM PageSpec := do
  let mut spec := spec
  for e in entries do
    match e.key, e.value with
    | "size", .ident name =>
      match pageSizes.lookup name.toLower with
      | some (w, h) => spec := { spec with width := w, height := h }
      | none =>
        diag ctx "E0324" s!"unknown page size '{name}'" pos
          (help := s!"known sizes: {String.intercalate ", " (pageSizes.map (·.1))}")
    | "width", .dim d => spec := { spec with width := d }
    | "height", .dim d => spec := { spec with height := d }
    | "margin", .dim d => spec := { spec with vmargin := d, hmargin := d }
    | "vmargin", .dim d => spec := { spec with vmargin := d }
    | "hmargin", .dim d => spec := { spec with hmargin := d }
    | "leading", .int n => spec := { spec with leading := n.toNat * 1000 }
    | "leading", .dim d =>
      -- A bare decimal like 1.04 reads as a dimension in points; the factor
      -- is what was meant.
      spec := { spec with leading := (d * 1000 / pt 1).toNat }
    | "leading", .ident f =>
      -- ...and one without a unit reaches here as a name.
      match Decl.parseDecimal f with
      | some (m, s) => spec := { spec with leading := (m * 1000 / s).toNat }
      | none => diag ctx "E0323" s!"'leading' in \\page expects a factor like 1.04, got '{f}'" pos
    | key, v =>
      if key == "header" || key == "footer" then
        -- The feature exists, just not as a page key: running content is
        -- inline content, which a key/value block cannot carry.
        let cmd := if key == "header" then "\\runninghead" else "\\runningfoot"
        diag ctx "E0327" s!"'{key}' is not a \\page key" pos
          (help := s!"declare it as {cmd}\{...} — it takes inline content, " ++
            "so use \\hfill to push part of it to the right")
      else if pageKeys.contains key then
        let expected := if key == "size" then "a page size name" else "a dimension"
        modify fun st => { st with
          diags := st.diags.push (Decl.wrongType ctx.file "page" key expected v pos) }
      else
        modify fun st => { st with
          diags := st.diags.push (Decl.unknownKey ctx.file "page" key pageKeys pos) }
  return spec

/-- `\fonts{...}`: family names per slot. `rm`/`sf`/`tt` are accepted as
aliases so a LaTeX habit does not become an error. -/
private def applyFonts (ctx : Ctx) (spec : FontSpec) (entries : Array Decl.Entry)
    (pos : Pos) : EM FontSpec := do
  let mut spec := spec
  for e in entries do
    match e.key, e.value with
    | "body", .str f => spec := { spec with body := some f }
    | "rm", .str f => spec := { spec with body := some f }
    | "sans", .str f => spec := { spec with sans := some f }
    | "sf", .str f => spec := { spec with sans := some f }
    | "mono", .str f => spec := { spec with mono := some f }
    | "tt", .str f => spec := { spec with mono := some f }
    | key, v =>
      if fontKeys.contains key then
        modify fun st => { st with
          diags := st.diags.push (Decl.wrongType ctx.file "fonts" key
            "a quoted family name" v pos) }
      else
        modify fun st => { st with
          diags := st.diags.push (Decl.unknownKey ctx.file "fonts" key fontKeys pos) }
  return spec

/-- `\tokens{...}`: named lengths. Entries are walked one at a time so a
token may be defined by scaling an earlier one (`sep = 0.6 * rhythm`);
parsing the block in one shot would leave those references unresolved. -/
private def applyTokens (ctx : Ctx) (toks : Tokens) (src : String) (pos : Pos) :
    EM Tokens := do
  let mut acc : Array (String × SymGlue) := toks.entries
  for entry in Decl.splitEntries src do
    match Decl.splitEntry entry with
    | none =>
      diag ctx "E0320" s!"invalid entry in \\tokens: {entry.quote}" pos
        (help := "entries look like: name = length")
    | some (key, valueSrc) =>
      match Decl.parseValue valueSrc acc with
      | some (.glue g) => acc := acc.push (key, g)
      | some (.dim d) => acc := acc.push (key, { width := Dim.Length.ofSp d })
      | some v =>
        modify fun st => { st with
          diags := st.diags.push (Decl.wrongType ctx.file "tokens" key
            "a length (10pt, 1.5ex, 0.6 * other)" v pos) }
      | none =>
        diag ctx "E0321" s!"cannot read length for '{key}': {valueSrc.quote}" pos
          (help := "lengths look like 10pt, 1.5ex, 2em, or 0.6 * other-token")
  return { entries := acc }

def styleKeys : List String :=
  ["font", "before", "after", "rule", "marker", "indent", "gap"]

/-- `\style{element}{...}`: how an element kind looks. `font` and `marker`
are inline content and elaborate as such; the rest are lengths and a palette
colour. A length may name a token, so the entries are read one at a time
against the tokens declared so far. -/
private def applyStyle (ctx : Ctx) (styles : Styles) (element src : String) (pos : Pos) :
    EM Styles := do
  unless styleableElements.contains element do
    diag ctx "E0328" s!"'{element}' is not a styleable element" pos
      (help := s!"elements: {String.intercalate ", " styleableElements}")
    return styles
  let mut st : ElementStyle := (styles.find? element).getD {}
  for entry in Decl.splitEntries src do
    match Decl.splitEntry entry with
    | none =>
      diag ctx "E0320" s!"invalid entry in \\style: {entry.quote}" pos
        (help := "entries look like: key = value")
    | some (key, valueSrc) =>
      let asInline : EM (Option (Array Inline)) := do
        let inner := if valueSrc.startsWith "{" && valueSrc.endsWith "}" && valueSrc.length ≥ 2
          then (valueSrc.drop 1).dropEnd 1 |>.toString else valueSrc
        let (toks, _) := Lex.lex ctx.file inner
        let (raws, _) := Parse.parse ctx.file toks
        -- Value text re-enters through the same door as the document, idiom
        -- translation included, or a \color inside a font spec would leak.
        let (raws, ds) := Compat.rewrite ctx.file raws
        modify fun st => { st with diags := st.diags ++ ds.filter (·.severity != .note) }
        return some (← elabInlines ctx raws)
      let asLength : EM (Option SymGlue) := do
        match Decl.parseValue valueSrc ctx.tokens.entries with
        | some (.glue g) => return some g
        | some (.dim d) => return some { width := Dim.Length.ofSp d }
        | _ =>
          diag ctx "E0321" s!"cannot read length for '{key}' in \\style: {valueSrc.quote}" pos
            (help := "lengths look like 10pt, 1.5ex, or a token name")
          return none
      match key with
      | "font" => st := { st with font := ← asInline }
      | "marker" => st := { st with marker := ← asInline }
      | "before" => st := { st with before := ← asLength }
      | "after" => st := { st with after := ← asLength }
      | "indent" => st := { st with indent := ← asLength }
      | "gap" => st := { st with gap := ← asLength }
      | "rule" =>
        match ctx.palette.find? valueSrc with
        | some c => st := { st with rule := some (c, some valueSrc) }
        | none =>
          match Decl.parseValue valueSrc with
          | some (.color r g b) => st := { st with rule := some (⟨r, g, b⟩, none) }
          | _ => diag ctx "E0326" s!"'{valueSrc}' is not in the palette" pos
      | _ =>
        modify fun st' => { st' with
          diags := st'.diags.push (Decl.unknownKey ctx.file "style" key styleKeys pos) }
  let rest := styles.entries.filter (·.1 != element)
  return { entries := rest.push (element, st) }

/-- `\palette{...}`: named colours. Every entry becomes usable both as
`\textcolor{name}{...}` and as a bare `\name` declaration. -/
private def applyPalette (ctx : Ctx) (pal : Palette) (entries : Array Decl.Entry)
    (pos : Pos) : EM Palette := do
  let mut pal := pal
  for e in entries do
    match e.value with
    | .color r g b =>
      if builtinNames.contains e.key then
        diag ctx "E0303" s!"palette name '{e.key}' collides with a built-in command" pos
      else
        pal := { pal with entries := pal.entries.push (e.key, ⟨r, g, b⟩) }
    | .ident other =>
      -- An alias, so two names that must never drift apart share one value.
      match pal.find? other with
      | some c => pal := { pal with entries := pal.entries.push (e.key, c) }
      | none =>
        diag ctx "E0326" s!"'{other}' is not in the palette" pos
          (help := "declare it first; aliases read earlier entries")
    | v =>
      modify fun st => { st with
        diags := st.diags.push (Decl.wrongType ctx.file "palette" e.key
          "a color like #7C3AED" v pos) }
  return pal

/-- `\output{...}`: what to build, so a document needs no CLI options.
`formats` takes a bare comma list (`formats = pdf, html`), so entries are
walked by hand: an entry without `=` continues the list. -/
private def applyOutput (ctx : Ctx) (o0 : OutputSpec) (src : String) (pos : Pos) :
    EM OutputSpec := do
  let mut o := o0
  let mut inFormats := false
  let addFormat (o : OutputSpec) (f : String) : EM OutputSpec := do
    if ["pdf", "html"].contains f then
      return { o with
        formats := if o.formats.contains f then o.formats else o.formats.push f }
    diag ctx "E0321" s!"'{f}' is not an output format" pos
      (help := some "formats: pdf, html")
    return o
  for entry in Decl.splitEntries src do
    match Decl.splitEntry entry with
    | some ("formats", v) =>
      inFormats := true
      o ← addFormat o v
    | some ("css", v) =>
      inFormats := false
      if ["own", "bulma", "none"].contains v then
        o := { o with css := some v }
      else
        diag ctx "E0321" s!"'{v}' is not a stylesheet mode" pos
          (help := some "css: own | bulma | none")
    | some (key, _) =>
      inFormats := false
      modify fun st => { st with
        diags := st.diags.push (Decl.unknownKey ctx.file "output" key
          ["formats", "css"] pos) }
    | none =>
      if inFormats then
        o ← addFormat o entry
      else
        diag ctx "E0320" s!"invalid entry in \\output: {entry.quote}" pos
          (help := some "entries look like: formats = pdf, html")
  return o

/-- `\pdfmeta{...}`: PDF document information. -/
private def applyMeta (ctx : Ctx) (m0 : Meta) (entries : Array Decl.Entry)
    (pos : Pos) : EM Meta := do
  let mut m := m0
  for e in entries do
    match e.key, e.value with
    | "title", .str s => m := { m with title := some s }
    | "author", .str s => m := { m with author := some s }
    | "subject", .str s => m := { m with subject := some s }
    | "keywords", .str s => m := { m with keywords := some s }
    | key, v =>
      if metaKeys.contains key then
        modify fun st => { st with
          diags := st.diags.push (Decl.wrongType ctx.file "pdfmeta" key "a string" v pos) }
      else
        modify fun st => { st with
          diags := st.diags.push (Decl.unknownKey ctx.file "pdfmeta" key metaKeys pos) }
  return m

private def cmpOp : String → Option CmpOp
  | "==" => some .eq
  | "=" => some .eq
  | "!=" => some .ne
  | "<=" => some .le
  | "<" => some .lt
  | ">=" => some .ge
  | ">" => some .gt
  | _ => none

/-- `\assert{ ... }`: a layout invariant, checked against the shipped page
tree. Grammar is deliberately tiny: `pages <op> N`, or `fonts.all_embedded`. -/
private def parseAssert (ctx : Ctx) (src : String) (pos : Pos) : EM (Option Assertion) := do
  let words := (src.splitOn " ").filterMap fun w =>
    let t := w.trimAscii.toString
    if t.isEmpty then none else some t
  let fail (why : String) : EM (Option Assertion) := do
    diag ctx "E0325" s!"cannot read assertion: {src.trimAscii.toString.quote}" pos
      (help := some why)
    return none
  match words with
  | ["fonts.all_embedded"] => return some ⟨.fontsAllEmbedded, some ⟨ctx.file, pos⟩⟩
  | ["pages", op, n] =>
    match cmpOp op, n.toInt? with
    | some o, some v => return some ⟨.pages o v, some ⟨ctx.file, pos⟩⟩
    | none, _ => fail s!"'{op}' is not a comparison (== != <= < >= >)"
    | _, none => fail s!"'{n}' is not a whole number"
  | _ => fail "supported forms: pages <op> N, fonts.all_embedded"

/-- Elaborate the whole document: split preamble and body around the
`document` environment, process declarations, then the body. -/
def elabDoc (file : String) (raws : Array Raw) : EM Doc := do
  let docIdx := raws.findIdx? fun r =>
    match r with
    | .env "document" _ _ => true
    | _ => false
  let (preamble, body, trailing) :=
    match docIdx with
    | some idx =>
      let bodyRaws := match raws[idx]! with
        | .env _ b _ => b
        | _ => #[]
      (raws.extract 0 idx, bodyRaws, raws.extract (idx + 1) raws.size)
    | none => (#[], raws, #[])
  let mut ctx : Ctx := { file := file }
  let mut docClass := "article"
  let mut classOptions := ""
  let mut page : PageSpec := {}
  let mut fonts : FontSpec := {}
  let mut palette : Palette := {}
  let mut tokens : Tokens := {}
  let mut head : Option (Array Inline) := none
  let mut foot : Option (Array Inline) := none
  let mut runningFrom : Nat := 1
  let mut styles : Styles := {}
  let mut info : Meta := {}
  let mut output : OutputSpec := {}
  let mut asserts : Array Assertion := #[]
  let mut textDiagged := false
  let mut i := 0
  repeat
    if h : i < preamble.size then
      let r := preamble[i]
      match r with
      | .space => i := i + 1
      | .par _ => i := i + 1
      | .ctrl "documentclass" pos =>
        i := i + 1
        let mut j := skipSpaces preamble i
        if let some (.sym '[' _) := preamble[j]? then
          let mut opts : Array Raw := #[]
          j := j + 1
          for _ in [j:preamble.size] do
            match preamble[j]? with
            | some (.sym ']' _) =>
              j := j + 1
              break
            | some r' =>
              opts := opts.push r'
              j := j + 1
            | none => break
          classOptions := rawSrc opts
          j := skipSpaces preamble j
        match preamble[j]? with
        | some (.group nameRaws _) =>
          i := j + 1
          docClass := (rawSrc nameRaws).trimAscii.toString
          if docClass != "article" && docClass != "slides" then
            diag ctx "E0309" s!"unknown document class '{docClass}'" pos
              (help := "classes: article | slides")
        | _ =>
          diag ctx "E0304" "'\\documentclass' needs a {class}" pos
      | .ctrl "define" pos =>
        i := i + 1
        let j := skipSpaces preamble i
        match preamble[j]? with
        | some (.ctrl newName npos) =>
          let mut sigRaws : Array Raw := #[]
          let mut k := j + 1
          let mut bodyRaws : Option (Array Raw) := none
          for _ in [k:preamble.size] do
            match preamble[k]? with
            | some (.group b _) =>
              bodyRaws := some b
              k := k + 1
              break
            | some r' =>
              sigRaws := sigRaws.push r'
              k := k + 1
            | none => break
          i := k
          if builtinNames.contains newName && (Lex.textSymbols.lookup newName).isNone then
            modify fun st => { st with diags := st.diags.push {
              severity := .warning, code := "W0303"
              message := s!"'\\{newName}' is built in; this definition is ignored"
              span := some ⟨ctx.file, npos⟩
              help := some "the built-in does what most definitions of this name do" } }
          else
            match bodyRaws with
            | some b =>
              let params ← parseSig ctx (rawSrc sigRaws) pos
              ctx := { ctx with
                user := ctx.user.push ⟨newName, params, trimRaws b⟩
                limit := ctx.user.size + 1 }
            | none =>
              diag ctx "E0303" s!"'\\define \\{newName}' is missing its \{body}" pos
        | _ =>
          diag ctx "E0303" "expected '\\define \\name(...)  {body}'" pos
          i := j + 1
      | .ctrl name pos =>
        i := i + 1
        if runningCtrl.contains name then
          -- `[from = 2]` keeps the opening page clean, as a title page is.
          let mut j := skipSpaces preamble i
          if let some (.sym '[' _) := preamble[j]? then
            let mut opt : Array Raw := #[]
            let mut k := j + 1
            for _ in [k:preamble.size + 1] do
              match preamble[k]? with
              | some (.sym ']' _) => k := k + 1; break
              | some r => opt := opt.push r; k := k + 1
              | none => break
            for e in Decl.splitEntries (rawSrc opt) do
              match Decl.splitEntry e with
              | some ("from", v) =>
                match v.trimAscii.toString.toNat? with
                | some n => runningFrom := n
                | none => diag ctx "E0321" s!"'from' needs a page number, got {v.quote}" pos
              | _ =>
                diag ctx "E0320" s!"unknown option in \\{name}: {e.quote}" pos
                  (help := "options: from = <page>")
            j := skipSpaces preamble k
          match preamble[j]? with
          | some (.group body _) =>
            i := j + 1
            let content ← elabInlines ctx body
            if name == "runninghead" then
              head := some content
            else
              foot := some content
          | _ =>
            diag ctx "E0304" s!"'\\{name}' needs one group of inline content" pos
        else if name == "style" then
          let j := skipSpaces preamble i
          let j2 := skipSpaces preamble (j + 1)
          match preamble[j]?, preamble[j2]? with
          | some (.group elem _), some (.group body _) =>
            i := j2 + 1
            styles ← applyStyle ctx styles (rawSrc elem) (rawSrc body) pos
          | _, _ =>
            diag ctx "E0304" "'\\style' needs {element} and a {...} block" pos
        else if declCtrl.contains name then
          let j := skipSpaces preamble i
          match preamble[j]? with
          | some (.group body _) =>
            i := j + 1
            let src := rawSrc body
            if name == "assert" then
              if let some a ← parseAssert ctx src pos then
                asserts := asserts.push a
            else if name == "output" then
              -- Parses its own entries: `formats` is a bare comma list, which
              -- a generic key/value pre-parse would break apart.
              output ← applyOutput ctx output src pos
            else if name == "tokens" then
              -- Parses its own entries one at a time; a generic pre-parse
              -- would reject `0.6 * rhythm` before the reference resolves.
              let tk ← applyTokens ctx tokens src pos
              tokens := tk
              ctx := { ctx with tokens := tk }
            else
              let (entries, ds) := Decl.parseBlock ctx.file src pos name
              modify fun st => { st with diags := st.diags ++ ds }
              if name == "page" then
                page ← applyPage ctx page entries pos
              else if name == "fonts" then
                fonts ← applyFonts ctx fonts entries pos
              else if name == "palette" then
                let pal ← applyPalette ctx palette entries pos
                palette := pal
                ctx := { ctx with palette := pal }
              else
                info ← applyMeta ctx info entries pos
          | _ =>
            diag ctx "E0304" s!"'\\{name}' needs a \{...} block" pos
        else if let some milestone := reservedCtrl.lookup name then
          diag ctx "E0307" s!"'\\{name}' is not implemented yet" pos
            (help := s!"planned for {milestone}; see PLAN.md")
          i := skipReservedArgs preamble i
        else
          diag ctx "E0301" s!"unknown command '\\{name}'" pos
            (help := "define it with \\define, or see PLAN.md for planned commands")
      | _ =>
        i := i + 1
        unless textDiagged do
          diag ctx "E0313" "only declarations may appear before '\\begin{document}'" none
          textDiagged := true
    else
      break
  let blocks ← elabBlocks ctx body
  if trailing.any (!isSpaceOrPar ·) then
    diag ctx "W0001" "content after '\\end{document}' is ignored" none (sev := .warning)
  return {
    docClass := docClass
    classOptions := classOptions
    page := page
    fonts := fonts
    palette := palette
    tokens := tokens
    head := head
    foot := foot
    runningFrom := runningFrom
    styles := styles
    info := info
    output := output
    asserts := asserts
    body := blocks
  }

/-- Elaborate parsed input. LaTeX idioms are rewritten first, so a document
written for another engine compiles as written. -/
def runRaws (file : String) (raws : Array Raw) (earlier : Array Diag := #[]) :
    Doc × Array Diag :=
  let (raws, compatDiags) := Compat.rewrite file raws
  let (doc, st) := (elabDoc file raws).run {}
  (doc, earlier ++ compatDiags ++ st.diags)

def run (file input : String) : Doc × Array Diag :=
  let (toks, lexDiags) := Lex.lex file input
  let (raws, parseDiags) := Parse.parse file toks
  runRaws file raws (lexDiags ++ parseDiags)

end LeanTex.Core.Elab
