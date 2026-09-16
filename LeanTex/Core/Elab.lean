import LeanTex.Core.Lex
import LeanTex.Core.Parse
import LeanTex.Core.Ir
import LeanTex.Core.Dim
import LeanTex.Core.Decl

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

structure ESt where
  diags : Array Diag := #[]

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
  [("fonts", "M3"), ("tokens", "M3"), ("palette", "M3"),
   ("block", "M3"), ("href", "M3"), ("link", "M3"), ("hfill", "M3"),
   ("vspace", "M3"), ("noindent", "M3"),
   ("fontfallback", "M5"), ("figure", "M5"), ("note", "M5")]

/-- Declarations that take a `{...}` block and are handled in the preamble. -/
def declCtrl : List String := ["page", "pdfmeta", "assert"]

def pageKeys : List String :=
  ["size", "width", "height", "margin", "vmargin", "hmargin", "header", "footer"]

/-- Page keys that are declared but not implemented yet, with the milestone
that will land them. Reported as pending, never as a type error. -/
def pagePending : List (String × String) := [("header", "M3"), ("footer", "M3")]

def metaKeys : List String := ["title", "author", "subject", "keywords"]

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
   ("_", "_"), ("~", "~"), (" ", " ")]

def blockOnly : List String :=
  ["section", "subsection", "subsubsection", "item", "documentclass", "define"]

def builtinNames : List String :=
  ["begin", "end", "par", "define", "ifgiven", "documentclass"] ++
  blockOnly ++ (escapes.map (·.1)) ++ (argStyles.map (·.1)) ++
  (declStyles.map (·.1)) ++ (reservedCtrl.map (·.1))

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
mutual

/-- Source text of raw content, trimmed. -/
def rawSrc (raws : Array Raw) : String :=
  (rawSrcList raws.toList).trimAscii.toString

def rawSrcList (rs : List Raw) : String :=
  match rs with
  | [] => ""
  | r :: rest => rawSrcOne r ++ rawSrcList rest

def rawSrcOne (r : Raw) : String :=
  match r with
  | .word s _ => s
  | .space => " "
  | .par _ => " "
  | .sym c _ => String.ofList [c]
  | .ctrl n _ => "\\" ++ n ++ " "
  | .group body _ => "{" ++ rawSrc body ++ "}"
  | .math d body _ =>
    let inner := rawSrc body
    if d then s!"\\[{inner}\\]" else s!"${inner}$"
  | .env n body _ => s!"\\begin\{{n}}" ++ rawSrc body ++ s!"\\end\{{n}}"
  | .verb s _ => s!"\\begin\{verbatim}{s}\\end\{verbatim}"

end

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

/-- Elaborate raw items as inline content. Nontermination is impossible by
design (a user command's body sees only earlier definitions), but the checker
cannot see that yet: de-partialing is scheduled proof work. -/
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
        if name == "\\" || name == "par" then
          acc := flushText acc sb
          sb := ""
          acc := acc.push .linebreak
        else if let some lit := escapes.lookup name then
          sb := sb ++ lit
        else if let some style := argStyles.lookup name then
          let j := skipSpaces raws i
          match raws[j]? with
          | some (.group body _) =>
            acc := flushText acc sb
            sb := ""
            acc := acc.push (.styled style (← elabInlines ctx body))
            i := j + 1
          | some (.word s _) =>
            acc := flushText acc sb
            sb := ""
            acc := acc.push (.styled style #[.text s])
            i := j + 1
          | _ =>
            diag ctx "E0304" s!"'\\{name}' needs an argument" pos
        else if let some style := declStyles.lookup name then
          let rest ← elabInlines ctx (raws.extract i raws.size)
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
          let mut bindings : Array (String × Option (Array Inline)) := #[]
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
          let callCtx : Ctx := { ctx with limit := k, args := bindings }
          acc := acc ++ (← elabInlines callCtx cmd.body)
        else if let some milestone := reservedCtrl.lookup name then
          diag ctx "E0307" s!"'\\{name}' is not implemented yet" pos
            (help := s!"planned for {milestone}; see PLAN.md")
          i := skipReservedArgs raws i
        else if blockOnly.contains name then
          diag ctx "E0312" s!"'\\{name}' is not allowed here" pos
        else
          diag ctx "E0301" s!"unknown command '\\{name}'" pos
            (help := "define it with \\define, or see PLAN.md for planned commands")
    else
      break
  return mergeText (flushText acc sb)

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
        | .ctrl n _ => (sectionLevel n).isSome
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
        | .ctrl n pos =>
          i := i + 1
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
      if name == "" || !name.toList.all Char.isAlpha then
        diag ctx "E0303" s!"invalid parameter name '{name}'" pos
          (help := "parameter names are letters only")
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
    | key, v =>
      if let some milestone := pagePending.lookup key then
        diag ctx "E0307" s!"'{key}' in \\page is not implemented yet" pos
          (help := s!"planned for {milestone}; see PLAN.md")
      else if pageKeys.contains key then
        let expected := if key == "size" then "a page size name" else "a dimension"
        modify fun st => { st with
          diags := st.diags.push (Decl.wrongType ctx.file "page" key expected v pos) }
      else
        modify fun st => { st with
          diags := st.diags.push (Decl.unknownKey ctx.file "page" key pageKeys pos) }
  return spec

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
  let mut info : Meta := {}
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
          if builtinNames.contains newName then
            diag ctx "E0303" s!"cannot redefine built-in '\\{newName}'" npos
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
        if declCtrl.contains name then
          let j := skipSpaces preamble i
          match preamble[j]? with
          | some (.group body _) =>
            i := j + 1
            let src := rawSrc body
            if name == "assert" then
              if let some a ← parseAssert ctx src pos then
                asserts := asserts.push a
            else
              let (entries, ds) := Decl.parseBlock ctx.file src pos name
              modify fun st => { st with diags := st.diags ++ ds }
              if name == "page" then
                page ← applyPage ctx page entries pos
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
    info := info
    asserts := asserts
    body := blocks
  }

/-- The full front end: lex, parse, elaborate. -/
def run (file input : String) : Doc × Array Diag :=
  let (toks, lexDiags) := Lex.lex file input
  let (raws, parseDiags) := Parse.parse file toks
  let (doc, st) := (elabDoc file raws).run {}
  (doc, lexDiags ++ parseDiags ++ st.diags)

end LeanTex.Core.Elab
