module

public import LeanTex.Core.PdfRead
public import LeanTex.Core.PdfFont
public import LeanTex.Core.PdfContentLex
public import LeanTex.Core.PdfFilters

/-! A PDF's text as a viewer extracts it (ISO 32000-2 §9.3–9.10, §14.6–14.9): shown strings through
ToUnicode in content order under their marked content, breaks where the pen jumps or the baseline
moves, `ActualText` standing for its sequence, and a tagged file's structure order. -/

namespace LeanTex.Core.PdfTextRead

open LeanTex.Core.PdfRead (Obj Doc Page)
open LeanTex.Core.PdfContentLex (Tok)

/-- What extracted text stands under: an artifact, a structure tree's marked-content sequence by
its identifier, or no marked content. -/
public inductive Mark where
  | artifact
  | content (mcid : Nat)
  | unmarked
  deriving DecidableEq, BEq, Repr, Inhabited

/-- What separates a run from the text before it: nothing, a word break, or a line break. -/
public inductive Brk where
  | none
  | word
  | line
  deriving DecidableEq, BEq, Repr, Inhabited

/-- The stronger of two breaks. -/
@[expose] public def Brk.max : Brk → Brk → Brk
  | .line, _ | _, .line => .line
  | .word, _ | _, .word => .word
  | .none, .none => .none

/-- A text or line matrix's six entries, or a transformation matrix's. -/
public structure Mat where
  a : Rat
  b : Rat
  c : Rat
  d : Rat
  e : Rat
  f : Rat
  deriving Inhabited, BEq, Repr

@[expose] public def Mat.id : Mat := ⟨1, 0, 0, 1, 0, 0⟩

/-- The matrix after a translation by `tx`, `ty` in its own space. -/
@[expose] public def Mat.move (m : Mat) (tx ty : Rat) : Mat :=
  { m with e := m.e + m.a * tx + m.c * ty, f := m.f + m.b * tx + m.d * ty }

/-- `m` then `n`, as PDF's row vectors compose them (§8.3.4). -/
@[expose] public def Mat.mul (m n : Mat) : Mat :=
  ⟨m.a * n.a + m.b * n.c, m.a * n.b + m.b * n.d, m.c * n.a + m.d * n.c, m.c * n.b + m.d * n.d,
   m.e * n.a + m.f * n.c + n.e, m.e * n.b + m.f * n.d + n.f⟩

/-- One item a content stream yields: a run of text under its mark after its break, or a form
XObject painted under a mark and transformation, read where it stands. -/
public inductive Item where
  | text (mark : Mark) (brk : Brk) (s : String)
  | form (mark : Mark) (ctm : Mat) (name : String)
  deriving Repr, Inhabited

/-- What a content stream's names resolve to: its fonts read for text and its named property
lists. -/
public structure Res where
  fonts : Std.HashMap String PdfFont.Loaded
  props : Std.HashMap String Obj
  deriving Inhabited

/-- An open marked-content sequence: the mark its content stands under, and the text standing
for it when it carries `ActualText`. -/
public structure Open where
  mark : Mark
  actual : Option String
  deriving Inhabited

/-- The text state `q` saves and `Q` restores (§9.3): the font and its size, the horizontal
scaling, and the character, word and line spacing. -/
public structure TextState where
  font : Option PdfFont.Loaded
  size : Rat
  scale : Rat
  charSp : Rat
  wordSp : Rat
  leading : Rat
  deriving Inhabited

/-- The interpreter's state: operands, open sequences innermost first, the text state and
transformation with their saved copies, the text matrices, the last glyph's end and squared size,
the pending break, whether replaced glyphs were shown since it, the items and the losses. -/
public structure St where
  args : Array Obj
  opens : List Open
  ts : TextState
  ctm : Mat
  saved : List (TextState × Mat)
  tm : Mat
  tlm : Mat
  pen : Option (Rat × Rat × Rat)
  brk : Brk
  held : Bool
  items : Array Item
  losses : Array String
  deriving Inhabited

/-- A text string's characters (§7.9.2.2): UTF-16BE or UTF-8 after their byte-order marks, else
bytes PDFDocEncoding reads as themselves; `none` for a byte it reads otherwise. -/
@[expose] public def textString? (b : ByteArray) : Option String :=
  let byte (i : Nat) : UInt8 := b[i]?.getD 0
  if b.size ≥ 2 && byte 0 == 0xFE && byte 1 == 0xFF then some (PdfFont.utf16 (b.extract 2 b.size))
  else if b.size ≥ 3 && byte 0 == 0xEF && byte 1 == 0xBB && byte 2 == 0xBF then
    String.fromUTF8? (b.extract 3 b.size)
  else if b.data.all fun x => (0x20 ≤ x && x < 0x7F) || x == 9 || x == 10 || x == 13 then
    some (String.ofList (b.data.toList.map fun x => Char.ofNat x.toNat))
  else none

/-- The mark content stands under while `opens` are open. -/
@[expose] public def markOf : List Open → Mark
  | [] => .unmarked
  | o :: _ => o.mark

/-- Whether an open sequence's `ActualText` stands for the content shown now. -/
@[expose] public def replaced (opens : List Open) : Bool := opens.any (·.actual.isSome)

/-- An operand by position. -/
@[expose] public def arg (a : Array Obj) (i : Nat) : Option Obj := a[i]?

/-- A number operand as an exact rational. -/
@[expose] public def num? (o : Obj) : Option Rat := PdfContentLex.numRat? o

/-- The mark a sequence opens: an artifact's content stays an artifact, an `Artifact` opens one,
an identified sequence its identifier, else its parent's mark. -/
@[expose] public def openMark (outer : Mark) (tag : String) (props : Option Obj) : Mark :=
  if outer == .artifact || tag == "Artifact" then .artifact
  else match props.bind (·.get? "MCID") with
    | some (.int n) => if 0 ≤ n then .content n.toNat else outer
    | _ => outer

/-- The `ActualText` a sequence's properties carry, as text. -/
@[expose] public def actualOf (props : Option Obj) : Option String :=
  (props.bind (·.get? "ActualText")).bind fun o =>
    (PdfContentLex.strBytes? o).bind textString?

/-- The break before a glyph of squared size `s2` at `(x, y)` on a baseline along `u`, the last
glyph having ended at `pen` with its squared size: a line break where the baseline moves by half
the larger size, a word break where the pen jumps along it by a fifth of the last size. -/
@[expose] public def breakAt (s2 : Rat) (u : Rat × Rat) (pen : Option (Rat × Rat × Rat))
    (x y : Rat) : Brk :=
  match pen with
  | none => .none
  | some (px, py, ps2) =>
    let uu := u.1 * u.1 + u.2 * u.2
    let across := u.1 * (y - py) - u.2 * (x - px)
    let along := u.1 * (x - px) + u.2 * (y - py)
    if 4 * (across * across) > max s2 ps2 * uu then .line
    else if 25 * (along * along) > ps2 * uu then .word
    else .none

/-- A run of text under the open sequences after a break, unless an `ActualText` stands for it. -/
@[expose] public def St.emitText (st : St) (brk : Brk) (s : String) : St :=
  if replaced st.opens || s.isEmpty then st
  else { st with items := st.items.push (.text (markOf st.opens) brk s) }

/-- A string's codes shown so far: the state, the text pending since the last break, the break
before it, and the first code's break. -/
public structure ShowAcc where
  st : St
  cur : String
  curBrk : Brk
  first : Option Brk

/-- One code of a string shown under text state `ts`: a break before it where the pen jumps or the
baseline moves, its text pending, the text matrix advanced by its width. -/
@[expose] public def St.showCode (ts : TextState) (a : ShowAcc) (code : PdfFont.Code) : ShowAcc :=
  let m := a.st.tm.mul a.st.ctm
  let s2 := ts.size * ts.size * (m.c * m.c + m.d * m.d)
  let here := Brk.max (if a.cur.isEmpty then a.curBrk else .none) (breakAt s2 (m.a, m.b) a.st.pen m.e m.f)
  let first := if a.first.isNone then some here else a.first
  let split := !a.cur.isEmpty && here != .none
  let st := if split then a.st.emitText a.curBrk a.cur else a.st
  let cur := if split then "" else a.cur
  let curBrk := if cur.isEmpty then here else a.curBrk
  let st := if code.text.isEmpty then
    { st with losses := st.losses.push s!"code {code.code} has no text" } else st
  let ws := if code.bytes == 1 && code.code == 32 then ts.wordSp else 0
  let tx := ((code.width / 1000) * ts.size + ts.charSp + ws) * ts.scale
  let tm := st.tm.move tx 0
  let e := tm.mul st.ctm
  { st := { st with tm, pen := some (e.e, e.f, s2) }, cur := cur ++ code.text, curBrk, first }

/-- A string shown in the current font (§9.4.3): each code's text, a word or line break before a
code where the pen jumps or the baseline moves on the page, the text matrix advanced by its width. -/
@[expose] public def St.showBytes (st : St) (b : ByteArray) : St :=
  match st.ts.font with
  | none => { st with losses := st.losses.push "a string shown with no font set" }
  | some f =>
    let a := (f.codes? b).foldl (St.showCode st.ts) ⟨st, "", st.brk, none⟩
    if replaced st.opens then
      { a.st with brk := if st.held then st.brk else (a.first.getD st.brk),
                  held := st.held || a.first.isSome }
    else
      let s := a.st.emitText a.curBrk a.cur
      { s with brk := if a.cur.isEmpty then a.curBrk else .none }

/-- One element of a `TJ` array: a string shown, a number moving the pen back by thousandths of
the size. -/
@[expose] public def St.showElem (st : St) (o : Obj) : St :=
  match PdfContentLex.strBytes? o with
  | some b => st.showBytes b
  | none => match num? o with
    | some n => { st with tm := st.tm.move (-(n / 1000) * st.ts.size * st.ts.scale) 0 }
    | none => st

/-- A `TJ` array: its strings shown, its numbers moving the pen back by thousandths of the size. -/
@[expose] public def St.showArray (st : St) (xs : Array Obj) : St := xs.foldl St.showElem st

/-- A text line moved by `tx`, `ty` in the line matrix's space (§9.4.2). -/
@[expose] public def St.nextLine (st : St) (tx ty : Rat) : St :=
  let m := st.tlm.move tx ty
  { st with tlm := m, tm := m }

/-- One operator over the operands read before it (§8.4.4, §9.3–9.4, §14.6). -/
@[expose] public def St.op (res : Res) (st : St) (name : String) : St :=
  let a := st.args
  let st := { st with args := #[] }
  let n (i : Nat) : Rat := ((arg a i).bind num?).getD 0
  match name with
  | "q" => { st with saved := (st.ts, st.ctm) :: st.saved }
  | "Q" => match st.saved with
    | (t, m) :: rest => { st with ts := t, ctm := m, saved := rest }
    | [] => st
  | "cm" => { st with ctm := Mat.mul ⟨n 0, n 1, n 2, n 3, n 4, n 5⟩ st.ctm }
  | "BT" => { st with tm := Mat.id, tlm := Mat.id }
  | "Tf" =>
    match arg a 0 with
    | some (.name nm) =>
      match res.fonts.get? nm with
      | some f => { st with ts := { st.ts with font := some f, size := n 1 } }
      | none => { st with ts := { st.ts with font := none, size := n 1 },
                          losses := st.losses.push s!"font {nm} unresolved" }
    | _ => st
  | "Tz" => { st with ts := { st.ts with scale := n 0 / 100 } }
  | "Tc" => { st with ts := { st.ts with charSp := n 0 } }
  | "Tw" => { st with ts := { st.ts with wordSp := n 0 } }
  | "TL" => { st with ts := { st.ts with leading := n 0 } }
  | "Tm" => let m : Mat := ⟨n 0, n 1, n 2, n 3, n 4, n 5⟩; { st with tm := m, tlm := m }
  | "Td" => st.nextLine (n 0) (n 1)
  | "TD" => { st.nextLine (n 0) (n 1) with ts := { st.ts with leading := -(n 1) } }
  | "T*" => st.nextLine 0 (-st.ts.leading)
  | "Tj" => match (arg a 0).bind PdfContentLex.strBytes? with
    | some b => st.showBytes b
    | none => st
  | "'" => match (arg a 0).bind PdfContentLex.strBytes? with
    | some b => (st.nextLine 0 (-st.ts.leading)).showBytes b
    | none => st
  | "\"" => match (arg a 2).bind PdfContentLex.strBytes? with
    | some b =>
      ({ st with ts := { st.ts with wordSp := n 0, charSp := n 1 } }.nextLine 0
        (-st.ts.leading)).showBytes b
    | none => st
  | "TJ" => match arg a 0 with
    | some (.arr xs) => st.showArray xs
    | _ => st
  | "BMC" => match arg a 0 with
    | some (.name tag) => { st with opens := ⟨openMark (markOf st.opens) tag none, none⟩ :: st.opens }
    | _ => st
  | "BDC" => match arg a 0 with
    | some (.name tag) =>
      let props := (arg a 1).bind fun
        | .name p => res.props.get? p
        | o => some o
      let o : Open := ⟨openMark (markOf st.opens) tag props, actualOf props⟩
      { st with opens := o :: st.opens }
    | _ => st
  | "EMC" => match st.opens with
    | o :: rest =>
      match o.actual with
      | some t =>
        let st' := { st with opens := rest }
        if replaced rest then st'
        else if t.isEmpty then { st' with held := false }
        else { st' with items := st'.items.push (.text o.mark st.brk t), brk := .none, held := false }
      | none => { st with opens := rest }
    | [] => { st with losses := st.losses.push "EMC with no open sequence" }
  | "Do" => match arg a 0 with
    | some (.name nm) =>
      if replaced st.opens then st
      else { st with items := st.items.push (.form (markOf st.opens) st.ctm nm) }
    | _ => st
  | _ => st

/-- One token through the interpreter. -/
@[expose] public def St.tok (res : Res) (st : St) : Tok → St
  | .val o => { st with args := st.args.push o }
  | .op name => st.op res name
  | .inline _ _ => { st with args := #[] }

/-- The interpreter's state before a stream, its content under `mark` and transformation `ctm`. -/
@[expose] public def St.init (mark : Mark) (ctm : Mat) : St :=
  { args := #[], opens := [⟨mark, none⟩],
    ts := { font := none, size := 0, scale := 1, charSp := 0, wordSp := 0, leading := 0 },
    ctm, saved := [], tm := Mat.id, tlm := Mat.id, pen := none, brk := .line, held := false,
    items := #[], losses := #[] }

/-- A content stream's items, read under `mark` and transformation `ctm`. -/
@[expose] public def readToks (res : Res) (mark : Mark) (toks : Array Tok) (ctm : Mat := Mat.id) :
    Array Item × Array String :=
  let st := toks.foldl (St.tok res) (St.init mark ctm)
  (st.items, st.losses)

/-! ### Documents -/

/-- Fonts already read, by object number, so a font shared by pages is read once. -/
public abbrev FontCache := Std.HashMap Nat PdfFont.Loaded

/-- A font's losses that bear on its text: its ToUnicode map or its encoding unread. -/
@[expose] public def textLosses (f : PdfFont.Loaded) : Array String :=
  f.losses.filterMap fun
    | .font k => if k.startsWith "tounicode" || k.startsWith "cmap" then some s!"font: {k}" else none
    | _ => none

/-- A resource dictionary's fonts read for text and its named property lists, fonts read through
the cache, with the text losses of fonts read afresh. -/
public def resOf (d : Doc) (cache : FontCache) (resources : Option Obj) :
    Res × FontCache × Array String := Id.run do
  let some r := resources.bind (d.deref · |>.toOption) | return (default, cache, #[])
  let mut cache := cache
  let mut losses : Array String := #[]
  let mut fonts : Std.HashMap String PdfFont.Loaded := {}
  match (d.field r "Font").toOption.getD none with
  | some (.dict es) =>
    for (k, v) in es do
      let cached := match v with
        | .ref num _ => cache.get? num
        | _ => none
      match cached with
      | some f => fonts := fonts.insert k f
      | none =>
        if let .ok fo := d.deref v then
          let f := PdfFont.load d fo
          losses := losses ++ textLosses f
          if let .ref num _ := v then cache := cache.insert num f
          fonts := fonts.insert k f
  | _ => pure ()
  let mut props : Std.HashMap String Obj := {}
  match (d.field r "Properties").toOption.getD none with
  | some (.dict es) =>
    for (k, v) in es do
      if let .ok (.dict pes) := d.deref v then
        props := props.insert k (.dict (pes.map fun (pk, pv) => (pk, (d.deref pv).toOption.getD pv)))
  | _ => pure ()
  return ({ fonts, props }, cache, losses)

/-- How deeply forms nested in forms are read; deeper nesting is a loss. -/
@[expose] public def formDepth : Nat := 12

/-- How many content tokens a file's forms may cost in all, read in place however often they are
painted: a fixed allowance and four per byte of the file. -/
@[expose] public def formBudget (d : Doc) : Nat := 65536 + 4 * d.bytes.size

/-- A run of text a page yields, form content read in place: its mark, its break and its
characters. -/
public structure Run where
  mark : Mark
  brk : Brk
  text : String
  deriving Repr, Inhabited

/-- A form's own mark under the mark of the sequence painting it: its artifacts stay artifacts,
anything else is the painting sequence's, since a form's identifiers name its own structure. -/
@[expose] public def relabel (outer inner : Mark) : Mark :=
  if inner == .artifact then .artifact else outer

/-- What reading forms in place carries along: fonts read, each form's tokens by object number,
the tokens spent of the budget, and the losses met. -/
public structure Expansion where
  fonts : FontCache
  toks : Std.HashMap Nat (Array Tok)
  spent : Nat
  losses : Array String
  deriving Inhabited

/-- A form's matrix (§8.10.1), the identity where it carries none. -/
@[expose] public def formMatrix (dict : Obj) : Mat :=
  match dict.get? "Matrix" with
  | some (.arr xs) =>
    let n (i : Nat) : Rat := (xs[i]?.bind num?).getD 0
    if xs.size == 6 then ⟨n 0, n 1, n 2, n 3, n 4, n 5⟩ else Mat.id
  | _ => Mat.id

/-- Items with their forms read in place, `depth` the nesting still allowed, `path` the forms
being read, a form painting itself a loss. -/
public def expand (d : Doc) (resources : Option Obj) (path : List Nat) (ex : Expansion) :
    Nat → Array Item → Array Run × Expansion
  | 0, items =>
    (items.filterMap fun
      | .text m b s => some ⟨m, b, s⟩
      | .form .. => none,
      if items.any (fun | .form .. => true | .text .. => false) then
        { ex with losses := ex.losses.push "forms nest past the reading's depth" } else ex)
  | depth + 1, items => Id.run do
    let mut runs : Array Run := #[]
    let mut ex := ex
    for it in items do
      match it with
      | .text m b s => runs := runs.push ⟨m, b, s⟩
      | .form m ctm n =>
        let xo := (resources.bind (d.deref · |>.toOption)).bind fun r =>
          match (d.field r "XObject").toOption.getD none with
          | some (.dict es) => (es.find? (·.1 == n)).map (·.2)
          | _ => none
        let num := match xo with
          | some (.ref k _) => some k
          | _ => none
        if num.any path.contains then
          ex := { ex with losses := ex.losses.push s!"form {n} paints itself" }
          continue
        match xo.bind fun o => (d.stream o).toOption.getD none with
        | some (dict, raw) =>
          if dict.get? "Subtype" == some (.name "Form") then
            let cached := num.bind ex.toks.get?
            let toks? := match cached with
              | some ts => some ts
              | none => match PdfFilters.decode dict raw with
                | .ok (.bytes data) => some (PdfContentLex.scan data)
                | _ => none
            match toks? with
            | none => ex := { ex with losses := ex.losses.push s!"form {n} does not decode" }
            | some toks =>
              if let some k := num then ex := { ex with toks := ex.toks.insert k toks }
              if ex.spent + toks.size > formBudget d then
                ex := { ex with losses := ex.losses.push s!"form {n} passes the reading's budget" }
                continue
              ex := { ex with spent := ex.spent + toks.size }
              let inner := ((dict.get? "Resources").bind (d.deref · |>.toOption)).orElse fun _ =>
                resources.bind (d.deref · |>.toOption)
              let (res, fonts, ls0) := resOf d ex.fonts inner
              let (items', ls) := readToks res m toks ((formMatrix dict).mul ctm)
              let (rs, ex') := expand d inner (num.toList ++ path)
                { ex with fonts, losses := ex.losses ++ ls0 ++ ls } depth items'
              ex := ex'
              runs := runs ++ rs.map fun r => { r with mark := relabel m r.mark }
        | none => ex := { ex with losses := ex.losses.push s!"XObject {n} unresolved" }
    return (runs, ex)

/-- A file's text: each page's object number, where it has one, with its runs in content order,
form content read in place, and what the reading could not read. -/
public structure Extracted where
  pages : Array (Option Nat × Array Run)
  losses : Array String
  deriving Inhabited

/-- The text an open file's pages show. -/
public def extractDoc (d : Doc) : Except String Extracted := do
  let pages ← d.pageList
  let mut out : Array (Option Nat × Array Run) := #[]
  let mut ex : Expansion := { fonts := {}, toks := {}, spent := 0, losses := #[] }
  for (num, p) in pages do
    let data ← d.content p
    let (res, fonts, ls0) := resOf d ex.fonts p.resources
    let (items, ls) := readToks res .unmarked (PdfContentLex.scan data)
    let (runs, ex') := expand d p.resources [] { ex with fonts, losses := ex.losses ++ ls0 ++ ls }
      formDepth items
    ex := ex'
    out := out.push (num, runs)
  return { pages := out, losses := ex.losses }

/-- The text a file's pages show, read from its bytes. -/
public def extract (b : ByteArray) : Except String Extracted := do
  extractDoc (← Doc.ofBytes b)

/-- Runs as text: a word break a space, a line break a line feed, none at the start. -/
@[expose] public def runsText (runs : Array Run) : String :=
  runs.foldl (fun acc r =>
    let sep := if acc.isEmpty then "" else match r.brk with
      | .line => "\n"
      | .word => " "
      | .none => ""
    acc ++ sep ++ r.text) ""

/-- Every page's runs in content order, artifacts kept or left out, each page opening a line. -/
@[expose] public def Extracted.contentRuns (x : Extracted) (artifacts : Bool) : Array Run :=
  x.pages.foldl (fun acc (_, runs) =>
    let rs := if artifacts then runs else runs.filter (·.mark != .artifact)
    match rs.toList with
    | [] => acc
    | r :: rest => acc ++ (({ r with brk := .line } :: rest).toArray)) #[]

/-- The text of every page in content order, artifacts kept or left out. -/
public def Extracted.contentText (x : Extracted) (artifacts : Bool) : String :=
  runsText (x.contentRuns artifacts)

/-! ### Structure order -/

/-- A structure tree's leaves in order (§14.7.2): each marked-content reference as its page's
object number and identifier, or a structure element's `ActualText` standing for its subtree. -/
public inductive Leaf where
  | mcr (page : Nat) (mcid : Nat)
  | actual (s : String)
  deriving Repr, Inhabited, BEq

/-- The leaves under an open file's structure tree root, depth first, every element visited once,
a negative identifier or a reference into a form's stream naming none; a tree the walk cannot
finish within the file's bytes is refused. -/
public def leavesOf (d : Doc) : Except String (Array Leaf) := do
  let (catalog, _) ← d.get d.root
  let some rootRef := catalog.get? "StructTreeRoot" | return #[]
  let root ← d.deref rootRef
  let pageNum : Option Obj → Option Nat := fun
    | some (.ref n _) => some n
    | _ => none
  let mut work : Array (Obj × Option Nat) := #[]
  match root.get? "K" with
  | some (.arr ks) => for k in ks.reverse do work := work.push (k, none)
  | some k => work := work.push (k, none)
  | none => pure ()
  let mut seen : Std.HashMap Nat Unit := {}
  let mut out : Array Leaf := #[]
  for _ in [0:d.bytes.size + d.objectCount + 4] do
    let some (k, pg) := work.back? | break
    work := work.pop
    match k with
    | .int n => if let some p := pg then if 0 ≤ n then out := out.push (.mcr p n.toNat)
    | o =>
      if let .ref n _ := o then
        if seen.contains n then continue
        seen := seen.insert n ()
      let e ← d.deref o
      let field (key : String) : Option Obj := (e.get? key).map fun v => (d.deref v).toOption.getD v
      match e, e.get? "Type" with
      | .arr ks, _ => for c in ks.reverse do work := work.push (c, pg)
      | .int n, _ => if let some p := pg then if 0 ≤ n then out := out.push (.mcr p n.toNat)
      | _, some (.name "MCR") =>
        let p := (pageNum (e.get? "Pg")).orElse fun _ => pg
        match field "MCID", p, e.get? "Stm" with
        | some (.int m), some p, none => if 0 ≤ m then out := out.push (.mcr p m.toNat)
        | _, _, _ => pure ()
      | _, some (.name "OBJR") => pure ()
      | _, _ =>
        let pg' := (pageNum (e.get? "Pg")).orElse fun _ => pg
        match (field "ActualText").bind PdfContentLex.strBytes? |>.bind textString? with
        | some t => out := out.push (.actual t)
        | none =>
          match e.get? "K" with
          | some (.arr ks) => for c in ks.reverse do work := work.push (c, pg')
          | some c => work := work.push (c, pg')
          | none => pure ()
  unless work.isEmpty do throw "malformed PDF: the structure tree exceeds the file"
  return out

/-- The runs a tagged file's structure reads in order: each marked-content reference's runs where
its page shows them, an element's `ActualText` in its place, each leaf opening a line. -/
public def structureRuns (d : Doc) (x : Extracted) : Except String (Array Run) := do
  let leaves ← leavesOf d
  let mut index : Std.HashMap (Nat × Nat) (Array Run) := {}
  for (num, runs) in x.pages do
    if let some p := num then
      for r in runs do
        if let .content m := r.mark then
          index := index.insert (p, m) ((index.getD (p, m) #[]).push r)
  let mut out : Array Run := #[]
  for l in leaves do
    match l with
    | .mcr p m =>
      match (index.getD (p, m) #[]).toList with
      | [] => pure ()
      | r :: rest => out := out ++ ({ r with brk := .line } :: rest).toArray
    | .actual s => out := out.push ⟨.unmarked, .line, s⟩
  return out

/-- The text a tagged file's structure reads, from its bytes. -/
public def structureText (b : ByteArray) : Except String String := do
  let d ← Doc.ofBytes b
  return runsText (← structureRuns d (← extractDoc d))

end LeanTex.Core.PdfTextRead
