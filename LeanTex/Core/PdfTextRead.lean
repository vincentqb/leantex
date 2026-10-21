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

/-- One item a content stream yields: a run of text under its mark after its break, or a form
XObject painted under a mark, read where it stands. -/
public inductive Item where
  | text (mark : Mark) (brk : Brk) (s : String)
  | form (mark : Mark) (name : String)
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

/-- A text or line matrix's six entries. -/
public structure Mat where
  a : Rat
  b : Rat
  c : Rat
  d : Rat
  e : Rat
  f : Rat
  deriving Inhabited, BEq

@[expose] public def Mat.id : Mat := ⟨1, 0, 0, 1, 0, 0⟩

/-- The matrix after a translation by `tx`, `ty` in its own space. -/
@[expose] public def Mat.move (m : Mat) (tx ty : Rat) : Mat :=
  { m with e := m.e + m.a * tx + m.c * ty, f := m.f + m.b * tx + m.d * ty }

/-- The interpreter's state: operands read so far, the open sequences innermost first, the text
state and its saved copies, the text and line matrices, where the last glyph shown ended and at
what size, the break pending before the next run, the items read and the losses met. -/
public structure St where
  args : Array Obj
  opens : List Open
  ts : TextState
  saved : List TextState
  tm : Mat
  tlm : Mat
  pen : Option (Rat × Rat × Rat)
  brk : Brk
  items : Array Item
  losses : Array String
  deriving Inhabited

/-- A text string's characters (§7.9.2.2): UTF-16BE or UTF-8 after their byte-order marks, else
bytes PDFDocEncoding reads as themselves; `none` for a byte it reads otherwise. -/
public def textString? (b : ByteArray) : Option String :=
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

/-- The break before a glyph of `size` whose origin is `(x, y)`, the last glyph shown having ended
at `pen` at its own size: a line break where the baseline moves by more than half the larger
size, a word break where the pen jumps forward or back by more than a fifth of the last size. -/
@[expose] public def breakAt (size : Rat) (pen : Option (Rat × Rat × Rat)) (x y : Rat) : Brk :=
  match pen with
  | none => .none
  | some (px, py, ps) =>
    let s := if size < 0 then -size else size
    let dy := if y < py then py - y else y - py
    let dx := if x < px then px - x else x - px
    if 2 * dy > max s ps then .line
    else if 5 * dx > ps then .word
    else .none

/-- A run of text under the open sequences after a break, unless an `ActualText` stands for it. -/
@[expose] public def St.emitText (st : St) (brk : Brk) (s : String) : St :=
  if replaced st.opens || s.isEmpty then st
  else { st with items := st.items.push (.text (markOf st.opens) brk s) }

/-- A string shown in the current font (§9.4.3): each code's text, a word or line break before a
code where the pen jumps or the baseline moves, the text matrix advanced by each code's width. -/
public def St.showBytes (st : St) (b : ByteArray) : St :=
  match st.ts.font with
  | none => { st with losses := st.losses.push "a string shown with no font set" }
  | some f => Id.run do
    let ts := st.ts
    let mut st := st
    let mut cur := ""
    let mut curBrk := st.brk
    let size := (let z := ts.size * st.tm.d; if z < 0 then -z else z)
    for code in f.codes? b do
      let x := st.tm.e
      let y := st.tm.f
      let here := Brk.max (if cur.isEmpty then curBrk else .none) (breakAt size st.pen x y)
      if !cur.isEmpty && here != .none then
        st := st.emitText curBrk cur
        cur := ""
      if cur.isEmpty then curBrk := here
      if code.text.isEmpty then st := { st with losses := st.losses.push s!"code {code.code} has no text" }
      cur := cur ++ code.text
      let ws := if code.bytes == 1 && code.code == 32 then ts.wordSp else 0
      let tx := ((code.width / 1000) * ts.size + ts.charSp + ws) * ts.scale
      st := { st with tm := st.tm.move tx 0 }
      st := { st with pen := some (st.tm.e, st.tm.f, size) }
    st := st.emitText curBrk cur
    return { st with brk := if cur.isEmpty then curBrk else .none }

/-- A `TJ` array: its strings shown, its numbers moving the pen back by thousandths of the size. -/
public def St.showArray (st : St) (xs : Array Obj) : St :=
  xs.foldl (fun st o => match PdfContentLex.strBytes? o with
    | some b => st.showBytes b
    | none => match num? o with
      | some n => { st with tm := st.tm.move (-(n / 1000) * st.ts.size * st.ts.scale) 0 }
      | none => st) st

/-- A text line moved by `tx`, `ty` in the line matrix's space (§9.4.2). -/
@[expose] public def St.nextLine (st : St) (tx ty : Rat) : St :=
  let m := st.tlm.move tx ty
  { st with tlm := m, tm := m }

/-- One operator over the operands read before it (§8.4.4, §9.3–9.4, §14.6). -/
public def St.op (res : Res) (st : St) (name : String) : St :=
  let a := st.args
  let st := { st with args := #[] }
  let n (i : Nat) : Rat := ((arg a i).bind num?).getD 0
  match name with
  | "q" => { st with saved := st.ts :: st.saved }
  | "Q" => match st.saved with
    | t :: rest => { st with ts := t, saved := rest }
    | [] => st
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
        if replaced rest || t.isEmpty then st'
        else { st' with items := st'.items.push (.text o.mark st.brk t), brk := .none }
      | none => { st with opens := rest }
    | [] => { st with losses := st.losses.push "EMC with no open sequence" }
  | "Do" => match arg a 0 with
    | some (.name nm) =>
      if replaced st.opens then st
      else { st with items := st.items.push (.form (markOf st.opens) nm) }
    | _ => st
  | _ => st

/-- One token through the interpreter. -/
public def St.tok (res : Res) (st : St) : Tok → St
  | .val o => { st with args := st.args.push o }
  | .op name => st.op res name
  | .inline _ _ => { st with args := #[] }

/-- The interpreter's state before a stream, its content under `mark`. -/
@[expose] public def St.init (mark : Mark) : St :=
  { args := #[], opens := [⟨mark, none⟩],
    ts := { font := none, size := 0, scale := 1, charSp := 0, wordSp := 0, leading := 0 },
    saved := [], tm := Mat.id, tlm := Mat.id, pen := none, brk := .line, items := #[],
    losses := #[] }

/-- A content stream's items, read under `mark`. -/
public def readToks (res : Res) (mark : Mark) (toks : Array Tok) : Array Item × Array String :=
  let st := toks.foldl (St.tok res) (St.init mark)
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
      if let .ok po := d.deref v then props := props.insert k po
  | _ => pure ()
  return ({ fonts, props }, cache, losses)

/-- How deeply forms nested in forms are read; deeper nesting is a loss. -/
@[expose] public def formDepth : Nat := 12

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

/-- Items with their forms read in place, `depth` the nesting still allowed. -/
public def expand (d : Doc) (resources : Option Obj) (cache : FontCache) :
    Nat → Array Item → Array Run × FontCache × Array String
  | 0, items =>
    (items.filterMap fun
      | .text m b s => some ⟨m, b, s⟩
      | .form _ _ => none, cache,
      if items.any (fun | .form .. => true | .text .. => false) then
        #["forms nest past the reading's depth"] else #[])
  | depth + 1, items => Id.run do
    let mut runs : Array Run := #[]
    let mut losses : Array String := #[]
    let mut cache := cache
    for it in items do
      match it with
      | .text m b s => runs := runs.push ⟨m, b, s⟩
      | .form m n =>
        let xo := (resources.bind (d.deref · |>.toOption)).bind fun r =>
          match (d.field r "XObject").toOption.getD none with
          | some (.dict es) => (es.find? (·.1 == n)).map (·.2)
          | _ => none
        match xo.bind fun o => (d.stream o).toOption.getD none with
        | some (dict, raw) =>
          if dict.get? "Subtype" == some (.name "Form") then
            match PdfFilters.decode dict raw with
            | .ok (.bytes data) =>
              let inner := ((dict.get? "Resources").bind (d.deref · |>.toOption)).orElse fun _ =>
                resources.bind (d.deref · |>.toOption)
              let (res, cache1, ls0) := resOf d cache inner
              let (items', ls) := readToks res m (PdfContentLex.scan data)
              let (rs, cache2, ls') := expand d inner cache1 depth items'
              cache := cache2
              runs := runs ++ rs.map fun r => { r with mark := relabel m r.mark }
              losses := losses ++ ls0 ++ ls ++ ls'
            | _ => losses := losses.push s!"form {n} does not decode"
        | none => losses := losses.push s!"XObject {n} unresolved"
    return (runs, cache, losses)

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
  let mut losses : Array String := #[]
  let mut cache : FontCache := {}
  for (num, p) in pages do
    let data ← d.content p
    let (res, cache1, ls0) := resOf d cache p.resources
    let (items, ls) := readToks res .unmarked (PdfContentLex.scan data)
    let (runs, cache2, ls') := expand d p.resources cache1 formDepth items
    cache := cache2
    out := out.push (num, runs)
    losses := losses ++ ls0 ++ ls ++ ls'
  return { pages := out, losses }

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

/-- The leaves under an open file's structure tree root, depth first, every element visited once;
a tree the walk cannot finish within the file's bytes is refused. -/
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
    | .int n => if let some p := pg then out := out.push (.mcr p n.toNat)
    | o =>
      if let .ref n _ := o then
        if seen.contains n then continue
        seen := seen.insert n ()
      let e ← d.deref o
      match e.get? "Type" with
      | some (.name "MCR") =>
        let p := (pageNum (e.get? "Pg")).orElse fun _ => pg
        match e.get? "MCID", p with
        | some (.int m), some p => out := out.push (.mcr p m.toNat)
        | _, _ => pure ()
      | some (.name "OBJR") => pure ()
      | _ =>
        let pg' := (pageNum (e.get? "Pg")).orElse fun _ => pg
        match (e.get? "ActualText").bind PdfContentLex.strBytes? |>.bind textString? with
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
