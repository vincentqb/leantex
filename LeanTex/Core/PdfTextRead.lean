module

public import LeanTex.Core.PdfRead
public import LeanTex.Core.PdfFont
public import LeanTex.Core.PdfContentLex
public import LeanTex.Core.PdfFilters

/-! A PDF's text as a viewer extracts it (ISO 32000-2 §9.10, §14.6–14.9): each shown string decoded
through its font's ToUnicode mapping in content order, under the marked content it stands in, an
`ActualText` standing for its sequence, and a tagged file's text in structure order. -/

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

/-- One item a content stream yields: a run of text under its mark, opening a new line or not, or
a form XObject painted under a mark, read where it stands. -/
public inductive Item where
  | text (mark : Mark) (line : Bool) (s : String)
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

/-- The text interpreter's state: operands read so far, the open sequences innermost first, the
current font, the text line's vertical position, whether the next run opens a line, the items
read and the losses met. -/
public structure St where
  args : Array Obj
  opens : List Open
  font : Option PdfFont.Loaded
  y : Option Rat
  line : Bool
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

/-- The mark content stands under while `opens` are open: the innermost artifact or identified
sequence, else none. -/
@[expose] public def markOf : List Open → Mark
  | [] => .unmarked
  | o :: _ => o.mark

/-- Whether an open sequence's `ActualText` stands for the content shown now. -/
@[expose] public def replaced (opens : List Open) : Bool := opens.any (·.actual.isSome)

/-- A string's text through the current font: each code's ToUnicode text, in order. -/
@[expose] public def shown (f : PdfFont.Loaded) (s : ByteArray) : String :=
  (f.codes? s).foldl (fun acc c => acc ++ c.text) ""

/-- Text shown under the open sequences: one run, unless an `ActualText` stands for it. -/
@[expose] public def St.show (st : St) (s : String) : St :=
  if replaced st.opens || s.isEmpty then st
  else { st with items := st.items.push (.text (markOf st.opens) st.line s), line := false }

/-- A string shown in the current font, or a loss where no font is set. -/
@[expose] public def St.showBytes (st : St) (b : ByteArray) : St :=
  match st.font with
  | some f => st.show (shown f b)
  | none => { st with losses := st.losses.push "no font set" }

/-- A `TJ` array's strings shown in order; its numbers move the pen and show nothing. -/
@[expose] public def St.showArray (st : St) (xs : Array Obj) : St :=
  xs.foldl (fun st o => match PdfContentLex.strBytes? o with
    | some b => st.showBytes b
    | none => st) st

/-- The vertical position a text matrix sets, opening a line where it changes. -/
@[expose] public def St.moveTo (st : St) (y : Rat) : St :=
  { st with y := some y, line := st.line || st.y != some y }

/-- The mark a sequence opens: an artifact, an identified sequence, else its parent's. -/
@[expose] public def openMark (outer : Mark) (tag : String) (props : Option Obj) : Mark :=
  if tag == "Artifact" then .artifact
  else match props.bind (·.get? "MCID") with
    | some (.int n) => if 0 ≤ n then .content n.toNat else outer
    | _ => outer

/-- The `ActualText` a sequence's properties carry, as text. -/
@[expose] public def actualOf (props : Option Obj) : Option String :=
  (props.bind (·.get? "ActualText")).bind fun o =>
    (PdfContentLex.strBytes? o).bind textString?

/-- A number operand as an exact rational. -/
@[expose] public def num? (o : Obj) : Option Rat := PdfContentLex.numRat? o

/-- An operand by position. -/
@[expose] public def arg (a : Array Obj) (i : Nat) : Option Obj := a[i]?

/-- One operator over the operands read before it (§9.3–9.4, §14.6). -/
public def St.op (res : Res) (st : St) (name : String) : St :=
  let a := st.args
  let st := { st with args := #[] }
  match name with
  | "BT" => { st with line := true }
  | "Tf" =>
    match arg a 0 with
    | some (.name n) =>
      match res.fonts.get? n with
      | some f => { st with font := some f }
      | none => { st with font := none, losses := st.losses.push s!"font {n} unresolved" }
    | _ => st
  | "Tm" => match (arg a 5).bind num? with
    | some y => st.moveTo y
    | none => st
  | "Td" | "TD" => match (arg a 1).bind num? with
    | some dy => if dy == 0 then st else { st with line := true, y := none }
    | none => st
  | "T*" => { st with line := true, y := none }
  | "Tj" => match (arg a 0).bind PdfContentLex.strBytes? with
    | some b => st.showBytes b
    | none => st
  | "'" => match (arg a 0).bind PdfContentLex.strBytes? with
    | some b => { st with line := true, y := none }.showBytes b
    | none => st
  | "\"" => match (arg a 2).bind PdfContentLex.strBytes? with
    | some b => { st with line := true, y := none }.showBytes b
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
      let st := { st with opens := rest }
      match o.actual with
      | some t => st.show t
      | none => st
    | [] => { st with losses := st.losses.push "EMC with no open sequence" }
  | "Do" => match arg a 0 with
    | some (.name n) =>
      if replaced st.opens then st
      else { st with items := st.items.push (.form (markOf st.opens) n) }
    | _ => st
  | _ => st

/-- One token through the interpreter. -/
public def St.tok (res : Res) (st : St) : Tok → St
  | .val o => { st with args := st.args.push o }
  | .op name => st.op res name
  | .inline _ _ => { st with args := #[] }

/-- The interpreter's state before a stream, its content under `mark`. -/
@[expose] public def St.init (mark : Mark) : St :=
  { args := #[], opens := [⟨mark, none⟩], font := none, y := none, line := true, items := #[],
    losses := #[] }

/-- A content stream's items, read under `mark`. -/
public def readToks (res : Res) (mark : Mark) (toks : Array Tok) : Array Item × Array String :=
  let st := toks.foldl (St.tok res) (St.init mark)
  (st.items, st.losses)

/-! ### Documents -/

/-- A resource dictionary's fonts read for text and its named property lists. -/
public def resOf (d : Doc) (resources : Option Obj) : Res := Id.run do
  let some r := resources.bind (d.deref · |>.toOption) | return default
  let mut fonts : Std.HashMap String PdfFont.Loaded := {}
  match (d.field r "Font").toOption.getD none with
  | some (.dict es) =>
    for (k, v) in es do
      if let .ok fo := d.deref v then fonts := fonts.insert k (PdfFont.load d fo)
  | _ => pure ()
  let mut props : Std.HashMap String Obj := {}
  match (d.field r "Properties").toOption.getD none with
  | some (.dict es) =>
    for (k, v) in es do
      if let .ok po := d.deref v then props := props.insert k po
  | _ => pure ()
  return { fonts, props }

/-- How deeply forms nested in forms are read; deeper nesting is a loss. -/
@[expose] public def formDepth : Nat := 12

/-- A run of text a page yields, form content read in place: its mark, whether it opens a line,
and its characters. -/
public structure Run where
  mark : Mark
  line : Bool
  text : String
  deriving Repr, Inhabited

/-- Items with their forms read in place, `depth` the nesting still allowed. -/
public def expand (d : Doc) (resources : Option Obj) : Nat → Array Item → Array Run × Array String
  | 0, items =>
    (items.filterMap fun
      | .text m l s => some ⟨m, l, s⟩
      | .form _ _ => none, if items.any (fun | .form .. => true | .text .. => false) then
        #["forms nest past the reading's depth"] else #[])
  | depth + 1, items => Id.run do
    let mut runs : Array Run := #[]
    let mut losses : Array String := #[]
    for it in items do
      match it with
      | .text m l s => runs := runs.push ⟨m, l, s⟩
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
              let (items', ls) := readToks (resOf d inner) m (PdfContentLex.scan data)
              let (rs, ls') := expand d inner depth items'
              runs := runs ++ rs
              losses := losses ++ ls ++ ls'
            | _ => losses := losses.push s!"form {n} does not decode"
        | none => losses := losses.push s!"XObject {n} unresolved"
    return (runs, losses)

/-- The page objects in page-tree order, each with its object number (§7.7.3). -/
public def pagesOf (d : Doc) : Except String (Array (Nat × Page)) := do
  let (catalog, _) ← d.get d.root
  let some pagesRef := catalog.get? "Pages"
    | throw "malformed PDF: the catalog has no /Pages"
  let mut work : Array (Obj × Option Obj × Option Obj × Option Obj × Option Obj) :=
    #[(pagesRef, none, none, none, none)]
  let mut seen : Std.HashMap Nat Unit := {}
  let mut out : Array (Nat × Page) := #[]
  for _ in [0:d.objectCount + 2] do
    let some (nodeRef, mb, cb, res, rot) := work.back? | break
    work := work.pop
    let num := match nodeRef with
      | .ref n _ => n
      | _ => 0
    if seen.contains num then throw s!"malformed PDF: page tree node {num} repeats"
    seen := seen.insert num ()
    let node ← d.deref nodeRef
    let mb := (node.get? "MediaBox").or mb
    let cb := (node.get? "CropBox").or cb
    let res := (node.get? "Resources").or res
    let rot := (node.get? "Rotate").or rot
    if node.get? "Type" matches some (.name "Page") then
      out := out.push (num, { node, mediaBox := mb, cropBox := cb, resources := res, rotate := rot })
    else
      match node.get? "Kids" with
      | some (.arr kids) =>
        for k in [0:kids.size] do
          if let some kid := kids[kids.size - 1 - k]? then
            work := work.push (kid, mb, cb, res, rot)
      | _ => throw "malformed PDF: a page tree node has neither /Type /Page nor /Kids"
  return out

/-- A file's text: each page's runs in content order, form content read in place, and what the
reading could not read. -/
public structure Extracted where
  pages : Array (Nat × Array Run)
  losses : Array String
  deriving Inhabited

/-- The text a file's pages show, read from its bytes. -/
public def extract (b : ByteArray) : Except String Extracted := do
  let d ← Doc.ofBytes b
  let pages ← pagesOf d
  let mut out : Array (Nat × Array Run) := #[]
  let mut losses : Array String := #[]
  for (num, p) in pages do
    let data ← d.content p
    let (items, ls) := readToks (resOf d p.resources) .unmarked (PdfContentLex.scan data)
    let (runs, ls') := expand d p.resources formDepth items
    out := out.push (num, runs)
    losses := losses ++ ls ++ ls'
  return { pages := out, losses }

/-- Runs as text: each line a line feed apart. -/
@[expose] public def runsText (runs : Array Run) : String :=
  runs.foldl (fun acc r => (if r.line && !acc.isEmpty then acc.push '\n' else acc) ++ r.text) ""

/-- The text of every page in content order, artifacts included or left out. -/
public def Extracted.contentText (x : Extracted) (artifacts : Bool) : String :=
  x.pages.foldl (fun acc (_, runs) =>
    let rs := if artifacts then runs else runs.filter (·.mark != .artifact)
    (if acc.isEmpty then acc else acc.push '\n') ++ runsText rs) ""

/-! ### Structure order -/

/-- A structure tree's leaves in order (§14.7.2): each marked-content reference as its page's
object number and identifier, or a structure element's `ActualText` standing for its subtree. -/
public inductive Leaf where
  | mcr (page : Nat) (mcid : Nat)
  | actual (s : String)
  deriving Repr, Inhabited

/-- The leaves under a structure tree's root, depth first, every element visited once. -/
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
  for _ in [0:4 * d.objectCount + 4] do
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
  return out

/-- The text a tagged file's structure reads in order: each marked-content reference's runs where
its page shows them, an element's `ActualText` in its place. -/
public def structureText (b : ByteArray) : Except String String := do
  let d ← Doc.ofBytes b
  let x ← extract b
  let leaves ← leavesOf d
  let text (p m : Nat) : String :=
    match x.pages.find? (·.1 == p) with
    | some (_, runs) => runsText (runs.filter (·.mark == .content m))
    | none => ""
  return leaves.foldl (fun acc l => match l with
    | .mcr p m => let t := text p m; acc ++ t
    | .actual s => acc ++ s) ""

end LeanTex.Core.PdfTextRead
