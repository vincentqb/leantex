module

public import LeanTex.Core.PdfCensus
import LeanTex.Core.PdfContentLex

namespace LeanTex.Core.PdfDests

open LeanTex.Core.PdfRead
open LeanTex.Core.PdfCensus (kindOf)
open LeanTex.Core.Dim (Sp)

/-! Where a file's navigation leads, read from its bytes by the engine's own reader (ISO 32000-2
§12.3.2, §12.6.4.2-4), never from the writer's intent. -/

/-- What carries a navigation: a link annotation, an outline item, the catalog's open action, or an
action dictionary. -/
public inductive Carrier where
  | link
  | outline
  | openAction
  | action
  deriving DecidableEq, Repr, Inhabited

/-- Why a navigation reaches no destination the file defines. -/
public inductive Why where
  /-- A link annotation or outline item naming neither a destination nor an action. -/
  | nowhere
  /-- An explicit destination whose first element is no page of the page tree. -/
  | notPage
  /-- An explicit destination whose fit type or operands Table 149 does not admit. -/
  | badFit
  /-- An explicit destination whose coordinates stand outside its page's media box. -/
  | offPage
  /-- A name neither the catalog's `/Dests` nor the name tree's `/Dests` defines as a reader finds
  it. -/
  | undefined
  /-- A destination in another file (`GoToR`, `GoToE`), which these bytes cannot show. -/
  | remote
  /-- A destination that is no name, string or array, an action that is no dictionary, or a
  carrier with both `/Dest` and `/A`. -/
  | malformed
  deriving DecidableEq, Repr, Inhabited

/-- One navigation reaching no destination the file defines. -/
public structure Finding where
  /-- The object whose value holds the navigation. -/
  obj : Nat
  carrier : Carrier
  /-- The destination as the file spells it. -/
  dest : Obj
  why : Why
  deriving Repr, Inhabited

public def Carrier.word : Carrier → String
  | .link => "a link annotation"
  | .outline => "an outline item"
  | .openAction => "the open action"
  | .action => "a go-to action"

public def Why.word : Why → String
  | .nowhere => "names no destination"
  | .notPage => "names no page of the page tree"
  | .badFit => "spells a fit Table 149 does not admit"
  | .offPage => "stands outside its page's media box"
  | .undefined => "names a destination the file does not define"
  | .remote => "leads into another file"
  | .malformed => "is malformed"

public def Finding.render (f : Finding) : String :=
  let spelled := (String.fromUTF8? f.dest.render).getD s!"<{f.dest.render.size} bytes>"
  s!"object {f.obj}: {f.carrier.word} to {spelled} {f.why.word}"

/-- What a judgement reads once: the objects by number, the page tree's pages with their media
boxes, and the two name-to-destination tables (§12.3.2.3). -/
private structure Ctx where
  vals : Std.HashMap Nat Obj
  /-- Each page of the page tree, with its media box `(x0, y0, x1, y1)` where it inherits one. -/
  pages : Std.HashMap Nat (Option (Sp × Sp × Sp × Sp))
  /-- The catalog's `/Dests` dictionary, which names map. -/
  names : Std.HashMap String Obj
  /-- The root of the name dictionary's `/Dests` tree, which strings map. -/
  strings : Option Obj

/-- The value behind a reference, one hop; a direct value unchanged; an unlisted reference the
null object (§7.3.10). -/
private def derefIn (vals : Std.HashMap Nat Obj) (o : Obj) : Obj :=
  if let .ref n _ := o then vals[n]?.getD .null else o

private def Ctx.deref (c : Ctx) (o : Obj) : Obj := derefIn c.vals o

/-- The nodes a tree reaches from `root` through `/Kids`, each listed object once, with its number
when reached by reference; a level adding no node ends the walk, so it takes at most one level per
listed object. -/
private def treeNodes (vals : Std.HashMap Nat Obj) (root : Obj) : Array (Option Nat × Obj) :=
  Id.run do
  let deref := derefIn vals
  let mut seen : Std.HashSet Nat := {}
  let mut out : Array (Option Nat × Obj) := #[]
  let mut level : Array Obj := #[root]
  for _ in [0:vals.size + 1] do
    if level.isEmpty then break
    let mut next : Array Obj := #[]
    for o in level do
      let num := match o with
        | .ref n _ => some n
        | _ => none
      unless num.any seen.contains do
        if let some n := num then seen := seen.insert n
        let v := deref o
        out := out.push (num, v)
        if let some (.arr kids) := (v.get? "Kids").map deref then
          next := next ++ kids
    level := next
  return out

/-- A rectangle's four numbers. -/
private def rectOf : Obj → Option (Sp × Sp × Sp × Sp)
  | .arr #[a, b, c, d] => do return (← a.sp?, ← b.sp?, ← c.sp?, ← d.sp?)
  | _ => none

/-- A page's media box, its own or the nearest ancestor's (§7.7.3.4), up the `/Parent` chain. -/
private def mediaBox (vals : Std.HashMap Nat Obj) (page : Obj) : Option (Sp × Sp × Sp × Sp) :=
  Id.run do
  let mut node := page
  for _ in [0:vals.size + 1] do
    if let some box := (node.get? "MediaBox").map (derefIn vals) |>.bind rectOf then return some box
    match node.get? "Parent" with
    | some p => node := derefIn vals p
    | none => return none
  return none

/-- The page objects the catalog's page tree reaches (§7.7.3), with their media boxes. -/
private def pageTree (vals : Std.HashMap Nat Obj) (pagesRoot : Obj) :
    Std.HashMap Nat (Option (Sp × Sp × Sp × Sp)) :=
  (treeNodes vals pagesRoot).foldl (fun s (num, v) => match num with
    | some n => if kindOf v == .page then s.insert n (mediaBox vals v) else s
    | none => s) {}

/-- Byte strings in ascending order (§7.9.6: keys ordered lexically by their bytes). -/
private def bytesLt : List UInt8 → List UInt8 → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a < b || (a == b && bytesLt as bs)

private def keyBytes (o : Obj) : Option (List UInt8) :=
  (PdfContentLex.strBytes? o).map (·.toList)

/-- Whether a node's `/Limits` hold a key. -/
private def limitsHold (node : Obj) (key : List UInt8) : Bool :=
  match node.get? "Limits" with
  | some (.arr #[lo, hi]) =>
    match keyBytes lo, keyBytes hi with
    | some l, some h => !bytesLt key l && !bytesLt h key
    | _, _ => false
  | _ => false

/-- A key's value in a name tree as a reader finds it (§7.9.6): down the kid whose `/Limits` hold
it, then in a leaf's `/Names`, whose keys stand in ascending order. -/
private def treeLookup (vals : Std.HashMap Nat Obj) (root : Obj) (key : List UInt8) :
    Option Obj := Id.run do
  let mut node := derefIn vals root
  for _ in [0:vals.size + 1] do
    match node.get? "Names" with
    | some (.arr kv) =>
      let pairs := (List.range (kv.size / 2)).filterMap fun i =>
        match kv[2 * i]?.bind keyBytes, kv[2 * i + 1]? with
        | some k, some d => some (k, d)
        | _, _ => none
      let keys := pairs.map (·.1)
      unless pairs.length == kv.size / 2 && (keys.zip keys.tail).all (fun (a, b) => bytesLt a b) do
        return none
      return (pairs.find? (·.1 == key)).map (·.2)
    | _ =>
      match (node.get? "Kids").map (derefIn vals) with
      | some (.arr kids) =>
        match kids.find? (fun k => limitsHold (derefIn vals k) key) with
        | some k => node := derefIn vals k
        | none => return none
      | _ => return none
  return none

/-- Table 149's fit types: the operands each takes, whether a null operand keeps the viewer's
current value, and which axis each operand reads (`true` horizontal). -/
private def fits : List (String × Nat × Bool × List Bool) :=
  [("XYZ", 3, true, [true, false]), ("Fit", 0, true, []), ("FitH", 1, true, [false]),
   ("FitV", 1, true, [true]), ("FitR", 4, false, [true, false, true, false]),
   ("FitB", 0, true, []), ("FitBH", 1, true, [false]), ("FitBV", 1, true, [true])]

private def operandOk (nullOk : Bool) : Obj → Bool
  | .int _ | .real _ => true
  | .null => nullOk
  | _ => false

/-- A fit and its operands after a destination's first element; within `box` where one is given. -/
private def fitWhy (box : Option (Sp × Sp × Sp × Sp)) (ds : Array Obj) : Option Why :=
  match (ds[1]? : Option Obj) with
  | some (.name f) => match fits.lookup f with
    | some (k, nullOk, axes) =>
      let ops := ds.extract 2 ds.size
      if ds.size != k + 2 || !ops.all (operandOk nullOk) then some .badFit
      else box.bind fun (x0, y0, x1, y1) =>
        let inside := (ops.toList.zip axes).all fun (o, horizontal) => match o.sp? with
          | some v => if horizontal then x0 ≤ v && v ≤ x1 else y0 ≤ v && v ≤ y1
          | none => true
        if inside then none else some .offPage
    | none => some .badFit
  | _ => some .badFit

/-- An explicit destination (§12.3.2.2): a page of the page tree, a fit type and its operands, inside
the page's media box. -/
private def explicit (c : Ctx) (ds : Array Obj) : Option Why :=
  match (ds[0]? : Option Obj) with
  | some (.ref n _) => match c.pages[n]? with
    | some box => fitWhy box ds
    | none => some .notPage
  | _ => some .notPage

/-- A named destination's value: an explicit array, or a dictionary whose `/D` is one. -/
private def named (c : Ctx) (v : Obj) : Option Why :=
  match c.deref v with
  | .arr ds => explicit c ds
  | o@(.dict _) => match (o.get? "D").map c.deref with
    | some (.arr ds) => explicit c ds
    | _ => some .malformed
  | _ => some .malformed

/-- Where a destination leads: an explicit array, a name the catalog's `/Dests` maps, or a string
the name tree maps (§12.3.2.3). -/
private def reach (c : Ctx) (d : Obj) : Option Why :=
  match c.deref d with
  | .arr ds => explicit c ds
  | .name n => match c.names[n]? with
    | some v => named c v
    | none => some .undefined
  | o@(.str _) => match keyBytes o with
    | some key => match c.strings.bind (treeLookup c.vals · key) with
      | some v => named c v
      | none => some .undefined
    | none => some .malformed
  | _ => some .malformed

private def finding (obj : Nat) (k : Carrier) (d : Obj) : Option Why → Array Finding
  | some why => #[{ obj, carrier := k, dest := d, why }]
  | none => #[]

/-- What a link annotation or outline item navigates by: its `/Dest`, or an `/A` that is an action
dictionary, judged where it stands. -/
private def carried (c : Ctx) (obj : Nat) (k : Carrier) (o : Obj) : Array Finding :=
  match o.get? "Dest", o.get? "A" with
  | some d, none => finding obj k d (reach c d)
  | some d, some _ => finding obj k d (some .malformed)
  | none, some a => match c.deref a with
    | .dict _ => #[]
    | other => finding obj k other (some .malformed)
  | none, none => finding obj k .null (some .nowhere)

/-- A structure destination (§12.3.2.3): a structure element, a fit and its operands. -/
private def structWhy (c : Ctx) (sd : Obj) : Option Why :=
  match c.deref sd with
  | .arr xs => match (xs[0]?).map c.deref with
    | some se@(.dict _) =>
      if (se.get? "S").isSome && (se.get? "P").isSome then fitWhy none xs else some .malformed
    | _ => some .malformed
  | _ => some .malformed

/-- What one dictionary navigates by and fails to reach: a link annotation's `/Dest`, a go-to
action's `/D` and structure destination, the catalog's open-action array. -/
private def own (c : Ctx) (obj : Nat) (o : Obj) : Array Finding :=
  let acted : Array Finding :=
    match o.get? "S" with
    | some (.name "GoTo") =>
      let d := (o.get? "D").getD .null
      finding obj .action d (reach c d) ++
        ((o.get? "SD").map fun sd => finding obj .action sd (structWhy c sd)).getD #[]
    | some (.name "GoToR") | some (.name "GoToE") =>
      finding obj .action ((o.get? "D").getD .null) (some .remote)
    | _ => #[]
  let shape : Array Finding :=
    match kindOf o with
    | .annot "Link" => carried c obj .link o
    | .catalog => match (o.get? "OpenAction").map c.deref with
      | some d@(.arr _) => finding obj .openAction d (reach c d)
      | _ => #[]
    | _ => #[]
  shape ++ acted

/-- The items an outline holds (§12.3.3), each listed object once: from the root's `/First`, along
`/Next` and down each item's `/First`. -/
private def outlineItems (vals : Std.HashMap Nat Obj) (root : Obj) : Array Nat := Id.run do
  let first (o : Obj) : Array Nat := match o.get? "First" with
    | some (.ref n _) => #[n]
    | _ => #[]
  let mut seen : Std.HashSet Nat := {}
  let mut out : Array Nat := #[]
  let mut todo : Array Nat := first (derefIn vals root)
  for _ in [0:vals.size + 1] do
    let mut next : Array Nat := #[]
    for n in todo do
      unless seen.contains n do
        seen := seen.insert n
        out := out.push n
        let item := vals[n]?.getD .null
        next := next ++ first item
        if let some (.ref m _) := item.get? "Next" then next := next.push m
    if next.isEmpty then break
    todo := next
  return out

mutual

private def walk (c : Ctx) (obj : Nat) (acc : Array Finding) : Obj → Array Finding
  | o@(.dict es) => walkEntries c obj (acc ++ own c obj o) es.toList
  | .arr xs => walkList c obj acc xs.toList
  | _ => acc

private def walkList (c : Ctx) (obj : Nat) (acc : Array Finding) : List Obj → Array Finding
  | [] => acc
  | x :: rest => walkList c obj (walk c obj acc x) rest

private def walkEntries (c : Ctx) (obj : Nat) (acc : Array Finding) :
    List (String × Obj) → Array Finding
  | [] => acc
  | (_, v) :: rest => walkEntries c obj (walk c obj acc v) rest

end

/-- Every navigation the listed objects make that reaches no destination the file defines: each
link annotation and outline item, each go-to action wherever it stands, and the open action. -/
public def unresolved (trailer : Obj) (es : Array Entry) : Array Finding :=
  let vals : Std.HashMap Nat Obj := es.foldl (fun m e => m.insert e.num e.val) {}
  let deref := derefIn vals
  let catalog := PdfCensus.catalogOf es trailer
  let dests := match (catalog.get? "Dests").map deref with
    | some (.dict kv) => kv.foldl (fun m (k, v) => if m.contains k then m else m.insert k v) {}
    | _ => {}
  let c : Ctx := { vals, pages := pageTree vals ((catalog.get? "Pages").getD .null)
                   names := dests
                   strings := ((catalog.get? "Names").map deref).bind (·.get? "Dests") }
  let outline := (outlineItems vals ((catalog.get? "Outlines").getD .null)).foldl
    (fun acc n => acc ++ carried c n .outline (vals[n]?.getD .null)) #[]
  es.foldl (fun acc e => walk c e.num acc e.val) outline

/-- `unresolved` over a file's bytes; an unreadable file is a named refusal. -/
public def ofBytes (b : ByteArray) : Except String (Array Finding) := do
  let x ← readXref b
  let es ← objectsOf b x
  return unresolved (x.trailer.getD (.dict #[])) es.val

end LeanTex.Core.PdfDests
