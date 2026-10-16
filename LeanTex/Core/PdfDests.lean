module

public import LeanTex.Core.PdfCensus
import LeanTex.Core.PdfContentLex

namespace LeanTex.Core.PdfDests

open LeanTex.Core.PdfRead
open LeanTex.Core.PdfCensus (kindOf)

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
  /-- A name neither the catalog's `/Dests` nor the name tree's `/Dests` defines. -/
  | undefined
  /-- A destination in another file (`GoToR`, `GoToE`), which these bytes cannot show. -/
  | remote
  /-- A destination that is no name, string or array, or a carrier with both `/Dest` and `/A`. -/
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
  | .undefined => "names a destination the file does not define"
  | .remote => "leads into another file"
  | .malformed => "is malformed"

public def Finding.render (f : Finding) : String :=
  let spelled := (String.fromUTF8? f.dest.render).getD s!"<{f.dest.render.size} bytes>"
  s!"object {f.obj}: {f.carrier.word} to {spelled} {f.why.word}"

/-- What a judgement reads once: the objects by number, the page tree's pages, and the two
name-to-destination tables (§12.3.2.3). -/
private structure Ctx where
  vals : Std.HashMap Nat Obj
  pages : Std.HashSet Nat
  /-- The catalog's `/Dests` dictionary, which names map. -/
  names : Std.HashMap String Obj
  /-- The name tree under the name dictionary's `/Dests`, which strings map, keyed by their bytes. -/
  strings : Std.HashMap String Obj

/-- The value behind a reference, one hop; a direct value unchanged; an unlisted reference the
null object (§7.3.10). -/
private def derefIn (vals : Std.HashMap Nat Obj) (o : Obj) : Obj :=
  if let .ref n _ := o then vals[n]?.getD .null else o

private def Ctx.deref (c : Ctx) (o : Obj) : Obj := derefIn c.vals o

/-- A string's bytes as a key, one character per byte. -/
private def bytesKey (bs : ByteArray) : String :=
  String.ofList (bs.toList.map fun b => Char.ofNat b.toNat)

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

/-- The page objects the catalog's page tree reaches (§7.7.3). -/
private def pageTree (vals : Std.HashMap Nat Obj) (pagesRoot : Obj) : Std.HashSet Nat :=
  (treeNodes vals pagesRoot).foldl (fun s (num, v) => match num with
    | some n => if kindOf v == .page then s.insert n else s
    | none => s) {}

/-- A name tree's leaves, string keys by their bytes, the first entry for a key winning (§7.9.6). -/
private def nameTree (vals : Std.HashMap Nat Obj) (root : Obj) : Std.HashMap String Obj :=
  (treeNodes vals root).foldl (fun m (_, v) => match v.get? "Names" with
    | some (.arr kv) =>
      (List.range (kv.size / 2)).foldl (fun m i =>
        match kv[2 * i]?.bind PdfContentLex.strBytes?, kv[2 * i + 1]? with
        | some k, some d => if m.contains (bytesKey k) then m else m.insert (bytesKey k) d
        | _, _ => m) m
    | _ => m) {}

/-- Table 149's fit types: the operands each takes, and whether a null operand keeps the viewer's
current value. -/
private def fits : List (String × Nat × Bool) :=
  [("XYZ", 3, true), ("Fit", 0, true), ("FitH", 1, true), ("FitV", 1, true),
   ("FitR", 4, false), ("FitB", 0, true), ("FitBH", 1, true), ("FitBV", 1, true)]

private def operandOk (nullOk : Bool) : Obj → Bool
  | .int _ | .real _ => true
  | .null => nullOk
  | _ => false

/-- An explicit destination (§12.3.2.2): a page of the page tree, a fit type and its operands. -/
private def explicit (c : Ctx) (ds : Array Obj) : Option Why :=
  match (ds[0]? : Option Obj) with
  | some (.ref n _) =>
    if !c.pages.contains n then some .notPage
    else match (ds[1]? : Option Obj) with
      | some (.name f) => match fits.lookup f with
        | some (k, nullOk) =>
          if ds.size == k + 2 && (ds.extract 2 ds.size).all (operandOk nullOk) then none
          else some .badFit
        | none => some .badFit
      | _ => some .badFit
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
  | o@(.str _) => match PdfContentLex.strBytes? o with
    | some bs => match c.strings[bytesKey bs]? with
      | some v => named c v
      | none => some .undefined
    | none => some .malformed
  | _ => some .malformed

/-- What one dictionary navigates by and fails to reach: a link annotation's or outline item's
`/Dest`, a go-to action's `/D` and structure destination, the catalog's open-action array. -/
private def own (c : Ctx) (obj : Nat) (o : Obj) : Array Finding :=
  let at_ (k : Carrier) (d : Obj) (w : Option Why) : Array Finding :=
    match w with
    | some why => #[{ obj, carrier := k, dest := d, why }]
    | none => #[]
  let carried (k : Carrier) : Array Finding :=
    match o.get? "Dest", o.get? "A" with
    | some d, none => at_ k d (reach c d)
    | some d, some _ => at_ k d (some .malformed)
    | none, some _ => #[]
    | none, none => at_ k .null (some .nowhere)
  let acted : Array Finding :=
    match o.get? "S" with
    | some (.name "GoTo") =>
      let d := (o.get? "D").getD .null
      let sd := match (o.get? "SD").map c.deref with
        | none => #[]
        | some (.arr xs) =>
          match (xs[0]?).map c.deref with
          | some se@(.dict _) =>
            if se.get? "Type" == some (.name "StructElem") then #[]
            else at_ .action (.arr xs) (some .malformed)
          | _ => at_ .action (.arr xs) (some .malformed)
        | some s => at_ .action s (some .malformed)
      at_ .action d (reach c d) ++ sd
    | some (.name "GoToR") | some (.name "GoToE") =>
      at_ .action ((o.get? "D").getD .null) (some .remote)
    | _ => #[]
  let shape : Array Finding :=
    match kindOf o with
    | .annot "Link" => carried .link
    | .outlineItem => carried .outline
    | .catalog => match (o.get? "OpenAction").map c.deref with
      | some d@(.arr _) => at_ .openAction d (reach c d)
      | _ => #[]
    | _ => #[]
  shape ++ acted

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
  let tree := match (catalog.get? "Names").map deref with
    | some names => match names.get? "Dests" with
      | some root => nameTree vals root
      | none => {}
    | none => {}
  let c : Ctx := { vals, pages := pageTree vals ((catalog.get? "Pages").getD .null)
                   names := dests, strings := tree }
  es.foldl (fun acc e => walk c e.num acc e.val) #[]

/-- `unresolved` over a file's bytes; an unreadable file is a named refusal. -/
public def ofBytes (b : ByteArray) : Except String (Array Finding) := do
  let x ← readXref b
  let es ← objectsOf b x
  return unresolved (x.trailer.getD (.dict #[])) es.val

end LeanTex.Core.PdfDests
