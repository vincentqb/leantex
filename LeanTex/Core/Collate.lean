module

import LeanTex.Core.Nfc
import LeanTex.Core.Hex
import LeanTex.Core.CollateData
public import Std.Data.HashMap

/-! Collation as biber sorts a reference list: the Unicode Collation Algorithm (UTS #10) at its
fourth level, uppercase first, with Unicode::Collate::Locale's tailorings. -/

namespace LeanTex.Core.Collate

/-- One string's weights, row by row. -/
public structure Key where
  primary : Array UInt32
  secondary : Array UInt32
  tertiary : Array UInt32
  deriving BEq, Repr, Inhabited

/-- One collation element in this module's rows; a zero weight is none on
its row. -/
public structure Elem where
  primary : UInt32
  secondary : UInt32
  tertiary : UInt32
  deriving BEq, Repr, Inhabited

/-- One generated row, `XXXX+YYYY=p.s.t,p.s.t` (`CollateData`): the
characters it weighs and its elements, when it reads. -/
public def decodeEntry (row : String) : Option (String × Array Elem) := do
  let [cps, ces] := row.splitOn "=" | none
  let chars ← (cps.splitOn "+").mapM fun h => (Hex.value? h.toList).map Char.ofNat
  let elems ← (ces.splitOn ",").filter (!·.isEmpty) |>.mapM fun ce => do
    let [p, s, t] := ce.splitOn "." | none
    pure { primary := UInt32.ofNat (← Hex.value? p.toList)
           secondary := UInt32.ofNat (← Hex.value? s.toList)
           tertiary := UInt32.ofNat (← Hex.value? t.toList) }
  if chars.isEmpty then none else some (String.ofList chars, elems.toArray)

/-- The rows of a space-separated generated table. -/
public def rowsOf (table : String) : List String :=
  (table.splitOn " ").filter (!·.isEmpty)

/-- The default table's elements of each Latin letter, by code point,
decoded once, on first use. -/
private def letterTable : Thunk (Std.HashMap UInt32 (Array Elem)) :=
  Thunk.mk fun _ => (rowsOf CollateData.latinLetters).foldl (init := {}) fun m row =>
    match decodeEntry row with
    | some (k, es) => match k.toList with
      | [c] => m.insert c.val es
      | _ => m
    | none => m

/-- The default table's second-level weight of each combining mark. -/
private def markTable : Thunk (Std.HashMap UInt32 UInt32) :=
  Thunk.mk fun _ => (rowsOf CollateData.markWeights).foldl (init := {}) fun m row =>
    match row.splitOn "=" with
    | [c, w] => match Hex.value? c.toList, Hex.value? w.toList with
      | some c, some w => m.insert (UInt32.ofNat c) (UInt32.ofNat w)
      | _, _ => m
    | _ => m

/-- ASCII punctuation and symbols in the default table's order. -/
private def punctOrder : String := "_-,;:!?.'\"()[]{}@*/\\&#%`^+<=>|~$"

/-- A mark's second-level weight: the table's, or after every mark it
weighs, by code point. -/
private def markWeight (c : Char) : UInt32 :=
  (markTable.get.get? c.val).getD (UInt32.ofNat (0x1000 + c.toNat))

private def lowRow : UInt32 := 0x02
private def upRow : UInt32 := 0x01
private def baseRow : UInt32 := 0x20

/-- One element pushed onto the rows: a primary weight with its accent and
case weights, or, with none, an accent weight alone. -/
private def pushElem (k : Key) (e : Elem) : Key :=
  if e.primary == 0 then
    { k with secondary := if e.secondary == 0 then k.secondary else k.secondary.push e.secondary }
  else
    { primary := k.primary.push e.primary
      secondary := if e.secondary == 0 then k.secondary else k.secondary.push e.secondary
      tertiary := k.tertiary.push e.tertiary }

/-- One character's weights pushed onto the rows. -/
private def push (k : Key) (c : Char) : Key :=
  let cs := Nfc.decompose c
  match cs.toList with
  | [] => k
  | base :: marks =>
    let k := match letterTable.get.get? base.val with
      | some es => es.foldl pushElem k
      | none =>
        let case : UInt32 := if Nfc.isUpper c then upRow else lowRow
        let lb := Nfc.toLower base
        let w : UInt32 :=
          if lb == ' ' || lb == '\t' || lb == '\n' || lb == ' ' then 0x0201
          else if lb.isDigit then UInt32.ofNat (0x1000 + (lb.toNat - '0'.toNat))
          else match punctOrder.toList.findIdx? (· == lb) with
            | some i => UInt32.ofNat (0x0300 + i)
            | none =>
              if Nfc.isLetter lb then UInt32.ofNat (0x10000 + lb.toNat)
              else UInt32.ofNat (0x0800 + lb.toNat)
        { primary := k.primary.push w, secondary := k.secondary.push baseRow,
          tertiary := k.tertiary.push case }
    marks.foldl (fun k m => { k with secondary := k.secondary.push (markWeight m) }) k

/-- A string's collation key. -/
public def key (s : String) : Key :=
  s.foldl push { primary := #[], secondary := #[], tertiary := #[] }

private def rowCompare (a b : Array UInt32) : Ordering := Id.run do
  for i in [0:Nat.min a.size b.size] do
    match compare (a[i]?.getD 0) (b[i]?.getD 0) with
    | .eq => pure ()
    | o => return o
  return compare a.size b.size

/-- Two keys in collation order: the rows in turn. -/
public def Key.compare (a b : Key) : Ordering :=
  (rowCompare a.primary b.primary).then
    ((rowCompare a.secondary b.secondary).then (rowCompare a.tertiary b.tertiary))

/-- A locale's tailoring: the entries it weighs otherwise — a run of
characters and its elements — the longest run, and whether accents compare
from the string's end (French Canadian's backwards second level). -/
public structure Tailoring where
  entries : Std.HashMap String (Array Elem) := {}
  longest : Nat := 0
  backwards : Bool := false

/-- A tailoring file's rows read into a tailoring. -/
private def decodeTailoring (backwards entries : String) : Tailoring :=
  (rowsOf entries).foldl (init := { backwards := backwards == "2" }) fun t row =>
    match decodeEntry row with
    | some (k, es) => { t with entries := t.entries.insert k es, longest := max t.longest k.length }
    | none => t


/-- The locale biber sorts by for a `sortlocale` value: a babel or
polyglossia language name through its `%LOCALE_MAP` (Biber::Utils
`locale2bcp47`), anything else as written. -/
public def biberLocale (name : String) : String :=
  (CollateData.biberLocales.lookup name).getD name

/-- The locale Unicode::Collate::Locale accepts for the one asked (Locale.pm `_locale`), else
`default`. -/
public def acceptedLocale (asked : String) : String := Id.run do
  let has (l : String) : Bool := ((CollateData.localeFiles.lookup l).getD "") != ""
  if asked.isEmpty then return "default"
  let l := String.ofList (asked.toLower.toList.map fun c =>
    if c == '-' || c == ' ' || c == '.' then '_' else c)
  let l := match l.splitOn "_" with
    | parts@(_ :: _ :: _) =>
      match CollateData.typeAliases.lookup (parts.getLast?.getD "") with
      | some full => "_".intercalate (parts.dropLast ++ [full])
      | none => l
    | _ => l
  if has l then return l
  let code := l.splitOn "_"
  let lan := code.headD ""
  let rest := code.drop 1
  let (scr, rest) := match rest with
    | c :: r => if c.length == 4 then (c.capitalize, r) else ("", rest)
    | [] => ("", [])
  let (reg, rest) := match rest with
    | c :: r => if c.length < 4 then (c.toUpper, r) else ("", rest)
    | [] => ("", [])
  let var := rest.headD ""
  let withVar := if var.isEmpty then [] else
    [s!"{lan}_{scr}_{reg}_{var}", s!"{lan}_{scr}__{var}", s!"{lan}_{reg}_{var}", s!"{lan}__{var}"]
  let found := (withVar ++ [s!"{lan}_{scr}_{reg}", s!"{lan}_{scr}", s!"{lan}_{reg}", lan]).find? has
  return found.getD "default"

/-- The tailoring file a locale sorts by (`""`: the default table). -/
public def localeFile (locale : String) : String :=
  (CollateData.localeFiles.lookup (acceptedLocale locale)).getD ""

/-- A tailoring file's weights, `none` for the default table and a tailoring of another script. -/
public def tailoringFor (file : String) : Option Tailoring :=
  if file.isEmpty then none
  else (CollateData.tailorings.foldl (init := none) fun acc (f, bw, es) =>
    if f == file then some (bw, es) else acc).map fun (bw, es) => decodeTailoring bw es

/-- Does a tailoring file weigh what this module's rows cannot say? -/
public def outsideRows (file : String) : Bool := CollateData.outsideRows.contains file

/-- A string's collation key under a tailoring: at each place the longest
run of characters the tailoring weighs takes its elements, any other
character its default weights (`key`). -/
public def keyWith (t : Tailoring) (s : String) : Key := Id.run do
  if t.entries.isEmpty && !t.backwards then return key s
  let cs := s.toList.toArray
  let mut k : Key := { primary := #[], secondary := #[], tertiary := #[] }
  let mut i := 0
  for _ in [0:cs.size] do
    if h : i < cs.size then
      let mut taken := 0
      for d in [0:t.longest] do
        let len := t.longest - d
        if taken == 0 && i + len ≤ cs.size then
          if let some es := t.entries.get? (String.ofList (cs.extract i (i + len)).toList) then
            k := es.foldl pushElem k
            taken := len
      if taken == 0 then
        k := push k cs[i]
        taken := 1
      i := i + taken
    else break
  return if t.backwards then { k with secondary := k.secondary.reverse } else k

end LeanTex.Core.Collate
