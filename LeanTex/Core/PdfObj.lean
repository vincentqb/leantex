import LeanTex.Core.PdfLex

namespace LeanTex.Core.PdfRead

/-- A parsed PDF object. Strings keep their verbatim bytes, delimiters
included, so copying one back out cannot change it; reals keep their raw
spelling for the same reason, read numerically only where a box needs a
value. -/
inductive Obj where
  | null
  | bool (v : Bool)
  | int (n : Int)
  /-- A real number, raw spelling kept. -/
  | real (raw : String)
  /-- A string, literal `(…)` or hex `<…>`, verbatim bytes with delimiters. -/
  | str (raw : ByteArray)
  | name (n : String)
  | arr (xs : Array Obj)
  | dict (es : Array (String × Obj))
  | ref (num : Nat) (gen : Nat)
  deriving Inhabited, BEq

def Obj.get? (o : Obj) (k : String) : Option Obj :=
  match o with
  | .dict es => (es.find? (·.1 == k)).map (·.2)
  | _ => none

def Obj.int? (o : Obj) : Option Int :=
  match o with
  | .int n => some n
  | _ => none

-- ## Rendering an object back to bytes (§7.3)

abbrev escapeName := PdfLex.escapeName

/-! ### `render`, the writer's one spelling

The bytes one object is written as. Bytes rather than a `String` because
`.str` keeps its verbatim payload, delimiters included, and a literal
string's bytes need not be valid UTF-8. Arrays separate their elements
with one space; a dictionary pads its delimiters and follows every entry
with a space — the canonical spelling `<< /Type /Catalog >>` reads as.
The walk threads the buffer it appends to, so a nested dictionary costs no
copy of the bytes already written. -/

mutual

def Obj.renderInto (acc : ByteArray) : Obj → ByteArray
  | .null => acc ++ "null".toUTF8
  | .bool true => acc ++ "true".toUTF8
  | .bool false => acc ++ "false".toUTF8
  | .int n => acc ++ (toString n).toUTF8
  | .real raw => acc ++ raw.toUTF8
  | .str raw => acc ++ raw
  | .name n => acc ++ ("/" ++ escapeName n).toUTF8
  | .arr xs => (Obj.renderList (acc.push 91) xs.toList).push 93
  | .dict es => Obj.renderEntries (acc ++ "<< ".toUTF8) es.toList ++ ">>".toUTF8
  | .ref num gen => acc ++ (s!"{num} {gen} R").toUTF8

/-- The `List` companion for an array's elements, one space between. -/
def Obj.renderList (acc : ByteArray) : List Obj → ByteArray
  | [] => acc
  | [x] => Obj.renderInto acc x
  | x :: rest => Obj.renderList ((Obj.renderInto acc x).push 32) rest

/-- The `List` companion for a dictionary's entries: `/Key value`, each
followed by a space. -/
def Obj.renderEntries (acc : ByteArray) : List (String × Obj) → ByteArray
  | [] => acc
  | (k, v) :: rest =>
    Obj.renderEntries ((Obj.renderInto (acc ++ ("/" ++ escapeName k ++ " ").toUTF8) v).push 32) rest

end

/-- The bytes one object is written as — the writer's single spelling, so
what a dictionary *is* and how it reads are one value and one function
(`parseVal_render_id`). -/
def Obj.render (o : Obj) : ByteArray := Obj.renderInto ByteArray.empty o

/-- An object shows as the bytes it is written as: the one spelling, so a
diagnostic and a file never disagree. A payload outside UTF-8 (a hex
string's raw bytes) shows its size instead. -/
instance : Repr Obj where
  reprPrec o _ :=
    match String.fromUTF8? (Obj.render o) with
    | some s => Std.Format.text s
      | none => Std.Format.text s!"<{(Obj.render o).size} bytes>"

namespace ObjReader

/-- An unfinished container. A dictionary alternates between its key and
value, and retains the original order (including duplicate keys). -/
inductive Frame where
  | arr (xs : Array Obj)
  | dct (es : Array (String × Obj)) (key : Option String)

inductive Token where
  | value (v : Obj)
  | arrayOpen
  | arrayClose
  | dictOpen
  | dictClose

/-- Scan one token from its first byte. Whitespace belongs to the caller;
container balancing belongs to the frame machine. -/
def readToken (b : ByteArray) (i : Nat) : Except String (Token × Nat) := do
  let c := PdfLex.at? b i
  if c == 256 then throw "truncated PDF: an object ends mid-file"
  if c == 91 then return (.arrayOpen, i+1)
  if c == 93 then return (.arrayClose, i+1)
  if c == 60 && PdfLex.at? b (i+1) == 60 then return (.dictOpen, i+2)
  if c == 62 && PdfLex.at? b (i+1) == 62 then return (.dictClose, i+2)
  if c == 60 then
    let j := PdfLex.scanHexEnd b (i+1)
    if PdfLex.at? b j != 62 then throw "truncated PDF: a hex string never closes"
    return (.value (.str (b.extract i (j+1))), j+1)
  if c == 40 then
    match PdfLex.scanLitString b i with
    | some j => return (.value (.str (b.extract i j)), j)
    | none => throw "truncated PDF: a string never closes"
  if c == 47 then
    let (nm,j) := PdfLex.parseName b i
    return (.value (.name nm), j)
  if PdfLex.numByte c then
    let (raw,j) := PdfLex.scanNumber b i
    if raw.contains '.' then return (.value (.real raw), j)
    match raw.toInt? with
    | none => throw s!"malformed PDF: unreadable number '{raw}'"
    | some n =>
      if n ≥ 0 then
        match PdfLex.tryRef b j with
        | some (gen,k) => return (.value (.ref n.toNat gen), k)
        | none => return (.value (.int n), j)
      else return (.value (.int n), j)
  if let some j := PdfLex.keywordAt b i "true" then return (.value (.bool true), j)
  if let some j := PdfLex.keywordAt b i "false" then return (.value (.bool false), j)
  if let some j := PdfLex.keywordAt b i "null" then return (.value .null, j)
  throw s!"malformed PDF: unexpected byte {c} in an object"

inductive State where
  | scan (stack : Array Frame) (pos : Nat)
  | result (r : Except String (Obj × Nat))

/-- Deliver a completed value to the surrounding container, or return it
when no frame remains. All container accumulation goes through this site. -/
def accept (stack : Array Frame) (v : Obj) (i : Nat) : ForInStep State :=
  match stack.back? with
  | none => .done (.result (.ok (v,i)))
  | some (.arr xs) =>
    .yield (.scan (stack.set! (stack.size-1) (.arr (xs.push v))) i)
  | some (.dct es none) =>
    match v with
    | .name k => .yield (.scan (stack.set! (stack.size-1) (.dct es (some k))) i)
    | _ => .done (.result (.error "malformed PDF: a dictionary key is not a name"))
  | some (.dct es (some k)) =>
    .yield (.scan (stack.set! (stack.size-1) (.dct (es.push (k,v)) none)) i)

/-- One byte-consuming transition of the actual reader. The progress
proof composes these transitions, including the final `done` transition;
it does not restate the loop as a different parser. -/
def step (b : ByteArray) : State → ForInStep State
  | .result r => .done (.result r)
  | .scan stack pos =>
    let i := PdfLex.skipWs b pos
    match readToken b i with
    | .error e => .done (.result (.error e))
    | .ok (.value v,j) => accept stack v j
    | .ok (.arrayOpen,j) => .yield (.scan (stack.push (.arr #[])) j)
    | .ok (.dictOpen,j) => .yield (.scan (stack.push (.dct #[] none)) j)
    | .ok (.arrayClose,j) =>
      match stack.back? with
      | some (.arr xs) => accept stack.pop (.arr xs) j
      | _ => .done (.result (.error "malformed PDF: unbalanced ']'"))
    | .ok (.dictClose,j) =>
      match stack.back? with
      | some (.dct es none) => accept stack.pop (.dict es) j
      | some (.dct _ (some k)) =>
        .done (.result (.error s!"malformed PDF: dictionary key /{k} has no value"))
      | _ => .done (.result (.error "malformed PDF: unbalanced '>>'"))

end ObjReader

/-- Parse one object at `i0` (§7.3). The frame stack avoids recursive calls
on input bytes, and the file's byte count bounds the transition loop. -/
def parseVal (b : ByteArray) (i0 : Nat) : Except String (Obj × Nat) :=
  let state := (forIn [0:b.size+2] (ObjReader.State.scan #[] i0)
    (fun _ s => pure (ObjReader.step b s)) : Id ObjReader.State).run
  match state with
  | .result r => r
  | .scan _ _ => .error "malformed PDF: an object nests deeper than the file is long"

end LeanTex.Core.PdfRead
