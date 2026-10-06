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

end LeanTex.Core.PdfRead
