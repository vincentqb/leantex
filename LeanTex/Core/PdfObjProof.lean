import LeanTex.Core.PdfObj
import LeanTex.Core.PdfNameProof
import LeanTex.Core.PdfStringProof

namespace LeanTex.Core.PdfRead

open PdfLex

/-- Names are byte strings in the reader. The writer substitutes a name
for the empty string; neither that substitution nor truncating a Unicode
scalar to a byte is reversible. -/
def Obj.NameSpelling (s : String) : Prop :=
  s ≠ "" ∧ ∀ c ∈ s.toList, c.toNat < 256

/-- The reader retains a numeric token containing a decimal point
verbatim. This is its spelling domain, not a claim of numeric validity:
the scanner also accepts repeated signs and decimal points. -/
def Obj.RealSpelling (s : String) : Prop :=
  '.' ∈ s.toList ∧ ∀ c ∈ s.toList, numByte c.toNat = true

/-- Exact string delimiters and a balanced literal body, or a hex body
which cannot contain a delimiter. The source bytes, including escapes
and whitespace, remain the object's value. -/
inductive Obj.StringSpelling : List Nat → Prop
  | literal {cs} : LiteralBody cs → StringSpelling (40 :: cs ++ [41])
  | hex {cs} :
      (∀ c ∈ cs, hexVal c ≠ none ∨ isWs c = true) →
      StringSpelling (60 :: cs ++ [62])

/-- A recursive, syntactic representability domain. In particular,
dictionary keys obey the same byte-name condition as name objects.
Nothing in this predicate calls the parser or assumes its result. -/
inductive Obj.Representable : Obj → Prop
  | null : Representable .null
  | bool (v) : Representable (.bool v)
  | int (n) : Representable (.int n)
  | real {s} : RealSpelling s → Representable (.real s)
  | str {b} : StringSpelling (b.data.toList.map UInt8.toNat) → Representable (.str b)
  | name {s} : NameSpelling s → Representable (.name s)
  | arr {xs} : (∀ x ∈ xs, Representable x) → Representable (.arr xs)
  | dict {es} : (∀ e ∈ es, NameSpelling e.1) → (∀ e ∈ es, Representable e.2) →
      Representable (.dict es)
  | ref (num gen) : Representable (.ref num gen)

theorem bytes_append_push (a b : ByteArray) (c : UInt8) :
    (a ++ b).push c = a ++ b.push c := by
  apply ByteArray.ext
  simp only [ByteArray.data_append, ByteArray.data_push, Array.append_push]

mutual

/-- Buffer accumulation preserves the complete prefix, for every object,
including raw strings outside UTF-8. This is the renderer's composition
law used to place its spelling inside a larger input. -/
theorem Obj.renderInto_append (a b : ByteArray) (o : Obj) :
    o.renderInto (a ++ b) = a ++ o.renderInto b := by
  cases o with
  | null | int _ | real _ | str _ | name _ | ref _ _ =>
    simp [Obj.renderInto, ByteArray.append_assoc]
  | bool v => cases v <;> simp [Obj.renderInto, ByteArray.append_assoc]
  | arr xs =>
    simp only [Obj.renderInto, bytes_append_push, Obj.renderList_append]
  | dict es =>
    simp only [Obj.renderInto, ByteArray.append_assoc, Obj.renderEntries_append]

theorem Obj.renderList_append (a b : ByteArray) (xs : List Obj) :
    Obj.renderList (a ++ b) xs = a ++ Obj.renderList b xs := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    cases xs with
    | nil => exact Obj.renderInto_append a b x
    | cons y ys =>
      simp only [Obj.renderList, Obj.renderInto_append, bytes_append_push,
        Obj.renderList_append]

theorem Obj.renderEntries_append (a b : ByteArray) (es : List (String × Obj)) :
    Obj.renderEntries (a ++ b) es = a ++ Obj.renderEntries b es := by
  cases es with
  | nil => rfl
  | cons e es =>
    rcases e with ⟨k,v⟩
    simp only [Obj.renderEntries, ByteArray.append_assoc, Obj.renderInto_append,
      bytes_append_push, Obj.renderEntries_append]

end

theorem Obj.renderInto_exact (a : ByteArray) (o : Obj) :
    o.renderInto a = a ++ o.render := by
  simpa [Obj.render] using Obj.renderInto_append a ByteArray.empty o

theorem Obj.renderList_exact (a : ByteArray) (xs : List Obj) :
    Obj.renderList a xs = a ++ Obj.renderList ByteArray.empty xs := by
  simpa using Obj.renderList_append a ByteArray.empty xs

theorem Obj.renderEntries_exact (a : ByteArray) (es : List (String × Obj)) :
    Obj.renderEntries a es = a ++ Obj.renderEntries ByteArray.empty es := by
  simpa using Obj.renderEntries_append a ByteArray.empty es

theorem Obj.name_octets (s : String) (hn : s ≠ "") :
    octets ("/" ++ escapeName s).toUTF8 =
      47 :: (s.toList.flatMap nameChars).map Char.toNat := by
  simp only [escapeName, PdfLex.escapeName_exact s hn]
  have ha : ∀ c ∈ '/' :: s.toList.flatMap nameChars, c.toNat < 128 := by
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · decide
    · obtain ⟨d,_,hd⟩ := List.mem_flatMap.mp hc
      exact nameChars_ascii d c hd
  have hh := octets_ascii _ ha
  simpa only [String.ofList_cons, show String.singleton '/' = "/" from rfl,
    List.map_cons, show '/'.toNat = 47 from rfl] using hh

theorem Obj.name_size (s : String) (hn : s ≠ "") :
    ("/" ++ escapeName s).toUTF8.size = 1+(s.toList.flatMap nameChars).length := by
  have hh := congrArg List.length (Obj.name_octets s hn)
  simpa [Nat.add_comm] using hh

end LeanTex.Core.PdfRead
