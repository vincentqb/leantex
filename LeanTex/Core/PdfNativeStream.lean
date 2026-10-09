module

public import LeanTex.Core.Pdf
public import LeanTex.Core.PdfCensus
import all LeanTex.Core.Pdf
import all LeanTex.Core.PdfCensus
import all LeanTex.Core.PdfRead
import all LeanTex.Core.PdfObj
import all LeanTex.Core.PdfLex
import all LeanTex.Core.PdfStreamSpelling

namespace LeanTex.Core.Pdf
open PdfRead PdfLex

/-! Source syntax of the streams emitted without an imported image graph.
The descriptions below cover the writer's literal prefixes; they contain
no parser result or assumption about the validity of a font program. -/

private def StreamPrefix.fields : StreamPrefix → Array (String × Obj)
  | .content => #[]
  | .openType => #[("Subtype", .name "OpenType")]
  | .trueType n => #[("Length1", .int n)]
  | .metadata => #[("Type", .name "Metadata"), ("Subtype", .name "XML")]
  | .figForm x0 y0 x1 y1 res group =>
    #[("Type", .name "XObject"), ("Subtype", .name "Form"),
      ("BBox", .arr #[.int x0, .int y0, .int x1, .int y1]), ("Resources", .ref res 0)] ++
    (if group then #[("Group", .dict #[("Type", .name "Group"), ("S", .name "Transparency"),
      ("I", .bool true)])] else #[])

public def StreamPrefix.dict (p : StreamPrefix) (filtered : Bool) (length : Nat) : Obj :=
  .dict (p.fields ++ (if filtered then #[("Filter", .name "FlateDecode")] else #[]) ++
    #[("Length", .int length)])

public def StreamPrefix.spelling (p : StreamPrefix) (filtered : Bool) (length : Nat) : ByteArray :=
  (s!"<< {p.fragment filtered} /Length {length} >>").toUTF8

public theorem StreamPrefix.dict_representable_exact (p : StreamPrefix) (filtered : Bool)
    (length : Nat) : (p.dict filtered length).Representable := by
  cases p
  case figForm x0 y0 x1 y1 res group =>
    have hbox : (Obj.arr #[.int x0, .int y0, .int x1, .int y1]).Representable := by
      apply Obj.Representable.arr
      intro x hx
      simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> exact Obj.Representable.int _
    have hgroup : (Obj.dict #[("Type", .name "Group"), ("S", .name "Transparency"),
        ("I", .bool true)]).Representable := by
      apply Obj.Representable.dict
      · intro e he
        simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl <;> simp [Obj.NameSpelling]
      · intro e he
        simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl
        · exact Obj.Representable.name (by simp [Obj.NameSpelling])
        · exact Obj.Representable.name (by simp [Obj.NameSpelling])
        · exact Obj.Representable.bool _
    cases filtered <;> cases group <;>
      unfold StreamPrefix.dict StreamPrefix.fields <;> apply Obj.Representable.dict
    all_goals intro e he
    all_goals simp only [Bool.false_eq_true, ↓reduceIte, Array.mem_append,
      List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at he
    repeat (any_goals (rcases he with he | he))
    all_goals try subst e
    all_goals first
      | exact Obj.Representable.name (by simp [Obj.NameSpelling])
      | exact Obj.Representable.int _
      | exact Obj.Representable.ref _ _
      | exact hbox
      | exact hgroup
      | solve | simp [Obj.NameSpelling]
  all_goals (cases filtered <;> unfold StreamPrefix.dict StreamPrefix.fields <;>
    apply Obj.Representable.dict)
  all_goals intro e he
  all_goals simp only [Bool.false_eq_true, ↓reduceIte, Array.mem_append,
    false_or, or_false, List.mem_toArray, List.mem_cons,
    List.not_mem_nil, or_false] at he
  repeat (any_goals (rcases he with he | he))
  all_goals try subst e
  all_goals first
    | exact Obj.Representable.name (by simp [Obj.NameSpelling])
    | exact Obj.Representable.int _
    | solve | simp [Obj.NameSpelling]

private theorem repr_natCast (n : Nat) : Int.repr (n : Int) = Nat.repr n := by
  simp [Int.repr_eq_ite]


private theorem push_append (b : ByteArray) (c : UInt8) :
    b.push c = b ++ ⟨#[c]⟩ := by
  apply ByteArray.ext
  rw [ByteArray.data_push, ByteArray.data_append]
  exact Array.push_eq_append

private def StreamPrefix.rendered (p : StreamPrefix) (filtered : Bool) (length : Nat) :
    ByteArray :=
  match p with
  | .content => Obj.paddedDict
      ((if filtered then #[("Filter", .name "FlateDecode")] else #[]) ++
        #[("Length", .int length)])
  | _ => (p.dict filtered length).render

set_option maxRecDepth 4096 in
private theorem StreamPrefix.spelling_rendered (p : StreamPrefix) (filtered : Bool)
    (length : Nat) : p.spelling filtered length = p.rendered filtered length := by
  cases p
  case figForm x0 y0 x1 y1 res group =>
    cases filtered <;> cases group <;>
      simp only [StreamPrefix.rendered, StreamPrefix.dict, StreamPrefix.fields,
        StreamPrefix.spelling, StreamPrefix.fragment, StreamPrefix.text,
        Bool.false_eq_true, ↓reduceIte, Obj.render, Obj.renderInto,
        Array.toList_append, List.append_nil, List.nil_append, List.cons_append,
        Obj.renderEntries, Obj.renderList, toString, push_append, String.append_assoc,
        utf8_append, ByteArray.append_assoc, ByteArray.empty_append]
    all_goals apply ByteArray.ext
    all_goals apply Array.toList_inj.mp
    all_goals simp only [ByteArray.data_append, Array.toList_append,
      String.toUTF8_eq_toByteArray, repr_natCast]
    all_goals rfl
  all_goals (cases filtered <;>
    simp only [StreamPrefix.rendered, StreamPrefix.dict, StreamPrefix.fields,
      StreamPrefix.spelling, StreamPrefix.fragment, StreamPrefix.text,
      Bool.false_eq_true, ↓reduceIte, Obj.paddedDict, Obj.render, Obj.renderInto,
      Array.toList_append, List.append_nil, List.nil_append, List.cons_append,
      Obj.renderEntries, toString, push_append, String.append_assoc, utf8_append,
      ByteArray.append_assoc, ByteArray.empty_append])
  all_goals apply ByteArray.ext
  all_goals apply Array.toList_inj.mp
  all_goals simp only [ByteArray.data_append, Array.toList_append,
    String.toUTF8_eq_toByteArray, Int.repr_eq_ite, Int.natCast_nonneg,
    ↓reduceIte, Int.toNat_natCast]
  all_goals rfl

/-- The four production prefixes spell the very dictionary they describe,
including the extra space emitted for an empty prefix. -/
public theorem StreamPrefix.spelling_exact (p : StreamPrefix) (filtered : Bool) (length : Nat) :
    (p.dict filtered length).Spelling (p.spelling filtered length) := by
  rw [p.spelling_rendered]
  have h := p.dict_representable_exact filtered length
  cases p
  case content =>
    simpa only [StreamPrefix.dict, StreamPrefix.fields, Array.empty_append,
      StreamPrefix.rendered] using Obj.Spelling.paddedDict h
  all_goals exact Obj.Spelling.render h

public theorem StreamPrefix.length_exact (p : StreamPrefix) (filtered : Bool) (length : Nat) :
    (p.dict filtered length).get? "Length" = some (.int length) := by
  cases p
  case figForm _ _ _ _ _ group =>
    cases filtered <;> cases group <;> simp [StreamPrefix.dict, StreamPrefix.fields, Obj.get?]
  all_goals cases filtered <;> simp [StreamPrefix.dict, StreamPrefix.fields, Obj.get?]

/-- These stream dictionaries never enter the font-dictionary census.
A font program's stream is distinct from the font and descriptor objects
that reference it. -/
public theorem StreamPrefix.kind_exact (p : StreamPrefix) (filtered : Bool) (length : Nat) :
    PdfCensus.kindOf (p.dict filtered length) ≠ .font := by
  cases p
  case figForm _ _ _ _ _ group =>
    cases filtered <;> cases group
    all_goals change PdfCensus.Kind.form ≠ .font; decide
  all_goals cases filtered
  all_goals first
    | change PdfCensus.Kind.other ≠ .font; decide
    | change PdfCensus.Kind.metadata ≠ .font; decide

/-- The row serializer emits the certified dictionary spelling followed
by precisely the retained bytes and the real closing markers. -/
public theorem native_row_bytes_exact (id : Nat) (p : StreamPrefix) (filtered : Bool)
    (raw : ByteArray) :
    rowInto ByteArray.empty id (.stream (p.fragment filtered) raw) =
      (s!"{id} 0 obj\n").toUTF8 ++ p.spelling filtered raw.size ++
        "\nstream\n".toUTF8 ++ raw ++ "\nendstream\nendobj\n".toUTF8 := by
  simp only [rowInto, StreamPrefix.spelling, toString, utf8_append,
    ByteArray.empty_append, ByteArray.append_assoc]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp only [ByteArray.data_append, Array.toList_append, String.toUTF8_eq_toByteArray]
  rfl

end LeanTex.Core.Pdf
