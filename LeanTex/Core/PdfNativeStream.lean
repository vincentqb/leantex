import LeanTex.Core.Pdf
import LeanTex.Core.PdfCensus

namespace LeanTex.Core.Pdf
open PdfRead PdfLex

/-! Source syntax of the streams emitted without an imported image graph.
The descriptions below cover the writer's literal prefixes; they contain
no parser result or assumption about the validity of a font program. -/

def StreamPrefix.fields : StreamPrefix → Array (String × Obj)
  | .content => #[]
  | .openType => #[("Subtype", .name "OpenType")]
  | .trueType n => #[("Length1", .int n)]
  | .metadata => #[("Type", .name "Metadata"), ("Subtype", .name "XML")]

def StreamPrefix.dict (p : StreamPrefix) (filtered : Bool) (length : Nat) : Obj :=
  .dict (p.fields ++ (if filtered then #[("Filter", .name "FlateDecode")] else #[]) ++
    #[("Length", .int length)])

def StreamPrefix.spelling (p : StreamPrefix) (filtered : Bool) (length : Nat) : ByteArray :=
  (s!"<< {p.fragment filtered} /Length {length} >>").toUTF8

theorem StreamPrefix.dict_representable_exact (p : StreamPrefix) (filtered : Bool)
    (length : Nat) : (p.dict filtered length).Representable := by
  cases p <;> cases filtered <;>
    unfold StreamPrefix.dict StreamPrefix.fields <;> apply Obj.Representable.dict
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

private theorem StreamPrefix.spelling_rendered (p : StreamPrefix) (filtered : Bool)
    (length : Nat) : p.spelling filtered length = p.rendered filtered length := by
  cases p <;> cases filtered <;>
    simp only [StreamPrefix.rendered, StreamPrefix.dict, StreamPrefix.fields,
      StreamPrefix.spelling, StreamPrefix.fragment, StreamPrefix.text,
      Bool.false_eq_true, ↓reduceIte, Obj.paddedDict, Obj.render, Obj.renderInto,
      Array.toList_append, List.append_nil, List.nil_append, List.cons_append,
      Obj.renderEntries, toString, push_append, String.append_assoc, utf8_append,
      ByteArray.append_assoc, ByteArray.empty_append]
  all_goals apply ByteArray.ext
  all_goals apply Array.toList_inj.mp
  all_goals simp only [ByteArray.data_append, Array.toList_append]
  all_goals rfl

/-- The four production prefixes spell the very dictionary they describe,
including the extra space emitted for an empty prefix. -/
theorem StreamPrefix.spelling_exact (p : StreamPrefix) (filtered : Bool) (length : Nat) :
    (p.dict filtered length).Spelling (p.spelling filtered length) := by
  rw [p.spelling_rendered]
  have h := p.dict_representable_exact filtered length
  cases p
  case content =>
    simpa only [StreamPrefix.dict, StreamPrefix.fields, Array.empty_append,
      StreamPrefix.rendered] using Obj.Spelling.paddedDict h
  all_goals exact Obj.Spelling.render h

theorem StreamPrefix.length_exact (p : StreamPrefix) (filtered : Bool) (length : Nat) :
    (p.dict filtered length).get? "Length" = some (.int length) := by
  cases p <;> cases filtered <;> simp [StreamPrefix.dict, StreamPrefix.fields, Obj.get?]

/-- These stream dictionaries never enter the font-dictionary census.
A font program's stream is distinct from the font and descriptor objects
that reference it. -/
theorem StreamPrefix.kind_exact (p : StreamPrefix) (filtered : Bool) (length : Nat) :
    PdfCensus.kindOf (p.dict filtered length) ≠ .font := by
  cases p <;> cases filtered
  all_goals first
    | change PdfCensus.Kind.other ≠ .font; decide
    | change PdfCensus.Kind.metadata ≠ .font; decide

/-- The row serializer emits the certified dictionary spelling followed
by precisely the retained bytes and the real closing markers. -/
theorem native_row_bytes_exact (id : Nat) (p : StreamPrefix) (filtered : Bool)
    (raw : ByteArray) :
    rowInto ByteArray.empty id (.stream (p.fragment filtered) raw) =
      (s!"{id} 0 obj\n").toUTF8 ++ p.spelling filtered raw.size ++
        "\nstream\n".toUTF8 ++ raw ++ "\nendstream\nendobj\n".toUTF8 := by
  simp only [rowInto, StreamPrefix.spelling, toString, utf8_append,
    ByteArray.empty_append, ByteArray.append_assoc]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp only [ByteArray.data_append, Array.toList_append]
  rfl

end LeanTex.Core.Pdf
