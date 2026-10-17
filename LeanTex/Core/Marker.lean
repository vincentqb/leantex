module

import LeanTex.Core.KeyVal

/-! The controls the engine's passes write for declarations they lower, each named with a leading
space, so a document's control space and words read as text where one would spell it. -/

namespace LeanTex.Core.Marker

/-- What a marker declares: an ink, a BCP 47 language, an NFSS series, a font slot by number, the
file the preamble's declarations come from, xcolor's page ground or its reset, `\fontsize`'s size
and leading, environ's `\BODY` in a definition's begin code, or cleveref's range of two labels. -/
public inductive Kind where
  | ink | lang | series | family | file | pageColor | pageColorReset | fontSize | environBody
  | crefRange | crefRangeUp
  deriving DecidableEq, Repr, Inhabited

public def Kind.words : List (String × Kind) :=
  [("ink", .ink), ("lang", .lang), ("series", .series), ("family", .family), ("file", .file),
   ("pagecolor", .pageColor), ("nopagecolor", .pageColorReset), ("fontsize", .fontSize),
   ("environ", .environBody), ("crefrange", .crefRange), ("Crefrange", .crefRangeUp)]

public def Kind.word (k : Kind) : String := ((Kind.words.find? (·.2 == k)).map (·.1)).getD ""

/-- How the passes read a marker: whether it declares a style, size or ink for the rest of its
group, past each paragraph break in it; changes the flowing palette; sets the page ground; and takes
the group after it as its argument. -/
public structure Reading where
  declares : Bool
  flows : Bool
  ground : Bool
  takesGroup : Bool

/-- Whether a marker opens a block where no paragraph is open. -/
public def Reading.opensBlock (r : Reading) : Bool := r.declares || r.ground

@[expose] public def Kind.reading : Kind → Reading
  | .ink => ⟨true, true, false, false⟩
  | .lang | .series | .family | .fontSize => ⟨true, false, false, false⟩
  | .pageColor | .pageColorReset => ⟨false, true, true, false⟩
  | .file | .environBody => ⟨false, false, false, false⟩
  | .crefRange | .crefRangeUp => ⟨false, false, false, true⟩

/-- A marker's control name: a space, its kind's word, a space and the value it carries. -/
public def name (k : Kind) (v : String) : String := " " ++ k.word ++ " " ++ v

/-- The kind and value a control's name spells, where it is a marker's. -/
public def read? (n : String) : Option (Kind × String) :=
  if n.front? == some ' ' then
    let cut := KeyVal.cutAt ' ' (n.toList.drop 1)
    cut.2.bind fun v => (Kind.words.lookup (String.ofList cut.1)).map (·, String.ofList v)
  else none

/-- How the passes read a control, where it is a marker. -/
public def readingOf? (n : String) : Option Reading := (read? n).map (·.1.reading)

/-- The value a control's name carries, where it is a marker of kind `k`. -/
public def value? (k : Kind) (n : String) : Option String :=
  (read? n).bind fun (k', v) => if k' == k then some v else none

/-- A control no declaring marker names carries no value of a declaring kind. -/
public theorem value?_none_of_declares {k : Kind} {n : String} (hk : k.reading.declares = true)
    (h : (readingOf? n).any (·.declares) = false) : value? k n = none := by
  unfold value?
  unfold readingOf? at h
  cases hr : read? n with
  | none => rfl
  | some p =>
    obtain ⟨k', v⟩ := p
    rw [hr] at h
    by_cases hkk : k' = k
    · subst hkk
      simp [hk] at h
    · simp [hkk]

/-- The reading of a control a marker names is its kind's. -/
public theorem readingOf?_of_read? {n : String} {k : Kind} {v : String}
    (h : read? n = some (k, v)) : readingOf? n = some k.reading := by
  simp [readingOf?, h]

/-- `\fontsize`'s size and leading as one marker's name. -/
public def fontSizeName (size leading : String) : String :=
  name .fontSize (size ++ "\u0000" ++ leading)

/-- `\fontsize`'s size and leading, read back from its marker's value. -/
public def fontSizeParts (spec : String) : Option (String × String) :=
  match spec.splitOn "\u0000" with
  | [size, leading] => some (size, leading)
  | _ => none

end LeanTex.Core.Marker
