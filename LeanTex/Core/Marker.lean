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
group, changes the flowing palette, opens a block where no paragraph is open, and takes the group
after it as its argument. -/
public structure Reading where
  declares : Bool
  flows : Bool
  opensBlock : Bool
  takesGroup : Bool

public def Kind.reading : Kind → Reading
  | .ink => ⟨true, true, true, false⟩
  | .lang => ⟨true, false, true, false⟩
  | .series | .family | .file | .environBody => ⟨false, false, false, false⟩
  | .pageColor | .pageColorReset => ⟨false, true, true, false⟩
  | .fontSize => ⟨true, false, false, false⟩
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

/-- `\fontsize`'s size and leading as one marker's name. -/
public def fontSizeName (size leading : String) : String :=
  name .fontSize (size ++ "\u0000" ++ leading)

/-- `\fontsize`'s size and leading, read back from its marker's value. -/
public def fontSizeParts (spec : String) : Option (String × String) :=
  match spec.splitOn "\u0000" with
  | [size, leading] => some (size, leading)
  | _ => none

end LeanTex.Core.Marker
