module

/-! # What an `inputenc` option names

The vocabulary of an input-encoding declaration, apart from the decoder
that reads files in it: the macro layer reads a package call's options
through these names, and the decoding door (`Encoding`) reads each file in
what they name. A leaf, so the macro layer imports no decoder. -/

namespace LeanTex.Core.Encoding

/-- The 8-bit encodings an `inputenc` declaration can name that the engine
reads. -/
public inductive Legacy where
  | windows1252
  | iso885915
  | macRoman
  deriving Repr, BEq, DecidableEq

/-- What an `inputenc` option names. inputenc reads every option it does
not declare as an encoding name, so any other spelling is an encoding the
engine has no table for. -/
public inductive Choice where
  /-- UTF-8, or ASCII, which UTF-8 reads unchanged. -/
  | utf8
  /-- An encoding the engine reads. -/
  | legacy (e : Legacy)
  /-- An encoding inputenc reads that the engine carries no table for. -/
  | unread
  deriving Repr, BEq, DecidableEq

public def ofOption : String → Choice
  | "utf8" | "utf8x" | "ascii" => .utf8
  | "latin1" | "ansinew" | "cp1252" => .legacy .windows1252
  | "latin9" => .legacy .iso885915
  | "applemac" => .legacy .macRoman
  | _ => .unread

/-- Do two `inputenc` options name one encoding? Spellings of one table do;
two encodings the engine has no table for are one only when spelled alike,
since nothing here says what either reads. -/
public def sameEncoding (a b : String) : Bool :=
  match ofOption a, ofOption b with
  | .unread, .unread => a == b
  | x, y => x == y

/-- The option in force in an `inputenc` load's options: the last, which
inputenc's option processing leaves in force, or none when there is none. -/
public def lastOption? (options : String) : Option String :=
  (((options.splitOn ",").map (·.trimAscii.toString)).filter (!·.isEmpty)).getLast?

/-- Does an `inputenc` load with these options declare an encoding other
than UTF-8? Then what it does to each file is the decoding door's to name,
and the load has nothing left to translate. -/
public def declaresNonUtf8 (options : String) : Bool :=
  (lastOption? options).any (ofOption · != .utf8)

end LeanTex.Core.Encoding
