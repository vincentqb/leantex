module

/-! What an `inputenc` option names, in a leaf so the macro layer imports no decoder. -/

namespace LeanTex.Core.Encoding

/-- The 8-bit encodings an `inputenc` declaration can name that the engine reads. -/
public inductive Legacy where
  | windows1252
  | iso885915
  | macRoman
  deriving Repr, BEq, DecidableEq

/-- What an `inputenc` option names; any spelling inputenc does not declare names an encoding. -/
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

/-- Whether two `inputenc` options name one encoding; two unread ones only when spelled alike. -/
public def sameEncoding (a b : String) : Bool :=
  match ofOption a, ofOption b with
  | .unread, .unread => a == b
  | x, y => x == y

/-- The option in force in an `inputenc` load's options: the last one, if any. -/
public def lastOption? (options : String) : Option String :=
  (((options.splitOn ",").map (·.trimAscii.toString)).filter (!·.isEmpty)).getLast?

/-- Does an `inputenc` load with these options declare an encoding other than UTF-8? -/
public def declaresNonUtf8 (options : String) : Bool :=
  (lastOption? options).any (ofOption · != .utf8)

end LeanTex.Core.Encoding
