module

namespace LeanTex.Core.Flate

/-- Why a stream does not decode: its output passes the caller's bound, or its bytes are not the
format they claim, as the reason says. -/
public inductive Error where
  | budget
  | malformed (why : String)
  deriving Repr, BEq, Inhabited

public instance : ToString Error where
  toString
    | .budget => "the stream decodes past its bound"
    | .malformed why => why

end LeanTex.Core.Flate
