module

public import LeanTex.Core.TexTextData

namespace LeanTex.Core

/-- TeX's own words for a row of the generated table, its slots filled. -/
public def Diag.tex (key : TexKey) (names : List String := []) : String :=
  key.row.fill names

/-- TeX's words where the source is TeX's, else the form's. -/
public def Diag.texOr (tex : Bool) (key : TexKey) (names : List String) (form : String) : String :=
  if tex then Diag.tex key names else form

end LeanTex.Core
