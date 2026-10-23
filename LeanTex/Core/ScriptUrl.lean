module

/-! Whether a URL runs script when followed, as the URL Standard reads its scheme. -/

namespace LeanTex.Core.Url

/-- Whether characters, read as the URL parser reads them past every tab and line end, open with
`pat` in any ASCII case. -/
@[expose] public def runsScriptFrom : List Char → List Char → Bool
  | [], _ => true
  | _ :: _, [] => false
  | p :: ps, c :: cs =>
    if c == '\t' || c == '\n' || c == '\r' then runsScriptFrom (p :: ps) cs
    else c.toLower == p && runsScriptFrom ps cs

/-- Whether a URL navigates by running script: its scheme `javascript` in any ASCII case, read as
the URL parser reads it, after leading C0 controls and spaces and with every tab and line end
removed. -/
@[expose] public def runsScript (url : String) : Bool :=
  runsScriptFrom "javascript:".toList (url.toList.dropWhile (·.toNat ≤ 0x20))

/-- An in-page fragment never runs script. -/
public theorem runsScript_fragment (a : String) : runsScript ("#" ++ a) = false := by
  simp [runsScript, runsScriptFrom, String.toList_append]

end LeanTex.Core.Url
