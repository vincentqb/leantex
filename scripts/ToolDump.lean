module

import LeanTex.Core.Decl

public section

/-! A reference tool's version line, readers of the oracles' tool output (the XML text dumps of
`pdftotext -bbox` and Ghostscript's `txtwrite`, ImageMagick's decimals) and point conversions. -/

/-- The first line a tool prints for `args`, or `unavailable` when it cannot run or fails. -/
def toolVersion (cmd : String) (args : Array String) (cwd : System.FilePath) : IO String := do
  try
    let out ← IO.Process.output { cmd, args, cwd }
    if out.exitCode == 0 then return ((out.stdout ++ out.stderr).splitOn "\n").headD ""
    return "unavailable"
  catch _ => return "unavailable"

/-- The value of the first `attr="…"` in a tag, as text. -/
def attrOf (line attr : String) : Option String := do
  let after ← (line.splitOn (attr ++ "=\""))[1]?
  (after.splitOn "\"").head?

/-- The text between `>` and `</word>`, the three XML entities the tools emit decoded with `&amp;`
last, trimmed. -/
def wordText (line : String) : String :=
  let after := String.intercalate ">" ((line.splitOn ">").drop 1)
  let body := (after.splitOn "</word>").headD ""
  (((body.replace "&lt;" "<").replace "&gt;" ">").replace "&amp;" "&").trimAscii.toString

/-- A decimal string of points to micro-points. -/
def microPt (s : String) : Option Int := do
  let (mantissa, scale) ← LeanTex.Core.Decl.parseDecimal s
  return mantissa * 1000000 / (scale : Int)

/-- Micro-points as a decimal string of points, six places. -/
def pointMicro (v : Int) : String :=
  let sign := if v < 0 then "-" else ""
  let n := v.natAbs
  let frac := toString (n % 1000000)
  s!"{sign}{n / 1000000}.{String.ofList (List.replicate (6 - frac.length) '0')}{frac}"

/-- A decimal as the tools print it (`0.0197563`, `+12.5`, `1.2e-05`); none for any other text. -/
def parseFloat (s : String) : Option Float := do
  let s := s.trimAscii.toString
  let (mant, exp) ← match s.splitOn "e" with
    | [m, e] => e.toInt?.map (m, ·)
    | [m] => some (m, 0)
    | _ => none
  let neg := mant.startsWith "-"
  let mant := if neg || mant.startsWith "+" then (mant.drop 1).toString else mant
  let (ip, fp) ← match mant.splitOn "." with
    | [i, f] => some (i, f)
    | [i] => some (i, "")
    | _ => none
  if ip.isEmpty && fp.isEmpty then none
  let i ← if ip.isEmpty then some 0 else ip.toNat?
  let f ← if fp.isEmpty then some 0 else fp.toNat?
  let v : Float := Float.ofNat i + Float.ofNat f / Float.ofNat (10 ^ fp.length)
  let v := if exp ≥ 0 then v * Float.ofNat (10 ^ exp.toNat) else v / Float.ofNat (10 ^ (-exp).toNat)
  return if neg then -v else v
