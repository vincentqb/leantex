module

namespace LeanTex.Core.PdfDate

/-! A document date as the PDF writes it twice: the Info dictionary's `D:` string (ISO 32000-2
§7.9.4) and the metadata's ISO 8601 (XMP Part 1 §8.2.1.1), from one declared value. -/

/-- A date at the precision declared: a day, or a day and a time, with its offset from UTC in
minutes when stated. -/
public structure Date where
  year : Nat
  month : Nat
  day : Nat
  time : Option (Nat × Nat × Nat) := none
  zone : Option Int := none
  deriving Repr, BEq, DecidableEq, Inhabited

private def digitsVal (cs : List Char) : Option Nat :=
  if cs.isEmpty || !cs.all Char.isDigit then none
  else some (cs.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0)

/-- The days in a month of the Gregorian calendar. -/
private def monthDays (year month : Nat) : Nat :=
  if month == 2 then
    if year % 4 == 0 && (year % 100 != 0 || year % 400 == 0) then 29 else 28
  else if month == 4 || month == 6 || month == 9 || month == 11 then 30 else 31

private def valid (d : Date) : Bool :=
  1 ≤ d.month && d.month ≤ 12 && 1 ≤ d.day && d.day ≤ monthDays d.year d.month &&
    (d.time.all fun (h, m, s) => h < 24 && m < 60 && s < 60) &&
    (d.zone.all fun z => z.natAbs < 24 * 60)

/-- `Z`, `+hh:mm` or `-hh:mm` (ISO 8601), or the empty suffix. -/
private def isoZone : List Char → Option (Option Int)
  | [] => some none
  | ['Z'] => some (some 0)
  | [s, h1, h2, ':', m1, m2] => do
    let h ← digitsVal [h1, h2]
    let m ← digitsVal [m1, m2]
    let v : Int := (h * 60 + m : Nat)
    if m ≥ 60 then none else if s == '+' then some (some v) else if s == '-' then some (some (-v)) else none
  | _ => none

/-- `YYYY-MM-DD`, then optionally `Thh:mm` or `Thh:mm:ss` and a zone. -/
private def iso (cs : List Char) : Option Date := do
  let [y1, y2, y3, y4, '-', mo1, mo2, '-', d1, d2] := cs.take 10 | none
  let year ← digitsVal [y1, y2, y3, y4]
  let month ← digitsVal [mo1, mo2]
  let day ← digitsVal [d1, d2]
  match cs.drop 10 with
  | [] => some { year, month, day }
  | 'T' :: h1 :: h2 :: ':' :: m1 :: m2 :: rest =>
    let h ← digitsVal [h1, h2]
    let m ← digitsVal [m1, m2]
    let (s, zoneCs) ← match rest with
      | ':' :: s1 :: s2 :: z => (digitsVal [s1, s2]).map (·, z)
      | z => some (0, z)
    let zone ← isoZone zoneCs
    some { year, month, day, time := some (h, m, s), zone }
  | _ => none

/-- Exactly `n` digits at the front, read, and what follows them. -/
private def digitsN (n : Nat) (cs : List Char) : Option (Nat × List Char) :=
  if (cs.take n).length == n then (digitsVal (cs.take n)).map (·, cs.drop n) else none

/-- An offset's hours, then `'` and its minutes, each after the one before, and a closing `'`. -/
private def offsetMinutes (cs : List Char) : Option Nat := do
  let (h, rest) ← digitsN 2 cs
  let (m, tail) ← match rest with
    | [] | ['\''] => some (0, [])
    | '\'' :: more => digitsN 2 more
    | _ => none
  if (tail == [] || tail == ['\'']) && m < 60 then some (h * 60 + m) else none

/-- The zone after a date's seconds: none, `Z` with no offset or a zero one, or a sign and its
offset. -/
private def pdfZone : List Char → Option (Option Int)
  | [] => some none
  | 'Z' :: rest => if rest.isEmpty || offsetMinutes rest == some 0 then some (some 0) else none
  | '+' :: rest => (offsetMinutes rest).map fun v => some (v : Int)
  | '-' :: rest => (offsetMinutes rest).map fun v => some (-(v : Int))
  | _ => none

/-- `D:YYYY`, then the month, day, hour, minute and second, each present only after the one before
and defaulting as ISO 32000-2 §7.9.4 says, then a zone after the seconds, as hyperref and the Info
dictionary spell it. -/
private def pdfSpelled (cs : List Char) : Option Date := do
  let 'D' :: ':' :: rest := cs | none
  let (year, rest) ← digitsN 4 rest
  if rest.isEmpty then return { year, month := 1, day := 1 }
  let (month, rest) ← digitsN 2 rest
  if rest.isEmpty then return { year, month, day := 1 }
  let (day, rest) ← digitsN 2 rest
  if rest.isEmpty then return { year, month, day }
  let (h, rest) ← digitsN 2 rest
  if rest.isEmpty then return { year, month, day, time := some (h, 0, 0) }
  let (m, rest) ← digitsN 2 rest
  if rest.isEmpty then return { year, month, day, time := some (h, m, 0) }
  let (sec, rest) ← digitsN 2 rest
  let zone ← pdfZone rest
  return { year, month, day, time := some (h, m, sec), zone }

/-- A date in the metadata's ISO 8601 spelling, refused out of range. -/
public def parseIso? (s : String) : Option Date := (iso s.trimAscii.toString.toList).filter valid

/-- A date in the Info dictionary's `D:` spelling, refused out of range. -/
public def parseInfo? (s : String) : Option Date :=
  (pdfSpelled s.trimAscii.toString.toList).filter valid

/-- A declared date in either spelling, refused out of range. -/
public def parse? (s : String) : Option Date := (parseIso? s).orElse fun _ => parseInfo? s

private def two (n : Nat) : String := if n < 10 then s!"0{n}" else toString n

private def four (n : Nat) : String :=
  let digits := toString n
  String.ofList (List.replicate (4 - digits.length) '0') ++ digits

/-- The Info dictionary's spelling: `D:YYYYMMDDHHmmSS` with `Z` or `+HH'mm'`. -/
public def Date.pdf (d : Date) : String :=
  let day := s!"D:{four d.year}{two d.month}{two d.day}"
  match d.time with
  | none => day
  | some (h, m, s) =>
    let zone := match d.zone with
      | none => ""
      | some 0 => "Z"
      | some z => (if z < 0 then "-" else "+") ++ s!"{two (z.natAbs / 60)}'{two (z.natAbs % 60)}'"
    day ++ s!"{two h}{two m}{two s}" ++ zone

/-- The metadata's spelling: `YYYY-MM-DD`, then `Thh:mm:ss` and `Z` or `+hh:mm`. -/
public def Date.xmp (d : Date) : String :=
  let day := s!"{four d.year}-{two d.month}-{two d.day}"
  match d.time with
  | none => day
  | some (h, m, s) =>
    let zone := match d.zone with
      | none => ""
      | some 0 => "Z"
      | some z => (if z < 0 then "-" else "+") ++ s!"{two (z.natAbs / 60)}:{two (z.natAbs % 60)}"
    day ++ s!"T{two h}:{two m}:{two s}" ++ zone

end LeanTex.Core.PdfDate
