module

public section

namespace LeanTex.Core.DateText

/-- The order of a numeric date's fields. -/
inductive Order where
  | ymd
  | dmy
  | mdy
  deriving BEq, Repr, Inhabited

/-- A datetime date format: the long and short forms, the US form, and the numeric forms with their
order, two-digit fields and two-digit year. -/
inductive Style where
  | long
  | short
  | us
  | numeric (order : Order) (padded : Bool) (shortYear : Bool)
  deriving BEq, Repr, Inhabited

/-- One piece of a set date: text, an ordinal suffix `\textsuperscript` raises, or the document's
`\dateseparator`. -/
inductive Piece where
  | text (s : String)
  | raised (s : String)
  | separator
  deriving BEq, Repr, Inhabited

/-- The format datetime's option or switch command `name` selects, without its `date` suffix. -/
def Style.ofName? : String → Option Style
  | "long" => some .long
  | "short" => some .short
  | "us" => some .us
  | "yyyymmdd" => some (.numeric .ymd true false)
  | "ddmmyyyy" => some (.numeric .dmy true false)
  | "dmyyyy" => some (.numeric .dmy false false)
  | "ddmmyy" => some (.numeric .dmy true true)
  | "dmyy" => some (.numeric .dmy false true)
  | "mmddyyyy" => some (.numeric .mdy true false)
  | "mdyyyy" => some (.numeric .mdy false false)
  | "mmddyy" => some (.numeric .mdy true true)
  | "mdyy" => some (.numeric .mdy false true)
  | _ => none

/-- The style names datetime's options spell. -/
def styleNames : List String :=
  ["long", "short", "us", "yyyymmdd", "ddmmyyyy", "dmyyyy", "ddmmyy", "dmyy", "mmddyyyy",
   "mdyyyy", "mmddyy", "mdyy"]

/-- The day of the week of a Gregorian date, 0 for Sunday, by Sakamoto's method. -/
def dayOfWeek (d m y : Nat) : Nat :=
  let t := #[0, 3, 2, 5, 0, 3, 5, 1, 4, 6, 2, 4]
  let y := if m < 3 then y - 1 else y
  (y + y / 4 - y / 100 + y / 400 + t.getD (m - 1) 0 + d) % 7

/-- English day names from Sunday, as datetime's `\dayofweeknameidenglish` spells them. -/
def dayNames : Array String :=
  #["Sunday", "Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday"]

/-- English month names from January, as datetime's `\monthnameenglish` spells them. -/
def monthNames : Array String :=
  #["January", "February", "March", "April", "May", "June", "July", "August", "September",
    "October", "November", "December"]

/-- English short day names from Sunday, as datetime's `\shortdayofweeknameidenglish` spells them. -/
def shortDayNames : Array String := #["Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat"]

/-- English short month names from January, as datetime's `\shortmonthnameenglish` spells them. -/
def shortMonthNames : Array String :=
  #["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sept", "Oct", "Nov", "Dec"]

/-- The English ordinal suffix fmtcount sets after `n`. -/
def ordinalSuffix (n : Nat) : String :=
  if n % 100 ≥ 11 && n % 100 ≤ 13 then "th"
  else match n % 10 with
    | 1 => "st"
    | 2 => "nd"
    | 3 => "rd"
    | _ => "th"

/-- Whether a day, month and year name a calendar date. -/
def valid (d m y : Nat) : Bool :=
  let leap := y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)
  let days := #[31, if leap then 29 else 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]
  1 ≤ m && m ≤ 12 && 1 ≤ d && d ≤ days.getD (m - 1) 0

private def twoDigits (n : Nat) : String :=
  if n < 10 then s!"0{n}" else toString n

/-- A date as datetime's `\formatdate` sets it in `style`, the day of the week first where `dow`,
the ordinal suffix raised where `raise`, numeric fields apart by `sep`. -/
def pieces (style : Style) (dow raise : Bool) (sep : Piece) (d m y : Nat) : Array Piece :=
  let month := monthNames.getD (m - 1) ""
  let day := dayNames.getD (dayOfWeek d m y) ""
  let ord : Array Piece :=
    if raise then #[.text (toString d), .raised (ordinalSuffix d)]
    else #[.text (toString d ++ ordinalSuffix d)]
  match style with
  | .long => (if dow then #[Piece.text (day ++ " ")] else #[]) ++ ord ++
      #[.text s!" {month}, {y}"]
  | .short => (if dow then #[Piece.text (shortDayNames.getD (dayOfWeek d m y) "" ++ " ")] else #[]) ++
      ord ++ #[.text s!" {shortMonthNames.getD (m - 1) ""}, {y}"]
  | .us => #[.text s!"{month} {d}, {y}"]
  | .numeric order padded shortYear =>
    let f (n : Nat) := if padded then twoDigits n else toString n
    let yr := if shortYear then twoDigits (y % 100) else toString y
    let fields := match order with
      | .ymd => [yr, f m, f d]
      | .dmy => [f d, f m, yr]
      | .mdy => [f m, f d, yr]
    fields.foldl (init := #[]) fun out f => (if out.isEmpty then out else out.push sep).push (.text f)

end LeanTex.Core.DateText
