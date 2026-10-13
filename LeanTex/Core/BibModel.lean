module

public import LeanTex.Core.Bib
public import Std.Data.HashMap
public import Std.Data.HashSet

/-! The bibliography's one entry model: a `.bib` entry and the two views BibTeX
and biber read of it. -/

namespace LeanTex.Core.Bib

/-- One side of a date as biber reads it: an astronomical
year and, when given, a month and a day. -/
public structure Date where
  year : Int
  month : Option Nat := none
  day : Option Nat := none
  division : Option String := none
  deriving Repr, BEq, Inhabited

/-- A date field's value as biber reads it: a start, `none` where open, and for
a range its end, `some none` where open. -/
public structure DateValue where
  start : Option Date
  stop : Option (Option Date) := none
  circa : Bool := false
  uncertain : Bool := false
  endCirca : Bool := false
  endUncertain : Bool := false
  unspecified : Option String := none
  deriving Repr, BEq, Inhabited

private def isAsciiDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

private def digitsVal (s : String) : Option Nat :=
  if !s.isEmpty && s.all isAsciiDigit then s.toNat? else none

/-- A Gregorian leap year, proleptic and astronomical (year 0 leaps). -/
private def leapYear (y : Int) : Bool :=
  (y % 4 == 0 && y % 100 != 0) || y % 400 == 0

/-- The days a month of a year has. -/
public def monthDays (y : Int) (m : Nat) : Nat :=
  if m == 2 then (if leapYear y then 29 else 28)
  else if m == 4 || m == 6 || m == 9 || m == 11 then 30 else 31

/-- ISO 8601-2's year divisions as biber names them. -/
public def yearDivisions : List (Nat × String) :=
  [(21, "spring"), (22, "summer"), (23, "autumn"), (24, "winter"),
   (25, "springN"), (26, "summerN"), (27, "autumnN"), (28, "winterN"),
   (29, "springS"), (30, "summerS"), (31, "autumnS"), (32, "winterS"),
   (33, "Q1"), (34, "Q2"), (35, "Q3"), (36, "Q4"), (37, "QD1"), (38, "QD2"), (39, "QD3"),
   (40, "S1"), (41, "S2")]

/-- A year as the profile writes it: `-?` and exactly four digits. -/
private def year4? (s : String) : Option Int :=
  let (neg, body) := if s.startsWith "-" then (true, (s.drop 1).toString) else (false, s)
  if body.length == 4 then (digitsVal body).map fun y => if neg then -(y : Int) else y
  else none

/-- A two-digit field in its range. -/
private def two? (s : String) (lo hi : Nat) : Option Nat :=
  if s.length == 2 then (digitsVal s).bind fun v => if lo ≤ v && v ≤ hi then some v else none
  else none

/-- A trailing mark stripped, with the white space around it. -/
private def stripMark (s : String) (mark : Char) : Option String :=
  let t := s.trimAsciiEnd.toString
  if t.endsWith (String.singleton mark) && t.length > 1 then
    some (t.dropEnd 1).trimAscii.toString
  else none

/-- A time `hh:mm:ss`, with milliseconds `.mmm` allowed and ignored. -/
private def timeOk (t : String) : Bool :=
  let t := match t.splitOn "." with
    | [a, ms] => if ms.length == 3 && ms.all isAsciiDigit then a else ""
    | [a] => a
    | _ => ""
  match t.splitOn ":" with
  | [h, m, s] => (two? h 0 23).isSome && (two? m 0 59).isSome && (two? s 0 59).isSome
  | _ => false

/-- One side of a date as biber reads it: `some none` for no date,
`some (some _)` for a date, `none` for text biber reads as no date. -/
private def parseSide (raw : String) : Option (Option (Date × Bool × Bool)) := do
  let s := raw.trimAscii.toString
  if s.isEmpty || s == ".." then return none
  let (s, uncertain) := match stripMark s '?' with
    | some t => (t, true)
    | none => (s, false)
  let (s, circa) := match stripMark s '~' with
    | some t => (t, true)
    | none => (s, false)
  let (s, circa, uncertain) := match stripMark s '%' with
    | some t => (t, true, true)
    | none => (s, circa, uncertain)
  -- a time zone: `Z` or `±hh:mm`
  let s := if s.endsWith "Z" then (s.dropEnd 1).toString
    else
      let n := s.length
      let tail := (s.drop (n - 6)).toString
      if n > 6 && (tail.startsWith "+" || tail.startsWith "-") && tail.toList[3]? == some ':' &&
          ((tail.drop 1).take 2).all isAsciiDigit && ((tail.drop 4).take 2).all isAsciiDigit &&
          s.contains 'T' then
        (s.dropEnd 6).toString
      else s
  let date ← do
    if s.startsWith "Y" then
      let body := (s.drop 1).toString
      let (neg, ds) := if body.startsWith "-" then (true, (body.drop 1).toString) else (false, body)
      let y ← if ds.length ≥ 5 then digitsVal ds else none
      some ({ year := if neg then -(y : Int) else y } : Date)
    else
      let (neg, body) := if s.startsWith "-" then (true, (s.drop 1).toString) else (false, s)
      let pre := if neg then "-" else ""
      match body.splitOn "T" with
      | [d, t] =>
        unless timeOk t do none
        match d.splitOn "-" with
        | [y, m, dd] =>
          let yv ← year4? (pre ++ y)
          let mv ← two? m 1 12
          let dv ← two? dd 1 31
          if dv ≤ monthDays yv mv then some { year := yv, month := some mv, day := some dv }
          else none
        | _ => none
      | [d] =>
        match d.splitOn "-" with
        | [y] => (year4? (pre ++ y)).map fun yv => { year := yv }
        | [y, m] =>
          let yv ← year4? (pre ++ y)
          match two? m 21 41 with
          | some dv => some { year := yv, division := yearDivisions.lookup dv }
          | none => (two? m 1 12).map fun mv => { year := yv, month := some mv }
        | [y, m, dd] =>
          let yv ← year4? (pre ++ y)
          let mv ← two? m 1 12
          let dv ← two? dd 1 31
          if dv ≤ monthDays yv mv then some { year := yv, month := some mv, day := some dv }
          else none
        | _ => none
      | _ => none
  return some (date, circa, uncertain)

/-- Unspecified digits (ISO 8601-2 §4.3): the range a value with `X` digits
spans, and its granularity. -/
private def unspecifiedRange (s : String) : Option (String × String × String) :=
  let ps := s.splitOn "-"
  let isX (p : String) := p == "XX"
  match ps with
  | [y] =>
    if y.length == 4 && (y.take 3).all isAsciiDigit && y.endsWith "X" then
      some ((y.take 3).toString ++ "0", (y.take 3).toString ++ "9", "yearindecade")
    else if y.length == 4 && (y.take 2).all isAsciiDigit && y.endsWith "XX" then
      some ((y.take 2).toString ++ "00", (y.take 2).toString ++ "99", "yearincentury")
    else none
  | [y, m] =>
    if y.length == 4 && y.all isAsciiDigit && isX m then
      some (y ++ "-01", y ++ "-12", "monthinyear")
    else none
  | [y, m, d] =>
    if y.length == 4 && y.all isAsciiDigit && isX d then
      if isX m then some (y ++ "-01-01", y ++ "-12-31", "dayinyear")
      else match two? m 1 12, digitsVal y with
        | some mv, some yv =>
          some (y ++ "-" ++ m ++ "-01", y ++ "-" ++ m ++ "-" ++ toString (monthDays yv mv),
            "dayinmonth")
        | _, _ => none
    else none
  | _ => none

/-- A biblatex date field as biber reads it: one side, or
two at a `/`, either open. -/
public def DateValue.parse (v : String) : Option DateValue := do
  let v := v.trimAscii.toString
  let parts := v.splitOn "/"
  let (sd, sep, ed) ← match parts with
    | [a] => some (a, false, "")
    | [a, b] => some (a, true, b)
    | _ => none
  if sd.trimAscii.isEmpty && ed.trimAscii.isEmpty then none
  let (sd, sep, ed, unspec) :=
    if sd.contains 'X' then
      match unspecifiedRange sd.trimAscii.toString with
      | some (a, b, u) => (a, true, b, some u)
      | none => (sd, sep, ed, none)
    else (sd, sep, ed, none)
  if sd.contains 'X' then none
  let start ← parseSide sd
  let stop ← if sep then (parseSide ed).map some else some none
  return { start := start.map (·.1), stop := stop.map (·.map (·.1)),
           circa := (start.map (·.2.1)).getD false, uncertain := (start.map (·.2.2)).getD false,
           endCirca := ((stop.join).map (·.2.1)).getD false,
           endUncertain := ((stop.join).map (·.2.2)).getD false, unspecified := unspec }

/-- The English months' three-letter openings, by which
biber reads a legacy `month`. -/
private def monthOpenings : Array String :=
  #["jan", "feb", "mar", "apr", "may", "jun", "jul", "aug", "sep", "oct", "nov", "dec"]

/-- A month's number from its value: the number, an English month's opening, or
one of the document's month names. -/
public def monthNumber (months : Array String) (v : String) : Option Nat :=
  let t := (text v).trimAscii.toString
  match digitsVal t with
  | some n => if 1 ≤ n && n ≤ 12 then some n else none
  | none =>
    let low := t.toLower
    let pick (ms : Array String) : Option Nat :=
      (ms.findIdx? fun m => m.toLower == low).map (· + 1)
    ((monthOpenings.findIdx? (low.startsWith ·)).map (· + 1)).orElse fun _ => pick months

/-- biber's default type map for BibTeX data: the biblatex type and the `type` a
thesis or report kind sets. -/
public def biberTypeMap : List (String × String × Option String) :=
  [("conference", "inproceedings", none), ("electronic", "online", none),
   ("www", "online", none), ("mastersthesis", "thesis", some "mathesis"),
   ("phdthesis", "thesis", some "phdthesis"), ("techreport", "report", some "techreport")]

/-- biber's default field map for BibTeX data (biber manual §3.1.2). -/
public def biberFieldMap : List (String × String) :=
  [("hyphenation", "langid"), ("address", "location"), ("school", "institution"),
   ("annote", "annotation"), ("archiveprefix", "eprinttype"), ("journal", "journaltitle"),
   ("primaryclass", "eprintclass"), ("key", "sortkey"), ("pdf", "file")]

/-- A field set unless the entry already has one by that name. -/
private def setIfAbsent (fs : Array (String × String)) (f v : String) : Array (String × String) :=
  if fs.any (·.1 == f) then fs else fs.push (f, v)

/-- An entry as biber reads it: BibTeX's type and field spellings renamed to
biblatex's unless already present. -/
public def Entry.biberView (e : Entry) : Entry := Id.run do
  let (kind, setType) := match biberTypeMap.find? (·.1 == e.kind) with
    | some (_, k, ty) => (k, ty)
    | none => (e.kind, none)
  let mut fs : Array (String × String) := #[]
  for (f, v) in e.fields do
    match biberFieldMap.lookup f with
    | some f' =>
      if e.fields.any (·.1 == f') then fs := fs.push (f, v) else fs := fs.push (f', v)
    | none => fs := fs.push (f, v)
  if let some ty := setType then fs := setIfAbsent fs "type" ty
  return { e with kind, fields := fs }

/-- What biber reads of one of an entry's date types. -/
public inductive DateParts where
  | parsed (dv : DateValue)
  | legacy (year : String) (month : Option String)
  | written (text : String)
  | none
  deriving Repr, BEq, Inhabited

/-- An entry's date of one type (`DateParts`). -/
public def Entry.dateParts (months : Array String) (e : Entry) (ty : String) : DateParts :=
  let nonEmpty (f : String) := (e.field? f).filter fun v => !v.trimAscii.toString.isEmpty
  let legacy : Option DateParts := (nonEmpty "year").map fun y =>
    .legacy (text y).trimAscii.toString ((nonEmpty "month").map fun m =>
      match monthNumber months m with
      | some n => toString n
      | none => (text m).trimAscii.toString)
  match nonEmpty (ty ++ "date") with
  | some v =>
    match DateValue.parse v with
    | some dv => .parsed dv
    | none => if ty.isEmpty then legacy.getD (.written (text v)) else .written (text v)
  | none => if ty.isEmpty then legacy.getD .none else .none

/-- The date an entry's label prints, with its type, or
`none` for biblatex's `nodate`. -/
public def Entry.labelDate (months : Array String) (e : Entry) : Option (String × DateParts) :=
  ["", "event", "orig", "url"].findSome? fun ty =>
    match e.dateParts months ty with
    | .none => none
    | p => some (ty, p)

/-- The BibTeX type a biblatex type reads as, `misc` where
BibTeX has no function for it. -/
private def bibtexKind (e : Entry) : String × Bool :=
  let ty := ((e.field? "type").map fun t => (text t).trimAscii.toString).getD ""
  match e.kind with
  | "thesis" =>
    if ty == "mathesis" || ty == "mastersthesis" then ("mastersthesis", true)
    else ("phdthesis", ty == "phdthesis" || ty.isEmpty)
  | "report" => ("techreport", ty == "techreport")
  | "online" | "electronic" | "www" => ("misc", false)
  | k => (k, false)

/-- An entry as a BibTeX style reads it: biblatex's spellings under BibTeX's
names where those are absent. -/
public def Entry.bibtexView (months : Array String) (e : Entry) : Entry := Id.run do
  let (kind, dropType) := bibtexKind e
  let mut fs := if dropType then e.fields.filter (·.1 != "type") else e.fields
  if let some j := e.field? "journaltitle" then fs := setIfAbsent fs "journal" j
  if let some l := e.field? "location" then fs := setIfAbsent fs "address" l
  if kind == "phdthesis" || kind == "mastersthesis" then
    if let some i := e.field? "institution" then fs := setIfAbsent fs "school" i
  if let some d := e.field? "date" then
    match DateValue.parse d with
    | none => fs := setIfAbsent fs "year" d
    | some dv =>
      let yr (d : Date) : String := if d.year < 0 then "−" ++ toString d.year.natAbs
        else toString d.year
      let yearText := match dv.start, dv.stop with
        | some a, some (some b) => if b.year == a.year then yr a else s!"{yr a}--{yr b}"
        | some a, some none => s!"{yr a}--"
        | none, some (some b) => s!"--{yr b}"
        | some a, none => yr a
        | none, _ => ""
      unless yearText.isEmpty do fs := setIfAbsent fs "year" yearText
      if dv.stop.isNone then
        if let some m := dv.start.bind (·.month) then
          fs := setIfAbsent fs "month" ((months[m - 1]?).getD (toString m))
  return { e with kind, fields := fs }

/-- BibTeX's cross-reference: the child takes each field it lacks from its
parent, except the parent's `crossref`. -/
public def inheritBibtex (child parent : Entry) : Entry :=
  { child with fields := child.fields ++ parent.fields.filter fun (f, _) =>
      f != "crossref" && !child.fields.any (·.1 == f) }

/-- One rule of biblatex's data inheritance (`\DeclareDataInheritance`). -/
public structure InheritRule where
  sources : List String
  targets : List String
  maps : List (String × String) := []
  withheld : List String := []
  deriving Repr, BEq

/-- biblatex's default inheritance setup, transcribed from biblatex.def. -/
public def biblatexInheritance : List InheritRule :=
  let titles (t : String) : List (String × String) :=
    [("title", t ++ "title"), ("subtitle", t ++ "subtitle"), ("titleaddon", t ++ "titleaddon")]
  let noTitles := ["shorttitle", "sorttitle", "indextitle", "indexsorttitle"]
  [{ sources := ["mvbook", "book"], targets := ["inbook", "bookinbook", "suppbook"]
     maps := [("author", "author"), ("author", "bookauthor")] },
   { sources := ["mvbook"], targets := ["book", "inbook", "bookinbook", "suppbook"]
     maps := titles "main", withheld := noTitles },
   { sources := ["mvcollection", "mvreference"]
     targets := ["collection", "reference", "incollection", "inreference", "suppcollection"]
     maps := titles "main", withheld := noTitles },
   { sources := ["mvproceedings"], targets := ["proceedings", "inproceedings"]
     maps := titles "main", withheld := noTitles },
   { sources := ["book"], targets := ["inbook", "bookinbook", "suppbook"]
     maps := titles "book", withheld := noTitles },
   { sources := ["collection", "reference"]
     targets := ["incollection", "inreference", "suppcollection"]
     maps := titles "book", withheld := noTitles },
   { sources := ["proceedings"], targets := ["inproceedings"]
     maps := titles "book", withheld := noTitles },
   { sources := ["periodical"], targets := ["article", "suppperiodical"]
     maps := [("title", "journaltitle"), ("subtitle", "journalsubtitle"),
       ("titleaddon", "journaltitleaddon")]
     withheld := noTitles },
   { sources := ["*"], targets := ["*"]
     withheld := ["ids", "crossref", "xref", "xdata", "entryset", "entrysubtype", "execute",
       "label", "options", "presort", "related", "relatedoptions", "relatedstring",
       "relatedtype", "shorthand", "shorthandintro", "sortkey"] }]

/-- Does a rule govern a parent of type `src` and a child of type `tgt`? -/
public def InheritRule.governs (r : InheritRule) (src tgt : String) : Bool :=
  (r.sources.contains "*" || r.sources.contains src) &&
    (r.targets.contains "*" || r.targets.contains tgt)

/-- The fields a parent lends a child under biblatex's
rules, in the order biber takes them. -/
public def lent (rules : List InheritRule) (child parent : Entry) : Array (String × String) :=
  let gov := rules.filter (·.governs parent.kind child.kind)
  let maps := gov.flatMap (·.maps)
  let mapped := maps.map (·.1)
  let withheld := gov.flatMap (·.withheld)
  (maps.filterMap fun (s, t) => (parent.field? s).map (t, ·)).toArray ++
    parent.fields.filter fun (f, _) => !mapped.contains f && !withheld.contains f

/-- biber's cross-reference under a rule set: the child takes the rest from what
its parent lends, the first lender winning. -/
public def inheritBiber (rules : List InheritRule) (child parent : Entry) : Entry :=
  { child with fields := child.fields ++ lent rules child parent }

/-- `xdata`: a data entry's fields set on the entry naming
it, each replacing the entry's own. -/
public def inheritXdata (fields lent : Array (String × String)) : Array (String × String) :=
  lent.foldl (init := fields) fun fs (f, v) =>
    if f == "xdata" || f == "ids" then fs
    else match fs.findIdx? (·.1 == f) with
      | some i => fs.modify i fun _ => (f, v)
      | none => fs.push (f, v)

/-- Which program reads the `.bib`: BibTeX for `.bst`
styles, biber for biblatex. -/
public inductive Processor where
  | bibtex
  | biber
  deriving Repr, BEq, Inhabited

/-- The fields of the two data models that carry what a
reader of a reference list is owed. -/
public def contentFields : List String :=
  ["author", "editor", "translator", "bookauthor", "annotator", "commentator", "introduction",
   "foreword", "afterword", "holder", "editora", "editorb", "editorc",
   "title", "subtitle", "titleaddon", "booktitle", "booksubtitle", "booktitleaddon",
   "maintitle", "mainsubtitle", "maintitleaddon", "journal", "journaltitle", "journalsubtitle",
   "journaltitleaddon", "issuetitle", "issuesubtitle", "issuetitleaddon", "origtitle",
   "reprinttitle", "eventtitle", "eventtitleaddon", "venue",
   "edition", "volume", "volumes", "part", "series", "number", "issue", "eid", "pages",
   "pagetotal", "chapter", "note", "addendum", "pubstate", "howpublished", "type", "version",
   "publisher", "address", "location", "school", "institution", "organization",
   "origlocation", "origpublisher", "language", "origlanguage",
   "year", "month", "date", "eventdate", "origdate", "urldate",
   "doi", "eprint", "url", "isbn", "issn", "isrn", "isan", "ismn", "iswc"]

/-- The name a processor reads a field under. -/
public def readsAs (proc : Processor) (kind f : String) : String :=
  match proc with
  | .bibtex =>
    match f with
    | "journaltitle" => "journal"
    | "location" => "address"
    | "date" => "year"
    | "institution" => if kind == "phdthesis" || kind == "mastersthesis" then "school" else f
    | _ => f
  | .biber =>
    match f with
    | "year" => "date"
    | "month" => "month"
    | g => (biberFieldMap.lookup g).getD g

/-- The default count of citing entries that brings an
uncited parent into the list. -/
public def minCrossrefs : Nat := 2

/-- An entry's references to other entries by one field. -/
public def Entry.refsBy (e : Entry) (field : String) : List String :=
  match e.field? field with
  | some v => ((text v).splitOn ",").map (·.trimAscii.toString) |>.filter (!·.isEmpty)
  | none => []

/-- The database keys a walk has yet to meet. -/
private def unmet (byKey : Std.HashMap String Entry) (seen : Std.HashSet String) : Nat :=
  (byKey.keys.filter fun k => !seen.contains k).length

private theorem unmet_insert_lt (byKey : Std.HashMap String Entry) (seen : Std.HashSet String)
    (k : String) (p : Entry) (hk : byKey.get? k = some p) (hs : seen.contains k = false) :
    unmet byKey (seen.insert k) < unmet byKey seen := by
  unfold unmet
  have hfilter : (byKey.keys.filter fun x => !(seen.insert k).contains x) =
      (byKey.keys.filter fun x => !seen.contains x).filter fun x => !(k == x) := by
    rw [List.filter_filter]
    congr 1
    funext x
    simp only [Std.HashSet.contains_insert, Bool.not_or]
  rw [hfilter, List.length_filter_lt_length_iff_exists]
  refine ⟨k, List.mem_filter.mpr ⟨?_, by simp [hs]⟩, by simp⟩
  rw [Std.HashMap.mem_keys, Std.HashMap.mem_iff_isSome_getElem?,
    ← Std.HashMap.get?_eq_getElem?, hk]
  rfl

/-- The breadth-first walk under `ancestry`. -/
private def ancestryGo (byKey : Std.HashMap String Entry) (field : String)
    (seen : Std.HashSet String) (out : Array Entry) (missing : Array String) :
    List String → Array Entry × Array String
  | [] => (out, missing)
  | k :: rest =>
    if _hs : seen.contains k then ancestryGo byKey field seen out missing rest
    else match _hk : byKey.get? k with
      | some p => ancestryGo byKey field (seen.insert k) (out.push p) missing (rest ++ p.refsBy field)
      | none =>
        ancestryGo byKey field seen out (if missing.contains k then missing else missing.push k) rest
termination_by frontier => (unmet byKey seen, frontier.length)
decreasing_by
  · exact Prod.Lex.right _ (by simp)
  · exact Prod.Lex.left _ _ (unmet_insert_lt byKey seen k p _hk (by simpa using _hs))
  · exact Prod.Lex.right _ (by simp)

/-- The entries an entry's references reach by one field, nearest first, each
once, and the keys that name no entry. -/
private def ancestry (byKey : Std.HashMap String Entry) (field : String) (start : Entry) :
    Array Entry × Array String :=
  ancestryGo byKey field (({} : Std.HashSet String).insert start.key) #[] #[] (start.refsBy field)

/-- The shape biblatex's data model gives a field: whether
it is a list, and of what. -/
private def datePart (f : String) : Bool :=
  ["", "event", "orig", "url"].any fun pre =>
    ["year", "month", "day", "hour", "minute", "second", "timezone", "yeardivision"].any fun p =>
      f == pre ++ p || f == pre ++ "end" ++ p

public def fieldShape (f : String) : Bool × String :=
  if ["afterword", "annotator", "author", "bookauthor", "commentator", "editor", "editora",
      "editorb", "editorc", "foreword", "holder", "introduction", "namea", "nameb", "namec",
      "translator", "shortauthor", "shorteditor", "sortname"].contains f then (true, "name")
  else if ["institution", "lista", "listb", "listc", "listd", "liste", "listf", "location",
      "organization", "origlocation", "origpublisher", "publisher"].contains f then
    (true, "literal")
  else if f == "language" || f == "origlanguage" then (true, "key")
  else if ["date", "eventdate", "origdate", "urldate"].contains f then (false, "date")
  else if datePart f then (false, "datepart")
  else if ["sortyear", "volume", "volumes"].contains f then (false, "integer")
  else if ["doi", "eprint", "file", "verba", "verbb", "verbc"].contains f then (false, "verbatim")
  else if f == "url" then (false, "uri")
  else if f == "pages" then (false, "range")
  else if ["crossref", "xref", "xdata", "ids", "entryset", "related"].contains f then
    (false, "entrykey")
  else if ["authortype", "editoratype", "editorbtype", "editorctype", "editortype",
      "bookpagination", "nameatype", "namebtype", "namectype", "pagination", "pubstate",
      "type"].contains f then (false, "key")
  else if f == "keywords" then (false, "keyword")
  else if f == "options" || f == "relatedoptions" then (false, "option")
  else if f == "execute" then (false, "code")
  else (false, "literal")

/-- What a field value spelling `xdata=` holds: `some (key, field, position)`
for a granular reference. -/
public def granularRef? (v : String) : Option (Option (String × String × Option Nat)) :=
  let v := v.trimAscii.toString
  if (v.take 6).toString.toLower != "xdata=" then none
  else
    let body := (v.drop 6).toString
    if body.isEmpty || body.any Char.isWhitespace then none
    else some <| match body.splitOn "-" with
      | [k, f] => if k.isEmpty || f.isEmpty then none else some (k, f, none)
      | [k, f, n] =>
        if k.isEmpty || f.isEmpty || n.isEmpty || !n.all Char.isDigit then none
        else some (k, f, n.toNat?)
      | _ => none

/-- Why biber does not resolve an inheritance reference, each named by W0425. -/
public inductive RefFault where
  /-- No entry holds the key. -/
  | missing
  /-- BibTeX's one reading of the database passed the parent
  before anything asked for it. -/
  | unread
  /-- The `xdata` names an entry that is no `@xdata` entry. -/
  | notData
  /-- Following it would reread a data entry being read; the
  path from the entry whose data it is. -/
  | cycle (path : Array String)
  /-- The granular reference's data entry holds no such field. -/
  | noField (field : String)
  /-- The data entry's list holds no item at that position. -/
  | noPosition (field : String) (n : Nat)
  /-- The two fields' shapes differ (`fieldShape`). -/
  | shapes (field : String)
  /-- A value spelling `xdata=` with no source field biber can read. -/
  | malformed
  deriving Repr, BEq

/-- An inheritance reference left unresolved: the entry, the field, the key, the
data entry's field, and why. -/
public structure RefReport where
  holder : String
  field : String
  target : String
  source : String := ""
  fault : RefFault
  deriving Repr, BEq

/-- The items of a list field, split on ` and ` at brace depth 0. -/
private def listItems (v : String) : Array String := splitNames v

/-- What a granular reference takes from its data entry. -/
private def lendItems (q : Entry) (field : String) (isList : Bool) (pos : Option Nat) :
    Except RefFault (Array String) :=
  match q.field? field with
  | none => .error (.noField field)
  | some v =>
    if !isList then .ok #[v]
    else
      let items := listItems v
      match pos with
      | none => .ok items
      | some n =>
        if n == 0 then .error (.noPosition field n)
        else match items[n - 1]? with
          | some x => .ok #[x]
          | none => .error (.noPosition field n)

/-- An entry with its `xdata` references resolved as biber resolves them, and
those left unresolved. -/
private def resolveXdataGo (byKey : Std.HashMap String Entry) (onPath : Std.HashSet String)
    (path : Array String) (e : Entry) : Entry × Array RefReport := Id.run do
  let mut fields := e.fields
  let mut reports : Array RefReport := #[]
  for (f, v) in e.fields do
    if f == "xdata" then
      for k in e.refsBy "xdata" do
        match _hk : byKey.get? k with
        | none => reports := reports.push ⟨e.key, f, k, "", .missing⟩
        | some p =>
          if p.kind != "xdata" then reports := reports.push ⟨e.key, f, k, "", .notData⟩
          else if _hs : onPath.contains k then
            reports := reports.push ⟨e.key, f, k, "", .cycle (path.push k)⟩
          else
            let (q, rs) := resolveXdataGo byKey (onPath.insert k) (path.push k) p
            reports := reports ++ rs
            fields := inheritXdata fields q.fields
    else
      unless v.contains '=' && (fieldShape f).2 != "date" do continue
      let isList := (fieldShape f).1
      let items := if isList then listItems v else #[v]
      unless items.any (granularRef? · |>.isSome) do continue
      -- Each reference is read from the last item, so the written positions stay the items' own.
      let mut out := items
      for j in [0:items.size] do
        let i := items.size - 1 - j
        match items[i]? with
        | none => pure ()
        | some item =>
          match granularRef? item with
          | none => pure ()
          | some none =>
            reports := reports.push ⟨e.key, f, item.trimAscii.toString, "", .malformed⟩
            out := out.eraseIdxIfInBounds i
          | some (some (k, xf, pos)) =>
            match _hk : byKey.get? k with
            | none =>
              reports := reports.push ⟨e.key, f, k, xf, .missing⟩
              out := out.eraseIdxIfInBounds i
            | some p =>
              if p.kind != "xdata" then
                reports := reports.push ⟨e.key, f, k, xf, .notData⟩
                out := out.eraseIdxIfInBounds i
              else if _hs : onPath.contains k then
                reports := reports.push ⟨e.key, f, k, xf, .cycle (path.push k)⟩
                out := out.eraseIdxIfInBounds i
              else
                let (q, rs) := resolveXdataGo byKey (onPath.insert k) (path.push k) p
                reports := reports ++ rs
                if fieldShape xf != fieldShape f then
                  reports := reports.push ⟨e.key, f, k, xf, .shapes xf⟩
                  out := out.eraseIdxIfInBounds i
                else match lendItems q xf isList pos with
                  | .error fault =>
                    let named := match fault with
                      | .noField _ => (p.field? xf).isSome
                      | _ => false
                    unless named do reports := reports.push ⟨e.key, f, k, xf, fault⟩
                    out := out.eraseIdxIfInBounds i
                  | .ok lent => out := (out.extract 0 i ++ lent) ++ out.extract (i + 1) out.size
      let value := " and ".intercalate out.toList
      fields := match fields.findIdx? (·.1 == f) with
        | some i =>
          if out.isEmpty then fields.eraseIdxIfInBounds i else fields.modify i fun _ => (f, value)
        | none => if out.isEmpty then fields else fields.push (f, value)
  return ({ e with fields }, reports)
termination_by unmet byKey onPath
decreasing_by
  all_goals exact unmet_insert_lt byKey onPath k p _hk (by simpa using _hs)

/-- An entry with its `xdata` resolved (`resolveXdataGo`), from the entry
itself. -/
private def resolveXdata (byKey : Std.HashMap String Entry) (e : Entry) : Entry × Array RefReport :=
  resolveXdataGo byKey (({} : Std.HashSet String).insert e.key) #[e.key] e

/-- An entry with its `crossref` chain resolved under the processor's
inheritance, farthest ancestor first. -/
private def withCrossref (proc : Processor) (byKey : Std.HashMap String Entry) (e : Entry) :
    Entry :=
  let chain := (ancestry byKey "crossref" e).1.toList
  let inh (c p : Entry) : Entry := match proc with
    | .bibtex => inheritBibtex c p
    | .biber => inheritBiber biblatexInheritance c p
  match chain.reverse with
  | [] => e
  | top :: below =>
    let parent := below.foldl (fun acc c => inh c acc) top
    inh e parent

/-- What a processor reads off the database for one document. -/
public structure Database where
  entries : Std.HashMap String Entry
  list : Array String
  /-- Each entry under the processor's view, before it inherits. -/
  own : Std.HashMap String Entry := {}
  /-- The inheritance references a listed entry's reading left unresolved. -/
  broken : Array RefReport := #[]

/-- A BibTeX view's `crossref` naming its parent by the parent's own key; BibTeX
matches keys case-insensitively. -/
private def canonicalCrossref (lower : Std.HashMap String String)
    (byKey : Std.HashMap String Entry) (e : Entry) : Entry :=
  match e.field? "crossref" with
  | some v =>
    let k := (text v).trimAscii.toString
    if byKey.contains k then e
    else match lower.get? k.toLower with
      | some canon => { e with fields := e.fields.map fun (f, x) =>
          if f == "crossref" then (f, canon) else (f, x) }
      | none => e
  | none => e

/-- A database under one processor before any list is read off it. -/
public structure Database.Prepared where
  proc : Processor
  viewed : Array Entry
  position : Std.HashMap String Nat
  /-- Each entry under the view, before it inherits. -/
  own : Std.HashMap String Entry
  /-- Each entry with its `xdata` resolved. -/
  withData : Std.HashMap String Entry
  /-- Each entry with its `xdata` and its `crossref` chain resolved. -/
  resolved : Std.HashMap String Entry
  /-- The keys of the entries that name a `crossref`. -/
  crossrefs : Array String
  /-- What each entry's `xdata` reading left unresolved. -/
  dataReports : Std.HashMap String (Array RefReport)

/-- Prepares a database for a processor; `months` are the
document's month names. -/
public def Database.prepare (proc : Processor) (months : Array String) (raw : Array Entry) :
    Database.Prepared :=
  let view (e : Entry) : Entry := match proc with
    | .bibtex => e.bibtexView months
    | .biber => e.biberView
  let viewed := raw.map view
  let viewed := if proc != .bibtex then viewed else
    let exact : Std.HashMap String Entry := viewed.foldl (fun m e => m.insert e.key e) {}
    let lower : Std.HashMap String String := viewed.foldl (init := {}) fun m e =>
      if m.contains e.key.toLower then m else m.insert e.key.toLower e.key
    viewed.map (canonicalCrossref lower exact)
  let own : Std.HashMap String Entry := viewed.foldl (fun m e => m.insert e.key e) {}
  let position : Std.HashMap String Nat :=
    viewed.zipIdx.foldl (fun m (e, i) => if m.contains e.key then m else m.insert e.key i) {}
  let read := viewed.map (resolveXdata own)
  let withData : Std.HashMap String Entry := read.foldl (fun m (e, _) => m.insert e.key e) own
  let resolved : Std.HashMap String Entry :=
    viewed.foldl (fun m e => match withData.get? e.key with
      | some x => m.insert e.key (withCrossref proc withData x)
      | none => m) withData
  let dataReports : Std.HashMap String (Array RefReport) :=
    read.foldl (fun m (e, rs) => if rs.isEmpty then m else m.insert e.key rs) {}
  let crossrefs := (viewed.filter fun e =>
    ((withData.get? e.key).map fun x => !(x.refsBy "crossref").isEmpty).getD false).map (·.key)
  { proc, viewed, position, own, withData, resolved, crossrefs, dataReports }

/-- The list a prepared database gives the keys `cited`, in
first-citation order. -/
public def Database.Prepared.list (d : Database.Prepared) (cited : Array String) : Database :=
  Id.run do
  let citedSet : Std.HashSet String := cited.foldl (·.insert ·) {}
  let refFields := match d.proc with
    | .bibtex => ["crossref"]
    | .biber => ["crossref", "xref"]
  let inOrder := ((citedSet.toArray.filterMap fun k => (d.position.get? k).map (·, k)).qsort
    (fun a b => a.1 < b.1)).filterMap fun (_, k) => d.withData.get? k
  -- BibTeX reads the database once: a parent is kept only after a cited child naming it.
  let firstChild : Std.HashMap String Nat := inOrder.foldl (init := {}) fun m e =>
    (e.refsBy "crossref").foldl (init := m) fun m p =>
      if m.contains p then m else match d.position.get? e.key with
        | some i => m.insert p i
        | none => m
  let unread (p : String) : Bool := d.proc == .bibtex && !citedSet.contains p &&
    match d.position.get? p, firstChild.get? p with
    | some pos, some first => pos < first
    | _, _ => false
  let mut counts : Std.HashMap String Nat := {}
  let mut met : Array String := #[]
  for e in inOrder do
    for fld in refFields do
      for p in e.refsBy fld do
        if d.own.contains p && !citedSet.contains p && !unread p then
          unless counts.contains p do met := met.push p
          counts := counts.insert p (counts.getD p 0 + 1)
  let added := met.filter fun p => counts.getD p 0 ≥ minCrossrefs &&
    ((d.own.get? p).all (·.kind != "xdata"))
  let listSet : Std.HashSet String := added.foldl (·.insert ·) citedSet
  let mut entries := d.resolved
  if d.proc == .bibtex then
    for k in d.crossrefs do
      if let some e := d.withData.get? k then
        if (e.refsBy "crossref").any unread then
          entries := entries.insert e.key { e with fields := e.fields.filter (·.1 != "crossref") }
        else if (e.refsBy "crossref").any (!listSet.contains ·) then
          if let some x := entries.get? e.key then
            entries := entries.insert e.key
              { x with fields := x.fields.filter (·.1 != "crossref") }
  -- An `@xdata` entry lends its fields and is never listed.
  let listed := (cited ++ added).filter fun k => (d.withData.get? k).all (·.kind != "xdata")
  let broken := listed.foldl (init := #[]) fun acc k =>
    match d.withData.get? k with
    | some e =>
      let acc := (ancestry d.withData "crossref" e).2.foldl
        (fun acc m => acc.push ⟨k, "crossref", m, "", .missing⟩) acc
      let acc := ((e.refsBy "crossref").filter unread).foldl
        (fun acc p => acc.push ⟨k, "crossref", p, "", .unread⟩) acc
      (d.dataReports.getD k #[]).foldl (fun acc r => if acc.contains r then acc else acc.push r) acc
    | none => acc
  return { entries, list := listed, own := d.own, broken }

/-- Reads a database for a processor: `months` are the month names, `cited` the
keys in first-citation order. -/
public def Database.read (proc : Processor) (months : Array String) (raw : Array Entry)
    (cited : Array String) : Database :=
  (Database.prepare proc months raw).list cited

private theorem find?_filter_keep (ys : Array (String × String)) (p : String × String → Bool)
    (f : String) (hp : ∀ x : String × String, x.1 = f → p x = true) :
    (ys.filter p).find? (·.1 == f) = ys.find? (·.1 == f) := by
  rw [Array.find?_filter]
  congr 1
  funext x
  by_cases hx : x.1 = f
  · simp [hx, hp x hx]
  · simp [hx]

private theorem find?_filter_drop (ys : Array (String × String)) (p : String × String → Bool)
    (f : String) (hp : ∀ x : String × String, x.1 = f → p x = false) :
    (ys.filter p).find? (·.1 == f) = none := by
  rw [Array.find?_eq_none]
  intro x hx hfx
  have h1 : x.1 = f := by simpa using hfx
  have h2 := (Array.mem_filter.mp hx).2
  rw [hp x h1] at h2
  exact absurd h2 (by decide)

private theorem any_name_false (xs : Array (String × String)) (f : String)
    (h : xs.find? (·.1 == f) = none) : xs.any (·.1 == f) = false := by
  cases hany : xs.any (·.1 == f) with
  | false => rfl
  | true =>
    obtain ⟨x, hx, hfx⟩ := Array.any_eq_true'.mp hany
    exact absurd hfx (Array.find?_eq_none.mp h x hx)

public theorem crossref_inherit_exact (child parent : Entry) (f : String) :
    (inheritBibtex child parent).field? f =
      if f = "crossref" then child.field? f
      else (child.field? f).or (parent.field? f) := by
  simp only [inheritBibtex, Entry.field?, Array.find?_append]
  by_cases hc : f = "crossref"
  · subst hc
    rw [find?_filter_drop _ _ _ (fun x hx => by simp [hx])]
    simp
  · simp only [hc, ↓reduceIte]
    cases hch : child.fields.find? (·.1 == f) with
    | some v => simp
    | none =>
      have hany := any_name_false child.fields f hch
      rw [find?_filter_keep _ _ _ (fun x hx => by simp [hx, hc, hany])]
      simp

public theorem biberInherit_exact (rules : List InheritRule) (child parent : Entry)
    (f : String) :
    (inheritBiber rules child parent).field? f =
      (child.field? f).or (((lent rules child parent).find? (·.1 == f)).map (·.2)) := by
  simp only [inheritBiber, Entry.field?, Array.find?_append]
  cases child.fields.find? (·.1 == f) <;> simp

public theorem lent_plain_exact (rules : List InheritRule) (child parent : Entry) (f : String)
    (hm : ∀ r ∈ rules, r.governs parent.kind child.kind = true →
      ∀ st ∈ r.maps, st.1 ≠ f ∧ st.2 ≠ f)
    (hw : ∀ r ∈ rules, r.governs parent.kind child.kind = true → f ∉ r.withheld) :
    ((lent rules child parent).find? (·.1 == f)).map (·.2) = parent.field? f := by
  simp only [lent, Entry.field?, Array.find?_append]
  rw [Array.find?_eq_none.mpr (by
    intro x hx hfx
    simp only [List.mem_toArray, List.mem_filterMap, List.mem_flatMap, List.mem_filter] at hx
    obtain ⟨⟨s, t⟩, ⟨r, ⟨hr, hg⟩, hst⟩, hx⟩ := hx
    have ht := (hm r hr hg (s, t) hst).2
    cases hp : (parent.fields.find? (·.1 == s)).map (·.2) with
    | none => simp [hp] at hx
    | some v =>
      simp only [hp, Option.map_some, Option.some.injEq] at hx
      subst hx
      exact ht (by simpa using hfx))]
  rw [Option.none_or, find?_filter_keep]
  intro x hx
  obtain ⟨g, v⟩ := x
  simp only at hx
  subst hx
  have hnm : g ∉ ((rules.filter (·.governs parent.kind child.kind)).flatMap (·.maps)).map (·.1) := by
    simp only [List.mem_map, List.mem_flatMap, List.mem_filter, not_exists, not_and]
    intro st hex hs
    obtain ⟨r, ⟨hr, hg⟩, hst⟩ := hex
    exact (hm r hr hg st hst).1 hs
  have hnw : g ∉ (rules.filter (·.governs parent.kind child.kind)).flatMap (·.withheld) := by
    simp only [List.mem_flatMap, List.mem_filter, not_exists, not_and]
    intro r hrg hgw
    exact hw r hrg.1 hrg.2 hgw
  simp [hnm, hnw]

end LeanTex.Core.Bib
