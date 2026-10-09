module

public import LeanTex.Core.BibModel
public import LeanTex.Core.BibText
public import LeanTex.Core.BibUnique
public import LeanTex.Core.Ir
import LeanTex.Core.BibStringsData
import Std.Data.HashMap

/-! biblatex's standard bibliography styles, `numeric` and `authoryear`,
transcribed from their sources at biblatex 3.21: the drivers of
standard.bbx, every bibliography macro, field, list and name format of
biblatex.def they call, the two style files' overrides (numeric.bbx,
authoryear.bbx), and English's strings and dates (english.lbx, its strings
read from the generated `BibStringsData`), under biblatex's default options
(`maxbibnames=3`, `minbibnames=1`, `maxitems=3`, `giveninits=false`,
`useprefix=false`, `useauthor`, `useeditor`, no `usetranslator`,
`abbreviate=true`, `date=comp`, `labeldate=year`, `urldate=short`,
`dateera=astronomical`, no `datecirca` or `dateuncertain`,
`mergedate=compact`, `dashed=true`, `block=none`) and the ones a load or an
entry's `options` sets (`BblOptions.forEntry`).

The reference list is written through biblatex's punctuation tracker
(biblatex.sty, "Punctuation"): a pending unit punctuation (`\setunit`,
`\newunit`, `\printunit`) prints only before the next print command that
prints, and `\addperiod`, `\addcomma`, … add a mark only where biblatex's
punctuation pairs allow it after the mark before — so an abbreviation dot
takes no second period, and a title ending in `?` takes none. Each driver
below is its standard.bbx namesake, macro for macro; what one prints of a
field is what `BCtx.read` records, which the list's accounting reads.

Two departures are declared. `\printtext[parens]{…}` around content that
prints nothing prints nothing here, where biblatex prints an empty pair — an
article with a volume and no date reads `Journal 3`, not `Journal 3 ()`. An
eprint of a type biblatex has no format for is set as its identifier, never
a link: biblatex links it to the identifier's own text as an address, which
leads nowhere. -/

namespace LeanTex.Core.Bib

/-- The two families of biblatex's standard styles whose reference lists
the engine sets: numeric labels over the standard drivers, and authoryear's
name-and-date head (authoryear.bbx). -/
public inductive BblStyle where
  | numeric
  | authoryear
  deriving Repr, BEq, Inhabited

/-- The biblatex options the drivers read, at biblatex's defaults (biblatex
manual §3.1.2). -/
public structure BblOptions where
  style : BblStyle := .numeric
  /-- The citations' family (`citestyle`), whose `.cbx` executes the
  uniqueness options: authoryear.cbx sets `uniquename` and `uniquelist`. -/
  cite : BblStyle := .numeric
  maxbibnames : Nat := 3
  minbibnames : Nat := 1
  maxcitenames : Nat := 3
  mincitenames : Nat := 1
  maxsortnames : Nat := 3
  minsortnames : Nat := 1
  uniquename : UniqueName := .off
  uniquelist : Bool := false
  maxitems : Nat := 3
  minitems : Nat := 1
  giveninits : Bool := false
  useprefix : Bool := false
  useauthor : Bool := true
  useeditor : Bool := true
  usetranslator : Bool := false
  abbreviate : Bool := true
  datecirca : Bool := false
  dateuncertain : Bool := false
  dashed : Bool := true
  isbn : Bool := true
  url : Bool := true
  doi : Bool := true
  eprint : Bool := true
  /-- The document's language (a BCP 47 tag): `clearlang`, biblatex's
  default, drops a `language` naming it. -/
  mainLang : String := "en"
  /-- `language=`: the language the list is worded in, where the load names
  one (`autodetect`, the default, follows babel's main language). -/
  language : Option String := none
  /-- babel's main language, as its options spell it. -/
  babelMain : Option String := none
  /-- `autolang=`: under `other`, `other*` and `langname` an entry with a
  `langid` is worded in its own language. -/
  autolang : String := "none"
  /-- An entry's `skipbib`: cited, numbered, never listed. -/
  skipbib : Bool := false
  /-- An entry's `skiplab`: no label — no number, no extradate letter. -/
  skiplab : Bool := false
  /-- An entry's `dataonly`'s `uniquename=false` and `uniquelist=false`. -/
  unique : Bool := true
  /-- `sortlocale=`: the locale the list sorts by; `auto`, the default, is
  babel's main language, as biblatex writes it into the control file. -/
  sortlocale : String := "auto"
  /-- `clearlang=`: a `language` naming the document's own is not printed. -/
  clearlang : Bool := true
  deriving Repr, BEq, Inhabited

/-- A boolean option's value as biblatex reads one: `true` or `false`, a
bare key `true`. -/
private def boolOpt (v : String) : Option Bool :=
  if v == "true" then some true else if v == "false" then some false else none

/-- The options a document's biblatex load declared, read back from the
declarations the compatibility pass carries to the bibliography (`bbx=`
names the list's family; `Compat` writes them): `none` when the document
loads no biblatex. A value that is not a number leaves the default. -/
public def BblOptions.ofDecls (decls : Option (Array String)) : Option BblOptions := do
  let ds ← decls
  let fam ← ds.findSome? fun d => (d.dropPrefix? "bbx=").map (·.toString)
  let cite : BblStyle :=
    if ds.contains "cbx=authoryear" then .authoryear else .numeric
  let val (k : String) : Option String := (ds.toList.reverse.findSome? fun d =>
    (d.dropPrefix? (k ++ "=")).map (·.toString))
  let num (k : String) (dflt : Nat) : Nat := ((val k).bind String.toNat?).getD dflt
  let flag (k : String) (dflt : Bool) : Bool := ((val k).bind boolOpt).getD dflt
  let maxnames := num "maxnames" 3
  let minnames := num "minnames" 1
  let giveninits := flag "giveninits" (flag "firstinits" false)
  let uniquename : UniqueName := match val "uniquename" with
    | some "true" | some "full" => .full
    | some "init" => .init
    | some "allinit" => .allinit
    | some "allfull" => .allfull
    | some "false" => .off
    | _ => if cite == .authoryear then .full else .off
  -- biblatex.sty's end-of-preamble check: a names' initials option turns
  -- `uniquename=full` into `init` and `allfull` into `allinit`, since a
  -- list that prints initials tells names apart by them.
  let uniquename := if !giveninits then uniquename else match uniquename with
    | .full => .init
    | .allfull => .allinit
    | .off => .off
    | .init => .init
    | .allinit => .allinit
  some { style := if fam == "authoryear" then .authoryear else .numeric
         cite
         maxbibnames := num "maxbibnames" maxnames
         minbibnames := num "minbibnames" minnames
         maxcitenames := num "maxcitenames" maxnames
         mincitenames := num "mincitenames" minnames
         maxsortnames := num "maxsortnames" maxnames
         minsortnames := num "minsortnames" minnames
         uniquename
         uniquelist := flag "uniquelist" (cite == .authoryear)
         language := val "language"
         babelMain := ds.toList.reverse.findSome? fun d => (d.dropPrefix? "mainlang=").map (·.toString)
         autolang := (val "autolang").getD "none"
         maxitems := num "maxitems" 3
         minitems := num "minitems" 1
         giveninits
         useprefix := flag "useprefix" false
         useauthor := flag "useauthor" true
         useeditor := flag "useeditor" true
         usetranslator := flag "usetranslator" false
         abbreviate := flag "abbreviate" true
         datecirca := flag "datecirca" false
         dateuncertain := flag "dateuncertain" false
         dashed := flag "dashed" true
         isbn := flag "isbn" true
         url := flag "url" true
         doi := flag "doi" true
         eprint := flag "eprint" true
         sortlocale := (val "sortlocale").getD "auto"
         clearlang := flag "clearlang" true }

/-- The sorting scheme the load declared (`sorting=`), biblatex's default
for the family where none is. -/
public def bblSorting (decls : Option (Array String)) : String :=
  ((decls.getD #[]).toList.reverse.findSome? fun d => (d.dropPrefix? "sorting=").map (·.toString)).getD
    "nty"

/-- An entry's `options` field (biblatex manual §2.2.3, "options"): its
comma-separated `key=value` items, a bare key `true`. -/
public def entryOptions (e : Entry) : List (String × String) :=
  match e.field? "options" with
  | none => []
  | some v =>
    ((text v).splitOn ",").filterMap fun item =>
      let item := item.trimAscii.toString
      if item.isEmpty then none
      else match item.splitOn "=" with
        | [k] => some (k.trimAscii.toString, "true")
        | k :: rest => some (k.trimAscii.toString, ("=".intercalate rest).trimAscii.toString)
        | [] => none

/-- The entry-scope options the engine applies (biblatex.sty's
`\DeclareBiblatexOption{…,entry}` and biber's `dataonly`), each read as the
document's option of that name is. -/
public def entryOptionKeys : List String :=
  ["useprefix", "giveninits", "firstinits", "maxnames", "minnames", "maxbibnames", "minbibnames",
   "maxcitenames", "mincitenames", "maxsortnames", "minsortnames", "maxitems", "minitems",
   "useauthor", "useeditor", "usetranslator", "abbreviate", "isbn", "url", "doi", "eprint",
   "skipbib", "skipbiblist", "skiplab", "dataonly"]

/-- The options an entry is set under: the document's, with its `options`
over them — `dataonly` is `skipbib`, `skiplab` and its names out of
uniqueness, as biber resolves it. -/
public def BblOptions.forEntry (o : BblOptions) (e : Entry) : BblOptions :=
  (entryOptions e).foldl (init := o) fun o (k, v) =>
    let n (d : Nat) : Nat := v.toNat?.getD d
    let b (d : Bool) : Bool := (boolOpt v).getD d
    match k with
    | "useprefix" => { o with useprefix := b o.useprefix }
    | "giveninits" | "firstinits" => { o with giveninits := b o.giveninits }
    | "maxnames" =>
      { o with maxbibnames := n o.maxbibnames, maxcitenames := n o.maxcitenames,
               maxsortnames := n o.maxsortnames }
    | "minnames" =>
      { o with minbibnames := n o.minbibnames, mincitenames := n o.mincitenames,
               minsortnames := n o.minsortnames }
    | "maxbibnames" => { o with maxbibnames := n o.maxbibnames }
    | "minbibnames" => { o with minbibnames := n o.minbibnames }
    | "maxcitenames" => { o with maxcitenames := n o.maxcitenames }
    | "mincitenames" => { o with mincitenames := n o.mincitenames }
    | "maxsortnames" => { o with maxsortnames := n o.maxsortnames }
    | "minsortnames" => { o with minsortnames := n o.minsortnames }
    | "maxitems" => { o with maxitems := n o.maxitems }
    | "minitems" => { o with minitems := n o.minitems }
    | "useauthor" => { o with useauthor := b o.useauthor }
    | "useeditor" => { o with useeditor := b o.useeditor }
    | "usetranslator" => { o with usetranslator := b o.usetranslator }
    | "abbreviate" => { o with abbreviate := b o.abbreviate }
    | "isbn" => { o with isbn := b o.isbn }
    | "url" => { o with url := b o.url }
    | "doi" => { o with doi := b o.doi }
    | "eprint" => { o with eprint := b o.eprint }
    | "skipbib" => { o with skipbib := b o.skipbib }
    | "skiplab" => { o with skiplab := b o.skiplab }
    | "dataonly" =>
      let on := b false
      if on then { o with skipbib := true, skiplab := true, unique := false } else o
    | _ => o

/-- The uniqueness options an entry's names are read under. -/
public def BblOptions.unique' (o : BblOptions) : UniqueOptions :=
  { uniquename := o.uniquename, uniquelist := o.uniquelist, maxcitenames := o.maxcitenames
    mincitenames := o.mincitenames, useprefix := o.useprefix }

/-- An entry's labelname under its options (biblatex.def `\DeclareLabelname`,
`useauthor`, `useeditor`, `usetranslator`): the field and its names, each
under the entry's `useprefix` where it sets no `useprefix` of its own, the
list read under the entry's citation counts. -/
public def BblOptions.labelName (o : BblOptions) (e : Entry) : Option (String × NameList) :=
  (labelNameList e o.useauthor o.useeditor o.usetranslator).map fun (f, l) =>
    let names := l.names.map fun n => { n with useprefix := n.useprefix.orElse fun _ => some o.useprefix }
    (f, { l with names, maxCite := some o.maxcitenames, minCite := some o.mincitenames
                 unique := o.unique })

/-! ## The punctuation tracker -/

/-- What the last printed mark leaves for the next one to read — TeX's
space factor as biblatex classifies it: an ordinary character, the entry's
start, or one of its punctuation marks (`dot` is an abbreviation's). -/
private inductive Sf where
  | letter
  | start
  | dot
  | comma
  | semicolon
  | colon
  | period
  | exclam
  | question
  deriving BEq

/-- `\DeclareCapitalPunctuation{.!?}`: a string after a sentence's end, or
at the entry's start, is capitalized. -/
private def Sf.capital : Sf → Bool
  | .start | .period | .exclam | .question => true
  | .letter | .dot | .comma | .semicolon | .colon => false

/-- biblatex's punctuation pairs (biblatex.sty `\blx@resetpunct`): may
`mark` follow what was printed last? After an ordinary character anything
may; a comma, semicolon or colon may follow an abbreviation dot, `!` or
`?`; `!` and `?` may follow a dot; a period or a dot follows no mark. -/
private def allowedAfter (mark prev : Sf) : Bool :=
  match prev with
  | .letter | .start => true
  | p =>
    match mark with
    | .comma | .semicolon | .colon => p == .dot || p == .exclam || p == .question
    | .exclam | .question => p == .dot
    | .letter | .start | .dot | .period => false

/-- The class a printed text leaves: its last character, read through the
quotes and brackets TeX's space factor reads through (biblatex's sfcodes
make an opening parenthesis transparent too, so `(Visited on …)` after a
period capitalizes). -/
private def sfAfter (prev : Sf) (s : String) : Sf :=
  match (s.toList.reverse.dropWhile fun c =>
      c == '”' || c == '’' || c == '“' || c == '‘' || c == ')' || c == ']' || c == '(' ||
        c == '[').head? with
  | none => prev
  | some '.' => .period
  | some ',' => .comma
  | some ';' => .semicolon
  | some ':' => .colon
  | some '!' => .exclam
  | some '?' => .question
  | some _ => .letter

/-- One of biblatex's punctuation commands. -/
private inductive Op where
  | period
  | dot
  | comma
  | semicolon
  | colon
  | space
  | nbspace
  | text (s : String)

/-- `\newunitpunct`, the unit and block separator: `\addperiod\space`. -/
private def newunitpunct : List Op := [.period, .space]

/-- The tracker's state, biblatex.sty's toggles (`blx@insert`,
`blx@lastins`, `blx@unit`, `blx@block`, `blx@keepunit`) and buffered unit
punctuation, over the output so far and the space a following mark may
take back (`\unspace`). -/
private structure Tk where
  out : Array Ir.Inline := #[]
  gap : Option String := none
  sf : Sf := .start
  insert : Bool := false
  lastins : Bool := false
  unit : Bool := false
  block : Bool := false
  keepunit : Bool := false
  unitPunct : List Op := newunitpunct
  parens : Nat := 0
  /-- Fields a macro cleared after printing them (`\clearname`,
  `\clearfield`): later macros read them as undefined. -/
  cleared : List String := []
  /-- The fields the driver read: what it decided about. -/
  read : List String := []
  /-- What reading the fields reported: diagnostics and boundary pictures. -/
  report : FieldReport := {}
  /-- The field texts read so far, across the list's entries. -/
  cache : FieldCache := {}

/-- What a driver reads: the entry, the options it is set under, the field
reading, the entry's extradate letter, whether its names repeat the last
entry's (authoryear's dash), its labelname's field with the names its
`uniquelist` shows, and the document's month names, which a legacy `month`
may spell. -/
private structure BCtx where
  e : Entry
  opts : BblOptions
  cv : FieldText
  extra : String
  dash : Bool
  labelUl : Option (String × Nat)
  months : Array String
  /-- The entry's label date (`Entry.labelDate`), read once. -/
  labelDate : Option (String × DateParts)
  /-- Set as `\fullcite` sets it: every name given first. -/
  fullcite : Bool := false

private abbrev BM := ReaderT BCtx (StateM Tk)

/-- The pending space, printed before content that follows it. -/
private def flushGap : BM Unit := modify fun t =>
  match t.gap with
  | some g => { t with out := if t.out.isEmpty then t.out else t.out.push (.text g), gap := none }
  | none => t

/-- The text a printed piece leaves the space factor of: a citation or a
reference a field holds sets its mark, which ends in a letter, a digit or
a bracket — never the `?` an unresolved one shows for now. A leaf of
`Ir.mapInlines`. -/
private def sfText (xs : Array Ir.Inline) : String :=
  Ir.plainText (Ir.mapInlines (fun x => match x with
    | .cite _ _ => .text "0"
    | .ref _ _ _ _ => .text "0"
    | x => x) xs)

/-- Print inline content: the pending space, then the content. -/
private def put (xs : Array Ir.Inline) : BM Unit := do
  unless xs.isEmpty do
    flushGap
    modify fun t => { t with out := t.out ++ xs, sf := sfAfter t.sf (sfText xs) }

private def putText (s : String) : BM Unit := put #[.text s]

/-- `\addperiod`, `\adddot`, `\addcomma`, …: take back a pending space, then
add the mark where the pair rule allows (`allowedAfter`). -/
private def addMark (m : Sf) (ch : String) : BM Unit := modify fun t =>
  let t := { t with gap := none }
  if allowedAfter m t.sf && !t.out.isEmpty then { t with out := t.out.push (.text ch), sf := m }
  else t

private def runOp : Op → BM Unit
  | .space => modify fun t => { t with gap := some " " }
  | .nbspace => modify fun t => { t with gap := some " " }
  | .text s => putText s
  | .period => do
    addMark .period "."
    modify fun t => if t.sf == .dot then { t with sf := .period } else t
  | .dot => do
    addMark .dot "."
    modify fun t => if t.sf == .period then { t with sf := .dot } else t
  | .comma => addMark .comma ","
  | .semicolon => addMark .semicolon ";"
  | .colon => addMark .colon ":"

/-- `\unspace`: the pending space taken back. -/
private def unspace : BM Unit := modify fun t => { t with gap := none }

/-- `\midsentence`: what follows reads as inside a sentence. -/
private def midsentence : BM Unit := modify fun t => { t with sf := .letter }

/-- `\isdot`: a period just printed is an abbreviation's dot. -/
private def isdot : BM Unit := modify fun t => if t.sf == .period then { t with sf := .dot } else t

/-- `\blx@begunit`: before content that prints, the buffered unit
punctuation once something is printed (`\newblockpunct` is empty under
`block=none`). -/
private def begunit : BM Unit := do
  let t ← get
  if t.insert then
    if t.unit then
      for op in t.unitPunct do runOp op
      modify fun t => { t with unit := false, keepunit := false }
    modify fun t => { t with block := false }

private def endunit : BM Unit := modify fun t => { t with insert := true, lastins := true }
private def nounit : BM Unit := modify fun t => { t with lastins := false }

/-- `\setunit{p}`. -/
private def setunit (p : List Op) : BM Unit := modify fun t =>
  if t.keepunit then t else { t with unitPunct := p, unit := true }

/-- `\setunit*{p}`: only after a print command that printed. -/
private def setunitStar (p : List Op) : BM Unit := do
  if (← get).lastins then setunit p

private def newunit : BM Unit := setunit newunitpunct
private def newblock : BM Unit := modify fun t => { t with block := true }

/-- `\printunit{p}`: buffered against every `\setunit` until it prints. -/
private def printunit (p : List Op) : BM Unit := modify fun t =>
  { t with unitPunct := p, keepunit := true, unit := true }

/-- A print command whose content is known to print. -/
private def printWith (body : BM Unit) : BM Unit := do
  begunit
  body
  endunit

/-- A field's TeX text through the reading in force, once per text
(`FieldCache.read`). -/
private def conv (s : String) : BM (Array Ir.Inline) := do
  let cv := (← read).cv
  let t ← get
  let ((xs, ds), cache) := t.cache.read cv s
  set { t with report := t.report ++ ds, cache }
  pure xs

/-- An entry's field, present when it holds more than white space and no
macro cleared it. -/
private def fld (name : String) : BM (Option String) := do
  modify fun t => if t.read.contains name then t else { t with read := name :: t.read }
  if (← get).cleared.contains name then return none
  pure (((← read).e.field? name).filter fun v => !v.trimAscii.toString.isEmpty)

/-- `\clearname`, `\clearfield`. -/
private def clear (name : String) : BM Unit := modify fun t => { t with cleared := name :: t.cleared }

private def has (name : String) : BM Bool := do pure (← fld name).isSome

/-- Content wrapped in a style: what `body` prints, under `st`. -/
private def styled (st : Ir.Style) (body : BM Unit) : BM Unit := do
  flushGap
  let n := (← get).out.size
  body
  modify fun t =>
    if t.out.size > n then
      { t with out := (t.out.extract 0 n).push (.styled st (t.out.extract n t.out.size)) }
    else t

/-- `\printtext[parens]{body}` (and `brackets`): the pair around what the
body prints, brackets inside parentheses (`\mkbibparens` alternates); the
pair prints only around content that printed (the declared departure). -/
private def wrapped (brackets : Bool) (body : BM Unit) : BM Unit := do
  let before ← get
  begunit
  let depth := (← get).parens
  let sq := brackets || depth % 2 == 1
  putText (if sq then "[" else "(")
  let n := (← get).out.size
  modify fun t => { t with parens := depth + 1, insert := false }
  body
  let t ← get
  if t.out.size == n then
    set { before with report := t.report, read := t.read, cleared := t.cleared }
    nounit
  else
    modify fun t => { t with parens := depth, gap := none }
    putText (if sq then "]" else ")")
    -- `\bibrightparen` is `)\midsentence`: what follows reads a letter
    modify fun t => { t with sf := .letter }
    endunit

/-! ## Strings -/

/-- One piece of a localized string: text, a punctuation command, or the
original-language list (`\lbx@sfromlang`, `\lbx@lfromlang`). -/
public inductive BibPiece where
  | txt (s : String)
  | dot
  | comma
  | semicolon
  | colon
  | space
  | nbspace
  | fromLang
  deriving Repr, BEq, Inhabited

/-- A string's TeX as its pieces, and whether every command in it was one
the pieces spell: `\adddot`, `\adddotspace`, `\addabbrvspace`, `\addspace`,
`\addnbspace`, `\addcomma`, `\finalandcomma` (English's is `\addcomma`),
`\addsemicolon`, `\finalandsemicolon`, `\addcolon`, a control space, `\S`
(`§`), `~` (a no-break space), and the original-language list. -/
public def bibStringPieces (src : String) : Array BibPiece × Bool := Id.run do
  let cs := src.toList.toArray
  let mut out : Array BibPiece := #[]
  let mut cur := ""
  let mut ok := true
  let mut i := 0
  for _ in [0:cs.size + 1] do
    if h : i < cs.size then
      let c := cs[i]
      if c == '\\' then
        let mut j := i + 1
        let mut name := ""
        for _ in [0:cs.size] do
          match cs[j]? with
          | some d => if d.isAlpha || d == '@' then name := name.push d; j := j + 1 else break
          | none => break
        if name.isEmpty then
          name := (cs[i + 1]?.map String.singleton).getD ""
          j := i + 2
        else
          -- a control word ends at the spaces after it, which TeX skips
          for _ in [0:cs.size] do
            if cs[j]? == some ' ' then j := j + 1 else break
        let ps : Option (Array BibPiece) := match name with
          | "adddot" => some #[.dot]
          | "adddotspace" => some #[.dot, .space]
          | "addabbrvspace" | "addspace" | " " => some #[.space]
          | "addnbspace" => some #[.nbspace]
          | "addcomma" | "finalandcomma" => some #[.comma]
          | "addsemicolon" | "finalandsemicolon" => some #[.semicolon]
          | "addcolon" => some #[.colon]
          | "S" => some #[.txt "§"]
          | "lbx@sfromlang" | "lbx@lfromlang" => some #[.fromLang]
          | _ => none
        match ps with
        | some ps =>
          unless cur.isEmpty do out := out.push (.txt cur)
          cur := ""
          out := out ++ ps
        | none =>
          ok := false
          cur := cur ++ name
        i := j
      else if c == '~' then
        unless cur.isEmpty do out := out.push (.txt cur)
        cur := ""
        out := out.push .nbspace
        i := i + 1
      else if c == '{' || c == '}' then
        i := i + 1
      else
        cur := cur.push c
        i := i + 1
    else break
  unless cur.isEmpty do out := out.push (.txt cur)
  return (out, ok)

/-- The strings by key, each form read into its pieces once per process,
on first use (`Unit`, as `Nfc`'s tables take it, so a document with no
biblatex list never builds it). -/
private def loadStrings (_ : Unit) : Std.HashMap String (Array BibPiece × Array BibPiece) :=
  BibStringsData.english.foldl (init := {}) fun m (k, longForm, shortForm) =>
    m.insert k ((bibStringPieces longForm).1, (bibStringPieces shortForm).1)

private def stringTable : Thunk (Std.HashMap String (Array BibPiece × Array BibPiece)) :=
  Thunk.mk loadStrings

/-- A bibliography string's pieces in the form the options ask for — the
short form under `abbreviate`, else the long. -/
private def bibStringOf (short : Bool) (key : String) : Option (Array BibPiece) :=
  (stringTable.get.get? key).map fun (longForm, shortForm) => if short then shortForm else longForm

/-- Is a value one of the strings' keys (`\ifbibstring`)? -/
private def isBibstring (v : String) : Bool :=
  stringTable.get.contains (text v).trimAscii.toString

private def capFirst (s : String) : String :=
  match s.toList with
  | c :: cs => String.ofList (c.toUpper :: cs)
  | [] => s

/-- A string's pieces printed in place, its first letter capitalized after
a sentence's end (`\bibstring`'s `\ifcapital`); the original-language list
as `fromLang` prints it, which a string of its own never holds. -/
private def putPiecesWith (fromLang : BM Unit) (ps : Array BibPiece) : BM Unit := do
  let cap := (← get).sf.capital
  let mut first := true
  for p in ps do
    match p with
    | .txt s =>
      putText (if first && cap then capFirst s else s)
      first := false
    | .dot => runOp .dot
    | .comma => runOp .comma
    | .semicolon => runOp .semicolon
    | .colon => runOp .colon
    | .space => runOp .space
    | .nbspace => runOp .nbspace
    | .fromLang => fromLang

/-- `\printlist[sfromoriglanguage]{origlanguage}` (`\lbx@sfromlang`): each
language as its `from` string, else as its name, joined as names are; an
entry without one takes the space before it back (`\unspace`). -/
private def fromLangList : BM Unit := do
  match ← fld "origlanguage" with
  | none => unspace
  | some v =>
    let langs := (splitNames v).toList.filter (· != "others")
    let o := (← read).opts
    for l in langs, i in [0:langs.length] do
      if i > 0 then
        if i + 1 < langs.length then
          runOp .comma
          runOp .space
        else
          if langs.length > 2 then runOp .comma
          runOp .space
          putPiecesWith (pure ()) ((bibStringOf o.abbreviate "and").getD #[.txt "and"])
          runOp .space
      let k := (text l).trimAscii.toString
      match bibStringOf o.abbreviate ("from" ++ k) with
      | some ps => putPiecesWith (pure ()) ps
      | none =>
        match bibStringOf o.abbreviate ("lang" ++ k) with
        | some ps => putPiecesWith (pure ()) ps
        | none => putText k

/-- A string's pieces printed in place (`putPiecesWith`), the
original-language list read off the entry (`fromLangList`). -/
private def putPieces (ps : Array BibPiece) : BM Unit := putPiecesWith fromLangList ps

/-- `\bibstring{key}`: a print command. A key no string answers prints as
written, as biblatex prints it. -/
private def bibstring (key : String) : BM Unit := do
  match bibStringOf (← read).opts.abbreviate key with
  | some ps => printWith (putPieces ps)
  | none => printWith (putText key)

/-- A string's pieces without the print command around them. -/
private def strPieces (key : String) : BM (Array BibPiece) := do
  pure ((bibStringOf (← read).opts.abbreviate key).getD #[.txt key])

/-- english.lbx's `\mkbibordinal`: `1st`, `2nd`, `3rd`, `4th`, … `11th`,
`12th`, `13th`, `21st`. -/
private def ordinal (n : Nat) : String :=
  let m := n % 100
  let suffix := if 10 < m && m < 20 then "th"
    else match n % 10 with
      | 1 => "st"
      | 2 => "nd"
      | 3 => "rd"
      | _ => "th"
  toString n ++ suffix

/-! ## Names -/

/-- How a name list is written (biblatex.def's name formats): given name
first (`given-family`, the `default`), or the first name family first and
the rest given first (`family-given/given-family`, authoryear's
`sortname`). -/
private inductive NameFmt where
  | givenFamily
  | sortname
  deriving BEq

/-- The format a field's names print in when the macro names none
(`\printnames{author}`): its `\DeclareNameAlias` — authoryear aliases
`author`, `editor`, `translator` and `bookauthor` (through `author`) to
`sortname`; numeric, and every other field, the default. -/
private def fmtOf (field : String) : BM NameFmt := do
  pure (if (← read).opts.style == .authoryear && !(← read).fullcite &&
      ["author", "editor", "translator", "bookauthor"].contains field then .sortname
    else .givenFamily)

/-- A name list's visible names and whether more are elided (biblatex's
`liststop` and `\ifmorenames`): past `max` names its `uniquelist`, else
the first `min`, show (`shownCount`); a closing `others` is never shown
and always elides. -/
private def visibleNames (v : String) (max min : Nat) (ul : Option Nat) : List Name × Bool :=
  let ns := (splitNames v).toList
  let others := ns.getLast? == some "others"
  let ns := if others then ns.dropLast else ns
  let shown := ns.take (shownCount ns.length max min ul)
  (shown.map parseNameBiber, others || shown.length < ns.length)

/-- `\ifprefchar`: a prefix ending in one of biblatex's prefix characters
(`'` and `-`) takes no space before the family name. -/
private def prefChar (s : String) : Bool := s.endsWith "'" || s.endsWith "-"

/-- One name in TeX by biblatex's `name:given-family` (`familyFirst`
false) or `name:family-given` (true): `Yan van der Example`, `Example, Yan
van der` — under `useprefix`, `Van der Example, Yan`, its prefix
capitalized where the name opens a sentence (`cap`) — `Zed Smith Jr.`,
`Smith Jr., Zed`; the given name its initials under `giveninits`. -/
private def nameTeX (o : BblOptions) (familyFirst : Bool) (n : Name) (cap : Bool := false) :
    String :=
  let given := if o.giveninits then initials n.first else n.first
  let up := n.useprefix.getD o.useprefix
  let sfx := if n.jr.isEmpty then "" else " " ++ n.jr
  let pre (p : String) : String := if n.von.isEmpty then "" else p ++ (if prefChar n.von then "" else " ")
  if familyFirst then
    if up && !n.von.isEmpty then
      pre (if cap then capFirst n.von else n.von) ++ n.last ++ sfx ++
        (if given.isEmpty then "" else ", " ++ given)
    else
      n.last ++ sfx ++ (if given.isEmpty && n.von.isEmpty then "" else ",") ++
        (if given.isEmpty then "" else " " ++ given) ++ (if n.von.isEmpty then "" else " " ++ n.von)
  else
    (if given.isEmpty then "" else given ++ " ") ++ pre n.von ++ n.last ++ sfx

/-- How many names a list holds, an elided list counting as many. -/
private def nameCount (v : String) : Nat :=
  let ns := splitNames v
  if ns.toList.getLast? == some "others" then 2 else ns.size

/-- Do two name lists hold the same names (`\ifnamesequal`)? -/
private def namesEqual (a b : String) : Bool :=
  (splitNames a).map (text ·.trimAscii.toString) == (splitNames b).map (text ·.trimAscii.toString)

/-- `\printnames[fmt]{field}`: each visible name by the format, joined by
biblatex's delimiters (`multinamedelim`, `finalnamedelim` with its serial
comma past two names) and closed by `et al.` when names are elided
(`name:andothers`). A print command. -/
private def printNames (field : String) (fmt : NameFmt) : BM Unit := do
  match ← fld field with
  | none => nounit
  | some v =>
    let o := (← read).opts
    let ul := (← read).labelUl.bind fun (f, n) => if f == field then some n else none
    let (ns, more) := visibleNames v o.maxbibnames o.minbibnames ul
    let andPs ← strPieces "and"
    let othersPs ← strPieces "andothers"
    printWith do
      let stop := ns.length
      for n in ns, i in [0:stop] do
        if i > 0 then
          if i + 1 < stop || more then
            runOp .comma
            runOp .space
          else
            if stop > 2 then runOp .comma
            runOp .space
            putPieces andPs
            runOp .space
        let cap := (← get).sf.capital && i == 0
        put (← conv (nameTeX o (fmt == .sortname && i == 0) n cap))
        isdot
      if more then
        if stop > 1 then runOp .comma
        runOp .space
        putPieces othersPs

/-- `\printnames{field}` under the field's own format (`fmtOf`). -/
private def printNamesOf (field : String) : BM Unit := do printNames field (← fmtOf field)

/-! ## Literal lists -/

/-- How a literal list's items print: as written with `\isdot` (the
`default` format, and `publisher`, `location`); a patent's `location`,
each a country's string or as written, joined by commas alone
(`\DeclareListFormat[patent]{location}`). -/
private inductive ListFmt where
  | plain
  | patentLocation
  deriving BEq

/-- `\printlist{field}`: the items of a literal list, split on `and`, each
`#1\isdot`, joined as names are and elided past `maxitems` with `et al.`
(`list:delim`, `list:andothers`); a patent's location every item, never
elided. A print command. -/
private def printList (field : String) (fmt : ListFmt := .plain) : BM Unit := do
  match ← fld field with
  | none => nounit
  | some v =>
    let o := (← read).opts
    let items := (splitNames v).toList
    let others := items.getLast? == some "others"
    let items := if others then items.dropLast else items
    let shown := if fmt == .plain && items.length > o.maxitems then items.take o.minitems
      else items
    let more := others || shown.length < items.length
    let andPs ← strPieces "and"
    let morePs ← strPieces "andmore"
    printWith do
      let stop := shown.length
      for it in shown, i in [0:stop] do
        if i > 0 then
          if fmt == .patentLocation || i + 1 < stop || more then
            runOp .comma
            runOp .space
          else
            if stop > 2 then runOp .comma
            runOp .space
            putPieces andPs
            runOp .space
        let key := (text it).trimAscii.toString
        if fmt == .patentLocation && isBibstring key then putPieces (← strPieces key)
        else
          put (← conv it)
          isdot
      if more then
        if stop > 1 then runOp .comma
        runOp .space
        putPieces morePs

/-- The language list (`\printlist{language}`): its items as their
strings — a key itself, or `lang` and the key — joined as names are, and
those the document's language makes redundant cleared (`clearlang`). -/
private def languageList : BM Unit := do
  match ← fld "language" with
  | none => nounit
  | some v =>
    let o := (← read).opts
    let langs := (splitNames v).toList.filter fun l =>
      !o.clearlang || Locale.babelTagOf (text l).trimAscii.toString != o.mainLang
    if langs.isEmpty then return (← nounit)
    let andPs ← strPieces "and"
    printWith do
      for l in langs, i in [0:langs.length] do
        if i > 0 then
          if i + 1 < langs.length then
            runOp .comma
            runOp .space
          else
            if langs.length > 2 then runOp .comma
            runOp .space
            putPieces andPs
            runOp .space
        let k := (text l).trimAscii.toString
        match bibStringOf o.abbreviate k, bibStringOf o.abbreviate ("lang" ++ k.toLower) with
        | some ps, _ => putPieces ps
        | none, some ps => putPieces ps
        | none, none => putText k

/-! ## Dates -/

/-- A year in a long date (`\stripzeros`), its era as `dateera=astronomical`
writes it: a year before the common era after `\bibdateeraprefix`, the
minus sign. -/
private def yearLong (y : Int) : String :=
  (if y < 0 then "−" else "") ++ toString y.natAbs

/-- A year as `\mkyearzeros` pads it — four digits at least — after the
era's minus sign. -/
private def yearZeros (y : Int) : String :=
  let s := toString y.natAbs
  (if y < 0 then "−" else "") ++ String.ofList (List.replicate (4 - s.length) '0') ++ s

/-- A month's string (`\mkbibmonth`). -/
private def monthPieces (m : Nat) : BM (Array BibPiece) := do
  let keys := #["january", "february", "march", "april", "may", "june", "july", "august",
    "september", "october", "november", "december"]
  match keys[m - 1]? with
  | some k => strPieces k
  | none => pure #[.txt (toString m)]

/-- english.lbx's `\mkbibdatelong{year}{month}{day}` over one date, its
year left out where a range prints it once (`withYear` false): `May 3,
2021`, `May 2021`, `2021`, the month and day joined by a no-break space; a
year division in place of the month (`\mkbibyeardivisiondatelong`: `Spr.
2020`), its year padded. -/
private def putDateLong (d : Date) (withYear : Bool) : BM Unit := do
  match d.division with
  | some div =>
    putPieces (← strPieces div)
    if withYear then
      runOp .space
      putText (yearZeros d.year)
  | none =>
    if let some m := d.month then
      putPieces (← monthPieces m)
      match d.day with
      | some _ => runOp .nbspace
      | none => if withYear then runOp .space
    if let some day := d.day then
      putText (toString day ++ (if withYear then "," else ""))
      if withYear then runOp .space
    if withYear then putText (yearLong d.year)

/-- `\datecircaprint` and `\dateuncertainprint`, under their options. -/
private def circaMark (on : Bool) : BM Unit := do
  if on && (← read).opts.datecirca then
    putPieces (← strPieces "circa")
    runOp .space

private def uncertainMark (on : Bool) : BM Unit := do
  if on && (← read).opts.dateuncertain then putText "?"

/-- A date value as `\printdate` prints it under `date=comp`, english.lbx's
`\mkdaterangecomp` (`\lbx@us@mkdaterangetrunc@long`): one date long, a
range's shared year once (`Mar. 1–5, 2018`, `June 10–July 2, 2012`, `Mar.–
May 2019`), its shared month once, an open end or start a dash (`1989–`,
`–2015`); `extra` the extradate letter `\printdateextra` adds, after the
date or its range's end. -/
private def putDateValue (dv : DateValue) (extra : String := "") : BM Unit := do
  let sameYear := match dv.start, dv.stop with
    | some a, some (some b) => a.year == b.year
    | _, _ => false
  circaMark dv.circa
  if let some a := dv.start then putDateLong a (!sameYear)
  uncertainMark dv.uncertain
  match dv.stop with
  | none => putText extra
  | some none =>
    putText extra
    putText "–"
  | some (some b) =>
    putText "–"
    circaMark dv.endCirca
    let sameMonth := sameYear && b.division.isNone &&
      (dv.start.bind (·.month)) == b.month && b.month.isSome
    putDateLong (if sameMonth then { b with month := none } else b) true
    putText extra
    uncertainMark dv.endUncertain

/-- A legacy year (with its month) as `\printdate` prints it: the month's
string and the year, a year that is a string's key as that string
(`forthcoming`), anything else as written. -/
private def putLegacy (year : String) (month : Option String) (extra : String := "") : BM Unit := do
  if let some m := month then
    match m.toNat? with
    | some n =>
      putPieces (← monthPieces n)
      runOp .space
    | none =>
      put (← conv m)
      runOp .space
  match year.toInt? with
  | some y => putText (yearLong y)
  | none =>
    if isBibstring year then putPieces (← strPieces year) else put (← conv year)
  putText extra

/-- The year format of a label date (`labeldate=year`, `\mkdaterangeyear`):
its years only, padded, the end year where it differs (`2019–2020`, `1989–`,
`–2015`); a legacy year as a string or as written; `extra` after the start,
or the end (`\mkdaterangeyearextra`). -/
private def putLabelYear (p : DateParts) (extra : String := "") : BM Unit := do
  match p with
  | .parsed dv =>
    if let some a := dv.start then putText (yearZeros a.year)
    match dv.stop with
    | none => putText extra
    | some none =>
      putText extra
      putText "–"
    | some (some b) =>
      if dv.start.any (·.year == b.year) then putText extra
      else
        putText ("–" ++ yearZeros b.year)
        putText extra
  | .legacy year _ =>
    match year.toInt? with
    | some y => putText (yearZeros y)
    | none => if isBibstring year then putPieces (← strPieces year) else put (← conv year)
    putText extra
  | .written s =>
    put (← conv s)
    putText extra
  | .none => putText extra

/-- `\ifnumerals`: a value of numerals alone — digits, the roman numeral
letters, spaces, `.` — and the characters and dashes a range or a list is
written with (`~ , ; - + /`, en and em dashes). `\ifnumeral` is the same
without the range characters. -/
public def isNumerals (range : Bool) (s : String) : Bool :=
  let t := s.trimAscii.toString
  !t.isEmpty && t.all fun c =>
    c.isDigit || "ivxlcdmIVXLCDM .".contains c ||
      (range && ("~,;-+/".contains c || c == '–' || c == '—'))

/-- A field's date parts (`Entry.dateParts`), the fields that decide it
recorded as read. -/
private def datePartsOf (ty : String) : BM DateParts := do
  for f in (if ty.isEmpty then ["date", "year", "month"] else [ty ++ "date"]) do
    discard (fld f)
  let ctx ← read
  pure (ctx.e.dateParts ctx.months ty)

/-- `\printdate` (and `\printeventdate`, `\printorigdate`): a date type's
value as `putDateValue` prints it, a legacy year as `putLegacy`, a value
biber cannot read as written. A print command. -/
private def printDateOf (ty : String) : BM Unit := do
  match ← datePartsOf ty with
  | .parsed dv => printWith (putDateValue dv)
  | .legacy y m => printWith (putLegacy y m)
  | .written s => printWith (put (← conv s))
  | .none => nounit

private def twoDigits (n : Nat) : String :=
  let s := toString n
  (if n < 10 then "0" else "") ++ s

/-- One date by english.lbx's `\mkbibdateshort`: `MM/DD/YYYY`, two-digit
month and day, four-digit year. -/
private def dateShort (d : Date) : String :=
  (match d.month with | some m => twoDigits m ++ "/" | none => "") ++
    (match d.day with | some day => twoDigits day ++ "/" | none => "") ++ yearZeros d.year

/-- `\printurldate` under `urldate=short` (`\mkdaterangeshort`). A print
command. -/
private def printUrldate : BM Unit := do
  match ← datePartsOf "url" with
  | .parsed dv =>
    printWith do
      if let some a := dv.start then putText (dateShort a)
      match dv.stop with
      | none => pure ()
      | some none => putText "–"
      | some (some b) => putText ("–" ++ dateShort b)
  | .written s => printWith (put (← conv s))
  | .legacy .. | .none => nounit

/-- The label date (biblatex.def `\DeclareLabeldate`, `Entry.labelDate`):
its type and value, the fields that decide it recorded as read. -/
private def labelDateOf : BM (Option (String × DateParts)) := do
  -- `\DeclareLabeldate` reads its fields in turn up to the first an entry
  -- has, and prints that one: a date field after it is never printed here.
  let ld := (← read).labelDate
  let upTo := match ld with
    | some ("", _) => ["date", "year", "month"]
    | some ("event", _) => ["date", "year", "eventdate"]
    | some ("orig", _) => ["date", "year", "eventdate", "origdate"]
    | some (_, _) => ["date", "year", "eventdate", "origdate", "urldate"]
    | none => []
  for f in upTo do discard (fld f)
  pure ld

/-- `\iflabeldateisdate`: the label date is the entry's own date (or its
legacy year), the one authoryear's head merges with its letter. -/
private def labelIsDate : BM Bool := do
  pure (match ← labelDateOf with
    | some ("", _) => true
    | _ => false)

/-- Is a label date's year numerals (`\iffieldnums{labelyear}`)? A date with
a start and a legacy year of digits are; text is as `isNumerals` reads it;
an open start and `nodate` are not. -/
private def labelNumerals : Option (String × DateParts) → Bool
  | some (_, .parsed dv) => dv.start.isSome
  | some (_, .legacy y _) => isNumerals true y
  | some (_, .written s) => isNumerals true s
  | some (_, .none) | none => false

/-- The extradate letter as its field format prints it (`extradate`): bare
after a label year of numerals, else in parentheses — brackets inside a
parenthesis, as `\mkbibparens` alternates. -/
private def extraText (numerals : Bool) (letter : String) : BM String := do
  if letter.isEmpty || numerals then return letter
  let sq := (← get).parens % 2 == 1
  return (if sq then "[" else "(") ++ letter ++ (if sq then "]" else ")")

/-! ## Field formats and bibliography macros (biblatex.def) -/

/-- How an entry type's `title` format sets a title: quoted (`\mkbibquote`)
for the contained works, as written for the supplementary ones, else
emphasized. -/
private inductive TitleFmt where
  | quoted
  | plain
  | emph
  deriving BEq

private def titleFmtOf (kind : String) : TitleFmt :=
  if ["article", "inbook", "incollection", "inproceedings", "patent", "thesis",
      "unpublished"].contains kind then .quoted
  else if ["suppbook", "suppcollection", "suppperiodical"].contains kind then .plain
  else .emph

/-- Quotation marks around what `body` prints (`\mkbibquote`). -/
private def quoted (body : BM Unit) : BM Unit := do
  putText "“"
  body
  putText "”"

/-- Content under a title format. -/
private def underFmt (fmt : TitleFmt) (body : BM Unit) : BM Unit :=
  match fmt with
  | .quoted => quoted body
  | .plain => body
  | .emph => styled .italic body

/-- A plain field: `#1` as written, `\isdot` after it where its format has
one. A print command. -/
private def pfield (name : String) (dot : Bool := false) : BM Unit := do
  match ← fld name with
  | some v => printWith do
      put (← conv v)
      if dot then isdot
  | none => nounit

/-- A field formatted `\ifbibstring{#1}{\bibstring{#1}}{#1}` (`type`,
`pubstate`). -/
private def keyedField (name : String) : BM Unit := do
  match ← fld name with
  | some v =>
    let k := (text v).trimAscii.toString
    if isBibstring k then bibstring k else printWith (put (← conv v))
  | none => nounit

/-- The title macros' shape (biblatex.def `title`, `booktitle`, `maintitle`,
`journal`, `periodical`, `issue`): the title and subtitle under one format,
`\subtitlepunct` between them, then the addendum — printed as a field even
when undefined, which resets `\setunit*`'s test, except where the macro
tests it first (`journal`, `periodical`: `addonIfDefined`). -/
private def titleMacro (title subtitle addon : String) (fmt : TitleFmt) (dotted : Bool := false)
    (addonIfDefined : Bool := false) : BM Unit := do
  if (← has title) || (← has subtitle) then
    let inner : BM Unit := do
      match ← fld title with
      | some t => printWith do
          put (← conv t)
          if fmt == .quoted || dotted then isdot
      | none => nounit
      setunit newunitpunct
      match ← fld subtitle with
      | some t => printWith do
          put (← conv t)
          if fmt == .quoted || dotted then isdot
      | none => nounit
    printWith (underFmt fmt inner)
    newunit
  match ← fld addon with
  | some a => printWith (put (← conv a))
  | none => unless addonIfDefined do nounit

private def title : BM Unit := do
  titleMacro "title" "subtitle" "titleaddon" (titleFmtOf (← read).e.kind)

private def booktitle : BM Unit := titleMacro "booktitle" "booksubtitle" "booktitleaddon" .emph
private def maintitle : BM Unit := titleMacro "maintitle" "mainsubtitle" "maintitleaddon" .emph
private def journal : BM Unit :=
  titleMacro "journaltitle" "journalsubtitle" "journaltitleaddon" .emph (dotted := true)
    (addonIfDefined := true)
private def periodical : BM Unit := do
  titleMacro "title" "subtitle" "titleaddon" (titleFmtOf (← read).e.kind) (addonIfDefined := true)
private def issue : BM Unit := titleMacro "issuetitle" "issuesubtitle" "issuetitleaddon" .emph

/-- `\mkbibacro{X}`: small capitals, lowercased. -/
private def acro (s : String) : Ir.Inline := .styled .smallcaps #[.text s.toLower]

/-- A verbatim identifier's printed form, monospaced, linked where its
format links it. -/
private def verbLink (target shown : String) : Ir.Inline :=
  .link target #[.styled .mono #[.text shown]]

/-- `isbn`, `issn`, `isrn`: `\mkbibacro{ISBN}\addcolon\space #1`. -/
private def acroField (name : String) : BM Unit := do
  match ← fld name with
  | some v => printWith do
      put #[acro name]
      runOp .colon
      runOp .space
      put (← conv v)
  | none => nounit

private def doiField : BM Unit := do
  match ← fld "doi" with
  | some d => printWith do
      put #[acro "DOI"]
      runOp .colon
      runOp .space
      put #[.link ("https://doi.org/" ++ urlText d) #[.styled .mono #[.text (urlText d)]]]
  | none => nounit

private def urlField : BM Unit := do
  match ← fld "url" with
  | some u => printWith do
      put #[acro "URL"]
      runOp .colon
      runOp .space
      put #[verbLink (urlText u) (urlText u)]
  | none => nounit

/-- The eprint formats biblatex.def declares, by `eprinttype` (each also
under the spelling its alias gives): the label, and the address the
identifier links to. -/
private def eprintFormats : List (String × String × String) :=
  [("hdl", "HDL", "http://hdl.handle.net/"), ("HDL", "HDL", "http://hdl.handle.net/"),
   ("jstor", "JSTOR", "http://www.jstor.org/stable/"),
   ("JSTOR", "JSTOR", "http://www.jstor.org/stable/"),
   ("pubmed", "PMID", "http://www.ncbi.nlm.nih.gov/pubmed/"),
   ("PubMed", "PMID", "http://www.ncbi.nlm.nih.gov/pubmed/"),
   ("googlebooks", "Google Books", "http://books.google.com/books?id="),
   ("Google Books", "Google Books", "http://books.google.com/books?id=")]

/-- The `eprint` macro: `arXiv: id [class]` linked to the abstract page
(`eprint:arxiv`, the class inside the link), a declared type's label and
its link (`eprintFormats`), and any other type — or none — as
`type: id (class)`, `eprint: id`, the identifier unlinked (the declared
departure). -/
private def eprintMacro : BM Unit := do
  match ← fld "eprint" with
  | none => nounit
  | some ep =>
    let ty := (← fld "eprinttype").map fun t => (text t).trimAscii.toString
    let cls := (← fld "eprintclass").map fun c => (text c).trimAscii.toString
    let id := urlText ep
    printWith do
      match ty with
      | some t =>
        if t == "arxiv" || t == "arXiv" then
          putText "arXiv"
          runOp .colon
          runOp .space
          let shown : Array Ir.Inline := #[.styled .mono #[.text id]] ++
            (match cls with
              | some c => #[.text " ", .styled .mono #[.text ("[" ++ c ++ "]")]]
              | none => #[])
          put #[.link ("https://arxiv.org/abs/" ++ id) shown]
        else match eprintFormats.lookup t with
          | some (label, base) =>
            putText label
            runOp .colon
            runOp .space
            put #[verbLink (base ++ id) id]
          | none =>
            putText t
            runOp .colon
            runOp .space
            put #[.styled .mono #[.text id]]
            if let some c := cls then
              runOp .space
              putText ("(" ++ c ++ ")")
      | none =>
        putText "eprint"
        runOp .colon
        runOp .space
        put #[.styled .mono #[.text id]]
        if let some c := cls then
          runOp .space
          putText ("(" ++ c ++ ")")

/-- `url+urldate`: the URL, and the visit date after a space
(`\mkbibparens{\bibstring{urlseen}\space#1}`). -/
private def urlUrldate : BM Unit := do
  urlField
  if (← datePartsOf "url") != .none then
    setunitStar [.space]
    wrapped false do
      bibstring "urlseen"
      setunit [.space]
      printUrldate

/-- `doi+eprint+url`, each under its option (standard.bbx: `url=true` for
`@online` whatever the load says). -/
private def doiEprintUrl : BM Unit := do
  let o := (← read).opts
  if o.doi then doiField
  newunit; newblock
  if o.eprint then eprintMacro
  newunit; newblock
  if o.url || (← read).e.kind == "online" then urlUrldate

/-- `addendum+pubstate`. -/
private def addendumPubstate : BM Unit := do
  pfield "addendum"
  newunit; newblock
  keyedField "pubstate"

/-- `\mkpageprefix[pagination]` over a value: `p.` before a numeral, `pp.`
before numerals (a range or a list), nothing before anything else; the
pagination a field names — `column`, `line`, `verse`, `section`,
`paragraph`, `none` — in place of `page`. -/
private def pagePrefix (pagination : Option String) (v : String) : BM (Array BibPiece) := do
  let kind := ((pagination.map fun p => (text p).trimAscii.toString).filter (!·.isEmpty)).getD "page"
  if kind == "none" then return #[]
  if isNumerals false v then
    return (← strPieces kind) ++ #[.nbspace]
  if isNumerals true v then
    return (← strPieces (kind ++ "s")) ++ #[.nbspace]
  return #[]

/-- A range's hyphens as biber writes the range (one en dash), its list
separators `, ` (`\mknormrange`'s `\bibrangessep`). -/
public def normRange (v : String) : String :=
  let items := ((v.replace ";" ",").splitOn ",").map (·.trimAscii.toString) |>.filter (!·.isEmpty)
  ", ".intercalate (items.map fun t =>
    let parts := (t.replace "–" "-").splitOn "-"
    if parts.length > 1 && isNumerals true t then
      "–".intercalate (parts.filter (!·.isEmpty))
    else t)

/-- The pages format (`\mkpageprefix[bookpagination]{#1}`), the range
biber's. -/
private def pagesField (name : String := "pages") : BM Unit := do
  match ← fld name with
  | none => nounit
  | some v =>
    let t := normRange (text v).trimAscii.toString
    let pre ← pagePrefix (← fld "bookpagination") t
    printWith do
      putPieces pre
      put (← conv t)

/-- `pagetotal` (`\mkpagetotal[bookpagination]`): `320 pp.`, `1 p.`, a
value that is no numeral as written. -/
private def pagetotalField : BM Unit := do
  match ← fld "pagetotal" with
  | none => nounit
  | some v =>
    let t := (text v).trimAscii.toString
    let kind := (((← fld "bookpagination").map fun p => (text p).trimAscii.toString).filter
      (!·.isEmpty)).getD "page"
    printWith do
      put (← conv v)
      if isNumerals false t && kind != "none" then
        runOp .nbspace
        putPieces (← strPieces (kind ++ "total" ++ (if t.toNat? == some 1 then "" else "s")))

/-- The edition format: an integer as `2nd ed.`, anything else as written
with `\isdot`. -/
private def editionField : BM Unit := do
  match ← fld "edition" with
  | none => nounit
  | some v =>
    let t := (text v).trimAscii.toString
    match t.toNat? with
    | some n => printWith do
        putText (ordinal n)
        runOp .nbspace
        putPieces (← strPieces "edition")
    | none => printWith do
        put (← conv v)
        isdot

/-- `volume`: a book's `\bibstring{volume}~#1`, a journal's (article,
periodical) as written. -/
private def volumeField : BM Unit := do
  match ← fld "volume" with
  | some v =>
    if ["article", "periodical"].contains (← read).e.kind then printWith (put (← conv v))
    else printWith do
      putPieces (← strPieces "volume")
      runOp .nbspace
      put (← conv v)
  | none => nounit

/-- `part`: `.#1`. -/
private def partField : BM Unit := do
  match ← fld "part" with
  | some p => printWith (put (#[.text "."] ++ (← conv p)))
  | none => nounit

/-- `volumes`: `3 vols.`. -/
private def volumesField : BM Unit := do
  match ← fld "volumes" with
  | some v => printWith do
      put (← conv v)
      runOp .nbspace
      putPieces (← strPieces "volumes")
  | none => nounit

/-- `chapter`: `chap. 4`. -/
private def chapterField : BM Unit := do
  match ← fld "chapter" with
  | some v => printWith do
      putPieces (← strPieces "chapter")
      runOp .nbspace
      put (← conv v)
  | none => nounit

/-- `version`: `version 1.2`. -/
private def versionField : BM Unit := do
  match ← fld "version" with
  | some v => printWith do
      putPieces (← strPieces "version")
      runOp .nbspace
      put (← conv v)
  | none => nounit

/-- `series`: a journal's (article, periodical) integer as `2nd ser.`, a
string's key as its string, anything else as written; any other type's as
written. -/
private def seriesField : BM Unit := do
  match ← fld "series" with
  | none => nounit
  | some v =>
    if ["article", "periodical"].contains (← read).e.kind then
      let t := (text v).trimAscii.toString
      match t.toNat? with
      | some n => printWith do
          putText (ordinal n)
          runOp .nbspace
          putPieces (← strPieces "jourser")
      | none => if isBibstring t then bibstring t else printWith (put (← conv v))
    else printWith (put (← conv v))

/-- `in:`: `In:`, its colon buffered against what follows. -/
private def inColon : BM Unit := do
  bibstring "in"
  printunit [.colon, .space]

/-- authoryear's merged date (`bbx:ifmergeddate` under `mergedate=compact`,
`\iflabeldateisdate`): the date its head prints with the letter. -/
private def mergedDate : BM Bool := do
  pure ((← read).opts.style == .authoryear && (← labelIsDate))

/-- The `date` macro: `\printdate`, which authoryear's merged label date
replaces. -/
private def dateMacro : BM Unit := do
  if ← mergedDate then nounit else printDateOf ""

/-- `issue+date`: `(issue date)`; authoryear's `(issue)` alone, the date
merged into the head, and nothing where there is no issue to print. -/
private def issueDate : BM Unit := do
  if (← mergedDate) && !(← has "issue") then return
  wrapped false do
    pfield "issue"
    setunitStar [.space]
    dateMacro
  newunit

/-- `volume+number+eid`. -/
private def volumeNumberEid : BM Unit := do
  volumeField
  setunitStar [.dot]
  pfield "number"
  setunit [.comma, .space]
  pfield "eid"

/-- `journal+issuetitle`, and `title+issuetitle` (`titleMacro` is the
journal or the periodical's own title). -/
private def issuetitleWith (titleMacro : BM Unit) : BM Unit := do
  titleMacro
  setunitStar [.space]
  if (← has "series") then
    newunit
    seriesField
    setunit [.space]
  volumeNumberEid
  setunit [.space]
  issueDate
  setunit [.colon, .space]
  issue
  newunit

/-- `event+venue+date`. -/
private def eventVenueDate : BM Unit := do
  pfield "eventtitle"
  newunit
  pfield "eventtitleaddon"
  if (← has "venue") || (← datePartsOf "event") != .none then
    setunit [.space]
    wrapped false do
      pfield "venue"
      setunitStar [.comma, .space]
      printDateOf "event"
  newunit

/-- `series+number`. -/
private def seriesNumber : BM Unit := do
  seriesField
  setunitStar [.space]
  pfield "number"
  newunit

/-- `publisher+location+date`, `institution+location+date`,
`organization+location+date`: the place, the list after a colon, the date. -/
private def listLocationDate (list : String) : BM Unit := do
  printList "location"
  if (← has list) then setunitStar [.colon, .space] else setunitStar [.comma, .space]
  printList list
  setunitStar [.comma, .space]
  dateMacro
  newunit

/-- `location+date`. -/
private def locationDate : BM Unit := do
  printList "location"
  setunitStar [.comma, .space]
  dateMacro
  newunit

/-- `chapter+pages`. -/
private def chapterPages : BM Unit := do
  chapterField
  setunit [.comma, .space]
  pfield "eid"
  setunit [.comma, .space]
  pagesField
  newunit

/-- `note+pages`. -/
private def notePages : BM Unit := do
  pfield "note" (dot := true)
  setunit [.comma, .space]
  pagesField
  newunit

/-- `maintitle+title`: the main title — unless it is the title itself,
which clears it — its volume and part, then the title. -/
private def maintitleTitle : BM Unit := do
  let mt ← fld "maintitle"
  let t ← fld "title"
  if mt.isSome && mt == t then
    clear "maintitle"
    clear "mainsubtitle"
    clear "maintitleaddon"
  else if mt.isSome then
    maintitle
    newunit; newblock
    if (← has "volume") then
      volumeField
      partField
      setunit [.colon, .space]
  title
  newunit

/-- `maintitle+booktitle`. -/
private def maintitleBooktitle : BM Unit := do
  if (← has "maintitle") then
    maintitle
    newunit; newblock
    if (← has "volume") then
      volumeField
      partField
      setunit [.colon, .space]
  booktitle
  newunit

/-! ### Names' roles -/

/-- Is the name list one of more than one name, or elided (`\ifnumgreater
{\value{editor}}{1}` or `\ifandothers{editor}`)? -/
private def plural (field : String) : BM Bool := do
  pure (((← fld field).map nameCount).getD 0 > 1)

/-- `authorstrg`. -/
private def authorstrg : BM Unit := do
  match (← fld "authortype").map (text ·.trimAscii.toString) with
  | none => pure ()
  | some ty =>
    if isBibstring ty then bibstring (if ← plural "author" then ty ++ "s" else ty)
    else printWith (put (← conv ty))

/-- `editorstrg` (and its `editora`… counterparts): `ed.`, `eds.`, or the
`editortype`'s string. -/
private def editorstrg : BM Unit := do
  let pl ← plural "editor"
  match (← fld "editortype").map (text ·.trimAscii.toString) with
  | none => bibstring (if pl then "editors" else "editor")
  | some ty =>
    if isBibstring ty then bibstring (if pl then ty ++ "s" else ty) else printWith (put (← conv ty))

/-- The roles a name list doubles (`editor+othersstrg`,
`translator+othersstrg`): `tr` where the translators are the list, one of
`co` and `an`, one of `in`, `fo` and `af`, each with the field it clears. -/
private def rolesOf (field : String) (withTranslator : Bool) : BM (String × List String) := do
  let some v ← fld field | return ("", [])
  let same (g : String) : BM Bool := do pure ((← fld g).any (namesEqual v ·))
  let mut suffix := ""
  let mut cleared : List String := []
  if withTranslator && (← same "translator") then
    suffix := suffix ++ "tr"
    cleared := "translator" :: cleared
  if ← same "commentator" then
    suffix := suffix ++ "co"
    cleared := "commentator" :: cleared
  else if ← same "annotator" then
    suffix := suffix ++ "an"
    cleared := "annotator" :: cleared
  if ← same "introduction" then
    suffix := suffix ++ "in"
    cleared := "introduction" :: cleared
  else if ← same "foreword" then
    suffix := suffix ++ "fo"
    cleared := "foreword" :: cleared
  else if ← same "afterword" then
    suffix := suffix ++ "af"
    cleared := "afterword" :: cleared
  return (suffix, cleared)

/-- `editor+othersstrg`: the editor's string with the roles the editors
also hold (`eds. and trans.`), those names cleared — where such a string
exists; else `editorstrg`. -/
private def editorOthersStrg : BM Unit := do
  let pl ← plural "editor"
  let base := match (← fld "editortype").map (text ·.trimAscii.toString) with
    | none => if pl then "editors" else "editor"
    | some ty => if pl then ty ++ "s" else ty
  let (suffix, cleared) ← rolesOf "editor" true
  if isBibstring (base ++ suffix) then
    bibstring (base ++ suffix)
    for f in cleared do clear f
  else editorstrg

/-- `translatorstrg`. -/
private def translatorstrg : BM Unit := do
  bibstring (if ← plural "translator" then "translators" else "translator")

/-- `translator+othersstrg`. -/
private def translatorOthersStrg : BM Unit := do
  let base := if ← plural "translator" then "translators" else "translator"
  let (suffix, cleared) ← rolesOf "translator" false
  for f in cleared do clear f
  bibstring (base ++ suffix)

/-- `bytypestrg{field}{role}`: `by` and the field's type where its string
exists, the type as written where not, `by` and the role with no type. -/
private def bytypestrg (field role : String) : BM Unit := do
  match (← fld (field ++ "type")).map (text ·.trimAscii.toString) with
  | none => bibstring ("by" ++ role)
  | some ty => if isBibstring ("by" ++ ty) then bibstring ("by" ++ ty) else printWith (putText ty)

/-- `byeditor+othersstrg`. -/
private def byeditorOthersStrg : BM Unit := do
  let base := match (← fld "editortype").map (text ·.trimAscii.toString) with
    | none => "byeditor"
    | some ty => "by" ++ ty
  let (suffix, cleared) ← rolesOf "editor" true
  if isBibstring (base ++ suffix) then
    bibstring (base ++ suffix)
    for f in cleared do clear f
  else bytypestrg "editor" "editor"

/-- `bytranslator+othersstrg`. -/
private def bytranslatorOthersStrg : BM Unit := do
  let (suffix, cleared) ← rolesOf "translator" false
  for f in cleared do clear f
  bibstring ("bytranslator" ++ suffix)

/-- `with<role>` (`withcommentator`, …): the role's string and its names. -/
private def withRole (field : String) : BM Unit := do
  if (← has field) then
    bibstring ("with" ++ field)
    setunit [.space]
    printNames field .givenFamily

/-- `withothers`. -/
private def withOthers : BM Unit := do
  for f in ["commentator", "annotator", "introduction", "foreword", "afterword"], i in [0:5] do
    if i > 0 then newunit
    withRole f
    clear f

/-- `bytranslator+others`. -/
private def bytranslatorOthers : BM Unit := do
  if (← has "translator") then
    bytranslatorOthersStrg
    setunit [.space]
    printNames "translator" .givenFamily
    clear "translator"
    newunit
  withOthers

/-- `byeditorx`: the `editora`, `editorb`, `editorc` lists, each after its
`by` string. -/
private def byeditorx : BM Unit := do
  for f in ["editora", "editorb", "editorc"] do
    if (← has f) then
      bytypestrg f "editor"
      setunit [.space]
      printNames f .givenFamily
      newunit

/-- `byeditor+others`. -/
private def byeditorOthers : BM Unit := do
  if (← has "editor") then
    byeditorOthersStrg
    setunit [.space]
    printNames "editor" .givenFamily
    clear "editor"
    newunit
  byeditorx
  bytranslatorOthers

/-- `byeditor`. -/
private def byeditor : BM Unit := do
  if (← has "editor") then
    bytypestrg "editor" "editor"
    setunit [.space]
    printNames "editor" .givenFamily
    newunit
  byeditorx

/-- `byauthor`: the author after `by`, where `useauthor=false` keeps it out
of the head. -/
private def byauthor : BM Unit := do
  if !(← read).opts.useauthor && (← has "author") then
    bytypestrg "author" "author"
    setunit [.space]
    printNames "author" .givenFamily

/-- `bybookauthor`. -/
private def bybookauthor : BM Unit := do
  let ba ← fld "bookauthor"
  let au ← fld "author"
  unless (match ba, au with | some b, some a => namesEqual a b | _, _ => false) do
    printNamesOf "bookauthor"

/-! ### The head (biblatex.def, and authoryear.bbx's renewals) -/

/-- authoryear's dash for a repeated name list (`\bibnamedash`, a box the
width of the hanging indent: the dash and the space after it). -/
private def nameDash : BM Unit := do
  printWith (putText "—")
  runOp .space

/-- authoryear's `labeltitle`: the `label`, else the `shorttitle` in the
title's format, else the title — which it clears. -/
private def labeltitle : BM Unit := do
  let fmt := titleFmtOf (← read).e.kind
  let inFmt (v : String) : BM Unit := printWith do
    underFmt fmt do
      put (← conv v)
      if fmt == .quoted then isdot
  match ← fld "label" with
  | some _ => pfield "label"
  | none =>
    match ← fld "shorttitle" with
    | some st => inFmt st
    | none =>
      match ← fld "title" with
      | some t =>
        inFmt t
        clear "title"
      | none => nounit

/-- authoryear's `date+extradate` (`mergedate=compact`): the label date in
parentheses — the entry's own date whole with its letter
(`\printdateextra`), any other label date as its years
(`\printlabeldateextra`), `n.d.` where there is none. -/
private def dateExtradate : BM Unit := do
  let ld ← labelDateOf
  let letter := (← read).extra
  wrapped false do
    let extra ← extraText (labelNumerals ld) letter
    match ld with
    | some ("", .parsed dv) => printWith (putDateValue dv extra)
    | some ("", .legacy y m) => printWith (putLegacy y m extra)
    | some (_, p) => printWith (putLabelYear p extra)
    | none => printWith do
        putPieces (← strPieces "nodate")
        putText extra

/-- The head a list of names opens, per style: numeric prints the names
and their role (`author`, `editor`, …); authoryear renews them to print the
names — or the dash, or the label title where the list is not used — then
the label date (authoryear.bbx `author`, `bbx:editor`, `bbx:translator`).
`strg` is the role's string macro. -/
private def headNames (field : String) (use : Bool) (strg : BM Unit) : BM Unit := do
  let ctx ← read
  let present := use && (← has field)
  if ctx.opts.style == .authoryear then
    if present then
      if field == "author" then
        if ctx.dash then nameDash
        else
          printNamesOf "author"
          if (← has "authortype") then setunit [.comma, .space] else setunit [.space]
        if (← has "authortype") then
          authorstrg
          setunit [.space]
      else
        if ctx.dash then nameDash
        else
          printNamesOf field
          setunit [.comma, .space]
        strg
        clear field
        setunit [.space]
    else
      labeltitle
      setunitStar [.space]
    dateExtradate
  else if present then
    printNamesOf field
    if field == "author" then
      if (← has "authortype") then
        setunit [.comma, .space]
        authorstrg
    else
      setunit [.comma, .space]
      strg
      clear field

/-- The head macros standard.bbx's drivers open with, by the names they
consult (`author/translator+others`, `author/editor+others/translator+others`,
`author/editor`, `editor+others`, `editor`, `author`): the first list the
options use and the entry has; authoryear's label title where none. -/
private inductive Head where
  | authorTranslator
  | authorEditorTranslator
  | authorEditor
  | editorOthers
  | editor
  | author
  deriving BEq

/-- The field a head prints, under the options: what authoryear's dash
compares. -/
private def Head.field (h : Head) (o : BblOptions) (e : Entry) : Option String :=
  let has (f : String) := (e.field? f).any fun v => !v.trimAscii.toString.isEmpty
  let au := o.useauthor && has "author"
  let ed := o.useeditor && has "editor"
  let tr := o.usetranslator && has "translator"
  match h with
  | .authorTranslator => if au then some "author" else if tr then some "translator" else none
  | .authorEditorTranslator =>
    if au then some "author" else if ed then some "editor" else if tr then some "translator"
    else none
  | .authorEditor => if au then some "author" else if ed then some "editor" else none
  | .editorOthers | .editor => if ed then some "editor" else none
  | .author => if au then some "author" else none

/-- A head, printed. -/
private def head (h : Head) : BM Unit := do
  let ctx ← read
  let f := h.field ctx.opts ctx.e
  let strg (field : String) : BM Unit :=
    if field == "editor" then (if h == .editor || h == .authorEditor then editorstrg else editorOthersStrg)
    else if field == "translator" then translatorOthersStrg
    else authorstrg
  match f with
  | some field => headNames field true (strg field)
  | none =>
    -- no list the options use: authoryear's label title; numeric prints nothing
    if ctx.opts.style == .authoryear then headNames "author" false (pure ()) else pure ()


/-! ## What citations read of the list's formats -/

/-- A string's plain text in its short form: its punctuation commands as
the marks they add, a no-break space as one. What a citation prints of a
string outside the tracker. -/
public def bblString (key : String) : Option String :=
  (bibStringOf true key).map fun pieces =>
    String.join (pieces.toList.map fun
      | .txt s => s
      | .dot => "."
      | .comma => ","
      | .semicolon => ";"
      | .colon => ":"
      | .space => " "
      | .nbspace => "\u00a0"
      | .fromLang => "")

/-- The label year a citation prints (`\printlabeldateextra`'s year part,
`labeldate=year`): the label date's years as `putLabelYear` prints them —
padded, an era's minus sign, a range's end where it differs — a legacy
year that is a string's key as that string, `n.d.` where there is no date;
and whether it reads as numerals, which decides how its letter is set. -/
public def bblLabelYear (months : Array String) (e : Entry) : String × Bool :=
  let ld := e.labelDate months
  let strOr (s : String) : String := if isBibstring s then (bblString s).getD s else text s
  let t := match ld with
    | some (_, .parsed dv) =>
      let a := (dv.start.map (yearZeros ·.year)).getD ""
      match dv.stop with
      | none => a
      | some none => a ++ "–"
      | some (some b) => if dv.start.any (·.year == b.year) then a else a ++ "–" ++ yearZeros b.year
    | some (_, .legacy y _) => match y.toInt? with
      | some v => yearZeros v
      | none => strOr y
    | some (_, .written s) => text s
    | some (_, .none) | none => (bblString "nodate").getD "n.d."
  (t, labelNumerals ld)

/-- A citation's postnote as biblatex's `postnote` format sets it
(`\mkpageprefix[pagination][\mknormrange]`): `p.` before a numeral, `pp.`
before numerals, the pagination the entry names in place of pages, the
range's hyphens one en dash; anything else as written. -/
public def bblPostnote (pagination : Option String) (post : String) : String :=
  let t := normRange post.trimAscii.toString
  let kind := ((pagination.map fun p => (text p).trimAscii.toString).filter (!·.isEmpty)).getD "page"
  let pre := if kind == "none" then ""
    else if isNumerals false t then (bblString kind).getD kind ++ "\u00a0"
    else if isNumerals true t then (bblString (kind ++ "s")).getD kind ++ "\u00a0"
    else ""
  pre ++ t

/-! ## The drivers (standard.bbx) -/

/-- The tail standard.bbx's drivers share after their place and date: the
identifier under `isbn` (`isbn`, `issn`, `isrn` by driver), the links, the
addendum and the publication state. -/
private def tail (ident : String) : BM Unit := do
  newunit; newblock
  if (← read).opts.isbn then acroField ident
  newunit; newblock
  doiEprintUrl
  newunit; newblock
  addendumPubstate

/-- `\setunit{\printdelim{nametitledelim}}\newblock` after the head. -/
private def nametitle : BM Unit := do
  setunit newunitpunct
  newblock

private def article : BM Unit := do
  head .authorTranslator
  nametitle
  title
  newunit
  languageList
  newunit; newblock
  byauthor
  newunit; newblock
  bytranslatorOthers
  newunit; newblock
  versionField
  newunit; newblock
  inColon
  issuetitleWith journal
  newunit
  byeditorOthers
  newunit
  notePages
  tail "issn"

private def book : BM Unit := do
  head .authorEditorTranslator
  nametitle
  maintitleTitle
  newunit
  languageList
  newunit; newblock
  byauthor
  newunit; newblock
  byeditorOthers
  newunit; newblock
  editionField
  newunit
  unless (← has "maintitle") do
    volumeField
    partField
  newunit
  volumesField
  newunit; newblock
  seriesNumber
  newunit; newblock
  pfield "note" (dot := true)
  newunit; newblock
  listLocationDate "publisher"
  newunit; newblock
  chapterPages
  newunit
  pagetotalField
  tail "isbn"

private def booklet : BM Unit := do
  head .authorEditorTranslator
  nametitle
  title
  newunit
  languageList
  newunit; newblock
  byauthor
  newunit; newblock
  byeditorOthers
  newunit; newblock
  pfield "howpublished"
  newunit; newblock
  keyedField "type"
  newunit; newblock
  pfield "note" (dot := true)
  newunit; newblock
  locationDate
  newunit; newblock
  chapterPages
  newunit
  pagetotalField
  newunit; newblock
  doiEprintUrl
  newunit; newblock
  addendumPubstate

/-- `collection` and `proceedings` (and their `mv` and `reference`
aliases). -/
private def collectionDriver (isProceedings : Bool) : BM Unit := do
  head .editorOthers
  nametitle
  maintitleTitle
  newunit
  languageList
  newunit; newblock
  if isProceedings then
    eventVenueDate
    newunit; newblock
  byeditorOthers
  newunit; newblock
  unless isProceedings do
    editionField
    newunit
  unless (← has "maintitle") do
    volumeField
    partField
  newunit
  volumesField
  newunit; newblock
  seriesNumber
  newunit; newblock
  pfield "note" (dot := true)
  newunit; newblock
  if isProceedings then
    printList "organization"
    newunit
  listLocationDate "publisher"
  newunit; newblock
  chapterPages
  newunit
  pagetotalField
  tail "isbn"

/-- `inbook` and `incollection` and `inproceedings`: the contribution, then
`In:` and the work it is in. -/
private def inDriver (kind : String) : BM Unit := do
  head .authorTranslator
  nametitle
  title
  newunit
  languageList
  newunit; newblock
  byauthor
  newunit; newblock
  inColon
  if kind == "inbook" then
    bybookauthor
    newunit; newblock
  maintitleBooktitle
  newunit; newblock
  if kind == "inproceedings" then
    eventVenueDate
    newunit; newblock
  byeditorOthers
  newunit; newblock
  unless kind == "inproceedings" do
    editionField
    newunit
  unless (← has "maintitle") do
    volumeField
    partField
  newunit
  volumesField
  newunit; newblock
  seriesNumber
  newunit; newblock
  pfield "note" (dot := true)
  newunit; newblock
  if kind == "inproceedings" then
    printList "organization"
    newunit
  listLocationDate "publisher"
  newunit; newblock
  chapterPages
  tail "isbn"

private def dataset : BM Unit := do
  head .authorEditorTranslator
  nametitle
  title
  newunit
  languageList
  newunit; newblock
  byauthor
  newunit; newblock
  byeditorOthers
  newunit; newblock
  keyedField "type"
  newunit
  editionField
  newunit
  versionField
  newunit; newblock
  seriesNumber
  newunit; newblock
  pfield "note" (dot := true)
  newunit; newblock
  printList "organization"
  newunit
  listLocationDate "publisher"
  newunit; newblock
  doiEprintUrl
  newunit; newblock
  addendumPubstate

private def manual : BM Unit := do
  head .authorEditor
  nametitle
  title
  newunit
  languageList
  newunit; newblock
  byauthor
  newunit; newblock
  byeditor
  newunit; newblock
  editionField
  newunit; newblock
  seriesNumber
  newunit; newblock
  keyedField "type"
  newunit
  versionField
  newunit
  pfield "note" (dot := true)
  newunit; newblock
  printList "organization"
  newunit
  listLocationDate "publisher"
  newunit; newblock
  chapterPages
  newunit
  pagetotalField
  tail "isbn"

private def misc : BM Unit := do
  head .authorEditorTranslator
  nametitle
  title
  newunit
  languageList
  newunit; newblock
  byauthor
  newunit; newblock
  byeditorOthers
  newunit; newblock
  pfield "howpublished"
  newunit; newblock
  keyedField "type"
  newunit
  versionField
  newunit
  pfield "note" (dot := true)
  newunit; newblock
  listLocationDate "organization"
  newunit; newblock
  doiEprintUrl
  newunit; newblock
  addendumPubstate

private def online : BM Unit := do
  head .authorEditorTranslator
  nametitle
  title
  newunit
  languageList
  newunit; newblock
  byauthor
  newunit; newblock
  byeditorOthers
  newunit; newblock
  versionField
  newunit
  pfield "note" (dot := true)
  newunit; newblock
  printList "organization"
  newunit; newblock
  dateMacro
  newunit; newblock
  doiEprintUrl
  newunit; newblock
  addendumPubstate

private def patent : BM Unit := do
  head .author
  nametitle
  title
  newunit
  languageList
  newunit; newblock
  byauthor
  newunit; newblock
  keyedField "type"
  setunitStar [.space]
  pfield "number"
  if (← has "location") then
    setunitStar [.space]
    wrapped false (printList "location" .patentLocation)
  newunit; newblock
  printNames "holder" .givenFamily
  newunit; newblock
  pfield "note" (dot := true)
  newunit; newblock
  dateMacro
  newunit; newblock
  doiEprintUrl
  newunit; newblock
  addendumPubstate

private def periodicalDriver : BM Unit := do
  head .editor
  nametitle
  issuetitleWith periodical
  newunit
  languageList
  newunit; newblock
  byeditor
  newunit; newblock
  pfield "note" (dot := true)
  tail "issn"

private def report : BM Unit := do
  head .author
  nametitle
  title
  newunit
  languageList
  newunit; newblock
  byauthor
  newunit; newblock
  keyedField "type"
  setunitStar [.space]
  pfield "number"
  newunit; newblock
  versionField
  newunit
  pfield "note" (dot := true)
  newunit; newblock
  listLocationDate "institution"
  newunit; newblock
  chapterPages
  newunit
  pagetotalField
  tail "isrn"

private def thesis : BM Unit := do
  head .author
  nametitle
  title
  newunit
  languageList
  newunit; newblock
  byauthor
  newunit; newblock
  pfield "note" (dot := true)
  newunit; newblock
  keyedField "type"
  newunit
  listLocationDate "institution"
  newunit; newblock
  chapterPages
  newunit
  pagetotalField
  tail "isbn"

private def unpublished : BM Unit := do
  head .author
  nametitle
  title
  newunit
  languageList
  newunit; newblock
  byauthor
  newunit; newblock
  pfield "howpublished"
  newunit; newblock
  keyedField "type"
  newunit; newblock
  eventVenueDate
  newunit; newblock
  pfield "note" (dot := true)
  newunit; newblock
  locationDate
  newunit; newblock
  doiEprintUrl
  newunit; newblock
  addendumPubstate

/-- The driver an entry type uses: standard.bbx's driver or the alias it
declares (`\DeclareBibliographyAlias`), every other type `misc`
(`\DeclareBibliographyAlias{*}{misc}`, `software` among them). -/
private def driverFor : String → BM Unit
  | "article" | "suppperiodical" | "review" => article
  | "book" | "mvbook" => book
  | "inbook" | "bookinbook" | "suppbook" => inDriver "inbook"
  | "incollection" | "suppcollection" | "inreference" => inDriver "incollection"
  | "inproceedings" => inDriver "inproceedings"
  | "collection" | "mvcollection" | "reference" | "mvreference" => collectionDriver false
  | "proceedings" | "mvproceedings" => collectionDriver true
  | "booklet" => booklet
  | "dataset" => dataset
  | "manual" => manual
  | "online" => online
  | "patent" => patent
  | "periodical" => periodicalDriver
  | "report" => report
  | "thesis" => thesis
  | "unpublished" => unpublished
  | _ => misc

/-- The head each driver opens with (`driverFor`'s first macro). -/
private def headOf : String → Head
  | "article" | "suppperiodical" | "review" | "inbook" | "bookinbook" | "suppbook"
  | "incollection" | "suppcollection" | "inreference" | "inproceedings" => .authorTranslator
  | "collection" | "mvcollection" | "reference" | "mvreference" | "proceedings"
  | "mvproceedings" => .editorOthers
  | "manual" => .authorEditor
  | "periodical" => .editor
  | "patent" | "report" | "thesis" | "unpublished" => .author
  | _ => .authorEditorTranslator

/-- Adjacent text nodes as one. -/
private def mergeTexts (xs : Array Ir.Inline) : Array Ir.Inline :=
  xs.foldl (fun acc x => match x, acc.back? with
    | .text b, some (.text a) => acc.pop.push (.text (a ++ b))
    | _, _ => acc.push x) #[]

/-- `\finentry`: the entry's period. -/
private def finentry : BM Unit := do
  modify fun t => { t with gap := none }
  runOp .period

/-- **One reference-list entry as biblatex's standard styles set it**, with
what reading its fields reported and the fields its driver read: the
entry's driver run over a fresh tracker under the options it is set under
(`BblOptions.forEntry`), closed by `\finentry`. `extra` is its extradate
letter, `dash` whether its names repeat the previous entry's (authoryear's
dash), `labelUl` its labelname's field and the names that list's
`uniquelist` shows, `months` the document's month names. -/
public def renderBblCached (opts : BblOptions) (cv : FieldText) (e : Entry) (extra : String)
    (dash : Bool) (labelUl : Option (String × Nat)) (months : Array String)
    (cache : FieldCache) : (Array Ir.Inline × FieldReport × List String) × FieldCache :=
  let run : BM Unit := do
    driverFor e.kind
    finentry
  let ctx : BCtx :=
    { e, opts := opts.forEntry e, cv, extra, dash, labelUl, months, labelDate := e.labelDate months }
  let (_, t) := (run.run ctx).run { cache }
  ((mergeTexts t.out, t.report, t.read), t.cache)

/-- `renderBblCached` with nothing read before. -/
public def renderBbl (opts : BblOptions) (cv : FieldText) (e : Entry) (extra : String := "")
    (dash : Bool := false) (labelUl : Option (String × Nat) := none)
    (months : Array String := Locale.en.months) :
    Array Ir.Inline × FieldReport × List String :=
  (renderBblCached opts cv e extra dash labelUl months {}).1

/-- What a field citation prints of an entry under biblatex's standard
styles (biblatex.def `\citetitle`, `\citeurl`, `\citedate`, `\fullcite`):
its label title — its `shorttitle`, else its `title`; the title itself for
`\citetitle*` (`full`) — under the `citetitle` format, its type's title
format; its `url`, a link; its date as `\printdate` prints it; and its
whole entry by its driver, every name given first (`\fullcite`'s
`\DeclareNameAlias{sortname}{default}`) and no closing period. `extra` is
its extradate letter. Beside the ink, the boundary pictures its fields set. -/
public def bblCiteField (opts : BblOptions) (cv : FieldText) (months : Array String) (e : Entry)
    (extra : String) (w : Ir.CiteField) (full : Bool) : Array Ir.Inline × Array (String × String) :=
  let run : BM Unit := match w with
    | .title => do
      let short := !full && (← has "shorttitle")
      match ← fld (if short then "shorttitle" else "title") with
      | some v =>
        let fmt := titleFmtOf (← read).e.kind
        printWith (underFmt fmt do
          put (← conv v)
          if fmt == .quoted then isdot)
      | none => nounit
    | .url => do
      match ← fld "url" with
      | some u => printWith (put #[verbLink (urlText u) (urlText u)])
      | none => nounit
    | .date => printDateOf ""
    | .full => driverFor e.kind
  let ctx : BCtx :=
    { e, opts := opts.forEntry e, cv, extra, dash := false, labelUl := none, months
      labelDate := e.labelDate months, fullcite := w == .full }
  let (_, t) := (run.run ctx).run {}
  (mergeTexts t.out, t.report.pictures)

/-- What a citation prints for an entry no name list labels, in place of
its names: authoryear.cbx's `cite:label` — the `label` field, else the
label title — and numeric.cbx's `textcite`, the label title. The label
title is biblatex.def's `\DeclareLabeltitle`, the `shorttitle`, else the
`title`, else the `maintitle`, under the `citetitle` format: quoted, its
period a dot, for an article and the six types biblatex.def lists beside
it, emphasized for every other. Beside the ink, the boundary pictures its
fields set. -/
public def bblCiteLabel (opts : BblOptions) (cv : FieldText) (months : Array String) (e : Entry) :
    Array Ir.Inline × Array (String × String) :=
  let run : BM Unit := do
    let label ← if opts.cite == .authoryear then fld "label" else pure none
    match label with
    | some v => printWith (put (← conv v))
    | none =>
      let title ← do
        match ← fld "shorttitle" with
        | some v => pure (some v)
        | none =>
          match ← fld "title" with
          | some v => pure (some v)
          | none => fld "maintitle"
      match title with
      | some v =>
        let quoted := ["article", "inbook", "incollection", "inproceedings", "patent", "thesis",
          "unpublished"].contains (← read).e.kind
        printWith (underFmt (if quoted then .quoted else .emph) do
          put (← conv v)
          if quoted then isdot)
      | none => nounit
  let ctx : BCtx :=
    { e, opts := opts.forEntry e, cv, extra := "", dash := false, labelUl := none, months
      labelDate := e.labelDate months }
  let (_, t) := (run.run ctx).run {}
  (mergeTexts t.out, t.report.pictures)

/-- The name list an authoryear head prints, as its dash compares it with
the previous entry's: the list the driver's head macro uses under the
entry's options (`Head.field`), its value; `none` where the head prints a
title, which resets the comparison. -/
public def bblHeadNames (o : BblOptions) (e : Entry) : Option String :=
  ((headOf e.kind).field (o.forEntry e) e).bind e.field?

end LeanTex.Core.Bib
