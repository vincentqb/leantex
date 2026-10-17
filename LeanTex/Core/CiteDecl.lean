module

import LeanTex.Core.KeyVal

/-! natbib's and biblatex's citation setup as typed declarations, each carried as one word the
elaborator reads back exactly. -/

namespace LeanTex.Core

/-- natbib's bare citation-setup words: `\setcitestyle`'s keywords, its `\bibstyle` door, sorting
and compression, and biblatex's citations. -/
public inductive CiteDecl.Word where
  | round | square | angle | curly | semicolon | colon | comma | authoryear | numbers
  | bibstyle | nobibstyle | sort | compress | biblatex
  deriving DecidableEq, Repr, Inhabited

/-- The keys a declaration gives a value: natbib's punctuation and `\citestyle`, biblatex's two
style families, sorting and main language, then the options a biblatex load carries to the
reference list. -/
public inductive CiteDecl.Key where
  | «open» | close | citesep | aysep | yysep | notesep | citestyle
  | bbx | cbx | sorting | mainlang
  | maxnames | minnames | maxbibnames | minbibnames | maxcitenames | mincitenames | maxsortnames
  | minsortnames | maxitems | minitems | giveninits | firstinits | useprefix | dashed | isbn | url
  | doi | eprint | uniquename | uniquelist | language | autolang | useauthor | useeditor
  | usetranslator | abbreviate | datecirca | dateuncertain | sortlocale | clearlang
  deriving DecidableEq, Repr, Inhabited

/-- The natbib package options the engine honours. -/
public inductive CiteDecl.Opt where
  | numbers | authoryear | round | square | angle | curly | comma | semicolon | colon
  | nobibstyle | bibstyle | sort | compress | sortCompress
  deriving DecidableEq, Repr, Inhabited

/-- One citation-setup declaration, natbib's or biblatex's. -/
public inductive CiteDecl where
  | word (w : CiteDecl.Word)
  | set (k : CiteDecl.Key) (v : String)
  | option (o : CiteDecl.Opt)
  deriving DecidableEq, Repr, Inhabited

namespace CiteDecl

public def Word.names : List (String × Word) :=
  [("round", .round), ("square", .square), ("angle", .angle), ("curly", .curly),
   ("semicolon", .semicolon), ("colon", .colon), ("comma", .comma), ("authoryear", .authoryear),
   ("numbers", .numbers), ("bibstyle", .bibstyle), ("nobibstyle", .nobibstyle), ("sort", .sort),
   ("compress", .compress), ("biblatex", .biblatex)]

public def Word.name (w : Word) : String := ((Word.names.find? (·.2 == w)).map (·.1)).getD ""

/-- The options a biblatex load carries to the reference list, as it spells them. -/
public def Key.carriedNames : List (String × Key) :=
  [("maxnames", .maxnames), ("minnames", .minnames), ("maxbibnames", .maxbibnames),
   ("minbibnames", .minbibnames), ("maxcitenames", .maxcitenames), ("mincitenames", .mincitenames),
   ("maxsortnames", .maxsortnames), ("minsortnames", .minsortnames), ("maxitems", .maxitems),
   ("minitems", .minitems), ("giveninits", .giveninits), ("firstinits", .firstinits),
   ("useprefix", .useprefix), ("dashed", .dashed), ("isbn", .isbn), ("url", .url), ("doi", .doi),
   ("eprint", .eprint), ("uniquename", .uniquename), ("uniquelist", .uniquelist),
   ("language", .language), ("autolang", .autolang), ("useauthor", .useauthor),
   ("useeditor", .useeditor), ("usetranslator", .usetranslator), ("abbreviate", .abbreviate),
   ("datecirca", .datecirca), ("dateuncertain", .dateuncertain), ("sortlocale", .sortlocale),
   ("clearlang", .clearlang)]

public def Key.names : List (String × Key) :=
  [("open", .open), ("close", .close), ("citesep", .citesep), ("aysep", .aysep),
   ("yysep", .yysep), ("notesep", .notesep), ("citestyle", .citestyle), ("bbx", .bbx),
   ("cbx", .cbx), ("sorting", .sorting), ("mainlang", .mainlang)] ++ Key.carriedNames

public def Key.name (k : Key) : String := ((Key.names.find? (·.2 == k)).map (·.1)).getD ""

/-- natbib's options as it spells them, in its own declaration order. -/
public def Opt.names : List (String × Opt) :=
  [("numbers", .numbers), ("authoryear", .authoryear), ("round", .round), ("square", .square),
   ("angle", .angle), ("curly", .curly), ("comma", .comma), ("semicolon", .semicolon),
   ("colon", .colon), ("nobibstyle", .nobibstyle), ("bibstyle", .bibstyle), ("sort", .sort),
   ("compress", .compress), ("sort&compress", .sortCompress)]

public def Opt.name (o : Opt) : String := ((Opt.names.find? (·.2 == o)).map (·.1)).getD ""

/-- The words natbib executes for an option. -/
public def Opt.words : Opt → List Word
  | .numbers => [.numbers, .square, .comma, .nobibstyle]
  | .authoryear => [.authoryear, .round, .semicolon, .bibstyle]
  | .round => [.round, .nobibstyle]
  | .square => [.square, .nobibstyle]
  | .angle => [.angle, .nobibstyle]
  | .curly => [.curly, .nobibstyle]
  | .comma => [.comma, .nobibstyle]
  | .semicolon | .colon => [.semicolon, .nobibstyle]
  | .nobibstyle => [.nobibstyle]
  | .bibstyle => [.bibstyle]
  | .sort => [.sort]
  | .compress => [.compress]
  | .sortCompress => [.sort, .compress]

/-- A declaration as the word that carries it: a bare word, or a key, `=` and its value. -/
public def spelling : CiteDecl → String
  | .word w => w.name
  | .set k v => k.name ++ "=" ++ v
  | .option o => "option=" ++ o.name

/-- The declaration a word spells, where it spells one. -/
public def ofSpelling? (s : String) : Option CiteDecl :=
  let cut := KeyVal.cutAt '=' s.toList
  let head := String.ofList cut.1
  match cut.2 with
  | none => (Word.names.lookup head).map .word
  | some v =>
    if head == "option" then (Opt.names.lookup (String.ofList v)).map .option
    else (Key.names.lookup head).map (.set · (String.ofList v))

/-- natbib loaded with the options given: one declaration per option it has, in its own order, and
the options it has none for. -/
public def natbibLoad (given : List String) : Array CiteDecl × List String :=
  ((Opt.names.filter (given.contains ·.1)).toArray.map (.option ·.2),
   given.filter fun o => (Opt.names.lookup o).isNone)

/-- A natbib option as a loss names it, from either surface. -/
public def natbibOption (o : String) : String := s!"'natbib' option '{o}'"

/-- The value the last declaration of `k` among `ds` gives it. -/
public def last? (ds : Array CiteDecl) (k : Key) : Option String :=
  ds.foldl (init := none) fun acc d => match d with
    | .set k' v => if k' == k then some v else acc
    | .word _ | .option _ => acc

/-- Whether a setup is biblatex's, whose files are the resources its list prints. -/
public def biblatex (ds : Array CiteDecl) : Bool := ds.contains (.word .biblatex)

/-- The natbib package options `ds` declares, where it declares nothing else. -/
public def options? (ds : Array CiteDecl) : Option (Array String) :=
  ds.mapM fun
    | .option o => some o.name
    | _ => none

/-- A value as TeX reads a delimited argument: one outer brace group stripped. -/
private def stripGroup (v : String) : String := Id.run do
  let cs := v.toList
  unless cs.head? == some '{' && cs.getLast? == some '}' do return v
  let mut depth : Int := 0
  let mut k := 0
  for c in cs do
    k := k + 1
    if c == '{' then depth := depth + 1
    else if c == '}' then
      depth := depth - 1
      if depth == 0 && k < cs.length then return v
  return String.ofList (cs.drop 1 |>.dropLast)

/-- A punctuation key's value as natbib reads it, one outer brace group stripped. -/
public def punct (k : Key) (v : String) : CiteDecl := .set k (stripGroup v)

/-- A `\setcitestyle` item as natbib reads it, compared exactly as written: a keyword, or a
punctuation key and its value. -/
public def ofItem? (item : String) : Option CiteDecl :=
  (ofSpelling? item).bind fun
    | .word w =>
      if [.sort, .compress, .biblatex, .bibstyle, .nobibstyle].contains w then none
      else some (.word w)
    | .set k v =>
      if [.open, .close, .citesep, .aysep, .yysep, .notesep].contains k then some (punct k v)
      else none
    | .option _ => none

end CiteDecl

end LeanTex.Core
