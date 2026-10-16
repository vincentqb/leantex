module

import LeanTex.Core.KeyVal

/-! natbib's and biblatex's citation setup as typed declarations, each carried as one word the
reference list reads back exactly. -/

namespace LeanTex.Core

/-- natbib's bare citation-setup words: `\setcitestyle`'s keywords, its `\bibstyle` door, sorting
and compression, and biblatex's citations. -/
public inductive CiteDecl.Word where
  | round | square | angle | curly | semicolon | colon | comma | authoryear | numbers
  | bibstyle | nobibstyle | sort | compress | biblatex
  deriving DecidableEq, Repr, Inhabited

/-- The keys a declaration gives a value: natbib's punctuation, `\citestyle` and package options,
biblatex's two style families, sorting and main language, then the options a biblatex load carries
to the reference list. -/
public inductive CiteDecl.Key where
  | «open» | close | citesep | aysep | yysep | notesep | citestyle | option
  | bbx | cbx | sorting | mainlang
  | maxnames | minnames | maxbibnames | minbibnames | maxcitenames | mincitenames | maxsortnames
  | minsortnames | maxitems | minitems | giveninits | firstinits | useprefix | dashed | isbn | url
  | doi | eprint | uniquename | uniquelist | language | autolang | useauthor | useeditor
  | usetranslator | abbreviate | datecirca | dateuncertain | sortlocale | clearlang
  deriving DecidableEq, Repr, Inhabited

/-- One citation-setup declaration, natbib's or biblatex's. -/
public inductive CiteDecl where
  | word (w : CiteDecl.Word)
  | set (k : CiteDecl.Key) (v : String)
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
   ("yysep", .yysep), ("notesep", .notesep), ("citestyle", .citestyle), ("option", .option),
   ("bbx", .bbx), ("cbx", .cbx), ("sorting", .sorting), ("mainlang", .mainlang)] ++
    Key.carriedNames

public def Key.name (k : Key) : String := ((Key.names.find? (·.2 == k)).map (·.1)).getD ""

/-- A declaration as the word that carries it: a bare word, or a key, `=` and its value. -/
public def spelling : CiteDecl → String
  | .word w => w.name
  | .set k v => k.name ++ "=" ++ v

/-- A word cut at its first `=`: what stands before it, and the rest past it. -/
private def splitEq : List Char → List Char × Option (List Char)
  | [] => ([], none)
  | c :: rest =>
    if c = '=' then ([], some rest) else
      let r := splitEq rest
      (c :: r.1, r.2)

/-- The declaration a word spells, where it spells one. -/
public def ofSpelling? (s : String) : Option CiteDecl :=
  match splitEq s.toList with
  | (w, none) => (Word.names.lookup (String.ofList w)).map .word
  | (k, some v) => (Key.names.lookup (String.ofList k)).map (.set · (String.ofList v))

private theorem splitEq_append (k r : List Char) (h : '=' ∉ k) :
    splitEq (k ++ r) = (k ++ (splitEq r).1, (splitEq r).2) := by
  induction k with
  | nil => rfl
  | cons c k ih =>
    simp only [List.mem_cons, not_or] at h
    simp [splitEq, ih h.2, Ne.symm h.1]

/-- Every declaration reads back from the word that carries it. -/
public theorem spelling_read_exact (d : CiteDecl) : ofSpelling? d.spelling = some d := by
  cases d with
  | word w =>
    have h : '=' ∉ w.name.toList := by cases w <;> decide
    have hl : Word.names.lookup w.name = some w := by cases w <;> rfl
    have hs := splitEq_append _ [] h
    simp only [List.append_nil, splitEq] at hs
    simp [spelling, ofSpelling?, hs, hl]
  | set k v =>
    have h : '=' ∉ k.name.toList := by cases k <;> decide
    have hl : Key.names.lookup k.name = some k := by cases k <;> rfl
    simp [spelling, ofSpelling?, String.toList_append, splitEq_append _ _ h, splitEq, hl]

/-- natbib's package options in its own declaration order, each as the words it executes. -/
public def natbibOptions : List (String × List Word) :=
  [("numbers", [.numbers, .square, .comma, .nobibstyle]),
   ("authoryear", [.authoryear, .round, .semicolon, .bibstyle]),
   ("round", [.round, .nobibstyle]), ("square", [.square, .nobibstyle]),
   ("angle", [.angle, .nobibstyle]), ("curly", [.curly, .nobibstyle]),
   ("comma", [.comma, .nobibstyle]), ("semicolon", [.semicolon, .nobibstyle]),
   ("colon", [.semicolon, .nobibstyle]), ("nobibstyle", [.nobibstyle]), ("bibstyle", [.bibstyle]),
   ("sort", [.sort]), ("compress", [.compress]), ("sort&compress", [.sort, .compress])]

/-- natbib loaded with the options given: one declaration per option it has, in its own order, and
the options it has none for. -/
public def natbibLoad (given : List String) : Array CiteDecl × List String :=
  ((natbibOptions.filter (given.contains ·.1)).toArray.map (.set .option ·.1),
   given.filter fun o => !natbibOptions.any (·.1 == o))

/-- The loss of an option natbib's table lacks, as either surface declares it. -/
public def natbibUnread (o : String) : String := s!"'natbib' option '{o}' is not honoured; skipped"

/-- The declarations `ds` executes, a package option as the words natbib's table gives it. -/
public def expand (ds : Array CiteDecl) : Array CiteDecl :=
  ds.flatMap fun
    | .set .option o => (((natbibOptions.lookup o).getD []).map CiteDecl.word).toArray
    | d => #[d]

/-- The value the last declaration of `k` among `ds` gives it. -/
public def last? (ds : Array CiteDecl) (k : Key) : Option String :=
  ds.foldl (init := none) fun acc d => match d with
    | .set k' v => if k' == k then some v else acc
    | .word _ => acc

/-- The natbib package options `ds` declares, where it declares nothing else. -/
public def options? (ds : Array CiteDecl) : Option (Array String) :=
  ds.mapM fun
    | .set .option o => some o
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

/-- A `\setcitestyle` item as natbib reads it, compared exactly as written: a keyword or the
`\bibstyle` door, or a punctuation key and its value, one outer brace group stripped. -/
public def ofItem? (item : String) : Option CiteDecl :=
  (ofSpelling? item).bind fun
    | .word w => if [.sort, .compress, .biblatex].contains w then none else some (.word w)
    | .set k v =>
      if [.open, .close, .citesep, .aysep, .yysep, .notesep].contains k then
        some (.set k (stripGroup v))
      else none

/-- The items of a `\setcitestyle` list, split at commas outside braces, kept as written. -/
public def items (src : String) : Array String := (KeyVal.split src).filter (!·.isEmpty)

end CiteDecl

end LeanTex.Core
