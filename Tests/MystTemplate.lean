module

public import Tests.Support

public section

open LeanTex.Core LeanTex.Core.MystTemplate
open LeanTex.Core.Jtex (Value)

namespace Tests.MystTemplate

/-- An invented template declaration in jtex v1's spelling. -/
private def yml : Array String :=
  #["jtex: v1", "title: Invented Template", "options:", "  - id: style", "    type: choice",
    "    choices: [one, two]", "    default: one", "  - id: journal", "    type: string",
    "    required: true", "    max_chars: 8", "  - id: count", "    type: number", "    min: 5",
    "    max: 1", "  - id: draft", "    type: boolean", "    condition:", "      id: style",
    "      value: two", "parts:", "  - id: abstract", "    required: true", "    max_words: 3",
    "  - id: keypoints", "    as_list: true", "doc:", "  - id: title", "    required: true",
    "  - id: keywords", "    required: true", "    condition:", "      id: style", "      value: two",
    "packages: [amsmath, natbib]", "files: [invented.cls]", "style:", "  bibliography: natbib"]

/-- An invented front matter: two authors, one corresponding, at affiliations by id and by name. -/
private def front : List (String × Value) :=
  [("title", .str "Kilo Lima"),
   ("authors", .arr [.obj [("name", .str "Ada Example"), ("affiliations", .arr [.str "zza"]),
      ("corresponding", .bool true), ("email", .str "ada@example.org")], .obj [("name", .str "Bo Van Sample"),
      ("affiliations", .str "Mike Institute")]]),
   ("affiliations", .arr [.obj [("id", .str "zza"), ("name", .str "Oscar College")]]),
   ("date", .str "2026-01-15"), ("bibliography", .str "refs.bib")]

/-- myst-templates' template.yml checks and extendFrontmatter, each answer below as myst-templates
1.x answers it for the same input. -/
def checks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  t "yaml: a plain scalar continues on lines indented past its key, as template.yml descriptions do"
    (Md.yamlTree #["a: one", "  two", "b: c"] == some (Md.Yaml.map #[("a", .scalar "one two"), ("b", .scalar "c")]))
  let some y := Md.yamlTree yml | t "template.yml: the invented declaration reads as YAML" false
  let (tpl, issues) := read y
  t s!"template.yml: options, parts, doc fields, packages, files and style read ({repr issues})"
    (tpl.options.size == 4 && tpl.parts.size == 2 && tpl.doc.size == 2 &&
      tpl.packages == #["amsmath", "natbib"] && tpl.files == #["invented.cls"] &&
      tpl.bibliography == some "natbib" && issues.isEmpty)
  t "template.yml: flipped bounds are swapped, as validateTemplateOptionDefinition swaps them"
    ((tpl.options.find? (·.id == "count")).any fun d => d.min == some 1 && d.max == some 5)
  let some bad := Md.yamlTree #["options:", "  - id: format", "    type: string", "  - id: x",
    "    type: colour", "  - id: y", "    type: choice", "doc:", "  - id: nonsense"]
    | t "template.yml: the faulty declaration reads as YAML" false
  let (_, bi) := read bad
  t s!"template.yml: a reserved id, an unknown type, choices missing, an unknown doc key and no jtex version are named ({repr bi})"
    (bi.size == 5 && bi.all (· matches .malformed _ _))
  let (opts, oi) := options tpl [("journal", .str "Long journal name"), ("colour", .str "red")]
  t s!"options: the default fills, a long string and an unknown key are named, the condition's option hidden ({repr oi})"
    (opts == [("style", .str "one")] && oi.contains (.optionUnknown "colour") &&
      oi.any (· matches .optionInvalid "journal" _) && !oi.contains (.optionUnknown "draft"))
  let (_, oi) := options tpl [("style", .str "three")]
  t "options: a required option missing and a choice outside its choices are named"
    (oi.contains (.optionMissing "journal") && oi.any (· matches .optionInvalid "style" _))
  let (opts, _) := options tpl [("style", .str "two"), ("journal", .str "J"), ("draft", .bool true)]
  t "options: an option whose condition holds is read" (opts.contains ("draft", .bool true))
  let (ps, pi) := parts tpl [("abstract", .one "four words are here"), ("keypoints", .one "only one"),
    ("summary", .one "x")] opts
  t s!"parts: an as-list part takes one text as a list, a long part and an unknown one are named ({repr pi})"
    (ps.contains ("keypoints", .many #["only one"]) && pi.contains (.partTooLong "abstract" 3 true) &&
      pi.contains (.partUnknown "summary"))
  let (_, pi) := parts tpl [] opts
  t "parts: a required part missing is named, never refused" (pi.contains (.partMissing "abstract"))
  t "doc: a required field under a holding condition is named where the front matter lacks it"
    (docIssues tpl front opts == #[.docMissing "keywords"] && docIssues tpl front [] == #[])
  let (doc, di) := extend front
  let authors := match doc.get "authors" with
    | .arr xs => xs
    | _ => []
  let affs := match doc.get "affiliations" with
    | .arr xs => xs
    | _ => []
  t s!"extend: the authors' affiliations by id and by name, indexed and lettered in the order named ({repr affs})"
    (affs.map (·.get "name") == [.str "Oscar College", .str "Mike Institute"] &&
      affs.map (·.get "letter") == [.str "A", .str "B"] && di.isEmpty)
  t "extend: each author indexed, its corresponding letter, given name and surname as myst splits them"
    (authors.map (·.get "index") == [.num 1, .num 2] &&
      ((authors.head?.map (·.get "corresponding")).any (·.get "letter" == .str "A")) &&
      authors.map (·.get "surname") == [.str "Example", .str "Van Sample"] &&
      ((authors[1]?.map (·.get "affiliations")).any fun a => ((a.get "0").get "index") == Value.num 2))
  t "extend: the date's fields and a lone .bib as bibtex"
    (doc.get "date" == .obj [("day", .str "15"), ("month", .str "1"), ("year", .str "2026")] &&
      doc.get "bibtex" == .str "refs.bib")
  let (undated, ui) := extend [("title", .str "Kilo")]
  t "extend: an undated document gets no date, never the clock's, and is named"
    (undated.get "date" == .undef && ui == #[.undated])
  let inline (dept : String) : Value := .obj [("name", .str "Mike Institute"), ("department", .str dept)]
  let (doc2, di2) := extend [("authors", .arr [.obj [("name", .str "Ada"), ("affiliations", .arr [inline "Physics"]),
      ("corresponding", .bool true)], .obj [("name", .str "Bo"), ("affiliation", inline "Mathematics")]]),
    ("keywords", .str "alpha, bravo; charlie"), ("date", .str "2024-02-31")]
  let affs2 := match doc2.get "affiliations" with
    | .arr xs => xs
    | _ => []
  t s!"extend: two affiliations of one institution stay two, as myst stashes them by content ({repr affs2})"
    (affs2.map (·.get "department") == [.str "Physics", .str "Mathematics"])
  t "extend: a corresponding author without an email is named and not corresponding"
    (di2.contains (.frontInvalid "authors.0.corresponding" "an email beside it") &&
      ((match doc2.get "authors" with | .arr xs => xs | _ => []).head?.any fun (a : Value) =>
        (a.get "corresponding").get "value" == Value.bool false))
  t "extend: keywords given as text split at commas and semicolons, a date that does not exist named"
    (doc2.get "keywords" == .arr [.str "alpha", .str "bravo", .str "charlie"] &&
      di2.contains (.dateUnread "2024-02-31"))
  let (doc3, _) := extend [("author", .arr [.str "Alias One"]), ("authors", .arr [
      .obj [("name", .str "Canon Two"), ("affiliations", .arr [.str "zzx"])],
      .obj [("name", .str "Canon Three"), ("affiliations", .arr [.obj [("id", .str "zzx"), ("name", .str "Real")]])]])]
  let names3 := match doc3.get "authors" with
    | .arr xs => xs.map (·.get "name")
    | _ => []
  t s!"extend: a key wins over its alias, and a later definition replaces a placeholder of its id ({repr names3})"
    (names3 == [.str "Canon Two", .str "Canon Three"] &&
      (match doc3.get "affiliations" with | .arr xs => xs.map (·.get "name") | _ => []) == [.str "Real"])
  let multi : OptionDef := { id := "styles", kind := .choice, choices := ["a", "b"], multiple := true }
  let tplM : TemplateYml := { options := #[multi] }
  let (om, mi) := options tplM [("styles", .arr [.str "a", .str "z"])]
  t "options: a multiple option keeps its valid items and names each invalid one"
    (om == [("styles", .arr [.str "a"])] && mi.size == 1)
  t "yaml: a key indented under a key with a value, or an item under one, is outside the subset"
    (Md.yamlTree #["a: one", "  b: two"] == none && Md.yamlTree #["a: one", "  - two"] == none)
  t "letters: the twentieth is T, a departure from myst's table, and the twenty-seventh AA"
    (letter 19 == "T" && letter 26 == "AA")

end Tests.MystTemplate
