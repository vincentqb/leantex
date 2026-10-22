module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests.MarkdownFront

/-- The YAML reader's nested blocks, and a markdown front matter's title block on the page: Pandoc's
`title`, `author`, `date` and `abstract`, and MyST's `authors` and `affiliations` mappings. -/
def checks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let tree := Md.yamlTree #["- name: Kilo Lima", "  affiliations: [zza]", "- Mike", "-", "  name: Oscar"]
  t s!"yaml: a sequence of mappings, a scalar item and an item opening below ({repr tree})"
    (tree == some (Md.Yaml.seq #[.map #[("name", .scalar "Kilo Lima"), ("affiliations", .seq #[.scalar "zza"])],
      .scalar "Mike", .map #[("name", .scalar "Oscar")]]))
  let nested := Md.yamlTree #["outer:", "  inner: x", "  list:", "    - a", "    - b", "text: |",
    "  one", "  two", "last: y"]
  t s!"yaml: nested mappings, a sequence under a key and a literal block scalar ({repr nested})"
    (nested == some (Md.Yaml.map #[("outer", .map #[("inner", .scalar "x"),
      ("list", .seq #[.scalar "a", .scalar "b"])]), ("text", .scalar "one\ntwo"), ("last", .scalar "y")]))
  t "yaml: a tab's indentation is outside the subset" (Md.yamlTree #["a:", "\tb: c"] == none)
  let flat := Md.yamlTree #["authors:", "  - name: Ada", "    affiliations:", "    - zza", "    email: a@example.org",
    "top:", "- x", "after: y", "a:", "b:"]
  t s!"yaml: a sequence at its key's indentation ends at that mapping's next key, and empty keys stay ({repr flat})"
    (flat == some (Md.Yaml.map #[("authors", .seq #[.map #[("name", .scalar "Ada"),
      ("affiliations", .seq #[.scalar "zza"]), ("email", .scalar "a@example.org")]]),
      ("top", .seq #[.scalar "x"]), ("after", .scalar "y"), ("a", .scalar ""), ("b", .scalar "")]))
  let page (src : String) : Array CensusPage × Array Diag :=
    let (doc, ds) := elabMd src
    (censusOf #[] (layoutOf oneFace doc), ds)
  let myst := "---\ntitle: Kilo Lima\nauthors:\n  - name: Ada Example\n    affiliations: [zza]\n" ++
    "  - name: Bo Sample\n    affiliations: [zzb]\naffiliations:\n  - id: zza\n    institution: Mike Institute\n" ++
    "  - id: zzb\n    institution: Oscar College\ndate: 2026-01-15\nabstract: |\n  An invented abstract.\n---\n\n" ++
    "# Papa\n\nBody text.\n"
  let (c, ds) := page myst
  t s!"front matter: MyST's title, authors, affiliations, date and abstract set the title block ({censusText c})"
    (["Kilo Lima", "Ada Example", "Bo Sample", "Mike Institute, Oscar College", "2026-01-15",
      "An invented abstract.", "Body text."].all (pageHas c 0 ·) && !pageHas c 0 "zza" &&
      ds.all (·.code != "W0307"))
  let order := ["Kilo Lima", "Ada Example", "An invented abstract.", "Body text."].map (lineYOf c 0 ·)
  t "front matter: the title, its authors and the abstract stand before the text, in order"
    (order.all (·.isSome) && (order.zip (order.drop 1)).all fun (a, b) => a.getD 0 < b.getD 0)
  let pandoc := "---\ntitle: Kilo Lima\nauthor: Ada Example\nabstract: An invented abstract.\n---\n\nBody text.\n"
  let (c, ds) := page pandoc
  t s!"front matter: Pandoc's title, author and abstract are read, and an undated document gets no date ({ds.map (·.message)})"
    (ds.all (·.code != "W0307") && ["Kilo Lima", "Ada Example", "An invented abstract."].all (pageHas c 0 ·) &&
      !(c[0]?.any fun p => p.lines.any fun l => (l.text.toList.filter Char.isDigit).length ≥ 4))
  t "front matter: authors at different affiliations are named as listed unmarked"
    ((page myst).2.any fun d => d.subject == some "md:affiliations")
  let (c, ds) := page "---\nauthor: Ada Example\ndate: 2026\n---\n\nBody.\n"
  t s!"front matter: a title block's keys without a title are named, never dropped ({ds.map (·.message)})"
    (!pageHas c 0 "Ada Example" && ["author", "date"].all fun k =>
      ds.any fun d => d.code == "W0307" && d.subject == some ("md:meta:" ++ k))
  let (_, ds) := page "---\ntitle: Kilo\nbibliography:\n  file: refs.bib\naffiliations:\n  - {id: a, name: X}\n---\n\nBody.\n"
  t s!"front matter: a nested bibliography and an unread affiliation are named ({ds.map (·.message)})"
    (["bibliography", "affiliations"].all fun k => ds.any fun d => d.code == "W0307" && d.subject == some ("md:meta:" ++ k))
  let (_, ds) := page "---\ntitle: Kilo\nshort_title: K\n---\n\nBody.\n"
  t "front matter: a key the title block does not read is named"
    (ds.any fun d => d.code == "W0307" && hasStr d.message "short_title")

end Tests.MarkdownFront
