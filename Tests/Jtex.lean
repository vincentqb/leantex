module

public import Tests.Support

public section

open LeanTex.Core.Jtex

namespace Tests.Jtex

/-- A template's rendering as text, each splice its name in brackets, or its refusal. -/
private def out (t : String) (ctx : Value) : String :=
  match render t ctx with
  | .ok ps => String.join (ps.toList.map (·.spelled))
  | .error e => "error: " ++ e

/-- jtex templates render as nunjucks 3.2.4 renders them under jtex's configuration, each answer
below nunjucks' own for the template. -/
def checks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let doc : Value := .obj [("doc", .obj [("title", .str "Kilo"), ("authors", .arr [
      .obj [("name", .str "Lima"), ("index", .num 1)], .obj [("name", .str "Mike"), ("index", .num 2)]])]),
    ("options", .obj [("flag", .bool true), ("style", .str "two")]), ("CONTENT", .splice "CONTENT")]
  t "jtex: variables print, a missing one prints nothing, a splice stands as itself"
    (out "[-doc.title-]|[- doc.missing -]|[-CONTENT-]" doc == "Kilo||⟦CONTENT⟧")
  t "jtex: a block's end drops one newline after it, and a dash strips its side's whitespace"
    (out "a\n[# if options.flag #]\nb\n[# endif #]\nc\n  [#- if true -#]  d\n[# endif #]" doc == "a\nb\ncd\n")
  t "jtex: a loop names its item and loop.last, else runs over an empty sequence"
    (out "[# for a in doc.authors #][-a.name-][# if not loop.last #], [# endif #][# endfor #]" doc == "Lima, Mike" &&
      out "[# for a in doc.missing #]x[# else #]none[# endfor #]" doc == "none")
  t "jtex: join reads an item's attribute, and length counts"
    (out "[- doc.authors | join(\", \", \"name\") -] [-doc.authors|length-]" doc == "Lima, Mike 2")
  -- nunjucks compiles `not a == b` to JavaScript's `!a == b`: `not` binds tighter than comparison
  t "jtex: not binds tighter than comparison, as nunjucks' compiled JavaScript reads it"
    (out "[# if not options.style == 'two' #]x[# else #]y[# endif #]" doc == "y" &&
      out "[# if not options.missing == false #]x[# endif #]" doc == "")
  t "jtex: a set inside a loop rebinds the name outside it, a fresh one stays in the loop"
    (out "[# set p = 'a' #][# for x in doc.authors #][# set p = x.name #][# set q = 1 #][# endfor #][-p-][-q-]" doc == "Mike")
  t "jtex: a string iterates its characters, and comparisons are JavaScript's loose ones"
    (out "[# for c in doc.title #][-c-].[# endfor #]" doc == "K.i.l.o." &&
      out "[# if doc.authors|length == '2' #]x[# endif #]" doc == "x")
  let titled : Value := .obj [("doc", .obj [("title", .str "50% of a_b & {c}")])]
  t "jtex: a value the document chose is escaped as TeX, the template's own text kept"
    ((render "\\title{[-doc.title-]}" titled).toOption.map (fun ps => String.join (ps.toList.map (Piece.tex id))) ==
      some "\\title{50\\% of a\\_b \\& \\{c\\}}")
  let tex (t : String) (ctx : Value) : Option String :=
    (render t ctx).toOption.map fun ps => String.join (ps.toList.map (Piece.tex id))
  let named : Value := .obj [("doc", .obj [("authors", .arr [.obj [("name", .str "A & B")],
    .obj [("name", .str "C_D")]])]), ("parts", .obj [("abstract", .splice "parts.abstract")])]
  t "jtex: a join's separator is the template's own TeX and its items the document's, escaped"
    (tex "\\author{[-doc.authors|join(\" \\\\and \", \"name\")-]}[# set s = ', ' #][-s-]" named ==
      some "\\author{A \\& B \\and C\\_D}, ")
  t "jtex: a part stands as its typed splice, never as text"
    ((render "[# if parts.abstract #]\\abstract{[-parts.abstract-]}[# endif #]" named).toOption ==
      some #[.text "\\abstract{", .splice "parts.abstract", .text "}"])
  t "jtex: two loop names, words after a closing tag and a misplaced not are refused"
    (["[# for k, v in doc #]x[# endfor #]", "[# if true #]x[# endif x #]", "[- 1 == not 2 -]",
      "[- doc.authors|join(', ' 'name') -]"].all fun t => (render t named).toOption.isNone)
  t "jtex: True is a variable, a string's \\n a newline, and .length JavaScript's"
    (out "[# if True #]y[# else #]n[# endif #][- \"a\\nb\" -][- doc.authors.length -]" named == "na\nb2")
  t "jtex: a tag outside the subset is refused by name"
    (out "[# include 'x' #]" doc == "error: a tag outside the subset: 'include'" &&
      (out "[# if true #]open" doc).startsWith "error:")

end Tests.Jtex
