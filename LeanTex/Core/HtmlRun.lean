module

public import LeanTex.Core.HtmlRead
public import LeanTex.Core.Html

/-! What a document the HTML parser builds runs: its script elements, event handlers, links to
script URLs and embedded documents. -/

namespace LeanTex.Core.HtmlRead

/-- What a document runs: a script element's text, an event handler, a link to a script URL, or an
element embedding a document or plugin of its own. -/
public inductive Run where
  | script (text : List Char)
  | handler (name value : String)
  | navigation (url : String)
  | embedding (tag : String)
  deriving DecidableEq, Repr

/-- A text with the white space at both its ends dropped. -/
@[expose] public def trimWs (l : List Char) : List Char :=
  ((l.dropWhile isWs).reverse.dropWhile isWs).reverse

/-- Whether a script element's type, as the parser stores its attributes, makes it a data block. -/
@[expose] public def dataBlock (attrs : Array (String × String)) : Bool :=
  (attrs.find? (·.1 == "type")).map (·.2) == some "application/ld+json"

/-- What an element's attributes run: an event handler, or a link to a script URL. -/
@[expose] public def attrRuns (attrs : List (String × String)) : List Run :=
  attrs.flatMap fun kv =>
    (if kv.1.startsWith "on" then [.handler kv.1 kv.2] else []) ++
      (if Html.scriptLink kv.1 kv.2 then [.navigation kv.2] else [])

/-- The elements that embed a document or a plugin, which may run script of their own. -/
@[expose] public def embeddingTags : List String := ["iframe", "frame", "object", "embed", "portal"]

/-- What an element itself runs, before its children: its embedding, its attributes' handlers and
links, and a script element's text outside a data block. -/
@[expose] public def elemRuns (tag : String) (attrs : Array (String × String)) (kids : Array Dom) :
    List Run :=
  (if embeddingTags.contains tag then [.embedding tag] else []) ++ attrRuns attrs.toList ++
    (if tag == "script" && !dataBlock attrs then
      [.script (trimWs (Dom.charsList kids.toList).toList)] else [])

mutual

/-- What a node and its descendants run, in document order, after `acc`. -/
@[expose] public def Dom.runsInto (acc : Array Run) : Dom → Array Run
  | .text _ => acc
  | .elem tag attrs kids => Dom.runsListInto (acc ++ (elemRuns tag attrs kids).toArray) kids.toList

@[expose] public def Dom.runsListInto (acc : Array Run) : List Dom → Array Run
  | [] => acc
  | d :: rest => Dom.runsListInto (Dom.runsInto acc d) rest

end

/-- What a node and its descendants run, in document order. -/
@[expose] public def Dom.runs (d : Dom) : List Run := (Dom.runsInto #[] d).toList

@[expose] public def Dom.runsList (l : List Dom) : List Run := (Dom.runsListInto #[] l).toList


end LeanTex.Core.HtmlRead
