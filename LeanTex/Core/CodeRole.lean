module

public import LeanTex.Core.ListingHighlight
public import LeanTex.Core.CodeRoles

/-!
The roles a listing's tokens paint in. Every Pygments token type maps, by
its parent chain, to one of six: the ink (text, identifiers — the name a
function, a class or a module is defined under among them — operators,
punctuation), keywords, names (builtins, decorators, attributes, labels,
properties), literals (strings, numbers, constants), comments, and the error
role for what must not ship — a proof hole, an unimplemented branch, a lexer
error. A role, never a type, is what a listing's colour and
weights resolve for (`CodeColor.resolve`), so two types of one role ship
alike: a Lean proof hole (`Generic.Error`) and Python's
`NotImplementedError` (`Name.Exception`) are both `error`.
-/
namespace LeanTex.Core.ListingHighlight

/-- A top-level type's own role, and its descendants'. A bare `Name` is an
identifier, which sets in the ink; the names below it — builtins,
decorators, attributes, labels, properties — take the name role, unless an
exception names theirs. -/
private def topRole : String → Role × Role
  | "Keyword" => (.keyword, .keyword)
  | "Name" => (.ink, .name)
  | "Literal" => (.literal, .literal)
  | "Comment" => (.comment, .comment)
  | "Error" => (.error, .error)
  | _ => (.ink, .ink)

/-- The types whose role is not their top level's, each with every
descendant that names none of its own: constants and character entities are
values; variables and other identifiers, and `self`, `cls` and the symbols
Lean's lexer files as pseudo-builtins, are ink, and so is the name a
function, a class or a module is defined or imported under, so a definition
reads as the plain uses of its name do, and as a Lean definition, whose name
Lean's lexer types as a plain identifier; a raised exception's name
is what must not ship; a preprocessor directive, a word operator and a
markup tag are the language's own words; a session's prompt and a
document's headings are read as keywords, a session's output as
commentary; what fails, a traceback and a deleted line, is an error, and
an inserted line a value. -/
private def exceptions : List (String × Role) :=
  [("Keyword.Constant", .literal), ("Name.Constant", .literal), ("Name.Entity", .literal),
   ("Name.Variable", .ink), ("Name.Other", .ink), ("Name.Builtin.Pseudo", .ink),
   ("Name.Function", .ink), ("Name.Class", .ink), ("Name.Namespace", .ink),
   ("Name.Exception", .error), ("Name.Tag", .keyword),
   ("Comment.Preproc", .keyword), ("Comment.PreprocFile", .keyword),
   ("Operator.Word", .keyword),
   ("Generic.Error", .error), ("Generic.Traceback", .error), ("Generic.Deleted", .error),
   ("Generic.Inserted", .literal), ("Generic.Output", .comment),
   ("Generic.Prompt", .keyword), ("Generic.Heading", .keyword),
   ("Generic.Subheading", .keyword)]

/-- A type's role: the nearest type of its chain, itself first, that an
exception names, else its top level's role for itself or its descendants. -/
public def Kind.role (k : Kind) : Role :=
  match k.chain.reverse.findSome? fun t => exceptions.lookup t.path with
  | some r => r
  | none =>
    match k.chain with
    | [] => .ink
    | [top] => (topRole top.path).1
    | top :: _ :: _ => (topRole top.path).2

end LeanTex.Core.ListingHighlight
