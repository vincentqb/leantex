module

public import LeanTex.Core.ListingHighlight

/-!
The roles a listing's tokens paint in. Every Pygments token type maps, by
its parent chain, to one of six: the ink (text, identifiers, operators,
punctuation), keywords, names (what a definition, an import or the
language's builtins name), literals (strings, numbers, constants), comments,
and the error role for what must not ship — a proof hole, an unimplemented
branch, a lexer error. A role, never a type, is what a listing's colour and
weights resolve for (`CodeColor.resolve`), so two types of one role ship
alike: a Lean proof hole (`Generic.Error`) and Python's
`NotImplementedError` (`Name.Exception`) are both `error`.
-/
namespace LeanTex.Core.ListingHighlight

public inductive Role where
  | ink | keyword | name | literal | comment | error
  deriving Repr, BEq, DecidableEq, Inhabited, Hashable

public def Role.all : List Role := [.ink, .keyword, .name, .literal, .comment, .error]

/-- The role's name, as a message spells it. -/
public def Role.word : Role → String
  | .ink => "ink"
  | .keyword => "keyword"
  | .name => "name"
  | .literal => "literal"
  | .comment => "comment"
  | .error => "error"

/-- The palette key a document declares the role's colour under. -/
public def Role.key (r : Role) : String := "code" ++ r.word

/-- A top-level type's own role, and its descendants'. A bare `Name` is an
identifier, which sets in the ink; the names below it name what a
definition, an import or the language introduces. -/
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
Lean's lexer files as pseudo-builtins, are ink; a raised exception's name
is what must not ship; a preprocessor directive, a word operator and a
markup tag are the language's own words; a session's prompt and a
document's headings are read as keywords, a session's output as
commentary; what fails, a traceback and a deleted line, is an error, and
an inserted line a value. -/
private def exceptions : List (String × Role) :=
  [("Keyword.Constant", .literal), ("Name.Constant", .literal), ("Name.Entity", .literal),
   ("Name.Variable", .ink), ("Name.Other", .ink), ("Name.Builtin.Pseudo", .ink),
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

/-- A role's weights, bold and italic: a keyword is bold and a comment
italic, as every style the engine ships sets them; the rest are upright and
regular, their colour alone telling them apart. -/
public def Role.weights : Role → Bool × Bool
  | .keyword => (true, false)
  | .comment => (false, true)
  | .ink | .name | .literal | .error => (false, false)

/-- One value per role. -/
public structure RoleTable (α : Type) where
  ink : α
  keyword : α
  name : α
  literal : α
  comment : α
  error : α

@[expose] public def RoleTable.get {α : Type} (t : RoleTable α) : Role → α
  | .ink => t.ink
  | .keyword => t.keyword
  | .name => t.name
  | .literal => t.literal
  | .comment => t.comment
  | .error => t.error

/-- Every role's value, each computed once. -/
public def RoleTable.ofFn {α : Type} (f : Role → α) : RoleTable α :=
  { ink := f .ink, keyword := f .keyword, name := f .name, literal := f .literal
    comment := f .comment, error := f .error }

public theorem RoleTable.get_ofFn {α : Type} (f : Role → α) (r : Role) :
    (RoleTable.ofFn f).get r = f r := by
  cases r <;> rfl

end LeanTex.Core.ListingHighlight
