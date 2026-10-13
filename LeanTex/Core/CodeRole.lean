module

public import LeanTex.Core.ListingHighlight
public import LeanTex.Core.CodeRoles

/-! The six roles a listing's tokens paint in, every Pygments token type mapped by its parent
chain: ink, keywords, names, literals, comments and errors. -/
namespace LeanTex.Core.ListingHighlight

/-- A top-level type's own role and its descendants'; a bare `Name` sets in the ink. -/
private def topRole : String → Role × Role
  | "Keyword" => (.keyword, .keyword)
  | "Name" => (.ink, .name)
  | "Literal" => (.literal, .literal)
  | "Comment" => (.comment, .comment)
  | "Error" => (.error, .error)
  | _ => (.ink, .ink)

/-- The types whose role is not their top level's, each with every descendant that names none of
its own. -/
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
