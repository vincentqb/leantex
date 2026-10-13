module

/-! The six roles a listing's tokens paint in, and a table of one value per role, in a leaf the
colour registry reads without the lexers. -/
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

/-- A role's weights, bold and italic: keywords bold, comments italic, the rest regular. -/
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
