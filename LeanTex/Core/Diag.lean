namespace LeanTex.Core

structure Pos where
  line : Nat := 1
  col : Nat := 1
  deriving Repr, BEq

def Pos.next (p : Pos) (newline : Bool) : Pos :=
  if newline then ⟨p.line + 1, 1⟩ else ⟨p.line, p.col + 1⟩

theorem Pos.next_newline (p : Pos) : p.next true = ⟨p.line + 1, 1⟩ := rfl

theorem Pos.next_same_line (p : Pos) : p.next false = ⟨p.line, p.col + 1⟩ := rfl

structure Span where
  file : String
  pos : Pos
  deriving Repr, BEq

inductive Severity where
  | error
  | warning
  | note
  deriving Repr, BEq

def Severity.label : Severity → String
  | .error => "error"
  | .warning => "warning"
  | .note => "note"

structure Diag where
  severity : Severity
  code : String
  message : String
  span : Option Span := none
  help : Option String := none
  deriving Repr, BEq

end LeanTex.Core
