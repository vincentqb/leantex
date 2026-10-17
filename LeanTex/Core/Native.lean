module

public import LeanTex.Core.NativeKey
public import LeanTex.Core.Parse
import LeanTex.Core.Decl

/-! The native settings the surfaces lower into, each carried to the elaborator as one word its entry
reader reads back exactly (`Native.render_parse_exact`). -/

namespace LeanTex.Core.Native

open LeanTex.Core.Parse

/-- A native setting a surface lowers into: `\page` entries by key, `\tokens` entries by the length
each names, `\palette` entries by role, or one element's `\style` entries, every value spelled as
the declaration grammar reads it. -/
public inductive Setting where
  | page (entries : Array (PageKey × String))
  | tokens (entries : Array (String × String))
  | palette (entries : Array (String × String))
  | style (element : String) (entries : Array (String × String))
  deriving DecidableEq, Repr, Inhabited

namespace Setting

/-- The control a setting's declaration opens with. -/
public def head : Setting → String
  | .page _ => "page"
  | .tokens _ => "tokens"
  | .palette _ => "palette"
  | .style _ _ => "style"

/-- What the declaration spells before its block: its control, and a style's element. -/
public def opening : Setting → String
  | .style el _ => "\\style{" ++ el ++ "}"
  | s => "\\" ++ s.head

/-- Each entry's key and value as written. -/
public def pairs : Setting → List (String × String)
  | .page es => es.toList.map fun (k, v) => (k.name, v)
  | .tokens es | .palette es | .style _ es => es.toList

/-- The declaration's block, its entries joined as an author writes them. -/
public def body (s : Setting) : String := ", ".intercalate (s.pairs.map fun (k, v) => k ++ " = " ++ v)

/-- The declaration as a translation note names it. -/
public def render (s : Setting) : String := s.opening ++ "{ " ++ s.body ++ " }"

/-- Whether an entry's key and value read back from the block, beside any other entries. -/
public def carried (kv : String × String) : Bool := Decl.plainKey kv.1 && Decl.wholeValue kv.2

/-- The setting without the entries its block cannot carry whole. -/
public def kept : Setting → Setting
  | .page es => .page (es.filter fun (k, v) => carried (k.name, v))
  | .tokens es => .tokens (es.filter carried)
  | .palette es => .palette (es.filter carried)
  | .style el es => .style el (es.filter carried)

/-- The declaration a translation note names, where the setting keeps an entry. -/
public def note? (s : Setting) : Option String := if s.kept.pairs.isEmpty then none else some s.kept.render

/-- The entries `kept` drops, as written. -/
public def dropped (s : Setting) : List (String × String) := s.pairs.filter (!carried ·)

/-- The tokens before the block: the control, and a style's element as one word. -/
public def openingRaws (s : Setting) (pos : Pos) : Array Raw :=
  match s with
  | .style el _ => #[.ctrl s.head pos, .group #[.word el pos] pos]
  | _ => #[.ctrl s.head pos]

/-- The setting's kept entries as the elaborator reads them: its opening and one word holding its
block, never lexed as TeX. -/
public def raws (s : Setting) (pos : Pos) : Array Raw :=
  let body := s.kept.body
  s.openingRaws pos ++ #[.group (if body.isEmpty then #[] else #[.word body pos]) pos]

end Setting

end LeanTex.Core.Native
