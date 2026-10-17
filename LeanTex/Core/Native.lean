module

public import LeanTex.Core.NativeKey
public import LeanTex.Core.Parse
import LeanTex.Core.Decl

/-! The native settings the surfaces lower into, each carried to the elaborator as one word its entry
reader reads back exactly (`Native.render_parse_exact`). -/

namespace LeanTex.Core.Native

open LeanTex.Core.Parse

/-- A native setting a surface lowers into: `\page` entries by key, or `\tokens` entries by the
length each names, every value spelled as the declaration grammar reads it. -/
public inductive Setting where
  | page (entries : Array (PageKey × String))
  | tokens (entries : Array (String × String))
  deriving DecidableEq, Repr, Inhabited

namespace Setting

/-- The control a setting's declaration opens with. -/
public def head : Setting → String
  | .page _ => "page"
  | .tokens _ => "tokens"

/-- Each entry's key and value as written. -/
public def pairs : Setting → List (String × String)
  | .page es => es.toList.map fun (k, v) => (k.name, v)
  | .tokens es => es.toList

/-- The declaration's block, its entries joined as an author writes them. -/
public def body (s : Setting) : String := ", ".intercalate (s.pairs.map fun (k, v) => k ++ " = " ++ v)

/-- The declaration as a translation note names it. -/
public def render (s : Setting) : String := "\\" ++ s.head ++ "{ " ++ s.body ++ " }"

/-- Whether an entry's key and value read back from the block, beside any other entries. -/
public def carried (kv : String × String) : Bool := Decl.plainKey kv.1 && Decl.wholeValue kv.2

/-- The setting without the entries its block cannot carry whole. -/
public def kept : Setting → Setting
  | .page es => .page (es.filter fun (k, v) => carried (k.name, v))
  | .tokens es => .tokens (es.filter carried)

/-- The declaration a translation note names, where the setting keeps an entry. -/
public def note? (s : Setting) : Option String := if s.kept.pairs.isEmpty then none else some s.kept.render

/-- The entries `kept` drops, as written. -/
public def dropped (s : Setting) : List (String × String) := s.pairs.filter (!carried ·)

/-- The setting's kept entries as the elaborator reads them: its control and one word holding its
block, never lexed as TeX. -/
public def raws (s : Setting) (pos : Pos) : Array Raw :=
  #[.ctrl s.head pos, .group #[.word s.kept.body pos] pos]

end Setting

end LeanTex.Core.Native
