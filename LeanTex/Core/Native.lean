module

public import LeanTex.Core.NativeKey
public import LeanTex.Core.Parse
import LeanTex.Core.Decl

/-! The native declarations the surfaces lower into: settings, each carried to the elaborator as one
word its entry reader reads back exactly (`Native.render_parse_exact`), TeX-valued styles with each
value one group, and heads, each operand one word. -/

namespace LeanTex.Core.Native

open LeanTex.Core.Parse

/-- A native setting a surface lowers into, by its entries: `\page` by key, `\tokens` by the length
each names, `\palette` by role, one element's `\style`, `\fonts` by slot, `\pdfmeta` by key, `\chrome`,
or a `\block`'s options, every value spelled as the declaration grammar reads it. -/
public inductive Setting where
  | page (entries : Array (PageKey × String))
  | tokens (entries : Array (String × String))
  | palette (entries : Array (String × String))
  | style (element : String) (entries : Array (String × String))
  | fonts (entries : Array (String × String))
  | pdfmeta (entries : Array (MetaKey × String))
  | chrome (entries : Array (String × String))
  | block (entries : Array (String × String))
  deriving DecidableEq, Repr, Inhabited

namespace Setting

/-- The control a setting's declaration opens with. -/
public def head : Setting → String
  | .page _ => "page"
  | .tokens _ => "tokens"
  | .palette _ => "palette"
  | .style _ _ => "style"
  | .fonts _ => "fonts"
  | .pdfmeta _ => "pdfmeta"
  | .chrome _ => "chrome"
  | .block _ => "block"

/-- Each entry's key and value as written. -/
public def pairs : Setting → List (String × String)
  | .page es => es.toList.map fun (k, v) => (k.name, v)
  | .pdfmeta es => es.toList.map fun (k, v) => (k.name, v)
  | .tokens es | .palette es | .style _ es | .fonts es | .chrome es | .block es => es.toList

/-- An entry as an author writes it, an empty value with nothing after its `=`. -/
public def entryText (kv : String × String) : String :=
  if kv.2.isEmpty then kv.1 ++ " =" else kv.1 ++ " = " ++ kv.2

/-- The declaration's block, its entries joined as an author writes them. -/
public def body (s : Setting) : String := ", ".intercalate (s.pairs.map entryText)

/-- What the declaration spells before its block: its control, and a style's element. -/
public def opening (s : Setting) : String :=
  match s with
  | .style el _ => "\\style{" ++ el ++ "}"
  | .page _ | .tokens _ | .palette _ | .fonts _ | .pdfmeta _ | .chrome _ | .block _ =>
    "\\" ++ s.head

/-- The declaration around a block `b`, as an author writes it. -/
public def spell (s : Setting) (b : String) : String :=
  match s with
  | .style el _ => "\\style{" ++ el ++ "}{ " ++ b ++ " }"
  | .block _ => "\\block[" ++ b ++ "]{}"
  | .page _ | .tokens _ | .palette _ | .fonts _ | .pdfmeta _ | .chrome _ =>
    "\\" ++ s.head ++ "{ " ++ b ++ " }"

/-- The declaration as a translation note names it. -/
public def render (s : Setting) : String := s.spell s.body

/-- Whether an entry's key and value read back from the block, beside any other entries. -/
public def carried (kv : String × String) : Bool :=
  Decl.plainKey kv.1 && (kv.2.isEmpty || Decl.wholeValue kv.2)

/-- The setting without the entries its block cannot carry whole. -/
public def kept : Setting → Setting
  | .page es => .page (es.filter fun (k, v) => carried (k.name, v))
  | .pdfmeta es => .pdfmeta (es.filter fun (k, v) => carried (k.name, v))
  | .tokens es => .tokens (es.filter carried)
  | .palette es => .palette (es.filter carried)
  | .style el es => .style el (es.filter carried)
  | .fonts es => .fonts (es.filter carried)
  | .chrome es => .chrome (es.filter carried)
  | .block es => .block (es.filter carried)

/-- The declaration a translation note names, where the setting keeps an entry. -/
public def note? (s : Setting) : Option String := if s.kept.pairs.isEmpty then none else some s.kept.render

/-- The entries `kept` drops, as written. -/
public def dropped (s : Setting) : List (String × String) := s.pairs.filter (!carried ·)

/-- The declaration's tokens around its block's raws `b`. -/
public def frame (s : Setting) (b : Array Raw) (pos : Pos) : Array Raw :=
  match s with
  | .style el _ => #[.ctrl "style" pos, .group #[.word el pos] pos, .group b pos]
  | .block _ => #[.ctrl "block" pos, .sym '[' pos] ++ b ++ #[.sym ']' pos, .group #[] pos]
  | .page _ | .tokens _ | .palette _ | .fonts _ | .pdfmeta _ | .chrome _ =>
    #[.ctrl s.head pos, .group b pos]

/-- The setting's kept entries as the elaborator reads them: one word holding its block, never
lexed as TeX, in its declaration's tokens. -/
public def raws (s : Setting) (pos : Pos) : Array Raw :=
  let body := s.kept.body
  s.frame (if body.isEmpty then #[] else #[.word body pos]) pos

end Setting

/-- A value a TeX-valued style carries: text the declaration grammar reads, which its translation
keeps whole (`Setting.carried`), or TeX its reader sets as inline content. -/
public inductive StyleValue where
  | text (v : String)
  | tex (raws : Array Raw)

/-- The value as its declaration spells it, TeX braced. -/
public def StyleValue.spell : StyleValue → String
  | .text v => v
  | .tex rs => rawSrcOne (.group rs {})

/-- A style holding TeX, `\style{element}{ key = value, ... }`: a text value one word, a TeX value
one group. -/
public def texStyle (element : String) (entries : Array (String × StyleValue)) (pos : Pos) :
    Array Raw :=
  let body := entries.foldl (init := #[]) fun out (k, v) =>
    let value : Array Raw := match v with
      | .text w => if w.isEmpty then #[] else #[.space, .word w pos]
      | .tex rs => #[.space, .group rs pos]
    (if out.isEmpty then out else out ++ #[.word "," pos, .space]) ++
      #[.word k pos, .space, .word "=" pos] ++ value
  #[.ctrl "style" pos, .group #[.word element pos] pos, .group body pos]

/-- That style as a translation note names it. -/
public def texStyleRender (element : String) (entries : Array (String × StyleValue)) : String :=
  "\\style{" ++ element ++ "}{ " ++
    ", ".intercalate (entries.toList.map fun (k, v) => Setting.entryText (k, v.spell)) ++ " }"

/-- A native command a surface lowers into, its operands words the elaborator reads as text: a
class, a theme, a theorem style, a command's or environment's head, a colour, the frame footer, a
reference list, a caption setup, or a running line from a page on. -/
public inductive Head where
  | documentclass (options : Array String) (cls : String)
  | theme (name : String)
  | theoremStyle (name : String)
  | define (cmd spec : String)
  | defineEnv (env spec : String)
  | textcolor (name : String)
  | framefoot
  | bibliography (style : Option String) (sources : Array String)
  | captionsetup (scope : Option String) (options : String)
  | runningFrom (foot : Bool) (fromPage : Nat)
  deriving DecidableEq, Repr, Inhabited

namespace Head

/-- The command as an author writes it. -/
public def render : Head → String
  | .documentclass os c =>
    "\\documentclass" ++ (if os.isEmpty then "" else "[" ++ ",".intercalate os.toList ++ "]") ++
      "{" ++ c ++ "}"
  | .theme n => "\\theme{" ++ n ++ "}"
  | .theoremStyle n => "\\theoremstyle{" ++ n ++ "}"
  | .define c sp => "\\define \\" ++ c ++ "(" ++ sp ++ ")"
  | .defineEnv e sp => "\\defineenv{" ++ e ++ "}(" ++ sp ++ ")"
  | .textcolor n => "\\textcolor{" ++ n ++ "}"
  | .framefoot => "\\framefoot"
  | .bibliography st ss =>
    (st.map ("\\bibliographystyle{" ++ · ++ "}")).getD "" ++
      "\\bibliography{" ++ ",".intercalate ss.toList ++ "}"
  | .captionsetup sc os => "\\captionsetup" ++ (sc.map ("[" ++ · ++ "]")).getD "" ++ "{" ++ os ++ "}"
  | .runningFrom foot n => (if foot then "\\runningfoot" else "\\runninghead") ++ s!"[from = {n}]" ++ "{}"

/-- The command's tokens, each operand one word. -/
public def raws (h : Head) (pos : Pos) : Array Raw :=
  let word (s : String) : Array Raw := if s.isEmpty then #[] else #[.word s pos]
  let bracket (s : String) : Array Raw := #[.sym '[' pos] ++ word s ++ #[.sym ']' pos]
  match h with
  | .documentclass os c =>
    #[.ctrl "documentclass" pos] ++ (if os.isEmpty then #[] else bracket (",".intercalate os.toList)) ++
      #[.group (word c) pos]
  | .theme n => #[.ctrl "theme" pos, .group (word n) pos]
  | .theoremStyle n => #[.ctrl "theoremstyle" pos, .group (word n) pos]
  | .define c sp => #[.ctrl "define" pos, .ctrl c pos, .word ("(" ++ sp ++ ")") pos]
  | .defineEnv e sp => #[.ctrl "defineenv" pos, .group (word e) pos, .word ("(" ++ sp ++ ")") pos]
  | .textcolor n => #[.ctrl "textcolor" pos, .group (word n) pos]
  | .framefoot => #[.ctrl "framefoot" pos]
  | .bibliography st ss =>
    (st.map fun s => #[.ctrl "bibliographystyle" pos, .group (word s) pos]).getD #[] ++
      #[.ctrl "bibliography" pos, .group (word (",".intercalate ss.toList)) pos]
  | .captionsetup sc os =>
    #[.ctrl "captionsetup" pos] ++ (sc.map bracket).getD #[] ++ #[.group (word os) pos]
  | .runningFrom foot n =>
    #[.ctrl (if foot then "runningfoot" else "runninghead") pos] ++ bracket s!"from = {n}" ++
      #[.group #[] pos]

end Head

end LeanTex.Core.Native
