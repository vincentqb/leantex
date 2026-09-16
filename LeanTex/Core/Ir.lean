import LeanTex.Core.Diag

namespace LeanTex.Core.Ir

open LeanTex.Core

inductive Style where
  | bold
  | italic
  | mono
  | smallcaps
  | emph
  | sans
  | normal
  | size (name : String)
  deriving Repr, BEq

def Style.label : Style → String
  | .bold => "bold"
  | .italic => "italic"
  | .mono => "mono"
  | .smallcaps => "smallcaps"
  | .emph => "emph"
  | .sans => "sans"
  | .normal => "normal"
  | .size n => s!"size:{n}"

inductive Inline where
  | text (s : String)
  | math (display : Bool) (src : String)
  | styled (style : Style) (body : Array Inline)
  | linebreak
  deriving Repr, BEq, Inhabited

inductive Block where
  | para (content : Array Inline)
  | section (level : Nat) (starred : Bool) (title : Array Inline)
  | list (ordered : Bool) (items : Array (Array Block))
  | center (body : Array Block)
  deriving Repr, BEq, Inhabited

structure Doc where
  docClass : String := "article"
  classOptions : String := ""
  body : Array Block := #[]
  deriving Repr, BEq, Inhabited

-- Display-only printers. Structural recursion through `List`, so no `partial`.

mutual

def dumpInlines (ind : String) (xs : Array Inline) : String :=
  dumpInlineList ind xs.toList

def dumpInlineList (ind : String) (xs : List Inline) : String :=
  match xs with
  | [] => ""
  | x :: rest => dumpInline ind x ++ dumpInlineList ind rest

def dumpInline (ind : String) (x : Inline) : String :=
  match x with
  | .text s => s!"{ind}text {s.quote}\n"
  | .math d src =>
    let kind := if d then "display" else "inline"
    s!"{ind}math {kind} {src.quote}\n"
  | .styled st body => s!"{ind}styled {st.label}\n" ++ dumpInlines (ind ++ "  ") body
  | .linebreak => s!"{ind}linebreak\n"

end

mutual

def dumpBlocks (ind : String) (xs : Array Block) : String :=
  dumpBlockList ind xs.toList

def dumpBlockList (ind : String) (xs : List Block) : String :=
  match xs with
  | [] => ""
  | b :: rest => dumpBlock ind b ++ dumpBlockList ind rest

def dumpItems (ind : String) (items : List (Array Block)) : String :=
  match items with
  | [] => ""
  | item :: rest =>
    s!"{ind}item\n" ++ dumpBlocks (ind ++ "  ") item ++ dumpItems ind rest

def dumpBlock (ind : String) (b : Block) : String :=
  match b with
  | .para content => s!"{ind}para\n" ++ dumpInlines (ind ++ "  ") content
  | .section level starred title =>
    let star := if starred then "*" else ""
    s!"{ind}section{star} {level}\n" ++ dumpInlines (ind ++ "  ") title
  | .list ordered items =>
    let kind := if ordered then "ordered" else "unordered"
    s!"{ind}list {kind}\n" ++ dumpItems (ind ++ "  ") items.toList
  | .center body => s!"{ind}center\n" ++ dumpBlocks (ind ++ "  ") body

end

def dumpDiag (d : Diag) : String :=
  let where' := match d.span with
    | some sp => s!"{sp.pos.line}:{sp.pos.col}"
    | none => "-"
  let help := match d.help with
    | some h => s!" | help: {h}"
    | none => ""
  s!"{d.severity.label}[{d.code}] {where'} {d.message}{help}\n"

def dump (doc : Doc) (diags : Array Diag) : String :=
  let opts := if doc.classOptions == "" then "" else s!" [{doc.classOptions}]"
  let head := s!"class {doc.docClass}{opts}\n"
  let body := dumpBlocks "" doc.body
  let ds :=
    if diags.isEmpty then
      "-- diagnostics\n(none)\n"
    else
      "-- diagnostics\n" ++ String.join (diags.toList.map dumpDiag)
  head ++ body ++ ds

end LeanTex.Core.Ir
