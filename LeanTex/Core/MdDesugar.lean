import LeanTex.Core.MdParse
import LeanTex.Core.Parse

/-! # Markdown's meaning: the desugaring into the surface AST

Markdown has no semantics of its own here. Its meaning *is* this function:
md AST → the tex-shaped surface AST the one elaborator reads. AST to AST,
never through generated tex text — generating text would put two parsers in
the pipeline and destroy the `.md` provenance every diagnostic downstream
carries.

The asymmetry is one-directional by design: md ⊂ tex-expressible. Where the
surface AST cannot express a markdown construct, the construct is *routed* —
named by a `W0307` carrying its own subject — rather than the elaborator
being extended to meet markdown. Four constructs are routed today
(`md:thematic-break`, `md:heading-depth`, `md:list-start`, `md:loose-list`),
each because the IR has no field for it; the routing is the record of what
the kernel owes, not a silence. -/

namespace LeanTex.Core.Md

open LeanTex.Core LeanTex.Core.Parse

/-- A `W0307`: a markdown construct the surface AST cannot yet express. The
subject is the construct, so repeats fold into one line with a site count
(`Diag.tallySites`) and the census can name what was lost. -/
def route (file : String) (subject : String) (what : String) (pos : Pos) : Diag :=
  { kind := .W0307, message := what, span := some ⟨file, pos⟩,
    subject := some ("md:" ++ subject) }

/-- Literal text as surface words and spaces: one `word` per run of
non-space characters. Going through `word` rather than through generated
source is also what lets markdown text carry `$`, `%` and `#` with no
escape — they never become control tokens. -/
def textRaws (s : String) (pos : Pos) : Array Raw := Id.run do
  let mut out : Array Raw := #[]
  let mut cur := ""
  let mut col := pos.col
  let mut wordCol := pos.col
  for ch in s.toList do
    if ch == ' ' || ch == '\t' then
      unless cur.isEmpty do
        out := out.push (.word cur ⟨pos.line, wordCol⟩)
        cur := ""
      out := out.push .space
      col := col + 1
      wordCol := col
    else
      if cur.isEmpty then wordCol := col
      cur := cur.push ch
      col := col + 1
  unless cur.isEmpty do out := out.push (.word cur ⟨pos.line, wordCol⟩)
  return out

/-- The control name a heading level takes. Levels beyond the third are
routed: the kernel has three sectioning levels, so a fourth is a level
question, not a markdown one. -/
def sectionCtrl : Nat → String
  | 0 | 1 => "section"
  | 2 => "subsection"
  | _ => "subsubsection"

mutual

/-- One inline node as surface raws. -/
def inlRaws (file : String) : Inl → Array Raw × Array Diag
  | .text s p => (textRaws s p, #[])
  | .code s p => (#[.ctrl "texttt" p, .group (textRaws s p) p], #[])
  | .soft _ => (#[.space], #[])
  | .hard p => (#[.ctrl "\\" p], #[])
  | .emph body p =>
    let (rs, ds) := inlListRaws file #[] #[] body.toList
    (#[.ctrl "emph" p, .group rs p], ds)
  | .strong body p =>
    let (rs, ds) := inlListRaws file #[] #[] body.toList
    (#[.ctrl "textbf" p, .group rs p], ds)
  | .link dest _ body p =>
    let (rs, ds) := inlListRaws file #[] #[] body.toList
    (#[.ctrl "href" p, .group (textRaws dest p) p, .group rs p], ds)
  | .image dest _ alt p =>
    let (_, ds) := inlListRaws file #[] #[] alt.toList
    (#[.ctrl "includegraphics" p, .group (textRaws dest p) p], ds)

/-- A list of inline nodes, accumulating: prepending to the recursive result
would copy it at every element. -/
def inlListRaws (file : String) (out : Array Raw) (ds : Array Diag) :
    List Inl → Array Raw × Array Diag
  | [] => (out, ds)
  | x :: rest =>
    let (rs, ds') := inlRaws file x
    inlListRaws file (out ++ rs) (ds ++ ds') rest

end

mutual

/-- One block as surface raws. -/
def blkRaws (file : String) : Blk → Array Raw × Array Diag
  | .para body p =>
    let (rs, ds) := inlListRaws file #[] #[] body.toList
    (rs.push (.par p), ds)
  | .heading level body p =>
    let (rs, ds) := inlListRaws file #[] #[] body.toList
    let ds := if level > 3 then
        ds.push (route file "heading-depth"
          "a markdown heading below the third level sets at the third" p)
      else ds
    (#[.ctrl (sectionCtrl level) p, .word "*" p, .group rs p], ds)
  | .code info text p =>
    let ds := if info.isEmpty then #[] else
      #[route file "code-info"
          "a fenced block's info string is not carried to the code block" p]
    (#[.verb "verbatim" text p], ds)
  | .rule p =>
    (#[], #[route file "thematic-break"
      "a thematic break has no block in this engine and is not drawn" p])
  | .quote body p =>
    let (rs, ds) := blkListRaws file #[] #[] body.toList
    (#[.env "quote" rs p], ds)
  | .list ordered start tight items p =>
    let (rs, ds) := itemsRaws file #[] #[] items.toList p
    let ds := if ordered && start != 1 then
        ds.push (route file "list-start"
          "an ordered list's start number is not carried and the list counts from one" p)
      else ds
    let ds := if tight then ds else
      ds.push (route file "loose-list"
        "a loose list sets as a tight one: its items' paragraph spacing is not carried" p)
    (#[.env (if ordered then "enumerate" else "itemize") rs p], ds)

def blkListRaws (file : String) (out : Array Raw) (ds : Array Diag) :
    List Blk → Array Raw × Array Diag
  | [] => (out, ds)
  | b :: rest =>
    let (rs, ds') := blkRaws file b
    blkListRaws file (out ++ rs) (ds ++ ds') rest

/-- One `\item` per list item, its blocks inside. -/
def itemsRaws (file : String) (out : Array Raw) (ds : Array Diag) :
    List (Array Blk) → Pos → Array Raw × Array Diag
  | [], _ => (out, ds)
  | it :: rest, p =>
    let (rs, ds') := blkListRaws file #[] #[] it.toList
    itemsRaws file ((out.push (.ctrl "item" p)) ++ rs) (ds ++ ds') rest p

end

/-- The whole document: markdown source to the surface AST the elaborator
reads, with the reader's own diagnostics carrying `.md` spans. -/
def desugar (file : String) (input : String) : Array Raw × Array Diag :=
  let (bs, ds) := blocks file input
  let (rs, ds') := blkListRaws file #[] #[] bs.toList
  (rs, ds ++ ds')

/-- The frontend a `.md` path selects: the reader plus the desugaring, in
the shape `Lex.lex` and `Parse.parse` present for `.tex`. -/
def read (file input : String) : Array Raw × Array Diag := desugar file input

end LeanTex.Core.Md
