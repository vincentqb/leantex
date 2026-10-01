import LeanTex.Core.MdParse
import LeanTex.Core.Parse
import LeanTex.Core.Decl
import LeanTex.Core.Ir

/-! # Markdown's meaning: the desugaring into the surface AST

Markdown has no semantics of its own here. Its meaning *is* this function:
md AST → the tex-shaped surface AST the one elaborator reads. AST to AST,
never through generated tex text — generating text would put two parsers in
the pipeline and destroy the `.md` provenance every diagnostic downstream
carries.

The asymmetry is one-directional by design: md ⊂ tex-expressible. Where the
surface AST cannot express a markdown construct, the construct is *routed* —
named by its own subject — rather than the elaborator being extended to meet
markdown. The code a route takes is decided by what reaches the page, which
is the registry's rule and not a habit:

* `W0307` (`pending`, floor `absent`) for a construct that ships nothing.
  One today: `md:thematic-break`, which has no block in this engine.
* `W0392` (`degraded`, floor `content`) for a construct that ships,
  diminished: `md:heading-depth`, `md:list-start`, `md:loose-list`,
  `md:link-title`, `md:image-title`, `md:code-info`, `md:image-alt`. Each of
  the first five once took `W0307`, and the census then read shipping
  constructs as absent content.

**No reader text reaches a re-parse.** Two surface constructs are read back
from option text by the elaborator — a listing's `[language=…]` head and an
image's `[alt=…]` run — and splicing reader text into either was an
injection path: an info string `a]b` shipped `b]` as code, and
`{r, echo=FALSE}` shipped `[language={r,]` as its first line. So what
crosses is never the author's text. A language crosses as an
`Ir.ListingLang`, the IR's own value, whose token grammar holds no character
the option head reads; a spelling outside it is routed (`md:code-info`). An
alternative crosses in the one spelling the elaborator's own option splitter
is checked to read back exactly (`altSource`); text no spelling can carry
has its straight double quotes set curly, and says so (`md:image-alt`). -/

namespace LeanTex.Core.Md

open LeanTex.Core LeanTex.Core.Parse

/-- A `W0307`: a markdown construct the surface AST cannot yet express *and*
whose content does not reach the page. `pending` means exactly that (its
floor is `absent`), so only a construct that ships nothing takes this code —
today the thematic break, which has no block in the engine at all.

A construct that *does* ship, diminished, takes `routeDegraded` instead. The
two were one code, and the census then read four shipping constructs as
absent content. -/
def route (file : String) (subject : String) (what : String) (pos : Pos) : Diag :=
  Diag.of .W0307 what (some ⟨file, pos⟩) (subject := some ("md:" ++ subject))

/-- A `W0392`: the construct sets, with part of its declaration dropped —
`degraded`, floor `content`, which is what the census must see for a heading
that sets one level up or a link that sets without its title. -/
def routeDegraded (file : String) (subject : String) (what : String) (pos : Pos)
    (help : Option String := none) : Diag :=
  Diag.of .W0392 what (some ⟨file, pos⟩) help (subject := some ("md:" ++ subject))

/-- The value the elaborator reads back from one `\includegraphics` option
source: `Decl.splitEntries`, then `Decl.splitEntry`, then the one layer of
braces or quotes `readImageOpts` strips, then its trim. `none` when the
source does not read as exactly one `alt` entry. -/
def altReadBack (src : String) : Option String :=
  match Decl.splitEntries src with
  | [e] =>
    match Decl.splitEntry e with
    | some ("alt", v) =>
      let v :=
        if v.startsWith "{" && v.endsWith "}" && v.length ≥ 2 then
          String.ofList (v.toList.drop 1).dropLast
        else if v.startsWith "\"" && v.endsWith "\"" && v.length ≥ 2 then
          String.ofList (v.toList.drop 1).dropLast
        else v
      some v.trimAscii.toString
    | _ => none
  | _ => none

/-- An option source for a text alternative that reads back as exactly that
text, checked with the reader's own splitter rather than argued: quoted,
where nothing but a `"` ends the value; else braced, where the splitter's
depth and string tracking must both come back balanced. `none` when neither
spelling reads back — the text is then not carried as written. -/
def altSource (t : String) : Option String :=
  let want := t.trimAscii.toString
  let quoted := "alt=\"" ++ t ++ "\""
  let braced := "alt={" ++ t ++ "}"
  if altReadBack quoted == some want then some quoted
  else if altReadBack braced == some want then some braced
  else none

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
        out := out.push (.word cur { pos with col := wordCol })
        cur := ""
      out := out.push .space
      col := col + 1
      wordCol := col
    else
      if cur.isEmpty then wordCol := col
      cur := cur.push ch
      col := col + 1
  unless cur.isEmpty do out := out.push (.word cur { pos with col := wordCol })
  return out

/-- The control name a heading level takes. Levels beyond the third are
routed: the kernel has three sectioning levels, so a fourth is a level
question, not a markdown one. -/
def sectionCtrl : Nat → String
  | 0 | 1 => "section"
  | 2 => "subsection"
  | _ => "subsubsection"

mutual

/-- One inline node's text. -/
def inlText1 : Inl → String
  | .text s _ => s
  | .code s _ => s
  | .soft _ => " "
  | .hard _ => " "
  | .emph b _ => inlTextList "" b.toList
  | .strong b _ => inlTextList "" b.toList
  | .link _ _ b _ => inlTextList "" b.toList
  | .image _ _ a _ => inlTextList "" a.toList

def inlTextList (acc : String) : List Inl → String
  | [] => acc
  | x :: rest => inlTextList (acc ++ inlText1 x) rest

end

/-- The flattened text of inline content: what an `alt` attribute carries,
which HTML states as text and markdown writes as inline content. -/
def inlText (xs : Array Inl) : String := inlTextList "" xs.toList

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
  | .link dest title body p =>
    let (rs, ds) := inlListRaws file #[] #[] body.toList
    let ds := if title.isEmpty then ds else
      ds.push (routeDegraded file "link-title"
        "a link's title is not carried: the link sets without it" p)
    (#[.ctrl "href" p, .group (textRaws dest p) p, .group rs p], ds)
  | .image dest title alt p =>
    -- The alternative rides `\includegraphics`'s own `alt` key in the one
    -- spelling the option splitter is checked to read back exactly
    -- (`altSource`). Text no spelling carries sets with its straight double
    -- quotes curly — still the alternative, and named.
    let text := String.ofList ((inlText alt).toList.map fun c => if c == '\t' then ' ' else c)
    let ds := if title.isEmpty then #[] else
      #[routeDegraded file "image-title"
        "an image's title is not carried: the image sets without it" p]
    if text.isEmpty then
      (#[.ctrl "includegraphics" p, .group (textRaws dest p) p], ds)
    else
      let (src, ds) := match altSource text with
        | some s => (s, ds)
        | none =>
          let curly := String.ofList (text.toList.map fun c => if c == '"' then '\u201d' else c)
          ((altSource curly).getD "alt=\"\"",
           ds.push (routeDegraded file "image-alt"
             "an image's text alternative sets with its straight double quotes as curly ones: \
the image option cannot carry them as written" p
             (help := some "write the alternative without straight double quotes")))
      let altRaws := textRaws src p
      (#[.ctrl "includegraphics" p, .sym '[' p] ++ altRaws
         ++ #[.sym ']' p, .group (textRaws dest p) p], ds)

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
        ds.push (routeDegraded file "heading-depth"
          "a markdown heading below the third level sets at the third" p)
      else ds
    (#[.ctrl (sectionCtrl level) p, .word "*" p, .group rs p], ds)
  | .code info text p =>
    -- The info string's first word is the language, which the IR carries
    -- (`Ir.ListingSpec.language`) and both artifacts project — the HTML
    -- `code` element's class and the markdown fence's info string. What
    -- crosses into `{lstlisting}`'s option head is an `Ir.ListingLang`, the
    -- IR's own value, never the author's word: its token grammar holds no
    -- `]`, `,`, `=` or brace, so the head reads it back unchanged. A word
    -- outside the grammar is routed, and the code sets as it is. The word is
    -- split on spaces and tabs, as §4.5's "first word" is.
    let word := ((info.split (fun c => c == ' ' || c == '\t')).find? (!·.isEmpty)).map
      (·.toString)
    match word with
    | none => (#[.verb "verbatim" text p], #[])
    | some w =>
      match Ir.listingLang? w with
      | some l => (#[.verb "lstlisting" ("[language=" ++ l.val ++ "]\n" ++ text) p], #[])
      | none =>
        (#[.verb "verbatim" text p],
         #[routeDegraded file "code-info"
            s!"the info word '{w}' is not a language a listing can carry: the code sets \
without a language" p
            (help := some "spell it as letters, digits, +, #, - or . (python, c++, c#)")])
  | .rule p =>
    (#[], #[route file "thematic-break"
      "a thematic break has no block in this engine and is not drawn" p])
  | .quote body p =>
    let (rs, ds) := blkListRaws file #[] #[] body.toList
    (#[.env "quote" rs p], ds)
  | .list ordered start tight items p =>
    let (rs, ds) := itemsRaws file #[] #[] items.toList p
    let ds := if ordered && start != 1 then
        ds.push (routeDegraded file "list-start"
          "an ordered list's start number is not carried and the list counts from one" p)
      else ds
    let ds := if tight then ds else
      ds.push (routeDegraded file "loose-list"
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
