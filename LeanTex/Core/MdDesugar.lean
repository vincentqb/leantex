module

public import LeanTex.Core.MdParse
public import LeanTex.Core.Parse
public import LeanTex.Core.Ir
import LeanTex.Core.Decl
import LeanTex.Core.Loop

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
  diminished: `md:list-start`, `md:loose-list`,
  `md:link-title`, `md:image-title`, `md:code-info`, `md:image-alt`,
  `md:disclosure`. Shipping content cannot take an absent-content loss.

All six heading ranks cross the native heading bridge as fixed names and
grouped inline raws. Their shared IR rank reaches both artifacts unchanged;
a body h1 remains distinct from document-title furniture.

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
private def route (file : String) (subject : String) (what : String) (pos : Pos) : Diag :=
  Diag.of .W0307 what (some ⟨file, pos⟩) (subject := some ("md:" ++ subject))

/-- A `W0392`: the construct sets, with part of its declaration dropped —
`degraded`, floor `content`, which is what the census must see for a link
that sets without its title or a disclosure whose body stays expanded. -/
private def routeDegraded (file : String) (subject : String) (what : String) (pos : Pos)
    (help : Option String := none) : Diag :=
  Diag.of .W0392 what (some ⟨file, pos⟩) help (subject := some ("md:" ++ subject))

/-- The value the elaborator reads back from one `\includegraphics` option
source: `Decl.splitEntries`, then `Decl.splitEntry`, then the one layer of
braces or quotes `readImageOpts` strips, then its trim. `none` when the
source does not read as exactly one `alt` entry. -/
public def altReadBack (src : String) : Option String :=
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
public def altSource (t : String) : Option String :=
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
public def textRaws (s : String) (pos : Pos) : Array Raw := Id.run do
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

private def TextOnly (rs : Array Raw) : Prop :=
  ∀ r ∈ rs, r = .space ∨ ∃ s p, r = .word s p

private theorem textOnly_word (rs : Array Raw) (s : String) (p : Pos)
    (h : TextOnly rs) : TextOnly (rs.push (.word s p)) := by
  intro r hr
  rcases Array.mem_push.mp hr with hr | hr
  · exact h r hr
  · exact Or.inr ⟨s, p, hr⟩

private theorem textOnly_space (rs : Array Raw) (h : TextOnly rs) :
    TextOnly (rs.push .space) := by
  intro r hr
  rcases Array.mem_push.mp hr with hr | hr
  · exact h r hr
  · exact Or.inl hr

/-- Author text cannot introduce a surface control, group or option. This
is a safety invariant over the actual lowering loop, before IR exists;
it does not claim a character census or how much input was consumed. -/
public theorem textRaws_covers (s : String) (pos : Pos) :
    ∀ r ∈ textRaws s pos, r = .space ∨ ∃ t p, r = .word t p := by
  change TextOnly (textRaws s pos)
  unfold textRaws
  refine Loop.bind_of_inv (fun (st : Array Raw × String × Nat × Nat) => TextOnly st.1)
    (Q := TextOnly) _ _
    (Loop.forIn_inv (fun (st : Array Raw × String × Nat × Nat) => TextOnly st.1)
      _ _ _ ?_ ?_) ?_
  · simp [TextOnly]
  · intro ch _ st hs
    dsimp only
    split
    · split
      · exact textOnly_space _ hs
      · exact textOnly_space _ (textOnly_word _ _ _ hs)
    · split <;> exact hs
  · intro st hs
    dsimp only
    split
    · exact hs
    · exact textOnly_word _ _ _ hs

/-- An empty HTML target can use the native target only if its key reaches
the page unchanged. An HTML fragment link names the original key, whereas
native labels sanitise it; accepting a changed key would break that link. -/
public def anchorRaws? (key : String) (p : Pos) : Option (Array Raw) :=
  if Ir.labelAnchor key == key then
    some #[.ctrl "hypertarget" p, .group #[.word key p] p, .group #[] p]
  else none

/-- A supported target's fragment remains the original key. -/
public theorem anchorRaws_fixed_point (key : String) (p : Pos) (rs : Array Raw)
    (h : anchorRaws? key p = some rs) : Ir.labelAnchor key = key := by
  unfold anchorRaws? at h
  split at h
  · simpa using ‹(Ir.labelAnchor key == key) = true›
  · contradiction

/-- Disclosure framing, over the surface AST before IR exists. Its only
new control is fixed; all summary raws stay inside one bold group, and the
entire body follows it in order. -/
public def disclosureRaws (summary body : Array Raw) (p : Pos) : Array Raw :=
  #[.ctrl "textbf" p, .group summary p, .par p] ++ body

/-- Framing cannot discard or reorder any body raw, or extract author text
from the summary's group. These are facts of lowering, not backend layout. -/
public theorem disclosureRaws_contract (summary body : Array Raw) (p : Pos) :
    (disclosureRaws summary body p).toList.drop 3 = body.toList ∧
    (disclosureRaws summary body p)[1]? = some (.group summary p) := by
  simp [disclosureRaws, Array.getElem?_append]

mutual

/-- One inline node's text. -/
private def inlText1 : Inl → String
  | .text s _ => s
  | .code s _ => s
  | .soft _ => " "
  | .hard _ => " "
  | .anchor _ _ => ""
  | .emph b _ => inlTextList "" b.toList
  | .strong b _ => inlTextList "" b.toList
  | .link _ _ b _ => inlTextList "" b.toList
  | .image _ _ a _ => inlTextList "" a.toList

private def inlTextList (acc : String) : List Inl → String
  | [] => acc
  | x :: rest => inlTextList (acc ++ inlText1 x) rest

end

/-- The flattened text of inline content: what an `alt` attribute carries,
which HTML states as text and markdown writes as inline content. -/
private def inlText (xs : Array Inl) : String := inlTextList "" xs.toList

mutual

/-- One inline node as surface raws. -/
private def inlRaws (file : String) : Inl → Array Raw × Array Diag
  | .text s p => (textRaws s p, #[])
  | .code s p => (#[.ctrl "texttt" p, .group (textRaws s p) p], #[])
  | .soft _ => (#[.space], #[])
  | .hard p => (#[.ctrl "\\" p], #[])
  | .anchor key p =>
    match anchorRaws? key p with
    | some rs => (rs, #[])
    | none =>
      (#[], #[Diag.of .E0390
        "this HTML target's key cannot be carried unchanged"
        (some ⟨file, p⟩) (some "use letters, digits, :, ., - or _ in the target key")
        (some "md:raw-html")])
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
private def inlListRaws (file : String) (out : Array Raw) (ds : Array Diag) :
    List Inl → Array Raw × Array Diag
  | [] => (out, ds)
  | x :: rest =>
    let (rs, ds') := inlRaws file x
    inlListRaws file (out ++ rs) (ds ++ ds') rest

end

mutual

/-- One block as surface raws. -/
private def blkRaws (file : String) : Blk → Array Raw × Array Diag
  | .para body p =>
    let (rs, ds) := inlListRaws file #[] #[] body.toList
    (rs.push (.par p), ds)
  | .heading level body p =>
    let (rs, ds) := inlListRaws file #[] #[] body.toList
    (Parse.headingRaws level rs p, ds)
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
  | .disclosure summary body p =>
    let (ss, sds) := inlListRaws file #[] #[] summary.toList
    let (rs, ds) := blkListRaws file #[] #[] body.toList
    (disclosureRaws ss rs p, (sds ++ ds).push (routeDegraded file "disclosure"
      "a disclosure sets its summary and body expanded: collapse behaviour is not carried" p))
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

private def blkListRaws (file : String) (out : Array Raw) (ds : Array Diag) :
    List Blk → Array Raw × Array Diag
  | [] => (out, ds)
  | b :: rest =>
    let (rs, ds') := blkRaws file b
    blkListRaws file (out ++ rs) (ds ++ ds') rest

/-- One `\item` per list item, its blocks inside. -/
private def itemsRaws (file : String) (out : Array Raw) (ds : Array Diag) :
    List (Array Blk) → Pos → Array Raw × Array Diag
  | [], _ => (out, ds)
  | it :: rest, p =>
    let (rs, ds') := blkListRaws file #[] #[] it.toList
    itemsRaws file ((out.push (.ctrl "item" p)) ++ rs) (ds ++ ds') rest p

end

/-- The whole document: markdown source to the surface AST the elaborator
reads, with the reader's own diagnostics carrying `.md` spans. -/
public def desugar (file : String) (input : String) : Array Raw × Array Diag :=
  let (bs, ds) := blocks file input
  let (rs, ds') := blkListRaws file #[] #[] bs.toList
  (rs, ds ++ ds')

/-- The frontend a `.md` path selects: the reader plus the desugaring, in
the shape `Lex.lex` and `Parse.parse` present for `.tex`. -/
public def read (file input : String) : Array Raw × Array Diag := desugar file input

end LeanTex.Core.Md
