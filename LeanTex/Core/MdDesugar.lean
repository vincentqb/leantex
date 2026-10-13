module

public import LeanTex.Core.MdParse
public import LeanTex.Core.Parse
public import LeanTex.Core.Ir
import LeanTex.Core.Decl
import LeanTex.Core.Loop

/-! # Markdown's meaning

The desugaring of the md AST into the surface AST the one elaborator reads. -/

namespace LeanTex.Core.Md

open LeanTex.Core LeanTex.Core.Parse

/-- A `W0307`: a markdown construct the surface AST cannot express and whose
content does not reach the page. -/
private def route (file : String) (subject : String) (what : String) (pos : Pos) : Diag :=
  Diag.of .W0307 what (some ⟨file, pos⟩) (subject := some ("md:" ++ subject))

/-- A `W0392`: the construct sets, with part of its declaration dropped. -/
private def routeDegraded (file : String) (subject : String) (what : String) (pos : Pos)
    (help : Option String := none) (output : Option Diag.Output := none) : Diag :=
  Diag.of .W0392 what (some ⟨file, pos⟩) help (subject := some ("md:" ++ subject))
    (output := output)

/-- The value the elaborator reads back from one `\includegraphics` option
source; `none` when it reads none. -/
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
text; `none` where no spelling does. -/
public def altSource (t : String) : Option String :=
  let want := t.trimAscii.toString
  let quoted := "alt=\"" ++ t ++ "\""
  let braced := "alt={" ++ t ++ "}"
  if altReadBack quoted == some want then some quoted
  else if altReadBack braced == some want then some braced
  else none

/-- Literal text as surface words and spaces, one `word` per
run of non-space characters. -/
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

/-- The native target for an empty HTML target, only when
its key reaches the page unchanged. -/
public def anchorRaws? (key : String) (p : Pos) : Option (Array Raw) :=
  if Ir.labelAnchor key == key then
    some #[.ctrl "hypertarget" p, .group #[.word key p] p, .group #[] p]
  else none

public theorem anchorRaws_fixed_point (key : String) (p : Pos) (rs : Array Raw)
    (h : anchorRaws? key p = some rs) : Ir.labelAnchor key = key := by
  unfold anchorRaws? at h
  split at h
  · simpa using ‹(Ir.labelAnchor key == key) = true›
  · contradiction

/-- A disclosure as the markdown disclosure environment: its `[open]` option,
the summary in one group, then the body. -/
public def disclosureRaws (summary body : Array Raw) (expanded : Bool) (p : Pos) : Array Raw :=
  #[.env Parse.markdownDisclosureEnv
    ((if expanded then #[.sym '[' p, .word "open" p, .sym ']' p] else #[]) ++
      #[.group summary p] ++ body) p]

public theorem disclosureRaws_contract (summary body : Array Raw) (expanded : Bool) (p : Pos) :
    ∃ opts, disclosureRaws summary body expanded p =
        #[.env Parse.markdownDisclosureEnv (opts ++ #[.group summary p] ++ body) p] ∧
      (opts = #[] ∨ opts = #[.sym '[' p, .word "open" p, .sym ']' p]) := by
  refine ⟨if expanded then #[.sym '[' p, .word "open" p, .sym ']' p] else #[], rfl, ?_⟩
  cases expanded <;> simp

mutual

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

/-- The flattened text of inline content, as an `alt` attribute carries it. -/
private def inlText (xs : Array Inl) : String := inlTextList "" xs.toList

mutual

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
    -- The alternative rides `\includegraphics`'s own `alt` key in the spelling `altSource` checks.
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

/-- A list of inline nodes, accumulating. -/
private def inlListRaws (file : String) (out : Array Raw) (ds : Array Diag) :
    List Inl → Array Raw × Array Diag
  | [] => (out, ds)
  | x :: rest =>
    let (rs, ds') := inlRaws file x
    inlListRaws file (out ++ rs) (ds ++ ds') rest

end

/-- A table column's spec letter; GFM's undeclared alignment is `l`. -/
public def TableAlign.specLetter : TableAlign → Char
  | .none => 'l'
  | .left => 'l'
  | .right => 'r'
  | .center => 'c'

/-- The cells of a row after its first, each after its `&`, each one group. -/
private def laterCellsRaws (file : String) (p : Pos) (out : Array Raw) (ds : Array Diag) :
    List (Array Inl) → Array Raw × Array Diag
  | [] => (out, ds)
  | cell :: rest =>
    let (rs, cds) := inlListRaws file #[] #[] cell.toList
    laterCellsRaws file p ((out.push (.sym '&' p)).push (.group rs p)) (ds ++ cds) rest

/-- A row's cells as groups, `&` between each two. -/
private def rowCellsRaws (file : String) (p : Pos) : List (Array Inl) → Array Raw × Array Diag
  | [] => (#[], #[])
  | cell :: rest =>
    let (rs, cds) := inlListRaws file #[] #[] cell.toList
    laterCellsRaws file p #[.group rs p] cds rest

/-- One row: its cells, closed by `\\`. -/
private def rowRaws (file : String) (row : Array (Array Inl)) (p : Pos) :
    Array Raw × Array Diag :=
  let cells := rowCellsRaws file p row.toList
  (cells.1.push (.ctrl "\\" p), cells.2)

/-- The data rows, each after the one before, the accumulator threaded. -/
private def rowsRaws (file : String) (p : Pos) (out : Array Raw) (ds : Array Diag) :
    List (Array (Array Inl)) → Array Raw × Array Diag
  | [] => (out, ds)
  | row :: rest =>
    let (rs, rds) := rowRaws file row p
    rowsRaws file p (out ++ rs) (ds ++ rds) rest

/-- A table as the booktabs `{tabular}` the surface AST already has. -/
public def tableRaws (file : String) (aligns : Array TableAlign)
    (header : Array (Array Inl)) (rows : Array (Array (Array Inl))) (p : Pos) :
    Array Raw × Array Diag :=
  let spec := String.ofList (aligns.toList.map TableAlign.specLetter)
  let (hr, hds) := rowRaws file header p
  let head : Array Raw := #[.group #[.sym '@' p, .group #[] p, .word spec p,
    .sym '@' p, .group #[] p] p, .ctrl "toprule" p]
  let (body, ds) := rowsRaws file p ((head ++ hr).push (.ctrl "midrule" p)) hds rows.toList
  (#[.env Parse.markdownTableEnv (body.push (.ctrl "bottomrule" p)) p], ds)

/-- What a markdown table may put at a `{tabular}` body's top level: groups,
`&`, `\\`, and booktabs' three rules. -/
public def TableTop (p : Pos) (r : Raw) : Prop :=
  (∃ g, r = .group g p) ∨ r = .sym '&' p ∨ r = .ctrl "\\" p
    ∨ r = .ctrl "toprule" p ∨ r = .ctrl "midrule" p ∨ r = .ctrl "bottomrule" p

private theorem tableTop_push (p : Pos) (xs : Array Raw) (r : Raw)
    (h : ∀ x ∈ xs, TableTop p x) (hr : TableTop p r) : ∀ x ∈ xs.push r, TableTop p x := by
  intro x hx
  rcases Array.mem_push.mp hx with hx | rfl
  · exact h x hx
  · exact hr

private theorem laterCellsRaws_tableTop (file : String) (p : Pos) (cells : List (Array Inl)) :
    ∀ (out : Array Raw) (ds : Array Diag), (∀ x ∈ out, TableTop p x) →
      ∀ x ∈ (laterCellsRaws file p out ds cells).1, TableTop p x := by
  induction cells with
  | nil => intro out ds h; exact h
  | cons cell rest ih =>
    intro out ds h
    unfold laterCellsRaws
    rcases inlListRaws file #[] #[] cell.toList with ⟨rs, cds⟩
    exact ih _ _ (tableTop_push p _ _ (tableTop_push p _ _ h (Or.inr (Or.inl rfl)))
      (Or.inl ⟨rs, rfl⟩))

private theorem rowCellsRaws_tableTop (file : String) (p : Pos) (cells : List (Array Inl)) :
    ∀ x ∈ (rowCellsRaws file p cells).1, TableTop p x := by
  cases cells with
  | nil => simp [rowCellsRaws]
  | cons cell rest =>
    unfold rowCellsRaws
    exact laterCellsRaws_tableTop file p rest _ _ (by
      intro x hx
      simp at hx
      exact hx ▸ Or.inl ⟨_, rfl⟩)

private theorem rowRaws_tableTop (file : String) (row : Array (Array Inl)) (p : Pos) :
    ∀ x ∈ (rowRaws file row p).1, TableTop p x :=
  tableTop_push p _ _ (rowCellsRaws_tableTop file p row.toList) (Or.inr (Or.inr (Or.inl rfl)))

private theorem rowsRaws_tableTop (file : String) (p : Pos) (rows : List (Array (Array Inl))) :
    ∀ (out : Array Raw) (ds : Array Diag), (∀ x ∈ out, TableTop p x) →
      ∀ x ∈ (rowsRaws file p out ds rows).1, TableTop p x := by
  induction rows with
  | nil => intro out ds h; exact h
  | cons row rest ih =>
    intro out ds h
    unfold rowsRaws
    have hr := rowRaws_tableTop file row p
    rcases hrow : rowRaws file row p with ⟨rs, rds⟩
    rw [hrow] at hr
    refine ih _ _ ?_
    intro x hx
    rcases Array.mem_append.mp hx with hx | hx
    · exact h x hx
    · exact hr x hx

public theorem tableRaws_contract (file : String) (aligns : Array TableAlign)
    (header : Array (Array Inl)) (rows : Array (Array (Array Inl))) (p : Pos) :
    ∃ body, (tableRaws file aligns header rows p).1 = #[.env Parse.markdownTableEnv body p] ∧
      ∀ x ∈ body, TableTop p x := by
  unfold tableRaws
  have hh := rowRaws_tableTop file header p
  rcases hhr : rowRaws file header p with ⟨hr, hds⟩
  rw [hhr] at hh
  dsimp only
  refine ⟨_, rfl, ?_⟩
  refine tableTop_push p _ _ ?_ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  refine rowsRaws_tableTop file p _ _ _ ?_
  refine tableTop_push p _ _ ?_ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  intro x hx
  rcases Array.mem_append.mp hx with hx | hx
  · simp at hx
    rcases hx with rfl | rfl
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact hh x hx

mutual

private def blkRaws (file : String) : Blk → Array Raw × Array Diag
  | .para body p =>
    let (rs, ds) := inlListRaws file #[] #[] body.toList
    (rs.push (.par p), ds)
  | .heading level body p =>
    let (rs, ds) := inlListRaws file #[] #[] body.toList
    (Parse.headingRaws level rs p, ds)
  | .code info text p =>
    -- The info string's first word is the language, crossing as an `Ir.ListingLang`.
    let word := ((info.split (fun c => c == ' ' || c == '\t')).find? (!·.isEmpty)).map
      (·.toString)
    match word with
    | none => (#[.verb "verbatim" ("\n" ++ text) p], #[])
    | some w =>
      match Ir.listingLang? w with
      | some l => (#[.verb "lstlisting" ("[language=" ++ l.val ++ "]\n" ++ text) p], #[])
      | none =>
        (#[.verb "verbatim" ("\n" ++ text) p],
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
  | .disclosure summary expanded body p =>
    let (ss, sds) := inlListRaws file #[] #[] summary.toList
    let (rs, ds) := blkListRaws file #[] #[] body.toList
    (disclosureRaws ss rs expanded p, sds ++ ds)
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
  | .table aligns header rows p => tableRaws file aligns header rows p

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

/-- The whole document: markdown source to the surface AST, with the reader's
own diagnostics carrying `.md` spans. -/
public def desugar (file : String) (input : String) : Array Raw × Array Diag :=
  let (bs, ds) := blocks file input
  let (rs, ds') := blkListRaws file #[] #[] bs.toList
  (rs, ds ++ ds')

/-- The frontend a `.md` path selects: the reader plus the desugaring. -/
public def read (file input : String) : Array Raw × Array Diag := desugar file input

end LeanTex.Core.Md
