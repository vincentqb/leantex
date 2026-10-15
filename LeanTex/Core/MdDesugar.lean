module

public import LeanTex.Core.MdParse
public import LeanTex.Core.Parse
public import LeanTex.Core.Ir
import LeanTex.Core.Decl
import LeanTex.Core.Loop
import LeanTex.Core.BibPunct
import LeanTex.Core.KeyVal

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
  | .cite items _ => " ".intercalate (items.toList.map fun it => "@" ++ it.key)

private def inlTextList (acc : String) : List Inl → String
  | [] => acc
  | x :: rest => inlTextList (acc ++ inlText1 x) rest

end

/-- The flattened text of inline content, as an `alt` attribute carries it. -/
private def inlText (xs : Array Inl) : String := inlTextList "" xs.toList

/-- One citation as natbib's commands take it: its key, its mode, and its notes as raws. -/
public structure CiteRaws where
  key : String
  mode : CiteMode
  pre : Array Raw
  post : Array Raw

/-- A raw run without its leading spaces. -/
public def dropSpaces (l : List Raw) : List Raw := l.dropWhile (· matches Raw.space)

/-- A suffix's opening separator, `,` or `:`, off its first word, with the spaces after it. -/
public def dropSeparator (l : List Raw) : List Raw :=
  match l with
  | Raw.word w p :: rest =>
    if w.startsWith "," || w.startsWith ":" then
      if (w.drop 1).isEmpty then dropSpaces rest else Raw.word (w.drop 1).toString p :: rest
    else l
  | _ => l

/-- A word without the braces that delimit a locator for a CSL processor, `none` when nothing is
left. -/
public def unbraceWord : Raw → Option Raw
  | Raw.word w p =>
    if (w.toList.filter fun c => c != '{' && c != '}').isEmpty then none
    else some (Raw.word (String.ofList (w.toList.filter fun c => c != '{' && c != '}')) p)
  | r => some r

/-- A suffix as natbib's postnote, as Pandoc's LaTeX writer sets it: its separating `,` or `:` and
the spaces after it off, and its locator braces dropped. -/
public def postNote (rs : Array Raw) : Array Raw :=
  ((dropSeparator (dropSpaces rs.toList)).filterMap unbraceWord).toArray

/-- natbib's optional arguments: none, `[post]`, or `[pre][post]`, each note one group. -/
private def citeOpts (pre post : Array Raw) (p : Pos) : Array Raw :=
  let note (r : Array Raw) : Array Raw := #[.sym '[' p, .group r p, .sym ']' p]
  let preArg := note pre
  let postArg := note post
  if pre.isEmpty && post.isEmpty then #[]
  else if pre.isEmpty then postArg
  else preArg ++ postArg

/-- One natbib citation command over its notes and keys. -/
public def citeCmdRaws (cmd : String) (pre post : Array Raw) (keys : Array String) (p : Pos) :
    Array Raw :=
  #[.ctrl cmd p] ++ citeOpts pre post p ++ #[.group #[.word (",".intercalate keys.toList) p] p]

/-- The command one citation of a `\citetext` takes. -/
private def textCmd : CiteMode → String
  | .authorInText => "citealt"
  | .suppressAuthor => "citeyear"
  | .normal => "citealp"

/-- `\citetext` around each citation's own command, joined by `; `. -/
private def citeTextRaws (items : List CiteRaws) (p : Pos) : Array Raw :=
  let body := items.foldl (init := #[]) fun acc c =>
    (if acc.isEmpty then acc else acc ++ #[.word ";" p, .space]) ++
      citeCmdRaws (textCmd c.mode) c.pre c.post #[c.key] p
  #[.ctrl "citetext" p, .group body p]

/-- A citation group as Pandoc's LaTeX writer sets it under natbib (`citationsToNatbib`): one
citation's own command, one `\citep` where only the first has a prefix and the last a suffix, the
author before the rest, or `\citetext` around each citation's command. -/
public def natbibRaws (items : List CiteRaws) (p : Pos) : Array Raw :=
  match items with
  | [] => #[]
  | [one] =>
    let cmd := match one.mode with
      | .authorInText => "citet"
      | .suppressAuthor => "citeyearpar"
      | .normal => "citep"
    citeCmdRaws cmd one.pre one.post #[one.key] p
  | first :: rest =>
    if (first :: rest).all (·.mode == .normal) && rest.all (·.pre.isEmpty) &&
        (first :: rest).dropLast.all (·.post.isEmpty) then
      citeCmdRaws "citep" first.pre ((rest.getLast?.map (·.post)).getD #[])
        ((first :: rest).map (·.key)).toArray p
    else if first.mode == .authorInText then
      citeCmdRaws "citeauthor" #[] #[] #[first.key] p ++ #[.space] ++
        citeTextRaws ({ first with mode := .suppressAuthor } :: rest) p
    else citeTextRaws (first :: rest) p

/-- Whether a key crosses natbib's comma-separated key list as itself. -/
public def keyCrosses (key : String) : Bool := KeyVal.items key == #[key]

/-- A citation group's raws: natbib's commands, or, where a key cannot cross natbib's key list,
its keys as text with the loss named. -/
private def citeGroupRaws (file : String) (items : Array CiteRaws) (p : Pos) :
    Array Raw × Array Diag :=
  match items.find? (!keyCrosses ·.key) with
  | none => (natbibRaws items.toList p, #[])
  | some bad =>
    (textRaws (" ".intercalate (items.toList.map fun c => "@" ++ c.key)) p,
     #[routeDegraded file "cite-key"
        s!"the citation key '{bad.key}' holds a comma or a brace no bibliography key can hold: \
the citation sets as its keys" p
        (help := some "spell the key as its .bib entry writes it")])

/-- An empty group, TeX's own end of a command's arguments, when `rs` opens on a word an
overlay-aware command before it would read as its `<…>` selector. -/
@[expose] public def selectorGuard (rs : Array Raw) (p : Pos) : Array Raw :=
  match rs[0]? with
  | some (Raw.word w _) => if w.startsWith "<" then #[.group #[] p] else #[]
  | _ => #[]

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
  | .cite items p =>
    let cs := citeItemsRaws file #[] #[] items.toList
    let g := citeGroupRaws file cs.1 p
    let plain (xs : Array Inl) : Bool := xs.all fun x => x matches .text .. | .soft _
    let styled := if items.all (fun it => plain it.pre && plain it.post) then #[] else
      #[routeDegraded file "cite-note"
        "a citation's prefix or suffix sets as plain text: its emphasis, code or links are dropped" p]
    (g.1, cs.2 ++ g.2 ++ styled)

/-- Each citation of a group with its notes as raws, accumulating. -/
private def citeItemsRaws (file : String) (out : Array CiteRaws) (ds : Array Diag) :
    List CiteItem → Array CiteRaws × Array Diag
  | [] => (out, ds)
  | .mk key mode pre post :: rest =>
    let a := inlListRaws file #[] #[] pre.toList
    let b := inlListRaws file #[] #[] post.toList
    citeItemsRaws file (out.push { key, mode, pre := a.1, post := postNote b.1 }) (ds ++ a.2 ++ b.2)
      rest

/-- A list of inline nodes, accumulating. -/
private def inlListRaws (file : String) (out : Array Raw) (ds : Array Diag) :
    List Inl → Array Raw × Array Diag
  | [] => (out, ds)
  | x :: rest =>
    let (rs, ds') := inlRaws file x
    let guard := match out.back? with
      | some (.group _ p) => selectorGuard rs p
      | _ => #[]
    inlListRaws file (out ++ guard ++ rs) (ds ++ ds') rest

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
  | nil => intro out _ h; exact h
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
  | nil => intro out _ h; exact h
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

private def blkRaws (file : String) (refs : Array Raw) : Blk → Array Raw × Array Diag
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
    let (rs, ds) := blkListRaws file refs #[] #[] body.toList
    (#[.env "quote" rs p], ds)
  | .disclosure summary expanded body p =>
    let (ss, sds) := inlListRaws file #[] #[] summary.toList
    let (rs, ds) := blkListRaws file refs #[] #[] body.toList
    (disclosureRaws ss rs expanded p, sds ++ ds)
  | .list ordered start tight items p =>
    let (rs, ds) := itemsRaws file refs #[] #[] items.toList p
    let ds := if ordered && start != 1 then
        ds.push (routeDegraded file "list-start"
          "an ordered list's start number is not carried and the list counts from one" p)
      else ds
    let ds := if tight then ds else
      ds.push (routeDegraded file "loose-list"
        "a loose list sets as a tight one: its items' paragraph spacing is not carried" p)
    (#[.env (if ordered then "enumerate" else "itemize") rs p], ds)
  | .table aligns header rows p => tableRaws file aligns header rows p
  | .lean attrs p =>
    let file := ((attrs.find? (·.1 == "file")).map (·.2)).getD ""
    let opts := (attrs.filter (·.1 != "file")).toList.map fun (k, v) => s!"{k} = \{{v}}"
    let bracket : Array Raw := if opts.isEmpty then #[] else
      #[.sym '[' p, .word (", ".intercalate opts) p, .sym ']' p]
    (#[.par p, .ctrl "inputlean" p] ++ bracket ++ #[.group #[.word file p] p], #[])
  -- The metadata block is read whole by `desugar`, before the blocks.
  | .metadata _ _ => (#[], #[])
  | .refs p =>
    (refs, if refs.isEmpty then
      #[route file "refs" "a '::: {#refs}' division places the reference list, and no list is \
declared for this file: nothing sets there" p] else #[])

private def blkListRaws (file : String) (refs : Array Raw) (out : Array Raw) (ds : Array Diag) :
    List Blk → Array Raw × Array Diag
  | [] => (out, ds)
  | b :: rest =>
    let (rs, ds') := blkRaws file refs b
    blkListRaws file refs (out ++ rs) (ds ++ ds') rest

/-- One `\item` per list item, its blocks inside. -/
private def itemsRaws (file : String) (refs : Array Raw) (out : Array Raw) (ds : Array Diag) :
    List (Array Blk) → Pos → Array Raw × Array Diag
  | [], _ => (out, ds)
  | it :: rest, p =>
    let (rs, ds') := blkListRaws file refs #[] #[] it.toList
    itemsRaws file refs ((out.push (.ctrl "item" p)) ++ selectorGuard rs p ++ rs) (ds ++ ds') rest p

end

mutual

/-- Whether a block holds a reference-list division anywhere. -/
private def holdsRefsOne : Blk → Bool
  | .refs _ => true
  | .quote body _ => holdsRefs body.toList
  | .disclosure _ _ body _ => holdsRefs body.toList
  | .list _ _ _ items _ => holdsRefsItems items.toList
  | .para .. | .heading .. | .code .. | .rule _ | .table .. | .lean .. | .metadata .. => false

private def holdsRefs : List Blk → Bool
  | [] => false
  | b :: rest => holdsRefsOne b || holdsRefs rest

private def holdsRefsItems : List (Array Blk) → Bool
  | [] => false
  | it :: rest => holdsRefs it.toList || holdsRefsItems rest

end

/-- Which markdown a reader reads: a document a run builds, or a file another document includes. -/
public inductive Role where
  | document
  | included
  deriving Repr, BEq, DecidableEq, Inhabited

/-- What a markdown file's metadata declares for its citations, and the keys it names unread. -/
public structure MetaRead where
  sources : Array String := #[]
  bibPos : Pos := { line := 1, col := 1 }
  style : Option String := none
  decls : Array String := #[]
  nocite : Option (Array String × Pos) := none
  title : Option (String × Pos) := none
  diags : Array Diag := #[]

/-- A metadata value's text, a sequence's items joined by `, `. -/
private def MetaValue.text : MetaValue → Option String
  | .scalar s => some s
  | .list items => some (", ".intercalate items.toList)
  | .unread => none

/-- A metadata value read as YAML's booleans, `none` for anything else. -/
private def MetaValue.bool? : MetaValue → Option Bool
  | .scalar s =>
    if ["true", "True", "TRUE", "yes", "Yes", "on"].contains s then some true
    else if ["false", "False", "FALSE", "no", "No", "off"].contains s then some false
    else none
  | _ => none

/-- The keys metadata reads, each with the role it is read in. -/
public def metaKeys : List (String × Role) :=
  [("bibliography", .document), ("biblio-style", .document), ("natbiboptions", .document),
   ("nocite", .document), ("nocite", .included), ("reference-section-title", .document),
   ("link-citations", .document), ("link-citations", .included)]

/-- What a metadata block's fields declare for citations, read as Pandoc reads them; every other
key is named, a key written twice taking its last value and a key ending in `_` ignored. -/
public def metaRead (file : String) (role : Role) (fields : Array MetaField) : MetaRead := Id.run do
  let fields := fields.filter fun f =>
    !f.key.endsWith "_" && (fields.findRev? (·.key == f.key)).any (·.pos == f.pos)
  let unread (f : MetaField) (why : String) (help : Option String := none) : Diag :=
    Diag.of .W0307 s!"the metadata key '{f.key}' is not read: {why}" (some ⟨file, f.pos⟩) help
      (subject := some ("md:meta:" ++ f.key))
  let mut out : MetaRead := {}
  for f in fields do
    let known := metaKeys.any fun (k, r) => k == f.key && r == role
    if !known then
      let csl := f.key == "csl" || f.key == "citation-style"
      let why := if role == .included && metaKeys.any (·.1 == f.key) then
          "an included file's citations take the including document's bibliography and style"
        else if csl then "no CSL processor reads it; citations set in a BibTeX style"
        else "its value does not reach the page"
      let help := if csl then
          some "declare 'biblio-style:' with plainnat, unsrtnat, abbrvnat, plain, unsrt, abbrv or alpha"
        else none
      out := { out with diags := out.diags.push (unread f why help) }
      continue
    match f.key, f.value with
    | "bibliography", v =>
      let paths := match v with
        | .scalar s => #[s]
        | .list items => items
        | .unread => #[]
      if v == .unread then
        let d := unread f "its value is not a path or a list of paths"
        out := { out with diags := out.diags.push d }
      out := { out with bibPos := f.pos }
      for path in paths do
        let path := path.trimAscii.toString
        if path.isEmpty then continue
        if !path.endsWith ".bib" || path.any (· == ',') then
          let d := Diag.of .W0307
            s!"the bibliography '{path}' is not read: the engine reads BibTeX .bib files named \
without a comma" (some ⟨file, f.pos⟩) (some "convert the entries to a .bib file beside the document")
            (subject := some ("md:meta:bibliography:" ++ path))
          out := { out with diags := out.diags.push d }
        else out := { out with sources := out.sources.push path }
    | "biblio-style", .scalar s => out := { out with style := some s.trimAscii.toString }
    | "natbiboptions", v =>
      let given := match v with
        | .scalar s => (KeyVal.items s).toList
        | .list items => items.toList.map fun (o : String) => o.trimAscii.toString
        | .unread => []
      for o in given do
        match Bib.natbibOptions.lookup o with
        | some ds => out := { out with decls := out.decls ++ ds.toArray }
        | none =>
          let d := Diag.of .W0307 s!"the natbib option '{o}' is not read: natbib reads no such option"
            (some ⟨file, f.pos⟩) (subject := some ("md:meta:natbiboptions:" ++ o))
          out := { out with diags := out.diags.push d }
    | "nocite", v =>
      match v.text with
      | some t =>
        let keys := citeKeys t
        if !keys.isEmpty then out := { out with nocite := some (keys, f.pos) }
      | none => out := { out with diags := out.diags.push (unread f "its value is not text") }
    | "reference-section-title", .scalar s =>
      out := { out with title := some (s.trimAscii.toString, f.pos) }
    | "link-citations", v =>
      if v.bool? == some false then
        let d := routeDegraded file "link-citations"
          "a citation links to its reference-list entry whatever 'link-citations' declares" f.pos
        out := { out with diags := out.diags.push d }
    | _, _ => out := { out with diags := out.diags.push (unread f "its value is not one the key takes") }
  return out

/-- natbib loaded with the declared options, where a bibliography is declared. -/
public def MetaRead.opening (m : MetaRead) : Array Raw :=
  if m.sources.isEmpty then #[] else
    #[.ctrl "@natbib" m.bibPos, .group (m.decls.map (.word · m.bibPos)) m.bibPos]

/-- The `nocite` keys as natbib's `\nocite`. -/
public def MetaRead.nociteRaws (m : MetaRead) : Array Raw :=
  match m.nocite with
  | some (keys, q) => citeCmdRaws "nocite" #[] #[] keys q
  | none => #[]

/-- The raws a file opens with, closed by a paragraph end. -/
public def MetaRead.prelude (m : MetaRead) : Array Raw :=
  if m.opening.isEmpty then #[] else m.opening.push (.par m.bibPos)

/-- The reference list's raws in its declared style, plainnat by Pandoc's default; empty where no
bibliography is declared. -/
public def MetaRead.list (m : MetaRead) : Array Raw :=
  if m.sources.isEmpty then #[] else
    #[.par m.bibPos, .ctrl Parse.markdownBibControl m.bibPos,
      .group #[.word (m.style.getD "plainnat") m.bibPos] m.bibPos,
      .group #[.word (",".intercalate m.sources.toList) m.bibPos] m.bibPos]

/-- The heading over a reference list set at the file's end: `reference-section-title`. -/
public def MetaRead.titleRaws (m : MetaRead) : Array Raw :=
  match m.title with
  | some tp => Parse.headingRaws .h1 (textRaws tp.1 tp.2) tp.2
  | none => #[]

/-- What a file ends with: the `nocite` keys, after every citation as Pandoc's LaTeX template sets
them, and the reference list with its title where no division placed it. -/
public def MetaRead.tail (m : MetaRead) (placed : Bool) : Array Raw :=
  let nocite := if m.nociteRaws.isEmpty then #[] else m.nociteRaws.push (.par m.bibPos)
  nocite ++ if placed || m.list.isEmpty then #[] else m.titleRaws ++ m.list

/-- A document's metadata fields, and the blocks after its metadata block. -/
public def splitMetadata (bs : Array Blk) : Array MetaField × Array Blk :=
  match bs[0]? with
  | some (Blk.metadata fs _) => (fs, bs.extract 1 bs.size)
  | _ => (#[], bs)

/-- The whole document: markdown source to the surface AST, with the reader's
own diagnostics carrying `.md` spans; its metadata opens it, and its reference list stands in
each `::: {#refs}` division, else at its end, as Pandoc places it. -/
public def desugar (file : String) (input : String) (dialect : Dialect := .document)
    (role : Role := .document) : Array Raw × Array Diag :=
  let read := blocksIn dialect file input
  let split := splitMetadata read.1
  let m := metaRead file role split.1
  let body := blkListRaws file m.list #[] #[] split.2.toList
  (m.prelude ++ body.1 ++ m.tail (holdsRefs split.2.toList), read.2 ++ m.diags ++ body.2)

/-- The frontend a `.md` path selects: the reader plus the desugaring. -/
public def read (file input : String) : Array Raw × Array Diag := desugar file input

/-- A markdown file another document includes: its citations join the including document's. -/
public def readIncluded (file input : String) : Array Raw × Array Diag :=
  desugar file input (role := .included)

end LeanTex.Core.Md
