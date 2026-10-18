module

public import LeanTex.Core.MdParse
public import LeanTex.Core.Parse
import LeanTex.Core.Lex
public import LeanTex.Core.MathParse
public import LeanTex.Core.Ir
import LeanTex.Core.Decl
import LeanTex.Core.UnusedSetting
import LeanTex.Core.Loop
import LeanTex.Core.KeyVal
import LeanTex.Core.CiteKey
import LeanTex.Core.MdSmart
import Std.Data.HashMap

/-! # Markdown's meaning

The desugaring of the md AST into the surface AST the one elaborator reads. -/

namespace LeanTex.Core.Md

open LeanTex.Core LeanTex.Core.Parse

/-- The environment a Lean division lowers to, which the driver replaces by the file it includes;
unforgeable because its name holds a space. -/
public def leanDivisionEnv : String := "markdown lean"

/-- A Lean division's request: the file it names and its other attributes, as written. -/
public structure LeanDivision where
  file : String
  attrs : Array (String × String)
  deriving Repr, BEq, Inhabited

/-- The request a Lean division's attributes make: its first `file`, and the others in order. -/
@[expose] public def LeanDivision.ofAttrs (attrs : Array (String × String)) : LeanDivision :=
  { file := ((attrs.find? (·.1 == "file")).map (·.2)).getD ""
    attrs := attrs.filter (·.1 != "file") }

/-- A division's request as the one raw the driver reads: the file's word, then a group per
attribute holding its key's word and its value's. -/
@[expose] public def LeanDivision.raw (d : LeanDivision) (p : Pos) : Raw :=
  .env leanDivisionEnv #[.group #[.word d.file p] p,
    .group (d.attrs.map fun (k, v) => .group #[.word k p, .word v p] p) p] p

private def attrsOf? : List Raw → Option (List (String × String))
  | [] => some []
  | .group kv _ :: rest => match kv.toList with
    | [.word k _, .word v _] => (attrsOf? rest).map ((k, v) :: ·)
    | _ => none
  | _ :: _ => none

/-- The request a division's raw spells, read back as `LeanDivision.raw` writes it. -/
public def LeanDivision.ofRaw? : Raw → Option LeanDivision
  | .env n body _ =>
    if n != leanDivisionEnv then none else
      match body.toList with
      | [.group file _, .group attrs _] =>
        match file.toList with
        | [.word f _] => (attrsOf? attrs.toList).map fun as => ⟨f, as.toArray⟩
        | _ => none
      | _ => none
  | _ => none

mutual

/-- Whether a raw requests a Lean division, in a group or an environment too. -/
@[expose] public def requestsDivision : Raw → Bool
  | .env n body _ => n == leanDivisionEnv || requestsDivisions body.toList
  | .group body _ => requestsDivisions body.toList
  | .word .. | .space | .par _ | .ctrl .. | .sym .. | .math .. | .verb .. => false

@[expose] public def requestsDivisions : List Raw → Bool
  | [] => false
  | r :: rest => requestsDivision r || requestsDivisions rest

end

/-- Each Lean division the raws request replaced by what `answer` includes for it, asked from `file`
or the file the input environment around it names. -/
public def includeDivisions [Monad m] (answer : LeanDivision → Span → m (Array Raw))
    (file : String) (out : Array Raw) : List Raw → m (Array Raw)
  | [] => pure out
  | r :: rest => do
    let here ← match LeanDivision.ofRaw? r, r with
      | some d, .env _ _ p => answer d ⟨file, p⟩
      | _, .env n body p => do
        let inner ← includeDivisions answer ((Parse.inputEnvFile? n).getD file) #[] body.toList
        pure #[.env n inner p]
      | _, .group body p => do
        let inner ← includeDivisions answer file #[] body.toList
        pure #[.group inner p]
      | _, r => pure #[r]
    includeDivisions answer file (out ++ here) rest
termination_by l => sizeOf l
decreasing_by raws_dec

/-- A `W0307`: a markdown construct the surface AST cannot express and whose
content does not reach the page. -/
private def route (file : String) (subject : String) (what : String) (pos : Pos) : Diag :=
  Diag.of .W0307 what (some ⟨file, pos⟩) (subject := some ("md:" ++ subject))

/-- The characters a docstring's formula may hold beside words, spaces, groups and controls. -/
@[expose] public def docMathSyms : List Char := ['^', '_', '~', '[', ']']

mutual

/-- Whether a raw is one a docstring's formula lowers to: words, spaces, groups, the controls the
math model reads and `docMathSyms`. -/
@[expose] public def docMathOk : Raw → Bool
  | .word _ _ | .space => true
  | .ctrl n _ => MathParse.knownCtrl n
  | .sym c _ => docMathSyms.contains c
  | .group body _ => docMathOkList body.toList
  | .par _ | .math .. | .env .. | .verb .. => false

@[expose] public def docMathOkList : List Raw → Bool
  | [] => true
  | r :: rest => docMathOk r && docMathOkList rest

end

/-- A position read in a fragment that begins at `p`, moved to its place there. -/
@[expose] public def fromFragment (p q : Pos) : Pos :=
  { q with line := p.line + q.line - 1, col := if q.line == 1 then p.col + q.col - 1 else q.col }

/-- The one formula `raws` hold, at `p`, where they were read `clean` and `docMathOk` admits it. -/
@[expose] public def docMathAt (display : Bool) (p : Pos) (raws : Array Raw) (clean : Bool) :
    Option Raw :=
  match raws.toList with
  | [.math d body _] =>
    if clean && d == display && docMathOkList body.toList then
      some (.math display (mapPosList (fromFragment p) #[] body.toList) p)
    else none
  | _ => none

/-- The formula a docstring's math span spells, at the span's place, where it lexes and parses
whole to one formula `docMathOk` admits. -/
public def docMathRaw (display : Bool) (src : String) (p : Pos) : Option Raw :=
  let delim := if display then "$$" else "$"
  let lexed := Lex.lex "" (delim ++ src ++ delim)
  let parsed := Parse.parse "" lexed.1
  docMathAt display p parsed.1 (lexed.2.isEmpty && parsed.2.isEmpty)

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
  | .citeText _ body _ => inlTextList "" body.toList
  | .math _ src _ => src
  | .note _ _ _ => ""

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

/-- A suffix's opening punctuation off its first word, with the spaces after it, as Pandoc's
`citeArguments` takes it off. -/
public def dropSeparator (l : List Raw) : List Raw :=
  match l with
  | Raw.word w p :: rest =>
    if [",", ":", ";", ".", "!", "?"].any (fun (m : String) => w.startsWith m) then
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

/-- Whether a key crosses natbib's comma-separated key list as itself. -/
public def keyCrosses (key : String) : Bool := KeyVal.items key == #[key]

/-- A work whose key cannot cross natbib's key list, as its text: its prefix, its braced key and its
suffix. -/
private def workText (c : CiteRaws) (p : Pos) : Array Raw :=
  let pre := if c.pre.isEmpty then #[] else c.pre.push .space
  let post := if c.post.isEmpty then #[] else #[Raw.word "," p, .space] ++ c.post
  pre ++ #[.word ("@{" ++ c.key ++ "}") p] ++ post

/-- `\citetext` around each citation's own command, joined by `; `, a work whose key cannot cross
natbib's key list set as its text. -/
private def citeTextRaws (items : List CiteRaws) (p : Pos) : Array Raw :=
  let body := items.foldl (init := #[]) fun acc c =>
    (if acc.isEmpty then acc else acc ++ #[.word ";" p, .space]) ++
      (if keyCrosses c.key then citeCmdRaws (textCmd c.mode) c.pre c.post #[c.key] p
       else workText c p)
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

/-- A citation group's works as natbib's commands, or, where a key cannot cross natbib's key list,
`\citetext` with that work as its text and the loss named; an author-in-text work's own text. -/
private def citeWorksRaws (file : String) (items : Array CiteRaws) (p : Pos) :
    Array Raw × Array Diag :=
  if items.isEmpty then (#[], #[]) else
  let bad := items.filter (!keyCrosses ·.key)
  if bad.isEmpty then (natbibRaws items.toList p, #[]) else
  let diags := bad.map fun c => routeDegraded file "cite-key"
    s!"the citation key '{c.key}' holds a comma or a brace no bibliography key can hold: the \
work sets as its key, uncited" p (help := some "spell the key as its .bib entry writes it")
  match items[0]? with
  | some first =>
    if first.mode == .authorInText then
      if keyCrosses first.key then
        (citeCmdRaws "citeauthor" #[] #[] #[first.key] p ++ #[.space] ++
          citeTextRaws ({ first with mode := .suppressAuthor } :: items.toList.drop 1) p, diags)
      else (textRaws (" ".intercalate (items.toList.map fun c => "@{" ++ c.key ++ "}")) p, diags)
    else (citeTextRaws items.toList p, diags)
  | none => (#[], diags)

/-- A citation group's raws: its works', a citation of every entry setting and listing nothing, as
Pandoc's citation processing reads one in the text. -/
private def citeGroupRaws (file : String) (items : Array CiteRaws) (p : Pos) :
    Array Raw × Array Diag :=
  let unset := if items.all (·.key != "*") then #[] else
    #[routeDegraded file "cite-every"
      "a citation of every entry in the text prints nothing and lists nothing, as Pandoc's citation \
processing reads it" p (help := some "list every entry with nocite: '@*' in the metadata")]
  let (rs, ds) := citeWorksRaws file (items.filter (·.key != "*")) p
  (rs, ds ++ unset)

mutual

/-- Whether inline content holds a citation of a work natbib's key list carries. -/
private def citesInl : Inl → Bool
  | .cite items _ => items.any fun c => c.key != "*" && keyCrosses c.key
  | .citeText key _ _ => keyCrosses key
  | .emph body _ => citesInls body.toList
  | .strong body _ => citesInls body.toList
  | .link _ _ body _ => citesInls body.toList
  | .image _ _ alt _ => citesInls alt.toList
  | .note _ body _ => citesInls body.toList
  | .text .. | .code .. | .anchor .. | .soft _ | .hard _ | .math .. => false

private def citesInls : List Inl → Bool
  | [] => false
  | x :: rest => citesInl x || citesInls rest

end

mutual

/-- Whether inline content spells a citation at all, one no key list carries included. -/
private def spellsCiteInl : Inl → Bool
  | .cite _ _ => true
  | .citeText _ _ _ => true
  | .emph body _ => spellsCiteInls body.toList
  | .strong body _ => spellsCiteInls body.toList
  | .link _ _ body _ => spellsCiteInls body.toList
  | .image _ _ alt _ => spellsCiteInls alt.toList
  | .note _ body _ => spellsCiteInls body.toList
  | .text .. | .code .. | .anchor .. | .soft _ | .hard _ | .math .. => false

private def spellsCiteInls : List Inl → Bool
  | [] => false
  | x :: rest => spellsCiteInl x || spellsCiteInls rest

end

/-- An empty group, TeX's own end of a command's arguments, when `rs` opens on a word an
overlay-aware command before it would read as its `<…>` selector. -/
@[expose] public def selectorGuard (rs : Array Raw) (p : Pos) : Array Raw :=
  match rs[0]? with
  | some (Raw.word w _) => if w.startsWith "<" then #[.group #[] p] else #[]
  | _ => #[]

/-- A word's opening quote as it reads after a word, closing, where the word follows an inline element
whose ink ends it, as Pandoc's smart punctuation reads `*x*'s`. -/
private def closingQuote (w : String) : String :=
  match w.toList with
  | '\'' :: '\'' :: rest => String.ofList ('”' :: rest)
  | '\'' :: rest => String.ofList ('’' :: rest)
  | '"' :: rest => String.ofList ('”' :: rest)
  | _ => w

/-- Whether text's opening quote closes after an inline element, as Pandoc reads it: always after
emphasis, else a single quote no later one pairs with, and a double one before a space or the end. -/
private def closesAfter (emphasis : Bool) (s : String) : Bool :=
  match s.toList with
  | '\'' :: rest => emphasis || !rest.contains '\''
  | '"' :: rest => emphasis || rest.head?.all (· == ' ')
  | _ => false

/-- Text's raws after an inline element, their first word's opening quote closing. -/
private def closeLeading (rs : Array Raw) : Array Raw :=
  match rs.toList with
  | .word w p :: rest => (Raw.word (closingQuote w) p :: rest).toArray
  | _ => rs

mutual

private def inlRaws (file : String) (dialect : Dialect) : Inl → Array Raw × Array Diag
  | .text s p => (textRaws s p, #[])
  | .code s p => (#[.ctrl "texttt" p, .group (textRaws s p) p], #[])
  -- A footnote's content sets where its reference stands, an empty definition's an empty note.
  | .note _ body p =>
    let (rs, ds) := inlListRaws file dialect #[] #[] body.toList
    (#[.ctrl "footnote" p, .group rs p], ds)
  | .math display src p =>
    match (if dialect.formulas then docMathRaw display src p else none) with
    | some r => (#[r], #[])
    | none =>
      let delim := if display then "$$" else "$"
      (#[.ctrl "texttt" p, .group (textRaws (delim ++ src ++ delim) p) p],
        #[routeDegraded file "docstring-math" "a formula sets as its source: it does not parse as \
a formula, or holds a control or a character the math model does not read" p])
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
    let (rs, ds) := inlListRaws file dialect #[] #[] body.toList
    (#[.ctrl "emph" p, .group rs p], ds)
  | .strong body p =>
    let (rs, ds) := inlListRaws file dialect #[] #[] body.toList
    (#[.ctrl "textbf" p, .group rs p], ds)
  | .link dest title body p =>
    let (rs, ds) := inlListRaws file dialect #[] #[] body.toList
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
    -- An alternative holding a citation rides its own control, which the elaborator reads whole.
    if citesInls alt.toList then
      let (rs, ads) := inlListRaws file dialect #[] #[] alt.toList
      (#[.ctrl Parse.markdownImageControl p, .group rs p, .group (textRaws dest p) p], ds ++ ads)
    else if text.isEmpty then
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
  -- The author's text links to the work's entry, which `\nocite` lists.
  | .citeText key body p =>
    let (rs, ds) := inlListRaws file dialect #[] #[] body.toList
    let listed := citeCmdRaws "nocite" #[] #[] #[key] p
    (#[.ctrl "href" p, .group (textRaws ("#" ++ Ir.bibAnchor key) p) p, .group rs p] ++ listed, ds)
  | .cite items p =>
    let cs := citeItemsRaws file dialect #[] #[] items.toList
    let g := citeGroupRaws file cs.1 p
    let plain (xs : Array Inl) : Bool := xs.all fun x => x matches .text .. | .soft _
    let styled := if items.all (fun it => plain it.pre && plain it.post) then #[] else
      #[routeDegraded file "cite-note"
        "a citation's prefix or suffix sets as plain text: its emphasis, code or links are dropped" p]
    (g.1, cs.2 ++ g.2 ++ styled)

/-- Each citation of a group with its notes as raws, accumulating. -/
private def citeItemsRaws (file : String) (dialect : Dialect) (out : Array CiteRaws)
    (ds : Array Diag) :
    List CiteItem → Array CiteRaws × Array Diag
  | [] => (out, ds)
  | .mk key mode pre post :: rest =>
    let a := inlListRaws file dialect #[] #[] pre.toList
    let b := inlListRaws file dialect #[] #[] post.toList
    citeItemsRaws file dialect (out.push { key, mode, pre := a.1, post := postNote b.1 })
      (ds ++ a.2 ++ b.2)
      rest

/-- A list of inline nodes, accumulating. -/
private def inlListRaws (file : String) (dialect : Dialect) (out : Array Raw) (ds : Array Diag) :
    List Inl → Array Raw × Array Diag
  | [] => (out, ds)
  | x :: rest =>
    let (rs, ds') := inlRaws file dialect x
    let emphasis := match out[out.size - 2]? with
      | some (.ctrl "emph" _) | some (.ctrl "textbf" _) => true
      | _ => false
    let closes := match x with
      | .text s _ => (out.back? matches some (.group ..)) && closesAfter emphasis s
      | _ => false
    let rs := if closes then closeLeading rs else rs
    let guard := match out.back? with
      | some (.group _ p) => selectorGuard rs p
      | _ => #[]
    inlListRaws file dialect (out ++ guard ++ rs) (ds ++ ds') rest

end

/-- A table column's spec letter; GFM's undeclared alignment is `l`. -/
public def TableAlign.specLetter : TableAlign → Char
  | .none => 'l'
  | .left => 'l'
  | .right => 'r'
  | .center => 'c'

/-- A table cell's inline content as raws. -/
private def cellRaws (file : String) (dialect : Dialect) (cell : Array Inl) :
    Array Raw × Array Diag :=
  inlListRaws file dialect #[] #[] cell.toList

/-- The cells of a row after its first, each after its `&`, each one group. -/
private def laterCellsRaws (cell : Array Inl → Array Raw × Array Diag) (p : Pos) (out : Array Raw)
    (ds : Array Diag) : List (Array Inl) → Array Raw × Array Diag
  | [] => (out, ds)
  | c :: rest =>
    let (rs, cds) := cell c
    laterCellsRaws cell p ((out.push (.sym '&' p)).push (.group rs p)) (ds ++ cds) rest

/-- A row's cells as groups, `&` between each two. -/
private def rowCellsRaws (cell : Array Inl → Array Raw × Array Diag) (p : Pos) :
    List (Array Inl) → Array Raw × Array Diag
  | [] => (#[], #[])
  | c :: rest =>
    let (rs, cds) := cell c
    laterCellsRaws cell p #[.group rs p] cds rest

/-- One row: its cells, closed by `\\`. -/
private def rowRaws (cell : Array Inl → Array Raw × Array Diag) (row : Array (Array Inl)) (p : Pos) :
    Array Raw × Array Diag :=
  let cells := rowCellsRaws cell p row.toList
  (cells.1.push (.ctrl "\\" p), cells.2)

/-- The data rows, each after the one before, the accumulator threaded. -/
private def rowsRaws (cell : Array Inl → Array Raw × Array Diag) (p : Pos) (out : Array Raw)
    (ds : Array Diag) : List (Array (Array Inl)) → Array Raw × Array Diag
  | [] => (out, ds)
  | row :: rest =>
    let (rs, rds) := rowRaws cell row p
    rowsRaws cell p (out ++ rs) (ds ++ rds) rest

/-- A table as the booktabs `{tabular}` the surface AST already has, each cell lowered by `cell`. -/
public def tableRaws (cell : Array Inl → Array Raw × Array Diag) (aligns : Array TableAlign)
    (header : Array (Array Inl)) (rows : Array (Array (Array Inl))) (p : Pos) :
    Array Raw × Array Diag :=
  let spec := String.ofList (aligns.toList.map TableAlign.specLetter)
  let (hr, hds) := rowRaws cell header p
  let head : Array Raw := #[.group #[.sym '@' p, .group #[] p, .word spec p,
    .sym '@' p, .group #[] p] p, .ctrl "toprule" p]
  let (body, ds) := rowsRaws cell p ((head ++ hr).push (.ctrl "midrule" p)) hds rows.toList
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

private theorem laterCellsRaws_tableTop (cell : Array Inl → Array Raw × Array Diag) (p : Pos)
    (cells : List (Array Inl)) :
    ∀ (out : Array Raw) (ds : Array Diag), (∀ x ∈ out, TableTop p x) →
      ∀ x ∈ (laterCellsRaws cell p out ds cells).1, TableTop p x := by
  induction cells with
  | nil => intro out _ h; exact h
  | cons c rest ih =>
    intro out ds h
    unfold laterCellsRaws
    rcases cell c with ⟨rs, cds⟩
    exact ih _ _ (tableTop_push p _ _ (tableTop_push p _ _ h (Or.inr (Or.inl rfl)))
      (Or.inl ⟨rs, rfl⟩))

private theorem rowCellsRaws_tableTop (cell : Array Inl → Array Raw × Array Diag) (p : Pos)
    (cells : List (Array Inl)) : ∀ x ∈ (rowCellsRaws cell p cells).1, TableTop p x := by
  cases cells with
  | nil => simp [rowCellsRaws]
  | cons c rest =>
    unfold rowCellsRaws
    exact laterCellsRaws_tableTop cell p rest _ _ (by
      intro x hx
      simp at hx
      exact hx ▸ Or.inl ⟨_, rfl⟩)

private theorem rowRaws_tableTop (cell : Array Inl → Array Raw × Array Diag)
    (row : Array (Array Inl)) (p : Pos) : ∀ x ∈ (rowRaws cell row p).1, TableTop p x :=
  tableTop_push p _ _ (rowCellsRaws_tableTop cell p row.toList) (Or.inr (Or.inr (Or.inl rfl)))

private theorem rowsRaws_tableTop (cell : Array Inl → Array Raw × Array Diag) (p : Pos)
    (rows : List (Array (Array Inl))) :
    ∀ (out : Array Raw) (ds : Array Diag), (∀ x ∈ out, TableTop p x) →
      ∀ x ∈ (rowsRaws cell p out ds rows).1, TableTop p x := by
  induction rows with
  | nil => intro out _ h; exact h
  | cons row rest ih =>
    intro out ds h
    unfold rowsRaws
    have hr := rowRaws_tableTop cell row p
    rcases hrow : rowRaws cell row p with ⟨rs, rds⟩
    rw [hrow] at hr
    refine ih _ _ ?_
    intro x hx
    rcases Array.mem_append.mp hx with hx | hx
    · exact h x hx
    · exact hr x hx

public theorem tableRaws_contract (cell : Array Inl → Array Raw × Array Diag)
    (aligns : Array TableAlign) (header : Array (Array Inl)) (rows : Array (Array (Array Inl)))
    (p : Pos) :
    ∃ body, (tableRaws cell aligns header rows p).1 = #[.env Parse.markdownTableEnv body p] ∧
      ∀ x ∈ body, TableTop p x := by
  unfold tableRaws
  have hh := rowRaws_tableTop cell header p
  rcases hhr : rowRaws cell header p with ⟨hr, hds⟩
  rw [hhr] at hh
  dsimp only
  refine ⟨_, rfl, ?_⟩
  refine tableTop_push p _ _ ?_ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  refine rowsRaws_tableTop cell p _ _ _ ?_
  refine tableTop_push p _ _ ?_ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  intro x hx
  rcases Array.mem_append.mp hx with hx | hx
  · simp at hx
    rcases hx with rfl | rfl
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact hh x hx

/-- What a list's markdown says that its lowering does not carry. -/
private def listLosses (file : String) (ordered : Bool) (start : Nat) (tight : Bool) (p : Pos) :
    Array Diag :=
  (if ordered && start != 1 then #[routeDegraded file "list-start"
      "an ordered list's start number is not carried and the list counts from one" p] else #[]) ++
  (if tight then #[] else #[routeDegraded file "loose-list"
      "a loose list sets as a tight one: its items' paragraph spacing is not carried" p])

mutual

private def blkRaws (file : String) (refs : Array Raw) (dialect : Dialect) :
    Blk → Array Raw × Array Diag
  | .para body p =>
    let (rs, ds) := inlListRaws file dialect #[] #[] body.toList
    (rs.push (.par p), ds)
  | .heading level body p =>
    let (rs, ds) := inlListRaws file dialect #[] #[] body.toList
    (Parse.headingRaws level rs p, ds)
  | .code info text p =>
    -- The info string's first word is the language, crossing as an `Ir.ListingLang`.
    let word := ((info.split (fun c => c == ' ' || c == '\t')).find? (!·.isEmpty)).map
      (·.toString)
    match word with
    | none => (#[.verb "verbatim" (.plain ("\n" ++ text)) p], #[])
    | some w =>
      match Ir.listingLang? w with
      | some l => (#[.verb "lstlisting" ⟨#[.language l], none, "", "\n" ++ text⟩ p], #[])
      | none =>
        (#[.verb "verbatim" (.plain ("\n" ++ text)) p],
         #[routeDegraded file "code-info"
            s!"the info word '{w}' is not a language a listing can carry: the code sets \
without a language" p
            (help := some "spell it as letters, digits, +, #, - or . (python, c++, c#)")])
  | .rule p =>
    (#[], #[route file "thematic-break"
      "a thematic break has no block in this engine and is not drawn" p])
  | .quote body p =>
    let (rs, ds) := blkListRaws file refs dialect #[] #[] body.toList
    (#[.env "quote" rs p], ds)
  | .disclosure summary expanded body p =>
    let (ss, sds) := inlListRaws file dialect #[] #[] summary.toList
    let (rs, ds) := blkListRaws file refs dialect #[] #[] body.toList
    (disclosureRaws ss rs expanded p, sds ++ ds)
  | .list ordered start tight items p =>
    let (rs, ds) := itemsRaws file refs dialect #[] #[] items.toList p
    (#[.env (if ordered then "enumerate" else "itemize") rs p],
      ds ++ listLosses file ordered start tight p)
  | .table aligns header rows p => tableRaws (cellRaws file dialect) aligns header rows p
  | .lean attrs p =>
    (if dialect.divisions then #[.par p, (LeanDivision.ofAttrs attrs).raw p] else #[], #[])
  -- The metadata block is read whole by `desugar`, before the blocks.
  | .metadata _ _ => (#[], #[])
  | .refs _ => (refs, #[])
  | .note _ _ _ => (#[], #[])

private def blkListRaws (file : String) (refs : Array Raw) (dialect : Dialect) (out : Array Raw)
    (ds : Array Diag) :
    List Blk → Array Raw × Array Diag
  | [] => (out, ds)
  | b :: rest =>
    let (rs, ds') := blkRaws file refs dialect b
    blkListRaws file refs dialect (out ++ rs) (ds ++ ds') rest

/-- One `\item` per list item, its blocks inside. -/
private def itemsRaws (file : String) (refs : Array Raw) (dialect : Dialect) (out : Array Raw)
    (ds : Array Diag) :
    List (Array Blk) → Pos → Array Raw × Array Diag
  | [], _ => (out, ds)
  | it :: rest, p =>
    let (rs, ds') := blkListRaws file refs dialect #[] #[] it.toList
    itemsRaws file refs dialect ((out.push (.ctrl "item" p)) ++ selectorGuard rs p ++ rs) (ds ++ ds')
      rest p

end

/-! ## Hybrid: a file's text as TeX -/

/-- A file's TeX comments cut after their `%`, so the markdown read under the hybrid option holds
none of their text, each line keeping its place and its end. -/
private def stripTexComments (input : String) : String :=
  "\n".intercalate ((input.splitOn "\n").map fun line => Id.run do
    let mut out := ""
    let mut backslashes := 0
    for c in line.toList do
      if c == '%' && backslashes % 2 == 0 then return out.push '%'
      out := out.push c
      backslashes := if c == '\\' then backslashes + 1 else 0
    return out)

/-- Where each line of `s` starts, counted in characters. -/
private def lineStartsOf (s : String) : Array Nat := Id.run do
  let mut out := #[0]
  let mut i := 0
  for c in s.toList do
    i := i + 1
    if c == '\n' then out := out.push i
  return out

/-- The file place of `q`, a place the lexer gives in a buffer of pieces whose starts in it and in
the file `anchors` holds, at the latest piece starting at or before it, searched from piece `k`. -/
private def placeFrom (starts : Array Nat) (anchors : Array (Nat × Pos)) (k : Nat) (q : Pos) :
    Nat × Pos := Id.run do
  let off := starts.getD (q.line - 1) 0 + (q.col - 1)
  let mut k := if (anchors.getD k (0, {})).1 ≤ off then k else 0
  for _ in [0:anchors.size] do
    if (anchors.getD (k + 1) (off + 1, {})).1 ≤ off then k := k + 1 else break
  match anchors[k]? with
  | some (start, p) =>
    (k, if start ≤ off then { q with line := p.line, col := p.col + (off - start) } else q)
  | none => (k, q)

/-- A hybrid file's TeX as one token stream: its text lexed where it stands, markdown's nodes
spelled around it, and every other node kept whole at its place. -/
private structure TexStream where
  toks : Array Lex.Token := #[]
  kept : Array (Array Raw) := #[]
  diags : Array Diag := #[]
  /-- Text not yet lexed, its length in characters, and where each of its pieces starts in it and
  in the file. -/
  buf : String := ""
  len : Nat := 0
  anchors : Array (Nat × Pos) := #[]

/-- The text not yet lexed, lexed into the stream at the file places its pieces came from. -/
private def TexStream.flush (st : TexStream) (file : String) : TexStream :=
  let ⟨toks, kept, diags, buf, len, anchors⟩ := st
  if buf.isEmpty then ⟨toks, kept, diags, buf, len, anchors⟩ else
  let (lexed, ds) := Lex.lex file buf
  let starts := lineStartsOf buf
  let (toks, _) := lexed.foldl (init := (toks, 0)) fun (out, k) t =>
    let (k, q) := placeFrom starts anchors k t.pos
    (out.push { t with pos := q }, k)
  let diags := ds.foldl (init := diags) fun out d =>
    out.push { d with span := d.span.map fun sp =>
      { sp with pos := (placeFrom starts anchors 0 sp.pos).2 } }
  ⟨toks, kept, diags, "", 0, #[]⟩

/-- Whether the text not yet lexed ends inside a verbatim capture, which a node after it joins as
markdown spells it. -/
private def TexStream.verbOpen (st : TexStream) (file : String) : Bool :=
  !st.buf.isEmpty && (Lex.lex file st.buf).2.any (·.kind == .E0102)

/-- Text at `p` into the stream. -/
private def TexStream.text (st : TexStream) (s : String) (p : Pos) : TexStream :=
  let ⟨toks, kept, diags, buf, len, anchors⟩ := st
  ⟨toks, kept, diags, buf ++ s, len + s.length, anchors.push (len, p)⟩

/-- A token at `p`, after the text before it. -/
private def TexStream.tok (st : TexStream) (file : String) (t : Lex.Tok) (p : Pos) : TexStream :=
  let ⟨toks, kept, diags, buf, len, anchors⟩ := st.flush file
  ⟨toks.push ⟨t, p⟩, kept, diags, buf, len, anchors⟩

/-- Raws a node lowers to, kept whole at `p`. -/
private def TexStream.keep (st : TexStream) (file : String) (rs : Array Raw × Array Diag)
    (p : Pos) : TexStream :=
  let ⟨toks, kept, diags, buf, len, anchors⟩ := st.flush file
  let k := kept.size
  ⟨toks.push ⟨.verb Parse.keptEnv (toString k), p⟩, kept.push rs.1, diags ++ rs.2, buf, len,
    anchors⟩

/-- The stream read as TeX once, each kept node back at its place. -/
private def TexStream.close (st : TexStream) (file : String) : Array Raw × Array Diag :=
  let ⟨toks, kept, diags, _, _, _⟩ := st.flush file
  let (raws, ds) := Parse.parse file toks
  (Parse.spliceKeptList kept #[] raws.toList, diags ++ ds)

mutual

/-- An inline node as markdown spells it, near enough for a verbatim capture holding it. -/
private def inlSpelling : Inl → String
  | .text s _ => s
  | .soft _ => "\n"
  | .hard _ => "\n"
  | .code s _ => "`" ++ s ++ "`"
  | .emph body _ => inlsSpelling "*" body.toList ++ "*"
  | .strong body _ => inlsSpelling "**" body.toList ++ "**"
  | .link dest _ body _ => inlsSpelling "[" body.toList ++ "](" ++ dest ++ ")"
  | .image dest _ alt _ => inlsSpelling "![" alt.toList ++ "](" ++ dest ++ ")"
  | .anchor key _ => "<a id=\"" ++ key ++ "\"></a>"
  | .citeText _ body _ => inlsSpelling "[" body.toList ++ "]"
  | .cite items _ =>
    "[" ++ "; ".intercalate (items.toList.map fun ⟨key, _, _, _⟩ => "@" ++ key) ++ "]"
  | .math display src _ => if display then "$$" ++ src ++ "$$" else "$" ++ src ++ "$"
  | .note label _ _ => "[^" ++ label ++ "]"

private def inlsSpelling (acc : String) : List Inl → String
  | [] => acc
  | x :: rest => inlsSpelling (acc ++ inlSpelling x) rest

end

/-- The stream with `x` joining a verbatim capture the text before it left open, if it did. -/
private def TexStream.spelled? (st : TexStream) (file : String) (x : Inl) (p : Pos) :
    Option TexStream :=
  if st.verbOpen file then some (st.text (inlSpelling x) p) else none

mutual

/-- One inline node into a hybrid file's stream: its text as TeX reads it, emphasis and links
spelled around their content, every other node kept whole. -/
private def texInl (file : String) (dialect : Dialect) (st : TexStream) : Inl → TexStream
  | .text s p => st.text s p
  | .soft p => st.text "\n" p
  | x@(.hard p) => (st.spelled? file x p).getD (st.tok file (.ctrl "\\") p)
  | x@(.emph body p) => match st.spelled? file x p with
    | some st => st
    | none =>
      (texInls file dialect ((st.tok file (.ctrl "emph") p).tok file .lbrace p) body.toList).tok file
        .rbrace p
  | x@(.strong body p) => match st.spelled? file x p with
    | some st => st
    | none =>
      (texInls file dialect ((st.tok file (.ctrl "textbf") p).tok file .lbrace p) body.toList).tok file
        .rbrace p
  | x@(.link dest title body p) => match st.spelled? file x p with
    | some st => st
    | none =>
      let st := (st.tok file (.ctrl "href") p).keep file (#[.group (textRaws dest p) p], #[]) p
      let st := (texInls file dialect (st.tok file .lbrace p) body.toList).tok file .rbrace p
      if title.isEmpty then st else
        { st with diags := st.diags.push (routeDegraded file "link-title"
          "a link's title is not carried: the link sets without it" p) }
  | x@(.citeText key body p) => match st.spelled? file x p with
    | some st => st
    | none =>
      let st := (st.tok file (.ctrl "href") p).keep file
        (#[.group (textRaws ("#" ++ Ir.bibAnchor key) p) p], #[]) p
      let st := (texInls file dialect (st.tok file .lbrace p) body.toList).tok file .rbrace p
      st.keep file (citeCmdRaws "nocite" #[] #[] #[key] p, #[]) p
  | x@(.code _ p) => (st.spelled? file x p).getD (st.keep file (inlRaws file dialect x) p)
  | x@(.image _ _ _ p) => (st.spelled? file x p).getD (st.keep file (inlRaws file dialect x) p)
  | x@(.math _ _ p) => (st.spelled? file x p).getD (st.keep file (inlRaws file dialect x) p)
  | x@(.note _ _ p) => (st.spelled? file x p).getD (st.keep file (inlRaws file dialect x) p)
  | x@(.anchor _ p) => (st.spelled? file x p).getD (st.keep file (inlRaws file dialect x) p)
  | x@(.cite _ p) => (st.spelled? file x p).getD (st.keep file (inlRaws file dialect x) p)

private def texInls (file : String) (dialect : Dialect) (st : TexStream) : List Inl → TexStream
  | [] => st
  | x :: rest => texInls file dialect (texInl file dialect st x) rest

end

mutual

/-- One block into a hybrid file's stream, a paragraph's text joining it and a container's blocks
read as a stream of their own, kept whole. -/
private def texBlk (file : String) (refs : Array Raw) (dialect : Dialect) (st : TexStream) :
    Blk → TexStream
  | .para body p =>
    let st := texInls file dialect st body.toList
    if st.verbOpen file then st.text "\n\n" p else st.tok file .par p
  | .heading level body p =>
    let (rs, ds) := (texInls file dialect {} body.toList).close file
    st.keep file (Parse.headingRaws level rs p, ds) p
  | .quote body p =>
    let (rs, ds) := (texBlks file refs dialect {} body.toList).close file
    st.keep file (#[.env "quote" rs p], ds) p
  | .disclosure summary expanded body p =>
    let (ss, sds) := (texInls file dialect {} summary.toList).close file
    let (rs, ds) := (texBlks file refs dialect {} body.toList).close file
    st.keep file (disclosureRaws ss rs expanded p, sds ++ ds) p
  | .list ordered start tight items p =>
    let (rs, ds) := texItems file refs dialect #[] #[] items.toList p
    st.keep file (#[.env (if ordered then "enumerate" else "itemize") rs p],
      ds ++ listLosses file ordered start tight p) p
  | .table aligns header rows p =>
    st.keep file (tableRaws (fun c => (texInls file dialect {} c.toList).close file) aligns header rows p) p
  | b@(.code _ _ p) => st.keep file (blkRaws file refs dialect b) p
  | b@(.rule p) => st.keep file (blkRaws file refs dialect b) p
  | b@(.lean _ p) => st.keep file (blkRaws file refs dialect b) p
  | b@(.metadata _ p) => st.keep file (blkRaws file refs dialect b) p
  | b@(.refs p) => st.keep file (blkRaws file refs dialect b) p
  | b@(.note _ _ p) => st.keep file (blkRaws file refs dialect b) p

private def texBlks (file : String) (refs : Array Raw) (dialect : Dialect) (st : TexStream) :
    List Blk → TexStream
  | [] => st
  | b :: rest => texBlks file refs dialect (texBlk file refs dialect st b) rest

/-- One `\item` per list item, its blocks a stream of their own. -/
private def texItems (file : String) (refs : Array Raw) (dialect : Dialect) (out : Array Raw)
    (ds : Array Diag) : List (Array Blk) → Pos → Array Raw × Array Diag
  | [], _ => (out, ds)
  | it :: rest, p =>
    let (rs, ds') := (texBlks file refs dialect {} it.toList).close file
    texItems file refs dialect ((out.push (.ctrl "item" p)) ++ selectorGuard rs p ++ rs)
      (ds ++ ds') rest p

end

/-- A file's blocks as raws, read as TeX within markdown's structure where `tex` says. -/
private def bodyRaws (file : String) (refs : Array Raw) (dialect : Dialect) (tex : Bool)
    (blocks : List Blk) :
    Array Raw × Array Diag :=
  if tex then (texBlks file refs dialect {} blocks).close file
  else blkListRaws file refs dialect #[] #[] blocks

mutual

/-- Where a block holds its first reference-list division. -/
private def refsAtOne : Blk → Option Pos
  | .refs p => some p
  | .quote body _ => refsAt body.toList
  | .disclosure _ _ body _ => refsAt body.toList
  | .list _ _ _ items _ => refsAtItems items.toList
  | .para .. | .heading .. | .code .. | .rule _ | .table .. | .lean .. | .metadata .. | .note .. =>
    none

private def refsAt : List Blk → Option Pos
  | [] => none
  | b :: rest => (refsAtOne b).orElse fun _ => refsAt rest

private def refsAtItems : List (Array Blk) → Option Pos
  | [] => none
  | it :: rest => (refsAt it.toList).orElse fun _ => refsAtItems rest

end

/-- Whether a table's cells hold inline content `inl` finds a citation in. -/
private def citesCells (inl : List Inl → Bool) (cells : List (Array Inl)) : Bool :=
  cells.any fun c => inl c.toList

mutual

/-- Whether a block holds inline content `inl` finds a citation in, anywhere. -/
private def citesBlk (inl : List Inl → Bool) : Blk → Bool
  | .para body _ => inl body.toList
  | .heading _ body _ => inl body.toList
  | .quote body _ => citesBlks inl body.toList
  | .disclosure summary _ body _ => inl summary.toList || citesBlks inl body.toList
  | .list _ _ _ items _ => citesItems inl items.toList
  | .table _ header rows _ =>
    citesCells inl header.toList || rows.toList.any (citesCells inl ·.toList)
  -- A Lean division's documentation view cites into the document's list.
  | .lean attrs _ => attrs.any fun (k, v) =>
    k == "show" && ((v.splitOn ",").map (·.trimAscii.toString)).contains "docs"
  | .note _ body _ => citesBlks inl body.toList
  | .code .. | .rule _ | .metadata .. | .refs _ => false

private def citesBlks (inl : List Inl → Bool) : List Blk → Bool
  | [] => false
  | b :: rest => citesBlk inl b || citesBlks inl rest

private def citesItems (inl : List Inl → Bool) : List (Array Blk) → Bool
  | [] => false
  | it :: rest => citesBlks inl it.toList || citesItems inl rest

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
  decls : Array CiteDecl := #[]
  nocite : Option (Array String × Pos) := none
  title : Option (Array Inl × Pos) := none
  /-- Each key the reader took, with its field's site, which only a citation reads. -/
  taken : Array (String × Pos) := #[]
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
key is named, as is a key written twice, which takes its last value, and in a document a citation
key with no bibliography to act on; a key ending in `_` is ignored. -/
public def metaRead (file : String) (role : Role) (fields : Array MetaField) : MetaRead := Id.run do
  let mut last : Std.HashMap String Nat := {}
  for (f, k) in fields.zipIdx do last := last.insert f.key k
  let declared := bibDeclared fields
  let unread (f : MetaField) (why : String) (help : Option String := none) : Diag :=
    Diag.of .W0307 s!"the metadata key '{f.key}' is not read: {why}" (some ⟨file, f.pos⟩) help
      (subject := some ("md:meta:" ++ f.key))
  let mut out : MetaRead := {}
  for (f, k) in fields.zipIdx do
    if f.key.endsWith "_" then continue
    if last.get? f.key != some k then
      out := { out with diags := out.diags.push (routeDegraded file ("meta-twice:" ++ f.key)
        s!"the metadata key '{f.key}' is written again below: its last value is read" f.pos) }
      continue
    let known := metaKeys.any fun (k, r) => k == f.key && r == role
    if !known then
      let csl := f.key == "csl" || f.key == "citation-style"
      let why := if role == .included && metaKeys.any (·.1 == f.key) then
          "an included file's citations take the including document's bibliography and style"
        else if csl then "no CSL processor reads it; citations set in a BibTeX style"
        else "its value does not reach the page"
      let help := if csl then
          some s!"declare 'biblio-style:' with {Diag.prose "or" CiteDecl.bibtexStyles}"
        else none
      out := { out with diags := out.diags.push (unread f why help) }
      continue
    if role == .document && !declared && f.key != "bibliography" then
      out := { out with diags := out.diags.push (unread f "the document declares no bibliography"
        (some "name the .bib file the citations take, as 'bibliography: refs.bib'")) }
      continue
    let before := out.diags.size
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
      let (decls, unread) := CiteDecl.natbibLoad given
      let ds := unread.toArray.map fun o =>
        Diag.of .W0104 (Diag.notHonoured (CiteDecl.natbibOption o)) (some ⟨file, f.pos⟩)
          (subject := some ("md:meta:natbiboptions:" ++ o))
      out := { out with decls := out.decls ++ decls, diags := out.diags ++ ds }
    | "nocite", v =>
      match v.text with
      | some t =>
        let keys := citeKeys t
        if !keys.isEmpty then out := { out with nocite := some (keys, f.pos) }
      | none => out := { out with diags := out.diags.push (unread f "its value is not text") }
    | "reference-section-title", .scalar t =>
      let (title, ds) := metaInlines file t.trimAscii.toString f.pos
      let lowered := inlListRaws file .document #[] #[] title.toList
      out := { out with title := some (title, f.pos), diags := out.diags ++ ds ++ lowered.2 }
    | "link-citations", v =>
      match v.bool? with
      | some false =>
        let d := routeDegraded file "link-citations"
          "a citation links to its reference-list entry whatever 'link-citations' declares" f.pos
        out := { out with diags := out.diags.push d }
      | some true => pure ()
      | none => out := { out with diags := out.diags.push (unread f "its value is not true or false") }
    | _, _ => out := { out with diags := out.diags.push (unread f "its value is not one the key takes") }
    if out.diags.size == before && f.key != "nocite" then
      out := { out with taken := out.taken.push (f.key, f.pos) }
  return out

/-- natbib loaded with the declared options, where a bibliography is declared. -/
public def MetaRead.opening (m : MetaRead) : Array Raw :=
  if m.sources.isEmpty then #[] else Parse.citeSetupRaws m.decls m.bibPos

/-- The `nocite` keys as natbib's `\nocite`. -/
public def MetaRead.nociteRaws (m : MetaRead) : Array Raw :=
  match m.nocite with
  | some (keys, q) => citeCmdRaws "nocite" #[] #[] keys q
  | none => #[]

/-- The raws a file opens with, closed by a paragraph end. -/
public def MetaRead.prelude (m : MetaRead) : Array Raw :=
  if m.opening.isEmpty then #[] else m.opening.push (.par m.bibPos)

/-- The reference list's raws in its declared style, plainnat by Pandoc's default; empty where no
bibliography is declared, or where nothing is cited, as Pandoc's citation processing sets none. -/
public def MetaRead.list (m : MetaRead) (cited : Bool) : Array Raw :=
  if m.sources.isEmpty || !(cited || m.nocite.isSome) then #[] else
    #[.par m.bibPos, .ctrl Parse.markdownBibControl m.bibPos,
      .group #[.word (m.style.getD "plainnat") m.bibPos] m.bibPos,
      .group #[.word (",".intercalate m.sources.toList) m.bibPos] m.bibPos]

/-- The heading over a reference list set at the file's end: `reference-section-title`. -/
public def MetaRead.titleRaws (file : String) (dialect : Dialect) (m : MetaRead) : Array Raw :=
  match m.title with
  | some (title, q) => Parse.headingRaws .h1 (inlListRaws file dialect #[] #[] title.toList).1 q
  | none => #[]

/-- What a file ends with: the `nocite` keys, after every citation as Pandoc's LaTeX template sets
them, and the reference list with its title where no division placed it. -/
public def MetaRead.tail (file : String) (dialect : Dialect) (m : MetaRead) (cited placed : Bool) :
    Array Raw :=
  let nocite := if m.nociteRaws.isEmpty then #[] else m.nociteRaws.push (.par m.bibPos)
  let list := m.list cited
  let title := m.titleRaws file dialect
  let titled := title ++ list
  nocite ++ if placed || list.isEmpty then #[] else titled

/-- A document's metadata fields, and the blocks after its metadata block. -/
public def splitMetadata (bs : Array Blk) : Array MetaField × Array Blk :=
  match bs[0]? with
  | some (Blk.metadata fs _) => (fs, bs.extract 1 bs.size)
  | _ => (#[], bs)

/-- Text with each abbreviation joined to the word after it by a non-breaking space where spaces
follow it, as Pandoc's smart punctuation joins it, unless a citation or a note follows the spaces. -/
private def joinAbbreviations (s : String) (citeNext : Bool) : String := Id.run do
  let cs := s.toList.toArray
  let mut out := ""
  let mut i := 0
  for _ in [0:cs.size + 1] do
    let some c := cs[i]? | break
    if c == ' ' || c == '\t' then
      let mut j := i
      for _ in [i:cs.size] do
        if (cs[j]?.map fun d => d == ' ' || d == '\t').getD false then j := j + 1 else break
      let joined := MdSmart.joinsAt cs i && !(j ≥ cs.size && citeNext)
      out := if joined then out.push '\u00a0' else out ++ String.ofList (cs.extract i j).toList
      i := j
    else
      out := out.push c
      i := i + 1
  return out

mutual

/-- Inline content with Pandoc's abbreviations joined to the words after them. -/
private def abbrevInls : List Inl → List Inl
  | [] => []
  | x :: rest =>
    let citeNext := match rest with
      | .cite .. :: _ | .note .. :: _ => true
      | _ => false
    abbrevInl citeNext x :: abbrevInls rest

private def abbrevInl (citeNext : Bool) : Inl → Inl
  | .text s p => .text (joinAbbreviations s citeNext) p
  | .emph body p => .emph (abbrevInls body.toList).toArray p
  | .strong body p => .strong (abbrevInls body.toList).toArray p
  | .link dest title body p => .link dest title (abbrevInls body.toList).toArray p
  | .image dest title alt p => .image dest title (abbrevInls alt.toList).toArray p
  | .cite items p => .cite (abbrevItems items.toList).toArray p
  | .citeText key body p => .citeText key (abbrevInls body.toList).toArray p
  | .note label body p => .note label (abbrevInls body.toList).toArray p
  | x@(.code ..) | x@(.anchor ..) | x@(.soft _) | x@(.hard _) | x@(.math ..) => x

private def abbrevItems : List CiteItem → List CiteItem
  | [] => []
  | .mk key mode pre post :: rest =>
    .mk key mode (abbrevInls pre.toList).toArray (abbrevInls post.toList).toArray :: abbrevItems rest

end

mutual

/-- A block with Pandoc's abbreviations joined in its inline content. -/
private def abbrevBlk : Blk → Blk
  | .para body p => .para (abbrevInls body.toList).toArray p
  | .heading l body p => .heading l (abbrevInls body.toList).toArray p
  | .quote body p => .quote (abbrevBlks body.toList).toArray p
  | .disclosure summary e body p =>
    .disclosure (abbrevInls summary.toList).toArray e (abbrevBlks body.toList).toArray p
  | .list o st t items p => .list o st t (abbrevItemBlks items.toList).toArray p
  | .table a header rows p =>
    .table a (header.map fun c => (abbrevInls c.toList).toArray)
      (rows.map fun r => r.map fun c => (abbrevInls c.toList).toArray) p
  | .note l body p => .note l (abbrevBlks body.toList).toArray p
  | b@(.code ..) | b@(.rule _) | b@(.lean ..) | b@(.metadata ..) | b@(.refs _) => b

private def abbrevBlks : List Blk → List Blk
  | [] => []
  | b :: rest => abbrevBlk b :: abbrevBlks rest

private def abbrevItemBlks : List (Array Blk) → List (Array Blk)
  | [] => []
  | item :: rest => (abbrevBlks item.toList).toArray :: abbrevItemBlks rest

end

/-- The whole document: markdown source to the surface AST, with the reader's
own diagnostics carrying `.md` spans; its metadata opens it, and its reference list stands in
its first `::: {#refs}` division, else at its end, as Pandoc places it. -/
public def desugar (file : String) (input : String) (dialect : Dialect := .document)
    (role : Role := .document) (citing : Bool := false)
    (known : Option (Std.HashSet String) := none) (tex : Bool := false) : Array Raw × Array Diag :=
  let read := blocksIn dialect file (if tex then stripTexComments input else input)
    (included := role == .included && citing) (known := known) (tex := tex)
    (notes := role == .document)
  let split := splitMetadata read.1
  let m := metaRead file role split.1
  -- Pandoc's smart punctuation reads a markdown document's text, not an included file's.
  let blocks := if dialect == .document && role == .document && !tex then abbrevBlks split.2.toList
    else split.2.toList
  let cited := citesBlks citesInls blocks
  let placed := refsAt blocks
  -- The heading the metadata sets over the list at the file's end, which the list drops where it
  -- lists nothing, as Pandoc's citation processing sets none.
  let m := if m.title.isSome && placed.isNone then { m with decls := m.decls.push (.word .sectionTitle) }
    else m
  -- premise: Tests.UnusedSettings.metadataChecks — a document spelling no citation reads none
  let unused := if role != .document || m.sources.isEmpty || m.nocite.isSome ||
      citesBlks spellsCiteInls blocks then #[]
    else m.taken.map fun (key, pos) => UnusedSetting.metaDiag file key pos
  let body := bodyRaws file (m.list cited) dialect tex blocks
  -- premise: mdMetadataChecks — a division with no bibliography to place is named
  let unplaced := match placed with
    | some p => if m.sources.isEmpty then
        #[route file "refs" "a '::: {#refs}' division places the reference list, and no \
bibliography is declared for this file: nothing sets there" p] else #[]
    | none => #[]
  (m.prelude ++ body.1 ++ m.tail file dialect cited placed.isSome,
    read.2 ++ m.diags ++ unused ++ body.2 ++ unplaced)

/-- The frontend a `.md` path selects: the reader plus the desugaring. -/
public def read (file input : String) : Array Raw × Array Diag := desugar file input

/-- A markdown file another document includes: its citations, where `cites` says the including
document reads them, join the including document's, and its text is TeX where `hybrid` says the
including document declares the markdown package's hybrid option. -/
public def readIncluded (file input : String) (cites : Bool) (hybrid : Bool := false) :
    Array Raw × Array Diag :=
  desugar file input (role := .included) (citing := cites) (tex := hybrid)

end LeanTex.Core.Md
