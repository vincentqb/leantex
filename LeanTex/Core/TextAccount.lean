module

public import LeanTex.Core.Ir
public import LeanTex.Core.Parse

namespace LeanTex.Core

/-- Where a character of a text comes from: the source token at a place, a mark the engine adds,
or text no place locates. -/
public inductive Origin where
  | source (span : Span)
  | engine
  | unplaced
  deriving Repr, DecidableEq

/-- The source tokens a diagnostic excuses: the token its span starts at, where its loss leaves
content absent. -/
@[expose] public def Diag.piece (d : Diag) : List Span :=
  if d.kind.loss matches .dropped | .pending then d.span.toList else []

/-- Whether two spans start at one place of one file, as `Pos`'s equality reads a place. -/
@[expose] public def Span.samePlace (a b : Span) : Bool :=
  a.file == b.file && a.pos.line == b.pos.line && a.pos.col == b.pos.col

public theorem Span.samePlace_self (s : Span) : Span.samePlace s s = true := by
  simp [Span.samePlace]

namespace Text

/-- The ASCII spelling TeX sets a typographic punctuation character from, quotes of either hand
read alike. -/
@[expose] public def spell (c : Char) : List Char :=
  if c = '‘' ∨ c = '’' ∨ c = '`' then ['\'']
  else if c = '“' ∨ c = '”' ∨ c = '"' then ['\'', '\'']
  else if c = '—' then ['-', '-', '-']
  else if c = '–' then ['-', '-']
  else if c = '…' then ['.', '.', '.']
  else if c = '¡' then ['!', '\'']
  else if c = '¿' then ['?', '\'']
  else [c]

@[expose] public def canon (s : List Char) : List Char := s.flatMap spell

/-- White space as one space per run, `prior` telling whether a run is open. -/
@[expose] public def squash : Bool → List Char → List Char
  | _, [] => []
  | prior, c :: rest =>
    if c.isWhitespace then
      if prior then squash true rest else ' ' :: squash true rest
    else c :: squash false rest

/-- Text as a reader compares it: TeX's punctuation spellings as one, a white-space run as one
space. -/
@[expose] public def norm (s : List Char) : List Char := squash false (canon s)

/-- The characters a text keeps once the places `named` are excused: every character but those
from an excused place and the engine's marks, the marks' white space kept. -/
@[expose] public def keep (named : List Span) (t : List (Char × Origin)) : List Char :=
  t.filterMap fun (c, o) => match o with
    | .source s => if named.any (Span.samePlace · s) then none else some c
    | .engine => if c.isWhitespace then some c else none
    | .unplaced => some c

@[expose] public def view (named : List Span) (t : List (Char × Origin)) : List Char :=
  norm (keep named t)

/-- The characters of `s`, each from `o`. -/
@[expose] public def chars (o : Origin) (s : String) : List (Char × Origin) := s.toList.map (·, o)

/-- Whether a white-space run is open after `t`, `prior` before it. -/
@[expose] public def endsOpen : Bool → List Char → Bool
  | prior, [] => prior
  | _, c :: rest => endsOpen c.isWhitespace rest

public theorem squash_append (prior : Bool) (a b : List Char) :
    squash prior (a ++ b) = squash prior a ++ squash (endsOpen prior a) b := by
  induction a generalizing prior with
  | nil => rfl
  | cons c rest ih =>
    by_cases hc : c.isWhitespace = true
    · cases prior <;> simp [squash, endsOpen, hc, ih]
    · simp [squash, endsOpen, hc, ih]

public theorem squash_idem (prior : Bool) (a : List Char) :
    squash prior (squash prior a) = squash prior a := by
  induction a generalizing prior with
  | nil => rfl
  | cons c rest ih =>
    by_cases hc : c.isWhitespace = true
    · cases prior <;> simp [squash, hc, ih]
    · simp [squash, hc, ih]

public theorem squash_open (a : List Char) : squash true (squash false a) = squash true a := by
  cases a with
  | nil => rfl
  | cons c rest =>
    by_cases hc : c.isWhitespace = true
    · simp [squash, hc, squash_idem]
    · simp [squash, hc, squash_idem]

public theorem endsOpen_squash (prior : Bool) (a : List Char) :
    endsOpen prior (squash prior a) = endsOpen prior a := by
  induction a generalizing prior with
  | nil => rfl
  | cons c rest ih =>
    by_cases hc : c.isWhitespace = true
    · cases prior <;> simp [squash, endsOpen, hc, ih]
    · simp [squash, endsOpen, hc, ih]

public theorem squash_congr (a b : List Char) :
    squash false (a ++ b) = squash false (squash false a ++ squash false b) := by
  rw [squash_append, squash_append, squash_idem, endsOpen_squash]
  cases endsOpen false a
  · rw [squash_idem]
  · rw [squash_open]

/-- Two white-space characters in a row read as the first. -/
public theorem squash_run (prior : Bool) (a b : List Char) (c d : Char)
    (hc : c.isWhitespace = true) (hd : d.isWhitespace = true) :
    squash prior (a ++ c :: d :: b) = squash prior (a ++ c :: b) := by
  rw [squash_append, squash_append]
  cases endsOpen prior a <;> simp [squash, hc, hd]

public theorem canon_append (a b : List Char) : canon (a ++ b) = canon a ++ canon b := by
  simp [canon]

public theorem keep_append (named : List Span) (a b : List (Char × Origin)) :
    keep named (a ++ b) = keep named a ++ keep named b := by
  simp [keep]

public theorem view_append (named : List Span) (a b : List (Char × Origin)) :
    view named (a ++ b) = squash false (view named a ++ view named b) := by
  simp only [view, norm, keep_append, canon_append]
  exact squash_congr _ _

public theorem view_congr (named : List Span) {a a' b b' : List (Char × Origin)}
    (ha : view named a = view named a') (hb : view named b = view named b') :
    view named (a ++ b) = view named (a' ++ b') := by
  rw [view_append, view_append, ha, hb]

/-- An engine space after an engine space reads as one. -/
public theorem view_space_run (named : List Span) (a b : List (Char × Origin)) :
    view named (a ++ (' ', .unplaced) :: (' ', .unplaced) :: b) =
      view named (a ++ (' ', .unplaced) :: b) := by
  simp only [view, norm, keep_append, canon_append]
  have h : ∀ l : List (Char × Origin), keep named ((' ', .unplaced) :: l) = ' ' :: keep named l :=
    fun l => by simp [keep]
  rw [h, h]
  have hs : canon (' ' :: ' ' :: keep named b) = ' ' :: ' ' :: canon (keep named b) := by
    simp [canon, spell]
  have hs' : canon (' ' :: keep named b) = ' ' :: canon (keep named b) := by
    simp [canon, spell]
  rw [hs, hs']
  exact squash_run false _ _ ' ' ' ' (by decide) (by decide)

public theorem keep_source (named : List Span) (s : Span) (w : String) :
    keep named (chars (.source s) w) =
      if named.any (Span.samePlace · s) then [] else w.toList := by
  cases h : named.any (Span.samePlace · s) <;>
    simp only [keep, chars, List.filterMap_map, Function.comp_def, h] <;> simp

/-- Two spellings TeX reads alike, from one source token, read alike. -/
public theorem view_token (named : List Span) (s : Span) {w w' : String}
    (h : canon w'.toList = canon w.toList) (a b : List (Char × Origin)) :
    view named (a ++ (chars (.source s) w' ++ b)) =
      view named (a ++ (chars (.source s) w ++ b)) := by
  simp only [view, norm, keep_append, canon_append, keep_source]
  split <;> simp [h]

/-- A named token's characters are excused. -/
public theorem view_named (named : List Span) (s : Span) (hs : s ∈ named)
    (l : List Char) (a b : List (Char × Origin)) :
    view named (a ++ (l.map (·, .source s) ++ b)) = view named (a ++ b) := by
  have hk : keep named (l.map (·, .source s)) = [] := by
    simp only [keep, List.filterMap_map, Function.comp_def]
    rw [List.filterMap_eq_nil_iff]
    intro c _
    have : named.any (Span.samePlace · s) = true :=
      List.any_eq_true.mpr ⟨s, hs, Span.samePlace_self s⟩
    simp [this]
  simp only [view, norm, keep_append, hk, List.nil_append]

@[simp] public theorem chars_empty (o : Origin) : chars o "" = [] := rfl

end Text

namespace Ir

mutual

/-- `plainTextList`'s characters onto `acc`, each from the innermost `.located` span holding it,
`o` outside any; a reference's, citation's or icon's words and a break's space are the engine's. -/
@[expose] public def locatedListOnto (o : Origin) (acc : Array (Char × Origin)) :
    List Inline → Array (Char × Origin)
  | [] => acc
  | x :: rest => locatedListOnto o (locatedOnto o acc x) rest

@[expose] public def locatedOnto (o : Origin) (acc : Array (Char × Origin)) (x : Inline) :
    Array (Char × Origin) :=
  match x with
  | .text s => acc ++ (Text.chars o s).toArray
  | .math _ src => acc ++ (Text.chars o (mathFloor src)).toArray
  | .formula _ _ body => acc ++ (Text.chars o (formulaFloor body)).toArray
  | .styled _ body => locatedListOnto o acc body.toList
  | .colored _ _ body => locatedListOnto o acc body.toList
  | .located span body => locatedListOnto (.source span) acc body.toList
  | .role _ body => locatedListOnto o acc body.toList
  | .link _ body => locatedListOnto o acc body.toList
  | .decorated _ body | .boxed _ body => locatedListOnto o acc body.toList
  | .onSteps _ body => locatedListOnto o acc body.toList
  | .altSteps _ firstPage otherPage =>
    locatedListOnto o (locatedListOnto o acc firstPage.toList) otherPage.toList
  | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _ | .pageNumber | .pageCount => acc
  | .image _ _ _ => acc
  | .icon _ label => acc ++ (Text.chars .engine label).toArray
  | .label _ => acc
  | .ref _ _ text _ => acc ++ (Text.chars .engine text).toArray
  | .cite _ keys => acc ++ (Text.chars .engine (citeMarks keys)).toArray
  | .cited _ _ ink => locatedListOnto o acc ink.toList
  | .footnote _ body => locatedListOnto o acc body.toList
  | .linebreak _ => acc.push (' ', .engine)

end

@[expose] public def locatedList (o : Origin) (xs : List Inline) : List (Char × Origin) :=
  (locatedListOnto o #[] xs).toList

@[expose] public def locatedOne (o : Origin) (x : Inline) : List (Char × Origin) :=
  (locatedOnto o #[] x).toList

/-- Inline content's characters with their origins. -/
@[expose] public def locatedText (xs : Array Inline) : List (Char × Origin) :=
  locatedList .unplaced xs.toList

mutual

private theorem locatedListOnto_acc (o : Origin) (acc : Array (Char × Origin)) :
    ∀ xs, locatedListOnto o acc xs = acc ++ locatedListOnto o #[] xs
  | [] => by simp [locatedListOnto]
  | x :: rest => by
    simp only [locatedListOnto]
    rw [locatedListOnto_acc o (locatedOnto o acc x) rest, locatedOnto_acc o acc x,
      locatedListOnto_acc o (locatedOnto o #[] x) rest, Array.append_assoc]

private theorem locatedOnto_acc (o : Origin) (acc : Array (Char × Origin)) (x : Inline) :
    locatedOnto o acc x = acc ++ locatedOnto o #[] x := by
  match x with
  | .text _ | .math _ _ | .formula _ _ _ | .icon _ _ | .ref _ _ _ _ | .cite _ _ =>
    simp [locatedOnto]
  | .linebreak _ => simp [locatedOnto]
  | .styled _ body | .colored _ _ body | .located _ body | .role _ body | .link _ body
  | .decorated _ body | .boxed _ body | .onSteps _ body | .cited _ _ body | .footnote _ body =>
    simp only [locatedOnto]
    exact locatedListOnto_acc _ acc body.toList
  | .altSteps _ a b =>
    simp only [locatedOnto]
    rw [locatedListOnto_acc o (locatedListOnto o acc a.toList) b.toList,
      locatedListOnto_acc o acc a.toList, locatedListOnto_acc o (locatedListOnto o #[] a.toList),
      Array.append_assoc]
  | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _ | .pageNumber | .pageCount
  | .image _ _ _ | .label _ => simp [locatedOnto]

end

@[simp] public theorem locatedList_nil (o : Origin) : locatedList o [] = [] := rfl

public theorem locatedList_cons (o : Origin) (x : Inline) (rest : List Inline) :
    locatedList o (x :: rest) = locatedOne o x ++ locatedList o rest := by
  simp only [locatedList, locatedOne, locatedListOnto]
  rw [locatedListOnto_acc, Array.toList_append]

@[simp] public theorem locatedOne_text (o : Origin) (s : String) :
    locatedOne o (.text s) = Text.chars o s := by
  simp [locatedOne, locatedOnto]

@[simp] public theorem locatedOne_located (o : Origin) (span : Span) (body : Array Inline) :
    locatedOne o (.located span body) = locatedList (.source span) body.toList := rfl

@[simp] public theorem locatedOne_role (o : Origin) (name : String) (body : Array Inline) :
    locatedOne o (.role name body) = locatedList o body.toList := rfl

mutual

private theorem locatedListOnto_erased (o : Origin) (acc : Array (Char × Origin)) :
    ∀ xs, (locatedListOnto o acc xs).toList.map (·.1) =
      acc.toList.map (·.1) ++ (plainTextList xs).toList
  | [] => by simp [locatedListOnto, plainTextList]
  | x :: rest => by
    simp only [locatedListOnto, plainTextList]
    rw [locatedListOnto_erased o _ rest, locatedOnto_erased o acc x]
    simp

private theorem locatedOnto_erased (o : Origin) (acc : Array (Char × Origin)) (x : Inline) :
    (locatedOnto o acc x).toList.map (·.1) = acc.toList.map (·.1) ++ (plainTextOne x).toList := by
  match x with
  | .text s | .math _ s | .icon _ s | .ref _ _ s _ =>
    simp [locatedOnto, plainTextOne, Text.chars, Function.comp_def]
  | .formula _ _ body | .cite _ body =>
    simp [locatedOnto, plainTextOne, Text.chars, Function.comp_def]
  | .linebreak _ => simp [locatedOnto, plainTextOne]
  | .styled _ body | .colored _ _ body | .located _ body | .role _ body | .link _ body
  | .decorated _ body | .boxed _ body | .onSteps _ body | .cited _ _ body | .footnote _ body =>
    simp only [locatedOnto, plainTextOne]
    exact locatedListOnto_erased _ acc body.toList
  | .altSteps _ a b =>
    simp only [locatedOnto, plainTextOne]
    rw [locatedListOnto_erased o _ b.toList, locatedListOnto_erased o acc a.toList]
    simp
  | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _ | .pageNumber | .pageCount
  | .image _ _ _ | .label _ => simp [locatedOnto, plainTextOne]

end

/-- Erasing the origins leaves `plainText`. -/
public theorem locatedText_erased (xs : Array Inline) :
    (locatedText xs).map (·.1) = (plainText xs).toList := by
  have h := locatedListOnto_erased .unplaced #[] xs.toList
  simpa [locatedText, locatedList, plainText] using h

public theorem locatedList_append (o : Origin) (a b : List Inline) :
    locatedList o (a ++ b) = locatedList o a ++ locatedList o b := by
  induction a with
  | nil => simp
  | cons x rest ih => simp [locatedList_cons, ih]

@[simp] public theorem locatedText_empty : locatedText #[] = [] := rfl

public theorem locatedText_push (xs : Array Inline) (x : Inline) :
    locatedText (xs.push x) = locatedText xs ++ locatedOne .unplaced x := by
  simp [locatedText, Array.toList_push, locatedList_append, locatedList_cons]

public theorem locatedText_append (xs ys : Array Inline) :
    locatedText (xs ++ ys) = locatedText xs ++ locatedText ys := by
  simp [locatedText, locatedList_append]

public theorem locatedText_mergeStep (out : Array Inline) (x : Inline) :
    locatedText (mergeStep out x) = locatedText out ++ locatedOne .unplaced x := by
  unfold mergeStep
  split
  · rename_i s t hb
    obtain ⟨ys, rfl⟩ := Array.back?_eq_some_iff.mp hb
    simp [Array.pop_push, locatedText_push, Text.chars]
  · simp [locatedText_push]

public theorem locatedText_mergeTexts (xs : Array Inline) :
    locatedText (mergeTexts xs) = locatedText xs := by
  have fold : ∀ (l : List Inline) (acc : Array Inline),
      locatedText (l.foldl mergeStep acc) = locatedText acc ++ locatedList .unplaced l := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons x rest ih =>
      intro acc
      simp [List.foldl, ih, locatedText_mergeStep, locatedList_cons]
  rw [mergeTexts, ← Array.foldl_toList, fold]
  simp [locatedText]

end Ir

namespace Parse

mutual

/-- The text slots of raws read in `file`, onto `acc`: a word's, symbol's (a tie as its no-break
space), formula's floor and verbatim's characters from their place, a space or break as a space,
and a group's or environment's body, an input's in its file; a control word sets none here. -/
@[expose] public def rawTextListOnto (file : String) (acc : Array (Char × Origin)) :
    List Raw → Array (Char × Origin)
  | [] => acc
  | r :: rest => rawTextListOnto file (rawTextOnto file acc r) rest

@[expose] public def rawTextOnto (file : String) (acc : Array (Char × Origin)) (r : Raw) :
    Array (Char × Origin) :=
  match r with
  | .word s p => acc ++ (Text.chars (.source ⟨file, p⟩) s).toArray
  | .space | .par _ => acc.push (' ', .unplaced)
  | .sym c p => acc.push (if c = '~' then '\u00a0' else c, .source ⟨file, p⟩)
  | .group body _ => rawTextListOnto file acc body.toList
  | .env name body _ => rawTextListOnto ((inputEnvFile? name).getD file) acc body.toList
  | .math _ body p => acc ++ (Text.chars (.source ⟨file, p⟩) (Ir.mathFloor (rawSrc body))).toArray
  | .verb _ v p => acc ++ (Text.chars (.source ⟨file, p⟩) v.text).toArray
  | .ctrl _ _ => acc

end

@[expose] public def rawTextList (file : String) (raws : List Raw) : List (Char × Origin) :=
  (rawTextListOnto file #[] raws).toList

@[expose] public def rawTextOne (file : String) (r : Raw) : List (Char × Origin) :=
  (rawTextOnto file #[] r).toList

@[expose] public def rawText (file : String) (raws : Array Raw) : List (Char × Origin) :=
  rawTextList file raws.toList

mutual

private theorem rawTextListOnto_acc (file : String) (acc : Array (Char × Origin)) :
    ∀ rs, rawTextListOnto file acc rs = acc ++ rawTextListOnto file #[] rs
  | [] => by simp [rawTextListOnto]
  | r :: rest => by
    simp only [rawTextListOnto]
    rw [rawTextListOnto_acc file (rawTextOnto file acc r) rest, rawTextOnto_acc file acc r,
      rawTextListOnto_acc file (rawTextOnto file #[] r) rest, Array.append_assoc]

private theorem rawTextOnto_acc (file : String) (acc : Array (Char × Origin)) (r : Raw) :
    rawTextOnto file acc r = acc ++ rawTextOnto file #[] r := by
  match r with
  | .word _ _ | .space | .par _ | .sym _ _ | .ctrl _ _ | .math _ _ _ | .verb _ _ _ =>
    simp [rawTextOnto]
  | .group body _ =>
    simp only [rawTextOnto]
    exact rawTextListOnto_acc file acc body.toList
  | .env name body _ =>
    simp only [rawTextOnto]
    exact rawTextListOnto_acc _ acc body.toList

end

@[simp] public theorem rawTextList_nil (file : String) : rawTextList file [] = [] := rfl

public theorem rawTextList_cons (file : String) (r : Raw) (rest : List Raw) :
    rawTextList file (r :: rest) = rawTextOne file r ++ rawTextList file rest := by
  simp only [rawTextList, rawTextOne, rawTextListOnto]
  rw [rawTextListOnto_acc, Array.toList_append]

@[simp] public theorem rawTextOne_word (file s : String) (p : Pos) :
    rawTextOne file (.word s p) = Text.chars (.source ⟨file, p⟩) s := by
  simp [rawTextOne, rawTextOnto]

@[simp] public theorem rawTextOne_space (file : String) :
    rawTextOne file .space = [(' ', .unplaced)] := rfl

@[simp] public theorem rawTextOne_par (file : String) (p : Pos) :
    rawTextOne file (.par p) = [(' ', .unplaced)] := rfl

@[simp] public theorem rawTextOne_sym (file : String) (c : Char) (p : Pos) :
    rawTextOne file (.sym c p) = [(if c = '~' then '\u00a0' else c, .source ⟨file, p⟩)] := rfl

@[simp] public theorem rawTextOne_group (file : String) (body : Array Raw) (p : Pos) :
    rawTextOne file (.group body p) = rawTextList file body.toList := rfl

@[simp] public theorem rawTextOne_env (file name : String) (body : Array Raw) (p : Pos) :
    rawTextOne file (.env name body p) =
      rawTextList ((inputEnvFile? name).getD file) body.toList := rfl

end Parse

end LeanTex.Core
