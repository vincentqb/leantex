module

public import LeanTex.Core.Html
public import LeanTex.Core.HtmlRead
import all LeanTex.Core.Html
import all LeanTex.Core.HtmlRead

/-! The HTML parser's reading of a rendered page is the rendered tree: tokenizing and building
the characters `Html.document` writes yields the typed tree with the renderer's whitespace as
text, its names lower-cased, under a condition on the tree the corpus checks. -/

namespace LeanTex.Core.Html

open HtmlRead

/-! ### Definitions: the renderer as characters, the condition read, the tree read -/

/-- An indentation's spaces. -/
@[expose] public def padL (i : Nat) : List Char := List.replicate (2 * i) ' '

/-- One attribute as the renderer writes it. -/
def attrL (kv : String × String) : List Char :=
  if kv.2.isEmpty then ' ' :: kv.1.toList
  else ' ' :: kv.1.toList ++ '=' :: '"' :: escapeAttr.go kv.2.toList ++ ['"']

/-- The attributes as the renderer writes them. -/
def attrsL (attrs : List (String × String)) : List Char := attrs.flatMap attrL

/-- Whether an element's children render inline. -/
public def inl (tag : String) (kids : Array Node) : Bool :=
  preserveTags.contains tag || phrasingTags.contains tag || isInlineOnly kids

/-- An end tag as written. -/
def closeL (tag : String) : List Char := '<' :: '/' :: tag.toList ++ ['>']

mutual

/-- A node's characters at an indentation, as `renderInto` appends them. -/
def rB : Node → Nat → List Char
  | .text s, i => padL i ++ escapeText.go s.toList ++ ['\n']
  | .style css, i =>
    padL i ++ "<style>\n".toList ++ (rawPayload "</style" css).toList ++ '\n' :: padL i ++
      closeL "style" ++ ['\n']
  | .script attrs js, i =>
    padL i ++ "<script".toList ++ attrsL attrs.toList ++ ">\n".toList ++
      (rawPayload "</script" js).toList ++ '\n' :: padL i ++ closeL "script" ++ ['\n']
  | .elem tag attrs kids, i =>
    if voidTags.contains tag then
      padL i ++ '<' :: tag.toList ++ attrsL attrs.toList ++ ['>'] ++ ['\n']
    else if inl tag kids then
      padL i ++ '<' :: tag.toList ++ attrsL attrs.toList ++ ['>'] ++ (lfGuard tag kids).toList ++
        rIL [] kids.toList ++ closeL tag ++ ['\n']
    else
      padL i ++ '<' :: tag.toList ++ attrsL attrs.toList ++ ['>'] ++ ['\n'] ++
        rBL [] kids.toList (i + 1) ++ padL i ++ closeL tag ++ ['\n']

/-- A node's characters inline, as `inlineRenderInto` appends them. -/
def rI : Node → List Char
  | .text s => escapeText.go s.toList
  | .style css => "<style>".toList ++ (rawPayload "</style" css).toList ++ closeL "style"
  | .script attrs js =>
    "<script".toList ++ attrsL attrs.toList ++ ['>'] ++ (rawPayload "</script" js).toList ++
      closeL "script"
  | .elem tag attrs kids =>
    if voidTags.contains tag then '<' :: tag.toList ++ attrsL attrs.toList ++ ['>']
    else '<' :: tag.toList ++ attrsL attrs.toList ++ ['>'] ++ (lfGuard tag kids).toList ++
      (rIL [] kids.toList ++ closeL tag)

/-- Nodes' characters at an indentation after `acc`. -/
def rBL (acc : List Char) : List Node → Nat → List Char
  | [], _ => acc
  | n :: rest, i => rBL (acc ++ rB n i) rest i

/-- Nodes' characters inline after `acc`. -/
def rIL (acc : List Char) : List Node → List Char
  | [] => acc
  | n :: rest => rIL (acc ++ rI n) rest

end

/-- The reading of characters from a state, as `parse` folds them. -/
def run (o : Option St) (cs : List Char) : Option St := cs.foldl (fun o c => o.bind (step · c)) o

/-- The builder with its current node's children rewritten. -/
def withTop (b : Builder) (g : Array Dom → Array Dom) : Builder :=
  match b.stack with
  | f :: rest => { b with stack := { f with kids := g f.kids } :: rest }
  | [] => b

/-- Two stacks with the same elements, children aside. -/
def sameShape : List Frame → List Frame → Prop
  | [], [] => True
  | f :: s, g :: t => f.ns = g.ns ∧ f.tag = g.tag ∧ f.attrs = g.attrs ∧ sameShape s t
  | _, _ => False

/-- The modes past the document's start, where a character is kept or refused. -/
def Late (m : Mode) : Prop := m ≠ .initial ∧ m ≠ .beforeHtml ∧ m ≠ .beforeHead

/-- Where escaped text is read: the data state, or a title's RCDATA. -/
inductive Home where
  | data
  | rcdata (n : String)

def Home.tok : Home → TState
  | .data => .data
  | .rcdata n => .raw .rcdata n

def Home.ret : Home → RefRet
  | .data => .data
  | .rcdata n => .rcdata n

/-- Characters inserted one by one at the current node. -/
@[expose] public def addL (kids : Array Dom) (cs : List Char) : Array Dom := cs.foldl addChar kids

/-- A character the tokenizer keeps inside a tag name. -/
@[expose] public def nameChar (c : Char) : Bool :=
  !isWs c && c != '/' && c != '>' && c != '\x00' && c != '\r'

/-- A tag name the tokenizer reads as one name: a letter, then name characters. -/
@[expose] public def validTag (tag : String) : Bool :=
  match tag.toList with
  | c :: rest => isAlpha c && rest.all nameChar
  | [] => false

/-- A character the tokenizer keeps inside an attribute name. -/
@[expose] public def keyChar (c : Char) : Bool :=
  nameChar c && c != '=' && c != '"' && c != '\'' && c != '<'

/-- Attributes the tokenizer reads back as written: names it reads as one name, distinct once
lower-cased, and values without a null. -/
@[expose] public def validAttrs (attrs : Array (String × String)) : Bool :=
  attrs.all (fun kv => !kv.1.isEmpty && kv.1.toList.all keyChar &&
    kv.2.toList.all (fun c => c != '\x00' && c != '\r')) &&
    decide (attrs.toList.map (fun kv => lower kv.1)).Nodup

/-- Attributes as the parser stores them: names lower-cased. -/
@[expose] public def lowAttrs (attrs : Array (String × String)) : Array (String × String) :=
  attrs.map fun kv => (lower kv.1, kv.2)

/-- The tag a state ends with when `>` follows: a name, a finished value, or a name with no value. -/
def readyTag : TState → Option TagTok
  | .tagName t => some t
  | .afterAttrValue t => some t
  | .attrName t k => some (t.add k "")
  | _ => none

/-- The tokenizer state a builder's content leaves after a start tag. -/
def after (c : Content) (name : String) (next : TState) : TState :=
  match c with
  | .data => next
  | k => .raw k name

/-- A builder reading a raw element's content: past the document's start, its current node the
element, no line feed pending. -/
structure InText (b : Builder) : Prop where
  text : inText b.stack = true
  late : Late b.mode
  nonempty : b.stack ≠ []
  noLF : b.dropLF = false

/-- The characters a raw-text state holds back: none, a `<`, or a partial end tag. -/
def pendOf : TState → List Char
  | .rawLt _ _ => ['<']
  | .rawEnd _ _ seen => '<' :: '/' :: seen.toList
  | _ => []

/-- A raw-text state after a prefix: the characters emitted and those held back make it up. -/
structure RawInv (k : Content) (n : String) (σ : TState) (e pre : List Char) : Prop where
  shape : σ = .raw k n ∨ σ = .rawLt k n ∨ ∃ seen, σ = .rawEnd k n seen
  pend : e ++ pendOf σ = pre

/-- The names of raw elements: lower-case ASCII letters. -/
def rawName (n : String) : Bool := n.toList.all (fun c => 'a' ≤ c && c ≤ 'z')

/-- A raw payload the tokenizer reads back inside its element: no null and no carriage return,
and in a script no `<!`, which opens the script's escaped states. -/
@[expose] public def payloadOk (script : Bool) (p : String) : Bool :=
  p.toList.all (fun c => c != '\x00' && c != '\r') &&
    !(script && decide (['<', '!'] <:+: p.toList))

/-- Whether a mode's start-tag rules insert an element named `t` as written. -/
@[expose] public def startOk (m : Mode) (s : List Frame) (t : String)
    (attrs : Array (String × String)) : Bool :=
  match m with
  | .inHead => headTags.contains t
  | .inBody => startAccepts s t attrs
  | _ => false

/-- The namespace an element is read in under a mode. -/
@[expose] public def nsIn (m : Mode) (s : List Frame) (t : String) : Ns :=
  if m == .inHead then .html else nsFor s t

mutual

/-- Whether the parser reads a node, rendered under a mode at this stack, as the stack builder
it is: every start tag inserted as written, every text kept, every raw payload ended only by its
own end tag, and no void element given children. -/
public def Accepts (m : Mode) (s : List Frame) : Node → Bool
  | .text t => t.toList.all fun c => c != '\r' && c != '\x00' && charKeeps m s c
  | .style css =>
    htmlContext s && startOk m s "style" #[] && payloadOk false (rawPayload "</style" css)
  | .script attrs js =>
    htmlContext s && validAttrs attrs && startOk m s "script" (lowAttrs attrs) &&
      payloadOk true (rawPayload "</script" js)
  | .elem tag attrs kids =>
    let t := lower tag
    let ns := nsIn m s t
    validTag tag && validAttrs attrs && !["html", "head", "body"].contains t &&
      startOk m s t (lowAttrs attrs) &&
      (HtmlRead.voidTags.contains t && ns == .html) == Html.voidTags.contains tag &&
      (ns != .html || t == tag) && (ns == .html || !lfTags.contains tag) &&
      (if Html.voidTags.contains tag then kids.isEmpty
       else match contentOf ns t with
         | .data => AcceptsList m (⟨ns, t, lowAttrs attrs, #[]⟩ :: s) kids.toList
         | .rcdata => kids.toList.all fun k => match k with
           | .text x => x.toList.all fun c => c != '\x00' && c != '\r'
           | _ => false
         | _ => false)

public def AcceptsList (m : Mode) (s : List Frame) : List Node → Bool
  | [] => true
  | n :: rest => Accepts m s n && AcceptsList m s rest

end

mutual

/-- The children a block-rendered node leaves at its parent: its indentation and line end as
text, its element with names lower-cased, a raw payload as its one text child. -/
public def fB (K : Array Dom) : Node → Nat → Array Dom
  | .text t, i => addL K (padL i ++ t.toList ++ ['\n'])
  | .style css, i =>
    addL ((addL K (padL i)).push
      (.elem "style" #[] (addL #[] ('\n' :: (rawPayload "</style" css).toList ++ '\n' :: padL i))))
      ['\n']
  | .script attrs js, i =>
    addL ((addL K (padL i)).push
      (.elem "script" (lowAttrs attrs)
        (addL #[] ('\n' :: (rawPayload "</script" js).toList ++ '\n' :: padL i)))) ['\n']
  | .elem tag attrs kids, i =>
    addL ((addL K (padL i)).push (.elem (lower tag) (lowAttrs attrs)
      (if Html.voidTags.contains tag then #[]
       else if inl tag kids then fIL #[] kids.toList
       else addL (fBL (addL #[] ['\n']) kids.toList (i + 1)) (padL i)))) ['\n']

/-- The children an inline-rendered node leaves at its parent. -/
public def fI (K : Array Dom) : Node → Array Dom
  | .text t => addL K t.toList
  | .style css => K.push (.elem "style" #[] (addL #[] (rawPayload "</style" css).toList))
  | .script attrs js =>
    K.push (.elem "script" (lowAttrs attrs) (addL #[] (rawPayload "</script" js).toList))
  | .elem tag attrs kids =>
    K.push (.elem (lower tag) (lowAttrs attrs)
      (if Html.voidTags.contains tag then #[] else fIL #[] kids.toList))

public def fBL (K : Array Dom) : List Node → Nat → Array Dom
  | [], _ => K
  | n :: rest, i => fBL (fB K n i) rest i

public def fIL (K : Array Dom) : List Node → Array Dom
  | [] => K
  | n :: rest => fIL (fI K n) rest

end

/-- A builder in a mode the rendered tree's parts are read in: the head or the body, with an
open element. -/
structure InFlow (b : Builder) : Prop where
  mode : b.mode = .inBody ∨ b.mode = .inHead
  nonempty : b.stack ≠ []

/-- The facts an accepted element's reading uses. -/
structure ElemOk (m : Mode) (s : List Frame) (tag : String) (attrs : Array (String × String))
    (kids : Array Node) : Prop where
  vtag : validTag tag = true
  vattrs : validAttrs attrs = true
  skel : lower tag ≠ "html" ∧ lower tag ≠ "head" ∧ lower tag ≠ "body"
  start : startOk m s (lower tag) (lowAttrs attrs) = true
  void : (HtmlRead.voidTags.contains (lower tag) && nsIn m s (lower tag) == .html) =
    Html.voidTags.contains tag
  same : nsIn m s (lower tag) ≠ .html ∨ lower tag = tag
  lf : nsIn m s (lower tag) = .html ∨ lfTags.contains tag = false
  kidsOk : (if Html.voidTags.contains tag then kids.isEmpty
       else match contentOf (nsIn m s (lower tag)) (lower tag) with
         | .data => AcceptsList m (⟨nsIn m s (lower tag), lower tag, lowAttrs attrs, #[]⟩ :: s) kids.toList
         | .rcdata => kids.toList.all fun k => match k with
           | .text x => x.toList.all fun c => c != '\x00' && c != '\r'
           | _ => false
         | _ => false) = true

/-- Whether a node is text a title's RCDATA reads back. -/
def rcText : Node → Bool
  | .text x => x.toList.all fun c => c != '\x00' && c != '\r'
  | _ => false

/-- The characters of a node when it is text. -/
def textOf : Node → List Char
  | .text x => x.toList
  | .style _ | .script _ _ | .elem .. => []

/-- The characters of a list's text nodes. -/
def textsOf (l : List Node) : List Char := l.flatMap textOf

/-- The `html` element's frame, its language as written. -/
@[expose] public def htmlFrame (lang : String) : Frame := ⟨.html, "html", #[("lang", lang)], #[]⟩

@[expose] public def headFrame : Frame := ⟨.html, "head", #[], #[]⟩

@[expose] public def bodyFrame : Frame := ⟨.html, "body", #[], #[]⟩

/-- Whether a page's language, head and body read back as the stack builder they are. -/
@[expose] public def DocOk (lang : String) (head body : Array Node) : Bool :=
  lang.toList.all (fun c => c != '\x00' && c != '\r') &&
    AcceptsList .inHead [headFrame, htmlFrame lang] head.toList &&
    AcceptsList .inBody [bodyFrame, htmlFrame lang] body.toList

/-- The children an element of the document's skeleton reads as. -/
public def fKids (tag : String) (kids : Array Node) (i : Nat) : Array Dom :=
  if inl tag kids then fIL #[] kids.toList
  else addL (fBL (addL #[] ['\n']) kids.toList (i + 1)) (padL i)

/-- The document the parser builds from a rendered page: the head, the whitespace after it, and
the body, which also takes the line ends after its own end tag and the document's. -/
public def fDoc (lang : String) (head body : Array Node) : Dom :=
  .elem "html" #[("lang", lang)]
    #[.elem "head" #[] (fKids "head" head 1), .text "\n  ",
      .elem "body" #[] (addL (fKids "body" body 1) ['\n', '\n'])]

/-- The body's text as the parser reads it: `fKids`'s characters, with the two line ends after
the body's end tag. -/
@[expose] public def bodyChars (body : Array Node) : String :=
  Dom.charsList (addL (fKids "body" body 1) ['\n', '\n']).toList

mutual

/-- The characters a tree's text nodes hold, outside style sheets and scripts. -/
@[expose] public def Node.ink : Node → List Char
  | .text s => s.toList
  | .style _ => []
  | .script _ _ => []
  | .elem tag _ kids =>
    if lower tag == "style" || lower tag == "script" then [] else Node.inkInto [] kids.toList

/-- The characters nodes' text holds, in order, after `acc`. -/
@[expose] public def Node.inkInto (acc : List Char) : List Node → List Char
  | [] => acc
  | n :: rest => Node.inkInto (acc ++ Node.ink n) rest

end

/-- The characters nodes' text holds, in order, outside style sheets and scripts. -/
@[expose] public def Node.inkList (l : List Node) : List Char := Node.inkInto [] l

/-- A character the page's text keeps once white space is set aside. -/
@[expose] public def inked (c : Char) : Bool := !isWs c

/-! ### The renderer as characters -/

theorem pushn_toList (s : String) (c : Char) (n : Nat) :
    (s.pushn c n).toList = s.toList ++ List.replicate n c := by
  rw [String.pushn_eq_repeat_push]
  induction n with
  | zero => simp [Nat.repeat]
  | succ n ih => simp [Nat.repeat, String.toList_push, ih, List.replicate_succ']

theorem pad_toList (i : Nat) : ("".pushn ' ' (2 * i)).toList = padL i := by
  simp [pushn_toList, padL]

theorem attrsInto_toList (acc : String) (attrs : Array (String × String)) :
    (attrsInto acc attrs).toList = acc.toList ++ attrsL attrs.toList := by
  unfold attrsInto
  rw [← Array.foldl_toList]
  generalize attrs.toList = l
  induction l generalizing acc with
  | nil => simp [attrsL]
  | cons kv rest ih =>
    obtain ⟨k, v⟩ := kv
    simp only [List.foldl_cons]
    rw [ih]
    simp only [attrsL, List.flatMap_cons, attrL, ← List.append_assoc]
    congr 1
    split <;> simp [String.toList_append, escapeAttr_spec, String.toList_ofList]

theorem rBL_acc (l : List Node) (i : Nat) : ∀ acc, rBL acc l i = acc ++ rBL [] l i := by
  induction l with
  | nil => intro acc; simp [rBL]
  | cons n rest ih =>
    intro acc
    simp only [rBL]
    rw [ih (acc ++ rB n i), ih ([] ++ rB n i)]
    simp

theorem rIL_acc (l : List Node) : ∀ acc, rIL acc l = acc ++ rIL [] l := by
  induction l with
  | nil => intro acc; simp [rIL]
  | cons n rest ih =>
    intro acc
    simp only [rIL]
    rw [ih (acc ++ rI n), ih ([] ++ rI n)]
    simp

theorem rBL_cons (n : Node) (rest : List Node) (i : Nat) :
    rBL [] (n :: rest) i = rB n i ++ rBL [] rest i := by
  rw [rBL, rBL_acc, List.nil_append]

theorem rIL_cons (n : Node) (rest : List Node) : rIL [] (n :: rest) = rI n ++ rIL [] rest := by
  rw [rIL, rIL_acc, List.nil_append]

mutual

theorem renderInto_toList (acc : String) : (n : Node) → (i : Nat) →
    acc.toList ++ rB n i = (renderInto acc n i).toList
  | .text s, i => by
    simp [renderInto, rB, String.toList_append, pad_toList, escapeText_spec, String.toList_ofList]
  | .style css, i => by
    simp [renderInto, rB, String.toList_append, pad_toList, closeL]
  | .script attrs js, i => by
    simp [renderInto, rB, String.toList_append, pad_toList, attrsInto_toList, closeL]
  | .elem tag attrs kids, i => by
    unfold renderInto
    by_cases hv : voidTags.contains tag = true
    · have hv' : tag ∈ voidTags := by simpa using hv
      simp [rB, hv', String.toList_append, pad_toList, attrsInto_toList]
    · have hv' : tag ∉ voidTags := by simpa using hv
      by_cases hi : (preserveTags.contains tag || phrasingTags.contains tag || isInlineOnly kids) = true
      · have hinl : inl tag kids = true := hi
        simp only [hv, hi, ite_true, Bool.false_eq_true, ite_false, String.toList_append,
          inlineRenderListInto_toList _ kids.toList, attrsInto_toList, pad_toList]
        simp [rB, hv', hinl, closeL]
      · have hinl : inl tag kids = false := by simpa [inl] using hi
        simp only [hv, hi, Bool.false_eq_true, ite_false, String.toList_append,
          renderListInto_toList _ kids.toList (i + 1), attrsInto_toList, pad_toList]
        simp [rB, hv', hinl, closeL]

theorem inlineRenderInto_toList (acc : String) : (n : Node) →
    acc.toList ++ rI n = (inlineRenderInto acc n).toList
  | .text s => by
    simp [inlineRenderInto, rI, String.toList_append, escapeText_spec, String.toList_ofList]
  | .style css => by simp [inlineRenderInto, rI, String.toList_append, closeL]
  | .script attrs js => by
    simp [inlineRenderInto, rI, String.toList_append, attrsInto_toList, closeL]
  | .elem tag attrs kids => by
    unfold inlineRenderInto
    by_cases hv : voidTags.contains tag = true
    · have hv' : tag ∈ voidTags := by simpa using hv
      simp [rI, hv', String.toList_append, attrsInto_toList]
    · have hv' : tag ∉ voidTags := by simpa using hv
      simp only [hv, Bool.false_eq_true, ite_false, String.toList_append,
        inlineRenderListInto_toList _ kids.toList, attrsInto_toList]
      simp [rI, hv', closeL]

theorem renderListInto_toList (acc : String) : (l : List Node) → (i : Nat) →
    (renderListInto acc l i).toList = acc.toList ++ rBL [] l i
  | [], _ => by simp [renderListInto, rBL]
  | n :: rest, i => by
    rw [renderListInto, renderListInto_toList _ rest i, ← renderInto_toList acc n i, rBL_cons]
    simp

theorem inlineRenderListInto_toList (acc : String) : (l : List Node) →
    (inlineRenderListInto acc l).toList = acc.toList ++ rIL [] l
  | [] => by simp [inlineRenderListInto, rIL]
  | n :: rest => by
    rw [inlineRenderListInto, inlineRenderListInto_toList _ rest, ← inlineRenderInto_toList acc n,
      rIL_cons]
    simp

end

/-! ### The reader over characters -/

theorem run_append (o : Option St) (a b : List Char) : run o (a ++ b) = run (run o a) b := by
  simp [run, List.foldl_append]

theorem run_none (cs : List Char) : run none cs = none := by
  induction cs with
  | nil => rfl
  | cons c rest ih => simpa [run] using ih

theorem run_nil (o : Option St) : run o [] = o := rfl

theorem run_cons (s : St) (c : Char) (cs : List Char) :
    run (some s) (c :: cs) = run (step s c) cs := by
  simp [run]

theorem withTop_comp (b : Builder) (g h : Array Dom → Array Dom) :
    withTop (withTop b g) h = withTop b (h ∘ g) := by
  unfold withTop
  cases hs : b.stack <;> simp [hs]

theorem withTop_mode (b : Builder) (g : Array Dom → Array Dom) : (withTop b g).mode = b.mode := by
  unfold withTop; cases b.stack <;> rfl

theorem withTop_dropLF (b : Builder) (g : Array Dom → Array Dom) :
    (withTop b g).dropLF = b.dropLF := by
  unfold withTop; cases b.stack <;> rfl

theorem withTop_id (b : Builder) (g : Array Dom → Array Dom) (hg : ∀ k, g k = k) :
    withTop b g = b := by
  rcases b with ⟨m, st, d⟩
  cases st <;> simp [withTop, hg]

theorem sameShape_refl : (s : List Frame) → sameShape s s
  | [] => trivial
  | _ :: s => ⟨rfl, rfl, rfl, sameShape_refl s⟩

theorem withTop_shape (b : Builder) (g : Array Dom → Array Dom) :
    sameShape (withTop b g).stack b.stack := by
  unfold withTop
  cases h : b.stack with
  | nil => simp [h, sameShape]
  | cons f rest => exact ⟨rfl, rfl, rfl, sameShape_refl rest⟩

theorem currentIs_shape (names : List String) {s t : List Frame} (h : sameShape s t) :
    currentIs names s = currentIs names t := by
  cases s <;> cases t <;> simp_all [sameShape, currentIs]

theorem charKeeps_shape (m : Mode) (c : Char) {s t : List Frame} (h : sameShape s t) :
    charKeeps m s c = charKeeps m t c := by
  simp [charKeeps, inText, inTableMode, currentIs_shape _ h]

theorem char_keeps (b : Builder) (c : Char) (hm : Late b.mode) (hs : b.stack ≠ [])
    (hk : charKeeps b.mode b.stack c = true) : char b c = some (withTop b (addChar · c)) := by
  obtain ⟨h1, h2, h3⟩ := hm
  cases hst : b.stack with
  | nil => exact absurd hst hs
  | cons f rest =>
    have hi : insertChar b c = some (withTop b (addChar · c)) := by
      simp [insertChar, withTop, hst]
    unfold char
    split
    · exact absurd ‹_› h1
    · exact absurd ‹_› h2
    · exact absurd ‹_› h3
    · rw [hk]; simpa using hi

theorem dropLF_false (b : Builder) (h : b.dropLF = false) : { b with dropLF := false } = b := by
  cases b; simp_all

theorem emit_char' (s : St) (c : Char) (next : TState) (b' : Builder)
    (hb : s.build.dropLF = true → c ≠ '\n') (hc : char { s.build with dropLF := false } c = some b') :
    emit s (.char c) next = some ⟨next, b'⟩ := by
  have : (s.build.dropLF && c == '\n') = false := by
    cases h : s.build.dropLF
    · rfl
    · simpa using hb h
  simp [emit, HtmlRead.build, this, hc]

theorem emit_char (s : St) (c : Char) (next : TState) (b' : Builder)
    (hb : s.build.dropLF = false) (hc : char s.build c = some b') :
    emit s (.char c) next = some ⟨next, b'⟩ :=
  emit_char' s c next b' (by simp [hb]) (by rw [dropLF_false _ hb]; exact hc)

theorem step_data (b : Builder) (c : Char) (h1 : c ≠ '<') (h2 : c ≠ '&') :
    step ⟨.data, b⟩ c = emit ⟨.data, b⟩ (.char c) .data := by
  simp [step, h1, h2]

theorem run_refName (b : Builder) (ret : RefRet) (name : List Char)
    (hname : name.all isAlnum = true) (hne : name ≠ []) : ∀ pre,
    run (some ⟨.ref ret pre, b⟩) (name ++ [';']) =
      (named (String.ofList (pre ++ name))).bind (deliver ⟨.ref ret (pre ++ name), b⟩ ret) := by
  induction name with
  | nil => exact absurd rfl hne
  | cons a rest ih =>
    intro pre
    simp only [List.all_cons, Bool.and_eq_true] at hname
    have ha : isAlnum a = true := hname.1
    have hah : a ≠ '#' := by rintro rfl; simp [isAlnum, isAlpha] at ha
    have hpre : step ⟨.ref ret pre, b⟩ a = some ⟨.ref ret (pre ++ [a]), b⟩ := by
      simp [step, ha, hah]
    rw [List.cons_append, run_cons, hpre]
    cases rest with
    | nil =>
      simp only [List.nil_append, run_cons, run_nil]
      simp [step, isAlnum, isAlpha]
    | cons a2 rest2 =>
      rw [ih hname.2 (by simp) (pre ++ [a])]
      simp [List.append_assoc]

theorem run_named (b : Builder) (ret : RefRet) (name : List Char) (r : String)
    (hname : name.all isAlnum = true) (hne : name ≠ []) (hr : named (String.ofList name) = some r) :
    run (some ⟨.ref ret [], b⟩) (name ++ [';']) = deliver ⟨.ref ret name, b⟩ ret r := by
  rw [run_refName b ret name hname hne []]
  simp [hr]

theorem run_numeric (b : Builder) (ret : RefRet) (d1 d2 : Char) (ch : Char)
    (h1 : (digitVal false d1).isSome = true) (h2 : (digitVal false d2).isSome = true)
    (hn : numeric (digitsValue false [d1, d2]) = some ch) :
    run (some ⟨.ref ret [], b⟩) ['#', d1, d2, ';'] =
      deliver ⟨.numRef ret false [d1, d2], b⟩ ret (String.singleton ch) := by
  have hx1 : d1 ≠ 'x' ∧ d1 ≠ 'X' := by
    constructor <;> rintro rfl <;> simp [digitVal] at h1
  have s1 : step ⟨.ref ret [], b⟩ '#' = some ⟨.numRef ret false [], b⟩ := by simp [step]
  have s2 : step ⟨.numRef ret false [], b⟩ d1 = some ⟨.numRef ret false [d1], b⟩ := by
    simp [step, hx1, h1]
  have s3 : step ⟨.numRef ret false [d1], b⟩ d2 = some ⟨.numRef ret false [d1, d2], b⟩ := by
    simp [step, h2]
  have s4 : step ⟨.numRef ret false [d1, d2], b⟩ ';' =
      deliver ⟨.numRef ret false [d1, d2], b⟩ ret (String.singleton ch) := by
    simp [step, digitVal, hn]
  rw [run_cons, s1, run_cons, s2, run_cons, s3, run_cons, s4, run_nil]

theorem step_home_ref (h : Home) (b : Builder) : step ⟨h.tok, b⟩ '&' = some ⟨.ref h.ret [], b⟩ := by
  cases h <;> simp [step, Home.tok, Home.ret]

theorem step_home_char (h : Home) (b : Builder) (c : Char) (h1 : c ≠ '<') (h2 : c ≠ '&')
    (h3 : c ≠ '\x00') : step ⟨h.tok, b⟩ c = emit ⟨h.tok, b⟩ (.char c) h.tok := by
  cases h <;> simp [step, Home.tok, h1, h2, h3]

theorem deliver_home (h : Home) (s : St) (c : Char) (b' : Builder)
    (hb : s.build.dropLF = true → c ≠ '\n')
    (hc : char { s.build with dropLF := false } c = some b') :
    deliver s h.ret (String.singleton c) = some ⟨h.tok, b'⟩ := by
  cases h <;> simp [deliver, Home.ret, Home.tok, emitChars, emit_char' s c _ b' hb hc]

theorem run_escChar (h : Home) (b : Builder) (c : Char) (hb : b.dropLF = true → c ≠ '\n')
    (hm : Late b.mode) (hs : b.stack ≠ []) (hk : charKeeps b.mode b.stack c = true)
    (hn : c ≠ '\x00') :
    run (some ⟨h.tok, b⟩) (escapeCharText c) =
      some ⟨h.tok, withTop { b with dropLF := false } (addChar · c)⟩ := by
  have hch := char_keeps { b with dropLF := false } c hm hs hk
  unfold escapeCharText
  by_cases ha : c = '&'
  · subst ha
    have e : "&amp;".toList = '&' :: ['a', 'm', 'p'] ++ [';'] := rfl
    rw [ite_eq_left (by decide), e, List.cons_append, run_cons, step_home_ref,
      run_named b h.ret ['a', 'm', 'p'] "&" (by decide) (by simp) (by simp [named])]
    exact deliver_home h _ '&' _ hb hch
  · by_cases hl : c = '<'
    · subst hl
      have e : "&lt;".toList = '&' :: ['l', 't'] ++ [';'] := rfl
      rw [ite_eq_right (by decide), ite_eq_left (by decide), e, List.cons_append, run_cons, step_home_ref,
        run_named b h.ret ['l', 't'] "<" (by decide) (by simp) (by simp [named])]
      exact deliver_home h _ '<' _ hb hch
    · by_cases hg : c = '>'
      · subst hg
        have e : "&gt;".toList = '&' :: ['g', 't'] ++ [';'] := rfl
        rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left (by decide), e, List.cons_append, run_cons,
          step_home_ref, run_named b h.ret ['g', 't'] ">" (by decide) (by simp) (by simp [named])]
        exact deliver_home h _ '>' _ hb hch
      · rw [ite_eq_right (by simpa using ha), ite_eq_right (by simpa using hl), ite_eq_right (by simpa using hg),
          run_cons, step_home_char h b c hl ha hn, emit_char' _ c _ _ hb hch, run_nil]

theorem run_escText (h : Home) (s : List Char) : ∀ (b : Builder), b.dropLF = false →
    Late b.mode → b.stack ≠ [] → (∀ c ∈ s, charKeeps b.mode b.stack c = true ∧ c ≠ '\x00') →
    run (some ⟨h.tok, b⟩) (escapeText.go s) = some ⟨h.tok, withTop b (addL · s)⟩ := by
  induction s with
  | nil =>
    intro b _ _ _ _
    have : withTop b (addL · []) = b := withTop_id b _ (fun _ => rfl)
    simp [escapeText.go, run_nil, this]
  | cons c rest ih =>
    intro b hb hm hs hk
    have hc := hk c (by simp)
    rw [escapeText.go, run_append, run_escChar h b c (by simp [hb]) hm hs hc.1 hc.2,
      dropLF_false _ hb]
    have hshape := withTop_shape b (addChar · c)
    rw [ih (withTop b (addChar · c)) (by rw [withTop_dropLF]; exact hb)
      (by rw [withTop_mode]; exact hm)
      (by unfold withTop; cases hst : b.stack <;> simp_all)
      (fun d hd => by
        rw [withTop_mode, charKeeps_shape _ _ hshape]
        exact hk d (by simp [hd])), withTop_comp]
    rfl

theorem withTop_dropLF_comm (b : Builder) (g : Array Dom → Array Dom) (d : Bool) :
    withTop { b with dropLF := d } g = { withTop b g with dropLF := d } := by
  rcases b with ⟨m, st, d0⟩
  cases st <;> rfl

/-- Escaped text read where a dropped line feed may be pending, the text not opening with one. -/
theorem run_escText' (h : Home) (s : List Char) (b : Builder)
    (hb : b.dropLF = true → s.head? ≠ some '\n') (hm : Late b.mode) (hs : b.stack ≠ [])
    (hk : ∀ c ∈ s, charKeeps b.mode b.stack c = true ∧ c ≠ '\x00') :
    run (some ⟨h.tok, b⟩) (escapeText.go s) =
      some ⟨h.tok, withTop { b with dropLF := b.dropLF && s.isEmpty } (addL · s)⟩ := by
  cases s with
  | nil => simp [escapeText.go, run_nil, withTop_id _ _ (fun _ => rfl), addL]
  | cons c rest =>
    have hc := hk c (by simp)
    rw [escapeText.go, run_append, run_escChar h b c (fun h1 => by simpa using hb h1) hm hs hc.1 hc.2]
    have hshape := withTop_shape { b with dropLF := false } (addChar · c)
    rw [run_escText h rest (withTop { b with dropLF := false } (addChar · c))
      (by rw [withTop_dropLF])
      (by rw [withTop_mode]; exact hm)
      (by unfold withTop; cases hst : b.stack <;> simp_all)
      (fun d hd => by
        rw [withTop_mode, charKeeps_shape _ _ hshape]
        exact hk d (by simp [hd])), withTop_comp]
    simp only [List.isEmpty_cons, Bool.and_false]
    rfl

/-! ### Tags -/

theorem lower_cons (c : Char) (rest : List Char) :
    lower (String.ofList (c :: rest)) = (String.singleton c.toLower) ++ lower (String.ofList rest) := by
  apply String.ext
  simp [lower, String.toList_append]

theorem string_push_append (a : String) (c : Char) (r : String) :
    a.push c ++ r = a ++ (String.singleton c ++ r) := by
  apply String.ext
  simp [String.toList_append, String.toList_push]

theorem run_tagName (b : Builder) (rest : List Char) (h : rest.all nameChar = true) :
    ∀ t : TagTok, run (some ⟨.tagName t, b⟩) rest =
      some ⟨.tagName { t with name := t.name ++ lower (String.ofList rest) }, b⟩ := by
  induction rest with
  | nil => intro t; simp [run_nil, lower]
  | cons c cs ih =>
    intro t
    simp only [List.all_cons, Bool.and_eq_true] at h
    have hc : nameChar c = true := h.1
    simp only [nameChar, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hc
    obtain ⟨⟨⟨⟨hw, hs⟩, hg⟩, hz⟩, _⟩ := hc
    have hstep : step ⟨.tagName t, b⟩ c = some ⟨.tagName { t with name := t.name.push c.toLower }, b⟩ := by
      simp [step, hw, hs, hg, hz]
    rw [run_cons, hstep, ih h.2]
    congr 3
    rw [lower_cons, string_push_append]

theorem run_tagOpen (b : Builder) (tag : String) (hv : validTag tag = true) :
    run (some ⟨.data, b⟩) ('<' :: tag.toList) = some ⟨.tagName ⟨false, lower tag, #[]⟩, b⟩ := by
  unfold validTag at hv
  cases ht : tag.toList with
  | nil => simp [ht] at hv
  | cons c rest =>
    rw [ht] at hv
    simp only [Bool.and_eq_true] at hv
    have h1 : step ⟨.data, b⟩ '<' = some ⟨.tagOpen, b⟩ := by simp [step]
    have hc : isAlpha c = true := hv.1
    have hns : c ≠ '/' ∧ c ≠ '!' := by
      constructor <;> rintro rfl <;> simp [isAlpha] at hc
    have h2 : step ⟨.tagOpen, b⟩ c = some ⟨.tagName ⟨false, String.singleton c.toLower, #[]⟩, b⟩ := by
      simp [step, hc, hns]
    rw [run_cons, h1, run_cons, h2, run_tagName b rest hv.2]
    congr 4
    have : tag = String.ofList (c :: rest) := by rw [← ht, String.ofList_toList]
    rw [this, lower_cons]

theorem run_endTag (b : Builder) (tag : String) (hv : validTag tag = true) :
    run (some ⟨.data, b⟩) ('<' :: '/' :: tag.toList) = some ⟨.tagName ⟨true, lower tag, #[]⟩, b⟩ := by
  unfold validTag at hv
  cases ht : tag.toList with
  | nil => simp [ht] at hv
  | cons c rest =>
    rw [ht] at hv
    simp only [Bool.and_eq_true] at hv
    have h1 : step ⟨.data, b⟩ '<' = some ⟨.tagOpen, b⟩ := by simp [step]
    have h2 : step ⟨.tagOpen, b⟩ '/' = some ⟨.endTagOpen, b⟩ := by simp [step]
    have hc : isAlpha c = true := hv.1
    have h3 : step ⟨.endTagOpen, b⟩ c = some ⟨.tagName ⟨true, String.singleton c.toLower, #[]⟩, b⟩ := by
      simp [step, hc]
    rw [run_cons, h1, run_cons, h2, run_cons, h3, run_tagName b rest hv.2]
    congr 4
    have : tag = String.ofList (c :: rest) := by rw [← ht, String.ofList_toList]
    rw [this, lower_cons]

theorem deliver_attr (b : Builder) (st : TState) (t : TagTok) (k v r : String) :
    deliver ⟨st, b⟩ (.attr t k v) r = some ⟨.attrValue t k (v ++ r), b⟩ := by
  simp [deliver]

theorem run_attrChar (b : Builder) (t : TagTok) (k v : String) (c : Char) (hn : c ≠ '\x00') :
    run (some ⟨.attrValue t k v, b⟩) (escapeCharAttr c) =
      some ⟨.attrValue t k (v.push c), b⟩ := by
  have href : step ⟨.attrValue t k v, b⟩ '&' = some ⟨.ref (.attr t k v) [], b⟩ := by simp [step]
  have hpush : ∀ c : Char, v ++ String.singleton c = v.push c := fun c => by
    apply String.ext; simp [String.toList_push]
  unfold escapeCharAttr
  by_cases h1 : c = '&'
  · subst h1
    have e : "&amp;".toList = '&' :: ['a', 'm', 'p'] ++ [';'] := rfl
    rw [ite_eq_left (by decide), e, List.cons_append, run_cons, href,
      run_named b _ ['a', 'm', 'p'] "&" (by decide) (by simp) (by simp [named]), deliver_attr]
    rw [show "&" = String.singleton '&' from rfl, hpush]
  · by_cases h2 : c = '<'
    · subst h2
      have e : "&lt;".toList = '&' :: ['l', 't'] ++ [';'] := rfl
      rw [ite_eq_right (by decide), ite_eq_left (by decide), e, List.cons_append, run_cons, href,
        run_named b _ ['l', 't'] "<" (by decide) (by simp) (by simp [named]), deliver_attr]
      rw [show "<" = String.singleton '<' from rfl, hpush]
    · by_cases h3 : c = '>'
      · subst h3
        have e : "&gt;".toList = '&' :: ['g', 't'] ++ [';'] := rfl
        rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left (by decide), e, List.cons_append,
          run_cons, href, run_named b _ ['g', 't'] ">" (by decide) (by simp) (by simp [named]),
          deliver_attr]
        rw [show ">" = String.singleton '>' from rfl, hpush]
      · by_cases h4 : c = '"'
        · subst h4
          have e : "&quot;".toList = '&' :: ['q', 'u', 'o', 't'] ++ [';'] := rfl
          rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left (by decide), e,
            List.cons_append, run_cons, href,
            run_named b _ ['q', 'u', 'o', 't'] "\"" (by decide) (by simp) (by simp [named]),
            deliver_attr]
          rw [show "\"" = String.singleton '"' from rfl, hpush]
        · by_cases h5 : c = '\''
          · subst h5
            have e : "&#39;".toList = '&' :: ['#', '3', '9', ';'] := rfl
            rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
              ite_eq_left (by decide), e, run_cons, href,
              run_numeric b _ '3' '9' '\'' (by decide) (by decide) (by decide), deliver_attr, hpush]
          · rw [ite_eq_right (by simpa using h1), ite_eq_right (by simpa using h2), ite_eq_right (by simpa using h3),
              ite_eq_right (by simpa using h4), ite_eq_right (by simpa using h5), run_cons]
            have : step ⟨.attrValue t k v, b⟩ c = some ⟨.attrValue t k (v.push c), b⟩ := by
              simp [step, h1, h4, hn]
            rw [this, run_nil]

theorem run_attrValue (b : Builder) (t : TagTok) (k : String) (cs : List Char)
    (h : ∀ c ∈ cs, c ≠ '\x00') : ∀ v, run (some ⟨.attrValue t k v, b⟩) (escapeAttr.go cs) =
      some ⟨.attrValue t k (v ++ String.ofList cs), b⟩ := by
  induction cs with
  | nil => intro v; simp [escapeAttr.go, run_nil]
  | cons c rest ih =>
    intro v
    rw [escapeAttr.go, run_append, run_attrChar b t k v c (h c (by simp)),
      ih (fun d hd => h d (by simp [hd]))]
    congr 3
    apply String.ext
    simp [String.toList_append, String.toList_push]

theorem run_attrName (b : Builder) (t : TagTok) (rest : List Char) (h : rest.all keyChar = true) :
    ∀ key, run (some ⟨.attrName t key, b⟩) rest =
      some ⟨.attrName t (key ++ lower (String.ofList rest)), b⟩ := by
  induction rest with
  | nil => intro key; simp [run_nil, lower]
  | cons c cs ih =>
    intro key
    simp only [List.all_cons, Bool.and_eq_true] at h
    have hc : keyChar c = true := h.1
    simp only [keyChar, nameChar, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hw, hs⟩, hg⟩, hz⟩, _⟩, he⟩, hq⟩, ha⟩, hl⟩ := hc
    have hstep : step ⟨.attrName t key, b⟩ c = some ⟨.attrName t (key.push c.toLower), b⟩ := by
      simp [step, hw, hs, hg, hz, he, hq, ha, hl]
    rw [run_cons, hstep, ih h.2]
    congr 3
    rw [lower_cons, string_push_append]

theorem keyChar_first (c : Char) (h : keyChar c = true) :
    isWs c = false ∧ c ≠ '/' ∧ c ≠ '>' ∧ c ≠ '=' ∧ c ≠ '"' ∧ c ≠ '\'' ∧ c ≠ '<' ∧ c ≠ '\x00' := by
  simp only [keyChar, nameChar, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hw, hs⟩, hg⟩, hz⟩, _⟩, he⟩, hq⟩, ha⟩, hl⟩ := h
  exact ⟨hw, hs, hg, he, hq, ha, hl, hz⟩

theorem run_attrStart (b : Builder) (st : TState) (t : TagTok) (hr : readyTag st = some t)
    (k : String) (hk : k.isEmpty = false) (hkc : k.toList.all keyChar = true) :
    run (some ⟨st, b⟩) (' ' :: k.toList) = some ⟨.attrName t (lower k), b⟩ := by
  cases hkl : k.toList with
  | nil => simp [← String.toList_eq_nil_iff, hkl] at hk
  | cons c rest =>
    rw [hkl] at hkc
    simp only [List.all_cons, Bool.and_eq_true] at hkc
    obtain ⟨hw, hs, hg, he, hq, ha, hl, hz⟩ := keyChar_first c hkc.1
    have hlow : lower k = String.singleton c.toLower ++ lower (String.ofList rest) := by
      have : k = String.ofList (c :: rest) := by rw [← hkl, String.ofList_toList]
      rw [this, lower_cons]
    have hfirst : ∃ st1, step ⟨st, b⟩ ' ' = some ⟨st1, b⟩ ∧
        step ⟨st1, b⟩ c = some ⟨.attrName t (String.singleton c.toLower), b⟩ := by
      cases st with
      | tagName t0 =>
        simp only [readyTag, Option.some.injEq] at hr
        subst hr
        exact ⟨.beforeAttrName t0, by simp [step, isWs], by simp [step, hw, hs, hg, he, hq, ha, hl, hz]⟩
      | afterAttrValue t0 =>
        simp only [readyTag, Option.some.injEq] at hr
        subst hr
        exact ⟨.beforeAttrName t0, by simp [step, isWs], by simp [step, hw, hs, hg, he, hq, ha, hl, hz]⟩
      | attrName t0 k0 =>
        simp only [readyTag, Option.some.injEq] at hr
        subst hr
        exact ⟨.afterAttrName t0 k0, by simp [step, isWs],
          by simp [step, hw, hs, hg, he, hq, ha, hl, hz]⟩
      | _ => simp [readyTag] at hr
    obtain ⟨st1, h1, h2⟩ := hfirst
    rw [run_cons, h1, run_cons, h2, run_attrName b t rest hkc.2, hlow]

theorem run_attr (b : Builder) (st : TState) (t : TagTok) (hr : readyTag st = some t)
    (k v : String) (hk : k.isEmpty = false) (hkc : k.toList.all keyChar = true)
    (hv : v.toList.all (fun c => c != '\x00' && c != '\r') = true) :
    ∃ st', run (some ⟨st, b⟩) (attrL (k, v)) = some ⟨st', b⟩ ∧
      readyTag st' = some (t.add (lower k) v) := by
  unfold attrL
  by_cases he : v.isEmpty = true
  · have hv0 : v = "" := by simpa using he
    subst hv0
    exact ⟨_, by simpa using run_attrStart b st t hr k hk hkc, rfl⟩
  · simp only [he, Bool.false_eq_true, ite_false]
    refine ⟨.afterAttrValue (t.add (lower k) v), ?_, rfl⟩
    have hz : ∀ c ∈ v.toList, c ≠ '\x00' := by
      intro c hc
      have := List.all_eq_true.mp hv c hc
      exact (by simpa using this : c ≠ '\x00' ∧ c ≠ '\r').1
    rw [show ' ' :: k.toList ++ '=' :: '"' :: escapeAttr.go v.toList ++ ['"'] =
        (' ' :: k.toList) ++ ('=' :: '"' :: (escapeAttr.go v.toList ++ ['"'])) by simp,
      run_append, run_attrStart b st t hr k hk hkc, run_cons]
    have h1 : step ⟨.attrName t (lower k), b⟩ '=' = some ⟨.beforeAttrValue t (lower k), b⟩ := by
      simp [step, isWs]
    have h2 : step ⟨.beforeAttrValue t (lower k), b⟩ '"' = some ⟨.attrValue t (lower k) "", b⟩ := by
      simp [step, isWs]
    rw [h1, run_cons, h2, run_append, run_attrValue b t (lower k) v.toList hz "", run_cons]
    simp [step, String.ofList_toList, run_nil]

theorem run_attrs (b : Builder) (attrs : List (String × String))
    (h : attrs.all (fun kv => !kv.1.isEmpty && kv.1.toList.all keyChar &&
      kv.2.toList.all (fun c => c != '\x00' && c != '\r')) = true) :
    ∀ st t, readyTag st = some t → ∃ st', run (some ⟨st, b⟩) (attrsL attrs) = some ⟨st', b⟩ ∧
      readyTag st' = some (attrs.foldl (fun t kv => t.add (lower kv.1) kv.2) t) := by
  induction attrs with
  | nil => intro st t hr; exact ⟨st, rfl, hr⟩
  | cons kv rest ih =>
    intro st t hr
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨hk, hkc⟩, hv⟩, hrest⟩ := h
    obtain ⟨st1, h1, hr1⟩ := run_attr b st t hr kv.1 kv.2 hk hkc hv
    obtain ⟨st2, h2, hr2⟩ := ih hrest st1 _ hr1
    refine ⟨st2, ?_, hr2⟩
    simp only [attrsL, List.flatMap_cons] at h2 ⊢
    rw [run_append, h1]
    exact h2

theorem fold_add (rest : List (String × String)) : ∀ t : TagTok,
    ((t.attrs.toList.map (·.1)) ++ rest.map (fun kv => lower kv.1)).Nodup →
    rest.foldl (fun t kv => t.add (lower kv.1) kv.2) t =
      { t with attrs := t.attrs ++ (rest.map fun kv => (lower kv.1, kv.2)).toArray } := by
  induction rest with
  | nil => intro t _; simp
  | cons kv rest ih =>
    intro t hnd
    have hnot : (t.attrs.any (·.1 == lower kv.1)) = false := by
      rw [Bool.eq_false_iff, ne_eq, ← Array.any_toList, List.any_eq_true]
      rintro ⟨x, hx, heq⟩
      have hmem : lower kv.1 ∈ t.attrs.toList.map (·.1) :=
        List.mem_map.mpr ⟨x, hx, by simpa using heq⟩
      have := List.nodup_append.mp hnd
      exact this.2.2 _ hmem _ (by simp) rfl
    have hadd : t.add (lower kv.1) kv.2 = { t with attrs := t.attrs.push (lower kv.1, kv.2) } := by
      simp [TagTok.add, hnot]
    rw [List.foldl_cons, hadd, ih]
    · simp
    · simpa [List.append_assoc] using hnd

theorem lowAttrs_eq (attrs : Array (String × String)) :
    (#[] : Array (String × String)) ++ (attrs.toList.map fun kv => (lower kv.1, kv.2)).toArray =
      lowAttrs attrs := by
  apply Array.toList_inj.mp
  simp [lowAttrs]

theorem validAttrs_parts (attrs : Array (String × String)) (h : validAttrs attrs = true) :
    attrs.toList.all (fun kv => !kv.1.isEmpty && kv.1.toList.all keyChar &&
      kv.2.toList.all (fun c => c != '\x00' && c != '\r')) = true ∧
      (attrs.toList.map fun kv => lower kv.1).Nodup := by
  simp only [validAttrs, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨?_, h.2⟩
  rw [← Array.all_toList] at h
  exact h.1

theorem emit_eq (s : St) (t : Tok) (next : TState) :
    emit s t next = (HtmlRead.build s.build t).map fun (b, c) =>
      ⟨after c (match t with | .start n _ _ => n | _ => "") next, b⟩ := by
  simp only [emit, after]
  congr 1

theorem run_startTag (b : Builder) (tag : String) (attrs : Array (String × String))
    (hv : validTag tag = true) (ha : validAttrs attrs = true) :
    run (some ⟨.data, b⟩) ('<' :: tag.toList ++ attrsL attrs.toList ++ ['>']) =
      (start { b with dropLF := false } (lower tag) (lowAttrs attrs) false).map
        fun (b', c) => ⟨after c (lower tag) .data, b'⟩ := by
  obtain ⟨hall, hnd⟩ := validAttrs_parts attrs ha
  obtain ⟨st, h1, hr⟩ := run_attrs b attrs.toList hall (.tagName ⟨false, lower tag, #[]⟩) _ rfl
  rw [show '<' :: tag.toList ++ attrsL attrs.toList ++ ['>'] =
      ('<' :: tag.toList) ++ (attrsL attrs.toList ++ ['>']) by simp, run_append,
    run_tagOpen b tag hv, run_append, h1, run_cons, run_nil]
  rw [fold_add _ _ (by simpa using hnd)] at hr
  simp only [lowAttrs_eq] at hr
  have hemit : ∀ t : TagTok, readyTag st = some t →
      step ⟨st, b⟩ '>' = emitTag ⟨st, b⟩ t false := by
    intro t hr
    cases st with
    | tagName t0 =>
      simp only [readyTag, Option.some.injEq] at hr; subst hr; simp [step, isWs]
    | afterAttrValue t0 =>
      simp only [readyTag, Option.some.injEq] at hr; subst hr; simp [step, isWs]
    | attrName t0 k0 =>
      simp only [readyTag, Option.some.injEq] at hr; subst hr; simp [step, isWs]
    | _ => simp [readyTag] at hr
  rw [hemit _ hr]
  simp [emitTag, emit_eq, HtmlRead.build]

theorem run_stopTag (b : Builder) (tag : String) (hv : validTag tag = true) :
    run (some ⟨.data, b⟩) (closeL tag) =
      (stop { b with dropLF := false } (lower tag)).map fun b' => ⟨.data, b'⟩ := by
  rw [show closeL tag = ('<' :: '/' :: tag.toList) ++ ['>'] by simp [closeL], run_append,
    run_endTag b tag hv, run_cons, run_nil]
  simp [step, isWs, emitTag, emit_eq, HtmlRead.build, after, Function.comp_def]

/-! ### Raw text -/

theorem InText.top {b : Builder} (h : InText b) (g : Array Dom → Array Dom) : InText (withTop b g) where
  text := by rw [show inText (withTop b g).stack = inText b.stack from
    currentIs_shape _ (withTop_shape b g)]; exact h.text
  late := by rw [withTop_mode]; exact h.late
  nonempty := by
    have := h.nonempty
    unfold withTop; cases hs : b.stack <;> simp_all
  noLF := by rw [withTop_dropLF]; exact h.noLF

theorem emit_text_char {b : Builder} (h : InText b) (σ next : TState) (c : Char) :
    emit ⟨σ, b⟩ (.char c) next = some ⟨next, withTop b (addChar · c)⟩ :=
  emit_char ⟨σ, b⟩ c next _ h.noLF (char_keeps b c h.late h.nonempty (by
    simp [charKeeps, h.text]))

theorem emitChars_text (cs : List Char) : ∀ {b : Builder}, InText b → ∀ (σ next : TState),
    emitChars ⟨σ, b⟩ cs next = some ⟨next, withTop b (addL · cs)⟩ := by
  induction cs with
  | nil =>
    intro b _ _ next
    simp [emitChars, withTop_id b _ (fun _ => rfl), addL]
  | cons c rest ih =>
    intro b h σ next
    simp only [emitChars, emit_text_char h, Option.bind_some]
    rw [ih (h.top _) next next, withTop_comp]
    rfl

theorem infix_lower_of_seen (e : List Char) (seen n : String) (c : Char) (hs : lower seen = n) :
    ('<' :: '/' :: n.toList) <:+: ((e ++ ('<' :: '/' :: seen.toList) ++ [c]).map Char.toLower) := by
  have hn : n.toList = seen.toList.map Char.toLower := by
    rw [← hs]; simp [lower]
  refine ⟨e.map Char.toLower, [c.toLower], ?_⟩
  simp [hn]

theorem raw_step (k : Content) (hk : k ≠ .rcdata) (n : String) {b : Builder} (hb : InText b)
    (σ : TState) (e pre : List Char) (hinv : RawInv k n σ e pre) (c : Char) (hz : c ≠ '\x00')
    (hterm : ¬ ('<' :: '/' :: n.toList) <:+: ((pre ++ [c]).map Char.toLower))
    (hbang : k = .script → ¬ ['<', '!'] <:+: (pre ++ [c])) :
    ∃ σ' e', step ⟨σ, withTop b (addL · e)⟩ c = some ⟨σ', withTop b (addL · e')⟩ ∧
      RawInv k n σ' e' (pre ++ [c]) := by
  have hB := hb.top (addL · e)
  have hcomp : ∀ cs, withTop (withTop b (addL · e)) (addL · cs) = withTop b (addL · (e ++ cs)) :=
    fun cs => by rw [withTop_comp]; congr 1; funext x; simp [addL, List.foldl_append]
  have hcompc : ∀ d, withTop (withTop b (addL · e)) (addChar · d) = withTop b (addL · (e ++ [d])) :=
    fun d => by rw [withTop_comp]; congr 1; funext x; simp [addL, List.foldl_append]
  obtain ⟨hshape, hpend⟩ := hinv
  rcases hshape with rfl | rfl | ⟨seen, rfl⟩
  · simp only [pendOf, List.append_nil] at hpend
    subst hpend
    by_cases hl : c = '<'
    · subst hl
      exact ⟨.rawLt k n, e, by simp [step], ⟨Or.inr (Or.inl rfl), rfl⟩⟩
    · refine ⟨.raw k n, e ++ [c], ?_, ⟨Or.inl rfl, by simp [pendOf]⟩⟩
      have : step ⟨.raw k n, withTop b (addL · e)⟩ c = emit ⟨.raw k n, withTop b (addL · e)⟩ (.char c) (.raw k n) := by
        simp [step, hl, hz, hk]
      rw [this, emit_text_char hB, hcompc]
  · simp only [pendOf] at hpend
    subst hpend
    by_cases hs : c = '/'
    · subst hs
      exact ⟨.rawEnd k n "", e, by simp [step], ⟨Or.inr (Or.inr ⟨"", rfl⟩), by simp [pendOf]⟩⟩
    · have hnb : ¬ (c = '!' ∧ k = .script) := by
        rintro ⟨rfl, rfl⟩
        exact hbang rfl ⟨e, [], by simp⟩
      have hb' : (c == '!' && k == .script) = false := by
        simpa [Bool.and_eq_true, beq_iff_eq] using hnb
      have hlt : step ⟨.rawLt k n, withTop b (addL · e)⟩ c =
          (emit ⟨.rawLt k n, withTop b (addL · e)⟩ (.char '<') (.raw k n)).bind
            (fun s => step.step' s c) := by
        simp [step, hs, hb']
      rw [hlt, emit_text_char hB, Option.bind_some, hcompc]
      have hB2 := hb.top (addL · (e ++ ['<']))
      by_cases hl : c = '<'
      · subst hl
        exact ⟨.rawLt k n, e ++ ['<'], by simp [step.step'], ⟨Or.inr (Or.inl rfl), by simp [pendOf]⟩⟩
      · refine ⟨.raw k n, e ++ ['<', c], ?_, ⟨Or.inl rfl, by simp [pendOf]⟩⟩
        have : step.step' ⟨.raw k n, withTop b (addL · (e ++ ['<']))⟩ c =
            emit ⟨.raw k n, withTop b (addL · (e ++ ['<']))⟩ (.char c) (.raw k n) := by
          simp [step.step', hl, hz, hk]
        rw [this, emit_text_char hB2, withTop_comp]
        congr 3; funext x; simp [addL, List.foldl_append]
  · simp only [pendOf] at hpend
    subst hpend
    by_cases ha : isAlpha c = true
    · refine ⟨.rawEnd k n (seen.push c), e, by simp [step, ha], ⟨Or.inr (Or.inr ⟨_, rfl⟩), ?_⟩⟩
      simp [pendOf, String.toList_push]
    · have hne : lower seen ≠ n := by
        intro hs
        exact hterm (by simpa [List.append_assoc] using infix_lower_of_seen e seen n c hs)
      have hstep : step ⟨.rawEnd k n seen, withTop b (addL · e)⟩ c =
          (emitChars ⟨.rawEnd k n seen, withTop b (addL · e)⟩ (rawBack seen) (.raw k n)).bind
            (fun s => step.step' s c) := by
        simp [step, ha, hne]
      rw [hstep, emitChars_text _ hB, Option.bind_some, hcomp]
      have hB2 := hb.top (addL · (e ++ rawBack seen))
      by_cases hl : c = '<'
      · subst hl
        exact ⟨.rawLt k n, e ++ rawBack seen, by simp [step.step'],
          ⟨Or.inr (Or.inl rfl), by simp [pendOf, rawBack]⟩⟩
      · refine ⟨.raw k n, e ++ rawBack seen ++ [c], ?_, ⟨Or.inl rfl, by simp [pendOf, rawBack]⟩⟩
        have : step.step' ⟨.raw k n, withTop b (addL · (e ++ rawBack seen))⟩ c =
            emit ⟨.raw k n, withTop b (addL · (e ++ rawBack seen))⟩ (.char c) (.raw k n) := by
          simp [step.step', hl, hz, hk]
        rw [this, emit_text_char hB2, withTop_comp]
        congr 3; funext x; simp [addL, List.foldl_append]

theorem raw_fold (k : Content) (hk : k ≠ .rcdata) (n : String) {b : Builder} (hb : InText b)
    (p : List Char) (hz : ∀ c ∈ p, c ≠ '\x00')
    (hterm : ¬ ('<' :: '/' :: n.toList) <:+: (p.map Char.toLower))
    (hbang : k = .script → ¬ ['<', '!'] <:+: p) :
    ∀ rest pre σ e, pre ++ rest = p → RawInv k n σ e pre →
      ∃ σ' e', run (some ⟨σ, withTop b (addL · e)⟩) rest = some ⟨σ', withTop b (addL · e')⟩ ∧
        RawInv k n σ' e' p := by
  intro rest
  induction rest with
  | nil =>
    intro pre σ e hp hinv
    rw [List.append_nil] at hp
    exact ⟨σ, e, rfl, hp ▸ hinv⟩
  | cons c rest ih =>
    intro pre σ e hp hinv
    have hpre : (pre ++ [c]) <+: p := ⟨rest, by simp [← hp]⟩
    obtain ⟨σ1, e1, h1, hinv1⟩ := raw_step k hk n hb σ e pre hinv c (hz c (by simp [← hp]))
      (fun hi => hterm (hi.trans (hpre.map Char.toLower).isInfix))
      (fun hs hi => hbang hs (hi.trans hpre.isInfix))
    rw [run_cons, h1]
    exact ih (pre ++ [c]) σ1 e1 (by simp [← hp]) hinv1

theorem run_rawEnd (k : Content) (n : String) (b : Builder) (cs : List Char)
    (h : cs.all isAlpha = true) : ∀ seen, run (some ⟨.rawEnd k n seen, b⟩) cs =
      some ⟨.rawEnd k n (seen ++ String.ofList cs), b⟩ := by
  induction cs with
  | nil => intro seen; simp [run_nil]
  | cons c rest ih =>
    intro seen
    simp only [List.all_cons, Bool.and_eq_true] at h
    have hs : step ⟨.rawEnd k n seen, b⟩ c = some ⟨.rawEnd k n (seen.push c), b⟩ := by
      simp [step, h.1]
    rw [run_cons, hs, ih h.2]
    congr 3
    apply String.ext
    simp [String.toList_push]

theorem rawName_alpha {n : String} (h : rawName n = true) : n.toList.all isAlpha = true := by
  unfold rawName at h
  rw [List.all_eq_true] at h ⊢
  intro c hc
  have := h c hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  simp [isAlpha, this]

theorem rawName_lower {n : String} (h : rawName n = true) : lower n = n := by
  unfold rawName at h
  apply String.ext
  simp only [lower, String.toList_ofList]
  conv => rhs; rw [← List.map_id n.toList]
  apply List.map_congr_left
  intro c hc
  have := List.all_eq_true.mp h c hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  simp only [id]
  unfold Char.toLower
  split
  · next hu =>
    exfalso
    have h1 : 'a' ≤ c := this.1
    have h2 : c ≤ 'Z' := hu.2
    exact absurd (Char.le_trans h1 h2) (by decide)
  · rfl

theorem raw_close (k : Content) (n : String) (hn : rawName n = true) {b : Builder}
    (hb : InText b) (σ : TState) (e p : List Char) (hinv : RawInv k n σ e p) :
    run (some ⟨σ, withTop b (addL · e)⟩) (closeL n) =
      (stop { withTop b (addL · p) with dropLF := false } n).map (⟨.data, ·⟩) := by
  have hB := hb.top (addL · e)
  have hlt : ∃ e', run (some ⟨σ, withTop b (addL · e)⟩) ['<'] =
      some ⟨.rawLt k n, withTop b (addL · e')⟩ ∧ e' = p := by
    obtain ⟨hshape, hpend⟩ := hinv
    rcases hshape with rfl | rfl | ⟨seen, rfl⟩
    · refine ⟨e, by simp [run_cons, run_nil, step], by simpa [pendOf] using hpend⟩
    · refine ⟨e ++ ['<'], ?_, by simpa [pendOf] using hpend⟩
      have : step ⟨.rawLt k n, withTop b (addL · e)⟩ '<' =
          (emit ⟨.rawLt k n, withTop b (addL · e)⟩ (.char '<') (.raw k n)).bind
            (fun s => step.step' s '<') := by simp [step]
      rw [run_cons, this, emit_text_char hB, Option.bind_some, run_nil, withTop_comp]
      simp only [step.step', ite_true, beq_self_eq_true]
      congr 3; funext x; simp [addL, List.foldl_append]
    · refine ⟨e ++ rawBack seen, ?_, by simpa [pendOf, rawBack] using hpend⟩
      have : step ⟨.rawEnd k n seen, withTop b (addL · e)⟩ '<' =
          (emitChars ⟨.rawEnd k n seen, withTop b (addL · e)⟩ (rawBack seen) (.raw k n)).bind
            (fun s => step.step' s '<') := by simp [step, isAlpha, isWs]
      rw [run_cons, this, emitChars_text _ hB, Option.bind_some, run_nil, withTop_comp]
      simp only [step.step', ite_true, beq_self_eq_true]
      congr 3; funext x; simp [addL, List.foldl_append]
  obtain ⟨e', h1, rfl⟩ := hlt
  rw [show closeL n = ['<'] ++ ('/' :: (n.toList ++ ['>'])) by simp [closeL], run_append, h1,
    run_cons]
  have h2 : step ⟨.rawLt k n, withTop b (addL · e')⟩ '/' = some ⟨.rawEnd k n "", withTop b (addL · e')⟩ := by
    simp [step]
  rw [h2, run_append, run_rawEnd k n _ n.toList (rawName_alpha hn) "", run_cons, run_nil]
  have hs : ("" ++ String.ofList n.toList) = n := by simp
  rw [hs]
  have : step ⟨.rawEnd k n n, withTop b (addL · e')⟩ '>' = emit ⟨.rawEnd k n n, withTop b (addL · e')⟩ (.stop n) .data := by
    simp [step, isAlpha, rawName_lower hn]
  rw [this, emit_eq]
  simp [HtmlRead.build, after, Function.comp_def]

/-! ### Reading the rendered tree -/

theorem run_escData (s : List Char) (b : Builder) (hb : b.dropLF = false) (hm : Late b.mode)
    (hs : b.stack ≠ []) (hk : ∀ c ∈ s, charKeeps b.mode b.stack c = true ∧ c ≠ '\x00') :
    run (some ⟨.data, b⟩) (escapeText.go s) = some ⟨.data, withTop b (addL · s)⟩ :=
  run_escText .data s b hb hm hs hk

theorem late_of {m : Mode} (h : m = .inBody ∨ m = .inHead) : Late m := by
  rcases h with rfl | rfl <;> exact ⟨by decide, by decide, by decide⟩

theorem ws_keeps (m : Mode) (s : List Frame) (c : Char) (h : c = ' ' ∨ c = '\n') :
    charKeeps m s c = true := by
  rcases h with rfl | rfl <;> simp [charKeeps, isWs]

theorem run_ws (b : Builder) (cs : List Char) (hb : b.dropLF = false) (hm : Late b.mode)
    (hs : b.stack ≠ []) (hw : ∀ c ∈ cs, c = ' ' ∨ c = '\n') :
    run (some ⟨.data, b⟩) cs = some ⟨.data, withTop b (addL · cs)⟩ := by
  have hplain : escapeText.go cs = cs := by
    apply escapeText_go_plain
    rw [List.any_eq_false]
    intro c hc
    rcases hw c hc with rfl | rfl <;> decide
  have := run_escText Home.data cs b hb hm hs (fun c hc => ⟨ws_keeps _ _ c (hw c hc), by
    rcases hw c hc with rfl | rfl <;> decide⟩)
  rw [hplain] at this
  exact this

theorem padL_ws (i : Nat) : ∀ c ∈ padL i, c = ' ' ∨ c = '\n' := by
  intro c hc
  simp only [padL, List.mem_replicate] at hc
  exact Or.inl hc.2

theorem addL_append (K : Array Dom) (a b : List Char) : addL K (a ++ b) = addL (addL K a) b := by
  simp [addL, List.foldl_append]

theorem stack_ne_withTop {b : Builder} (h : b.stack ≠ []) (g : Array Dom → Array Dom) :
    (withTop b g).stack ≠ [] := by
  unfold withTop; cases hs : b.stack <;> simp_all

theorem text_parts {m : Mode} {s : List Frame} {t : String} (h : Accepts m s (.text t) = true) :
    ∀ c ∈ t.toList, charKeeps m s c = true ∧ c ≠ '\x00' := by
  simp only [Accepts, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  intro c hc
  exact ⟨(h c hc).2, (h c hc).1.2⟩

theorem simB_text (t : String) (i : Nat) (b : Builder) (hm : b.mode = .inBody ∨ b.mode = .inHead)
    (hs : b.stack ≠ []) (hd : b.dropLF = false) (h : Accepts b.mode b.stack (.text t) = true) :
    run (some ⟨.data, b⟩) (rB (.text t) i) = some ⟨.data, withTop b (fB · (.text t) i)⟩ := by
  have hl := late_of hm
  have hk := text_parts h
  simp only [rB]
  rw [run_append, run_append, run_ws b _ hd hl hs (padL_ws i)]
  have hs1 := stack_ne_withTop hs (addL · (padL i))
  rw [run_escData t.toList _ (by rw [withTop_dropLF]; exact hd) (by rw [withTop_mode]; exact hl)
    hs1 (fun c hc => by
      rw [withTop_mode, charKeeps_shape _ _ (withTop_shape b _)]; exact hk c hc), withTop_comp]
  rw [run_ws _ _ (by rw [withTop_dropLF]; exact hd) (by rw [withTop_mode]; exact hl)
    (stack_ne_withTop hs _) (by simp), withTop_comp]
  congr 3
  funext K
  simp [fB, addL_append]

theorem simI_text (t : String) (b : Builder) (hm : b.mode = .inBody ∨ b.mode = .inHead)
    (hs : b.stack ≠ []) (hd : b.dropLF = true → t.toList.head? ≠ some '\n')
    (h : Accepts b.mode b.stack (.text t) = true) :
    run (some ⟨.data, b⟩) (rI (.text t)) =
      some ⟨.data, withTop { b with dropLF := b.dropLF && t.toList.isEmpty } (fI · (.text t))⟩ := by
  simp only [rI, fI]
  exact run_escText' Home.data t.toList b hd (late_of hm) hs (text_parts h)

/-! ### Acceptance reads the stack's elements only -/

theorem sameShape_cons {f g : Frame} {s t : List Frame} (h : sameShape (f :: s) (g :: t)) :
    f.ns = g.ns ∧ f.tag = g.tag ∧ f.attrs = g.attrs ∧ sameShape s t := h

theorem sameShape_nil_left {t : List Frame} (h : sameShape [] t) : t = [] := by
  cases t <;> simp_all [sameShape]

theorem sameShape_nil_right {s : List Frame} (h : sameShape s []) : s = [] := by
  cases s <;> simp_all [sameShape]

theorem inButtonScope_shape (n : String) : ∀ {s t : List Frame}, sameShape s t →
    inButtonScope n s = inButtonScope n t
  | [], t, h => by rw [sameShape_nil_left h]
  | f :: s, [], h => by simp [sameShape] at h
  | f :: s, g :: t, h => by
    obtain ⟨h1, h2, _, h4⟩ := sameShape_cons h
    simp only [inButtonScope, h1, h2, inButtonScope_shape n h4]

theorem listItemCloses_shape (names : List String) : ∀ {s t : List Frame}, sameShape s t →
    listItemCloses names s = listItemCloses names t
  | [], t, h => by rw [sameShape_nil_left h]
  | f :: s, [], h => by simp [sameShape] at h
  | f :: s, g :: t, h => by
    obtain ⟨h1, h2, _, h4⟩ := sameShape_cons h
    simp only [listItemCloses, h1, h2, listItemCloses_shape names h4]

theorem openAnchor_shape : ∀ {s t : List Frame}, sameShape s t → openAnchor s = openAnchor t
  | [], t, h => by rw [sameShape_nil_left h]
  | f :: s, [], h => by simp [sameShape] at h
  | f :: s, g :: t, h => by
    obtain ⟨h1, h2, _, h4⟩ := sameShape_cons h
    simp only [openAnchor, h1, h2, openAnchor_shape h4]

theorem inCell_shape : ∀ {s t : List Frame}, sameShape s t → inCell s = inCell t
  | [], t, h => by rw [sameShape_nil_left h]
  | f :: s, [], h => by simp [sameShape] at h
  | f :: s, g :: t, h => by
    obtain ⟨h1, h2, _, h4⟩ := sameShape_cons h
    simp only [inCell, h1, h2, inCell_shape h4]

theorem integrationPoint_shape {f g : Frame} (h1 : f.ns = g.ns) (h2 : f.tag = g.tag)
    (h3 : f.attrs = g.attrs) : integrationPoint f = integrationPoint g := by
  simp only [integrationPoint, h1, h2, h3]

theorem htmlContext_shape {s t : List Frame} (h : sameShape s t) : htmlContext s = htmlContext t := by
  cases s with
  | nil => rw [sameShape_nil_left h]
  | cons f s =>
    cases t with
    | nil => simp [sameShape] at h
    | cons g t =>
      obtain ⟨h1, h2, h3, _⟩ := sameShape_cons h
      simp only [htmlContext, h1, integrationPoint_shape h1 h2 h3]

theorem nsFor_shape (name : String) {s t : List Frame} (h : sameShape s t) :
    nsFor s name = nsFor t name := by
  unfold nsFor
  rw [htmlContext_shape h]
  split
  · rfl
  · cases s with
    | nil => rw [sameShape_nil_left h]
    | cons f s =>
      cases t with
      | nil => simp [sameShape] at h
      | cons g t => exact (sameShape_cons h).1

theorem bodyAccepts_shape (name : String) {s t : List Frame} (h : sameShape s t) :
    bodyAccepts s name = bodyAccepts t name := by
  unfold bodyAccepts inTableMode tablePartOk
  rw [currentIs_shape ["table", "colgroup", "thead", "tbody", "tfoot", "tr"] h,
    currentIs_shape ["table"] h, currentIs_shape ["colgroup"] h,
    currentIs_shape ["thead", "tbody", "tfoot"] h, currentIs_shape ["tr"] h,
    currentIs_shape headings h, inCell_shape h, inButtonScope_shape "p" h,
    listItemCloses_shape ["li"] h, listItemCloses_shape ["dd", "dt"] h, openAnchor_shape h]

theorem sameShape_push (f : Frame) {s t : List Frame} (h : sameShape s t) :
    sameShape (f :: s) (f :: t) := ⟨rfl, rfl, rfl, h⟩

theorem dispatchOdd_shape (name : String) {s t : List Frame} (h : sameShape s t) :
    dispatchOdd s name = dispatchOdd t name := by
  cases s with
  | nil => rw [sameShape_nil_left h]
  | cons f s =>
    cases t with
    | nil => simp [sameShape] at h
    | cons g t =>
      obtain ⟨h1, h2, h3, _⟩ := sameShape_cons h
      simp only [dispatchOdd, h1, h2, integrationPoint_shape h1 h2 h3]

theorem startOk_shape (m : Mode) (name : String) (attrs : Array (String × String))
    {s t : List Frame} (h : sameShape s t) : startOk m s name attrs = startOk m t name attrs := by
  unfold startOk startAccepts
  rw [htmlContext_shape h, bodyAccepts_shape _ h, dispatchOdd_shape _ h]

theorem nsIn_shape (m : Mode) (name : String) {s t : List Frame} (h : sameShape s t) :
    nsIn m s name = nsIn m t name := by
  unfold nsIn; rw [nsFor_shape _ h]

mutual

theorem Accepts_shape (m : Mode) {s t : List Frame} (h : sameShape s t) : (n : Node) →
    Accepts m s n = Accepts m t n
  | .text x => by simp only [Accepts, charKeeps_shape _ _ h]
  | .style css => by simp only [Accepts, htmlContext_shape h, startOk_shape _ _ _ h]
  | .script attrs js => by simp only [Accepts, htmlContext_shape h, startOk_shape _ _ _ h]
  | .elem tag attrs kids => by
    simp only [Accepts, startOk_shape _ _ _ h, nsIn_shape _ _ h]
    congr 1
    split
    · rfl
    · split
      · exact AcceptsList_shape m (sameShape_push _ h) kids.toList
      · rfl
      · rfl

theorem AcceptsList_shape (m : Mode) {s t : List Frame} (h : sameShape s t) : (l : List Node) →
    AcceptsList m s l = AcceptsList m t l
  | [] => rfl
  | n :: rest => by
    simp only [AcceptsList, Accepts_shape m h n, AcceptsList_shape m h rest]

end

/-! ### Start tags in the modes -/

theorem void_data (ns : Ns) (t : String) (h : HtmlRead.voidTags.contains t = true) :
    contentOf ns t = .data := by
  unfold contentOf
  split
  · rfl
  · have : t ∈ HtmlRead.voidTags := by simpa using h
    simp only [HtmlRead.voidTags, List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> rfl

theorem void_not_pre (t : String) (h : HtmlRead.voidTags.contains t = true) :
    (t == "pre" || t == "listing") = false := by
  have : t ∈ HtmlRead.voidTags := by simpa using h
  simp only [HtmlRead.voidTags, List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> rfl

theorem start_open (b : Builder) (hm : b.mode = .inBody ∨ b.mode = .inHead) (t : String)
    (a : Array (String × String)) (h : startOk b.mode b.stack t a = true)
    (hv : (HtmlRead.voidTags.contains t && nsIn b.mode b.stack t == .html) = false) :
    start { b with dropLF := false } t a false =
      some (Builder.mk b.mode (Frame.mk (nsIn b.mode b.stack t) t a #[] :: b.stack)
          (b.mode == .inBody && nsIn b.mode b.stack t == .html && (t == "pre" || t == "listing")),
        contentOf (nsIn b.mode b.stack t) t) := by
  rcases hm with hm | hm
  · simp only [startOk, hm] at h
    have hns : nsIn b.mode b.stack t = nsFor b.stack t := by simp [nsIn, hm]
    rw [hns] at hv ⊢
    have hvoid : voidAs (nsFor b.stack t) t false = false := by
      unfold voidAs; split
      · next he => simpa [he] using hv
      · rfl
    simp [start, hm, h, hvoid, HtmlRead.insert]
  · simp only [startOk, hm] at h
    have hns : nsIn b.mode b.stack t = .html := by simp [nsIn, hm]
    rw [hns] at hv ⊢
    have hv' : t ∉ HtmlRead.voidTags := by simpa using hv
    have h' : t ∈ headTags := by simpa using h
    simp [start, hm, h', hv', HtmlRead.insert]

theorem start_void (b : Builder) (hm : b.mode = .inBody ∨ b.mode = .inHead) (hs : b.stack ≠ [])
    (t : String) (a : Array (String × String)) (h : startOk b.mode b.stack t a = true)
    (hv : (HtmlRead.voidTags.contains t && nsIn b.mode b.stack t == .html) = true) :
    start { b with dropLF := false } t a false =
      some (withTop { b with dropLF := false } (·.push (.elem t a #[])), .data) := by
  simp only [Bool.and_eq_true, beq_iff_eq] at hv
  obtain ⟨hv1, hv2⟩ := hv
  have hc := void_data .html t hv1
  have hp := void_not_pre t hv1
  cases hst : b.stack with
  | nil => exact absurd hst hs
  | cons f rest =>
    have hv1' : t ∈ HtmlRead.voidTags := by simpa using hv1
    rcases hm with hm | hm
    · simp only [startOk, hm] at h
      have hns : nsFor b.stack t = .html := by simpa [nsIn, hm] using hv2
      rw [hst] at h hns
      have hvoid : voidAs .html t false = true := by simp [voidAs, hv1']
      simp [start, hm, h, hvoid, hns, HtmlRead.insert, hc, hp, withTop, Frame.close]
    · simp only [startOk, hm] at h
      have h' : t ∈ headTags := by simpa using h
      simp [start, hm, h', hv1', HtmlRead.insert, hc, withTop, Frame.close]

/-! ### Raw payloads in place -/

theorem infix_sep {t A B : List Char} {x : Char} (hx : x ∉ t) (h : t <:+: A ++ x :: B) :
    t <:+: A ∨ t <:+: B := by
  obtain ⟨u, v, huv⟩ := h
  rw [List.append_assoc] at huv
  rcases List.append_eq_append_iff.mp huv with ⟨a', h1, h2⟩ | ⟨c', h1, h2⟩
  · rcases List.append_eq_append_iff.mp h2.symm with ⟨a'', h3, h4⟩ | ⟨c'', h3, _⟩
    · cases a'' with
      | nil => left; exact ⟨u, [], by simp [h1, h3]⟩
      | cons y ys =>
        cases ys with
        | nil =>
          simp at h4
          exact absurd (h4.1 ▸ (by rw [h3]; simp)) hx
        | cons z zs =>
          simp at h4
          exact absurd (h4.1 ▸ (by rw [h3]; simp)) hx
    · left; exact ⟨u, c'', by rw [h1, h3]; simp⟩
  · cases c' with
    | nil =>
      cases t with
      | nil => right; exact List.nil_infix
      | cons y ys =>
        simp at h2
        exact absurd (h2.1 ▸ (by simp)) hx
    | cons y ys =>
      simp at h2
      right; exact ⟨ys, v, by rw [h2.2]; simp⟩

theorem toLower_space : Char.toLower ' ' = ' ' := by decide

theorem toLower_lf : Char.toLower '\n' = '\n' := by decide

theorem no_sep_block (t raw : List Char) (i : Nat) (ht1 : '\n' ∉ t) (ht2 : ' ' ∉ t) (hne : t ≠ [])
    (hr : ¬ t <:+: raw) : ¬ t <:+: ('\n' :: raw ++ '\n' :: padL i) := by
  intro h
  rw [show '\n' :: raw ++ '\n' :: padL i = [] ++ '\n' :: (raw ++ '\n' :: padL i) by simp] at h
  rcases infix_sep ht1 h with h1 | h1
  · exact hne (List.eq_nil_of_infix_nil h1)
  · rcases infix_sep ht1 h1 with h2 | h2
    · exact hr h2
    · obtain ⟨c, hc⟩ : ∃ c, c ∈ t := by
        cases t with
        | nil => exact absurd rfl hne
        | cons c _ => exact ⟨c, by simp⟩
      have := h2.subset hc
      simp only [padL, List.mem_replicate] at this
      exact ht2 (this.2 ▸ hc)

theorem no_term_block (t raw : List Char) (i : Nat) (ht1 : '\n' ∉ t) (ht2 : ' ' ∉ t) (hne : t ≠ [])
    (hr : ¬ t <:+: raw.map Char.toLower) :
    ¬ t <:+: (('\n' :: raw ++ '\n' :: padL i).map Char.toLower) := by
  have hm : (('\n' :: raw ++ '\n' :: padL i).map Char.toLower) =
      '\n' :: raw.map Char.toLower ++ '\n' :: padL i := by
    simp [padL, toLower_lf, toLower_space, List.map_replicate]
  rw [hm]
  exact no_sep_block t _ i ht1 ht2 hne hr

theorem style_no_term (css : String) :
    ¬ ('<' :: '/' :: "style".toList) <:+: ((rawPayload "</style" css).toList.map Char.toLower) := by
  have h := rawPayload_style_no_terminator css
  intro hi
  have : hasTerm "</style".toList ((rawPayload "</style" css).toList.map Char.toLower) = true :=
    (hasTerm_iff _ _ (by decide)).mpr hi
  rw [h] at this
  exact Bool.false_ne_true this

theorem script_no_term (js : String) :
    ¬ ('<' :: '/' :: "script".toList) <:+: ((rawPayload "</script" js).toList.map Char.toLower) := by
  have h := rawPayload_script_no_terminator js
  intro hi
  have : hasTerm "</script".toList ((rawPayload "</script" js).toList.map Char.toLower) = true :=
    (hasTerm_iff _ _ (by decide)).mpr hi
  rw [h] at this
  exact Bool.false_ne_true this

/-- An element's end tag at the current node, its children read: the element closed into its
parent. -/
theorem stop_close (b1 : Builder) (hm : b1.mode = .inBody ∨ b1.mode = .inHead) (hs : b1.stack ≠ [])
    (hd : b1.dropLF = false) (ns : Ns) (t : String) (a : Array (String × String)) (X : Array Dom)
    (ht : t ≠ "body" ∧ t ≠ "head") :
    stop { mode := b1.mode, stack := Frame.mk ns t a X :: b1.stack, dropLF := false } t =
      some (withTop b1 (·.push (.elem t a X))) := by
  rcases b1 with ⟨m, st, dl⟩
  simp only at hd hs hm ⊢
  subst hd
  cases st with
  | nil => exact absurd rfl hs
  | cons f rest =>
    have hb : (t == "body") = false := by simpa using ht.1
    have hh : (t == "head") = false := by simpa using ht.2
    rcases hm with rfl | rfl
    · simp [stop, hb, closeCurrent, Frame.close, withTop]
    · simp [stop, hh, closeCurrent, Frame.close, withTop]

/-- A raw element's content and end tag read after its start tag: the payload its one text. -/
theorem run_rawElem (b1 : Builder) (hm : b1.mode = .inBody ∨ b1.mode = .inHead)
    (hs : b1.stack ≠ []) (hd : b1.dropLF = false) (k : Content) (hk : k ≠ .rcdata)
    (name : String) (hn : rawName name = true) (hname : name = "style" ∨ name = "script")
    (a : Array (String × String)) (p : List Char) (hz : ∀ c ∈ p, c ≠ '\x00')
    (hterm : ¬ ('<' :: '/' :: name.toList) <:+: (p.map Char.toLower))
    (hbang : k = .script → ¬ ['<', '!'] <:+: p) :
    run (some ⟨.raw k name, Builder.mk b1.mode (Frame.mk .html name a #[] :: b1.stack) false⟩)
        (p ++ closeL name) =
      some ⟨.data, withTop b1 (·.push (.elem name a (addL #[] p)))⟩ := by
  let b2 : Builder := Builder.mk b1.mode (Frame.mk .html name a #[] :: b1.stack) false
  have hT : InText b2 := {
    text := by rcases hname with rfl | rfl <;> simp [b2, inText, currentIs]
    late := late_of hm
    nonempty := by simp [b2]
    noLF := rfl }
  have h0 : withTop b2 (addL · []) = b2 := withTop_id b2 _ (fun _ => rfl)
  obtain ⟨σ, e, h1, hinv⟩ := raw_fold k hk name hT p hz hterm hbang p [] (.raw k name) []
    (by simp) ⟨Or.inl rfl, by simp [pendOf]⟩
  rw [h0] at h1
  rw [run_append, h1, raw_close k name hn hT σ e p hinv]
  have hw : { withTop b2 (addL · p) with dropLF := false } =
      Builder.mk b1.mode (Frame.mk .html name a (addL #[] p) :: b1.stack) false := by
    simp [b2, withTop]
  rw [hw, stop_close b1 hm hs hd .html name a _ (by rcases hname with rfl | rfl <;> decide)]
  rfl

theorem sameShape_trans : ∀ {s t u : List Frame}, sameShape s t → sameShape t u → sameShape s u
  | [], [], [], _, _ => trivial
  | _ :: _, _ :: _, _ :: _, ⟨a, b, c, d⟩, ⟨a', b', c', d'⟩ =>
    ⟨a.trans a', b.trans b', c.trans c', sameShape_trans d d'⟩
  | [], _ :: _, _, h, _ => absurd h (by simp [sameShape])
  | _ :: _, [], _, h, _ => absurd h (by simp [sameShape])
  | [], [], _ :: _, _, h => absurd h (by simp [sameShape])
  | _ :: _, _ :: _, [], _, h => absurd h (by simp [sameShape])

theorem stack_shape_withTop (b : Builder) (g : Array Dom → Array Dom) (s : List Frame)
    (h : sameShape b.stack s) : sameShape (withTop b g).stack s :=
  sameShape_trans (withTop_shape b g) h

theorem sameShape_symm : ∀ {s t : List Frame}, sameShape s t → sameShape t s
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨a, b, c, d⟩ => ⟨a.symm, b.symm, c.symm, sameShape_symm d⟩
  | [], _ :: _, h => absurd h (by simp [sameShape])
  | _ :: _, [], h => absurd h (by simp [sameShape])

theorem nsIn_html_of (m : Mode) (s : List Frame) (t : String) (hc : htmlContext s = true)
    (ht : t ≠ "svg" ∧ t ≠ "math") : nsIn m s t = .html := by
  unfold nsIn nsFor
  split
  · rfl
  · simp [ht.1, ht.2]

theorem lower_style : lower "style" = "style" := by decide

theorem lower_script : lower "script" = "script" := by decide

theorem rawName_style : rawName "style" = true := by decide

theorem rawName_script : rawName "script" = true := by decide

theorem payload_parts (script : Bool) (p : String) (h : payloadOk script p = true) :
    (∀ c ∈ p.toList, c ≠ '\x00') ∧ (script = true → ¬ ['<', '!'] <:+: p.toList) := by
  simp only [payloadOk, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true',
    Bool.and_eq_false_iff, decide_eq_false_iff_not] at h
  refine ⟨fun c hc => (h.1 c hc).1, fun hs => ?_⟩
  rcases h.2 with h2 | h2
  · simp [hs] at h2
  · exact h2

theorem block_payload_parts (script : Bool) (raw : String) (i : Nat) (h : payloadOk script raw = true) :
    (∀ c ∈ '\n' :: raw.toList ++ '\n' :: padL i, c ≠ '\x00') ∧
      (script = true → ¬ ['<', '!'] <:+: ('\n' :: raw.toList ++ '\n' :: padL i)) := by
  obtain ⟨h1, h2⟩ := payload_parts script raw h
  refine ⟨fun c hc => ?_, fun hs => no_sep_block _ _ i (by decide) (by decide) (by simp) (h2 hs)⟩
  by_cases hr : c ∈ raw.toList
  · exact h1 c hr
  · have : c = '\n' ∨ c = ' ' := by
      simp [padL, hr] at hc
      rcases hc with h | h
      · exact Or.inl h
      · exact Or.inr h.2
    rcases this with rfl | rfl <;> decide

theorem InFlow.top {b : Builder} (h : InFlow b) (g : Array Dom → Array Dom) : InFlow (withTop b g) :=
  ⟨by rw [withTop_mode]; exact h.mode, stack_ne_withTop h.nonempty g⟩

theorem InFlow.late {b : Builder} (h : InFlow b) : Late b.mode := late_of h.mode

theorem style_parts {m : Mode} {s : List Frame} {css : String}
    (h : Accepts m s (.style css) = true) :
    htmlContext s = true ∧ startOk m s "style" #[] = true ∧
      payloadOk false (rawPayload "</style" css) = true := by
  simp only [Accepts, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem script_parts {m : Mode} {s : List Frame} {attrs : Array (String × String)} {js : String}
    (h : Accepts m s (.script attrs js) = true) :
    htmlContext s = true ∧ validAttrs attrs = true ∧ startOk m s "script" (lowAttrs attrs) = true ∧
      payloadOk true (rawPayload "</script" js) = true := by
  simp only [Accepts, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- A raw element read from its start tag to its end tag, its payload `p`. -/
theorem run_rawNode (b1 : Builder) (hf : InFlow b1) (hd : b1.dropLF = false) (name : String)
    (hname : name = "style" ∨ name = "script") (k : Content)
    (hk : k = (if name == "style" then .rawtext else .script))
    (a : Array (String × String)) (ha : validAttrs a = true)
    (hctx : htmlContext b1.stack = true) (hok : startOk b1.mode b1.stack name (lowAttrs a) = true)
    (p : List Char) (hz : ∀ c ∈ p, c ≠ '\x00')
    (hterm : ¬ ('<' :: '/' :: name.toList) <:+: (p.map Char.toLower))
    (hbang : k = .script → ¬ ['<', '!'] <:+: p) :
    run (some ⟨.data, b1⟩) (('<' :: name.toList ++ attrsL a.toList ++ ['>']) ++ (p ++ closeL name)) =
      some ⟨.data, withTop b1 (·.push (.elem name (lowAttrs a) (addL #[] p)))⟩ := by
  have hlow : lower name = name := by rcases hname with rfl | rfl <;> decide
  have hvt : validTag name = true := by rcases hname with rfl | rfl <;> decide
  have hns : nsIn b1.mode b1.stack name = .html :=
    nsIn_html_of _ _ _ hctx (by rcases hname with rfl | rfl <;> decide)
  have hv : (HtmlRead.voidTags.contains name && nsIn b1.mode b1.stack name == .html) = false := by
    have : HtmlRead.voidTags.contains name = false := by rcases hname with rfl | rfl <;> decide
    rw [this, Bool.false_and]
  rw [run_append, run_startTag b1 name a hvt ha, hlow,
    start_open b1 hf.mode name _ hok hv, hns]
  have hc : contentOf .html name = k := by
    rcases hname with rfl | rfl <;> simp [contentOf, hk]
  have hpre : (b1.mode == .inBody && Ns.html == Ns.html && (name == "pre" || name == "listing")) = false := by
    rcases hname with rfl | rfl <;> simp
  have hkd : k ≠ .data := by rcases hname with rfl | rfl <;> simp [hk]
  have hkr : k ≠ .rcdata := by rcases hname with rfl | rfl <;> simp [hk]
  have haf : after k name .data = .raw k name := by
    cases k <;> simp_all [after]
  simp only [Option.map_some, hc, hpre, haf]
  exact run_rawElem b1 hf.mode hf.nonempty hd k hkr name
    (by rcases hname with rfl | rfl <;> decide) hname (lowAttrs a) p hz hterm hbang

theorem simB_style (css : String) (i : Nat) (b : Builder) (hf : InFlow b) (hd : b.dropLF = false)
    (h : Accepts b.mode b.stack (.style css) = true) :
    run (some ⟨.data, b⟩) (rB (.style css) i) = some ⟨.data, withTop b (fB · (.style css) i)⟩ := by
  obtain ⟨hctx, hok, hpay⟩ := style_parts h
  obtain ⟨hz, _⟩ := block_payload_parts false _ i hpay
  have e : rB (.style css) i = padL i ++ ((('<' :: "style".toList ++ attrsL (#[] : Array (String × String)).toList ++ ['>']) ++
      (('\n' :: (rawPayload "</style" css).toList ++ '\n' :: padL i) ++ closeL "style")) ++ ['\n']) := by
    simp [rB, attrsL]
  rw [e, run_append, run_ws b _ hd hf.late hf.nonempty (padL_ws i), run_append]
  have hf1 := hf.top (addL · (padL i))
  have hshape := withTop_shape b (addL · (padL i))
  rw [run_rawNode (withTop b (addL · (padL i))) hf1 (by rw [withTop_dropLF]; exact hd) "style"
    (Or.inl rfl) .rawtext rfl #[] (by simp [validAttrs]) (by rw [htmlContext_shape hshape]; exact hctx)
    (by rw [withTop_mode, startOk_shape _ _ _ hshape]; exact hok) _ hz
    (no_term_block _ _ i (by decide) (by decide) (by simp) (style_no_term css)) (by simp),
    withTop_comp, run_ws _ _ (by rw [withTop_dropLF]; exact hd)
      (by rw [withTop_mode]; exact hf.late) (stack_ne_withTop hf.nonempty _) (by simp),
    withTop_comp]
  congr 3
  funext K
  simp [fB, lowAttrs]

/-! ### Elements -/

theorem bodyAccepts_textarea (s : List Frame) : bodyAccepts s "textarea" = false := by
  unfold bodyAccepts tablePartOk
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;>
    simp_all [bodyTags]

theorem bodyAccepts_listing (s : List Frame) : bodyAccepts s "listing" = false := by
  unfold bodyAccepts tablePartOk
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;>
    simp_all [bodyTags]

theorem elem_parts {m : Mode} {s : List Frame} {tag : String} {attrs : Array (String × String)}
    {kids : Array Node} (h : Accepts m s (.elem tag attrs kids) = true) : ElemOk m s tag attrs kids := by
  simp only [Accepts, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, bne_iff_ne, ne_eq,
    Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨h1, h2, ?_, h4, h5, ?_, ?_, h8⟩
  · simp only [List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_false_iff,
      beq_eq_false_iff_ne, ne_eq] at h3
    exact ⟨h3.1, h3.2.1, h3.2.2⟩
  · rcases h6 with h6 | h6
    · exact Or.inl h6
    · exact Or.inr (by simpa using h6)
  · rcases h7 with h7 | h7
    · exact Or.inl (by simpa using h7)
    · exact Or.inr (by simpa using h7)

theorem run_open (b1 : Builder) (hf : InFlow b1) (tag : String) (attrs : Array (String × String))
    (kids : Array Node) (h : ElemOk b1.mode b1.stack tag attrs kids)
    (hnv : Html.voidTags.contains tag = false) :
    run (some ⟨.data, b1⟩) ('<' :: tag.toList ++ attrsL attrs.toList ++ ['>']) =
      some ⟨after (contentOf (nsIn b1.mode b1.stack (lower tag)) (lower tag)) (lower tag) .data,
        Builder.mk b1.mode
          (Frame.mk (nsIn b1.mode b1.stack (lower tag)) (lower tag) (lowAttrs attrs) #[] :: b1.stack)
          (b1.mode == .inBody && nsIn b1.mode b1.stack (lower tag) == .html &&
            (lower tag == "pre" || lower tag == "listing"))⟩ := by
  rw [run_startTag b1 tag attrs h.vtag h.vattrs, start_open b1 hf.mode _ _ h.start (by rw [h.void, hnv])]
  rfl

theorem run_close (b1 : Builder) (hf : InFlow b1) (hd : b1.dropLF = false) (tag : String)
    (hv : validTag tag = true) (hs : lower tag ≠ "body" ∧ lower tag ≠ "head") (ns : Ns)
    (a : Array (String × String)) (X : Array Dom) (d : Bool) :
    run (some ⟨.data, Builder.mk b1.mode (Frame.mk ns (lower tag) a X :: b1.stack) d⟩) (closeL tag) =
      some ⟨.data, withTop b1 (·.push (.elem (lower tag) a X))⟩ := by
  rw [run_stopTag _ tag hv]
  have : { Builder.mk b1.mode (Frame.mk ns (lower tag) a X :: b1.stack) d with dropLF := false } =
      Builder.mk b1.mode (Frame.mk ns (lower tag) a X :: b1.stack) false := rfl
  rw [this, stop_close b1 hf.mode hf.nonempty hd ns (lower tag) a X hs]
  rfl

theorem ElemOk.shape {m : Mode} {s t : List Frame} {tag : String} {attrs : Array (String × String)}
    {kids : Array Node} (h : ElemOk m s tag attrs kids) (hs : sameShape t s) :
    ElemOk m t tag attrs kids where
  vtag := h.vtag
  vattrs := h.vattrs
  skel := h.skel
  start := by rw [startOk_shape _ _ _ hs]; exact h.start
  void := by rw [nsIn_shape _ _ hs]; exact h.void
  same := by rw [nsIn_shape _ _ hs]; exact h.same
  lf := by rw [nsIn_shape _ _ hs]; exact h.lf
  kidsOk := by
    have := h.kidsOk
    rw [nsIn_shape _ _ hs]
    split at this
    · next hv => simp only [hv, ite_true]; exact this
    · next hv =>
      simp only [hv, Bool.false_eq_true, ite_false] at this ⊢
      split
      · next hc =>
        rw [hc] at this
        rw [AcceptsList_shape _ (sameShape_push _ hs)]
        exact this
      · next hc => rw [hc] at this; exact this
      · next hc1 hc2 =>
        exfalso
        cases hcc : contentOf (nsIn m s (lower tag)) (lower tag) <;> simp_all

theorem headTags_not_lf (t : String) (h : headTags.contains t = true) :
    t ≠ "pre" ∧ t ≠ "listing" ∧ t ≠ "textarea" := by
  have : t ∈ headTags := by simpa using h
  simp only [headTags, List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem ns_html_body {m : Mode} {s : List Frame} {t : String} (h : nsIn m s t = .html)
    (hm : m = .inBody) : htmlContext s = true := by
  unfold nsIn nsFor at h
  rw [hm] at h
  simp only [show (Mode.inBody == Mode.inHead) = false from rfl, Bool.false_eq_true, ite_false] at h
  split at h
  · next hc => exact hc
  · next hc =>
    exfalso
    cases s with
    | nil => simp [htmlContext] at hc
    | cons f rest =>
      simp only [htmlContext] at hc
      exact hc (by simp [h])

theorem lf_eq_dl {m : Mode} {s : List Frame} {tag : String} {attrs : Array (String × String)}
    {kids : Array Node} (h : ElemOk m s tag attrs kids) (hm : m = .inBody ∨ m = .inHead) :
    lfTags.contains tag = (m == .inBody && nsIn m s (lower tag) == .html &&
      (lower tag == "pre" || lower tag == "listing")) := by
  have hst := h.start
  by_cases hl : lfTags.contains tag = true
  · rw [hl]
    have hns : nsIn m s (lower tag) = .html := by
      rcases h.lf with h1 | h1
      · exact h1
      · rw [h1] at hl; exact absurd hl (by decide)
    have ht : lower tag = tag := by
      rcases h.same with h1 | h1
      · exact absurd hns h1
      · exact h1
    have hmem : tag ∈ lfTags := by simpa using hl
    simp only [lfTags, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hm with hm | hm
    · have hc := ns_html_body hns hm
      simp only [startOk, hm, startAccepts, hc, ite_true] at hst
      rcases hmem with rfl | rfl | rfl
      · rw [ht] at hns ⊢; rw [hm] at hns; simp [hm, hns]
      · rw [ht, bodyAccepts_listing] at hst; exact absurd hst (by simp)
      · rw [ht, bodyAccepts_textarea] at hst; exact absurd hst (by simp)
    · simp only [startOk, hm] at hst
      have := headTags_not_lf _ hst
      rw [ht] at this
      rcases hmem with rfl | rfl | rfl <;> simp_all
  · have hl' : lfTags.contains tag = false := by simpa using hl
    rw [hl']
    symm
    simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq, Bool.or_eq_false_iff]
    by_cases hb : m = .inBody
    · by_cases hns : nsIn m s (lower tag) = .html
      · right
        have ht : lower tag = tag := by
          rcases h.same with h1 | h1
          · exact absurd hns h1
          · exact h1
        rw [ht]
        constructor
        · intro hp; rw [hp] at hl'; exact absurd hl' (by decide)
        · intro hp; rw [hp] at hl'; exact absurd hl' (by decide)
      · left; right; exact hns
    · left; left; simpa using hb

theorem leadsLF_cons_text_empty (rest : List Node) : leadsLF (.text "" :: rest) = leadsLF rest := by
  simp [leadsLF]

theorem withTop_mk (m : Mode) (ns : Ns) (t : String) (a : Array (String × String)) (K : Array Dom)
    (rest : List Frame) (d : Bool) (g : Array Dom → Array Dom) :
    withTop (Builder.mk m (Frame.mk ns t a K :: rest) d) g = Builder.mk m (Frame.mk ns t a (g K) :: rest) d :=
  rfl

theorem step_lf_dropped (b : Builder) (hb : b.dropLF = true) :
    step ⟨.data, b⟩ '\n' = some ⟨.data, { b with dropLF := false }⟩ := by
  simp [step, emit, HtmlRead.build, hb]

/-- An element whose children render inline, read from its start tag to its end tag. -/
theorem run_elemInline (b1 : Builder) (hf1 : InFlow b1) (hd1 : b1.dropLF = false) (tag : String)
    (attrs : Array (String × String)) (kids : Array Node) (h : ElemOk b1.mode b1.stack tag attrs kids)
    (hnv : Html.voidTags.contains tag = false)
    (hc : contentOf (nsIn b1.mode b1.stack (lower tag)) (lower tag) = .data)
    (ihIL : ∀ b', InFlow b' → (b'.dropLF = true → leadsLF kids.toList = false) →
      AcceptsList b'.mode b'.stack kids.toList = true →
      run (some ⟨.data, b'⟩) (rIL [] kids.toList) =
        some ⟨.data, withTop { b' with dropLF := b'.dropLF && (rIL [] kids.toList).isEmpty }
          (fIL · kids.toList)⟩) :
    run (some ⟨.data, b1⟩) (('<' :: tag.toList ++ attrsL attrs.toList ++ ['>']) ++
        ((lfGuard tag kids).toList ++ (rIL [] kids.toList ++ closeL tag))) =
      some ⟨.data, withTop b1 (·.push (.elem (lower tag) (lowAttrs attrs) (fIL #[] kids.toList)))⟩ := by
  have hkids : AcceptsList b1.mode (⟨nsIn b1.mode b1.stack (lower tag), lower tag, lowAttrs attrs, #[]⟩ ::
      b1.stack) kids.toList = true := by
    have := h.kidsOk
    simp only [hnv, Bool.false_eq_true, ite_false, hc] at this
    exact this
  rw [run_append, run_open b1 hf1 tag attrs kids h hnv, hc]
  simp only [after]
  have hlf := lf_eq_dl h hf1.mode
  generalize (b1.mode == .inBody && nsIn b1.mode b1.stack (lower tag) == .html &&
    (lower tag == "pre" || lower tag == "listing")) = dl at hlf ⊢
  have hguard : lfGuard tag kids = if (dl && leadsLF kids.toList) = true then "\n" else "" := by
    unfold lfGuard; rw [hlf]
  have hfin : ∀ d, run (some ⟨.data, Builder.mk b1.mode (Frame.mk (nsIn b1.mode b1.stack (lower tag))
      (lower tag) (lowAttrs attrs) (fIL #[] kids.toList) :: b1.stack) d⟩) (closeL tag) =
      some ⟨.data, withTop b1 (·.push (.elem (lower tag) (lowAttrs attrs) (fIL #[] kids.toList)))⟩ :=
    fun d => run_close b1 hf1 hd1 tag h.vtag ⟨h.skel.2.2, h.skel.2.1⟩ _ _ _ d
  by_cases hg : (dl && leadsLF kids.toList) = true
  · rw [hguard, ite_eq_left hg]
    have hdl1 : dl = true := by simp_all
    show run (some _) ('\n' :: (rIL [] kids.toList ++ closeL tag)) = _
    rw [run_cons, step_lf_dropped _ hdl1]
    rw [run_append, ihIL (Builder.mk b1.mode (Frame.mk (nsIn b1.mode b1.stack (lower tag))
      (lower tag) (lowAttrs attrs) #[] :: b1.stack) false) ⟨hf1.mode, by simp⟩ (by simp) hkids,
      withTop_mk, hfin]
  · rw [hguard, ite_eq_right hg]
    show run (some _) (rIL [] kids.toList ++ closeL tag) = _
    rw [run_append, ihIL (Builder.mk b1.mode (Frame.mk (nsIn b1.mode b1.stack (lower tag))
      (lower tag) (lowAttrs attrs) #[] :: b1.stack) dl) ⟨hf1.mode, by simp⟩
      (fun h1 => by simp_all) hkids, withTop_mk, hfin]

theorem fIL_texts (l : List Node) (hl : l.all rcText = true) : ∀ K, fIL K l = addL K (textsOf l) := by
  induction l with
  | nil => intro K; rfl
  | cons n rest ih =>
    intro K
    simp only [List.all_cons, Bool.and_eq_true] at hl
    cases n with
    | text x => simp [fIL, fI, textsOf, textOf, ih hl.2, addL_append]
    | _ => simp [rcText] at hl

theorem run_rcTexts (n : String) (l : List Node) (hl : l.all rcText = true) :
    ∀ b : Builder, InText b → run (some ⟨.raw .rcdata n, b⟩) (rIL [] l) =
      some ⟨.raw .rcdata n, withTop b (addL · (textsOf l))⟩ := by
  induction l with
  | nil => intro b _; simp [rIL, textsOf, run_nil, withTop_id b _ (fun _ => rfl), addL]
  | cons k rest ih =>
    intro b hb
    simp only [List.all_cons, Bool.and_eq_true] at hl
    cases k with
    | text x =>
      have hx : ∀ c ∈ x.toList, charKeeps b.mode b.stack c = true ∧ c ≠ '\x00' := by
        intro c hc
        have := hl.1
        simp [rcText] at this
        exact ⟨by simp [charKeeps, hb.text], (this c hc).1⟩
      have h1 := run_escText (Home.rcdata n) x.toList b hb.noLF hb.late hb.nonempty hx
      simp only [Home.tok] at h1
      rw [rIL_cons, rI, run_append, h1, ih hl.2 _ (hb.top _), withTop_comp]
      simp only [textsOf, List.flatMap_cons, textOf]
      congr 3
      funext K
      simp [addL_append]
    | _ => simp [rcText] at hl

theorem contentOf_rcdata {ns : Ns} {t : String} (h : contentOf ns t = .rcdata) :
    ns = .html ∧ (t = "title" ∨ t = "textarea") := by
  unfold contentOf at h
  split at h
  · cases h
  · next hns =>
    have hns' : ns = .html := by cases ns <;> simp_all
    refine ⟨hns', ?_⟩
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · next ht => simpa using ht
        · cases h

/-- A title read from its start tag to its end tag, its text as RCDATA. -/
theorem run_elemRcdata (b1 : Builder) (hf1 : InFlow b1) (hd1 : b1.dropLF = false) (tag : String)
    (attrs : Array (String × String)) (kids : Array Node) (h : ElemOk b1.mode b1.stack tag attrs kids)
    (hnv : Html.voidTags.contains tag = false)
    (hc : contentOf (nsIn b1.mode b1.stack (lower tag)) (lower tag) = .rcdata) :
    run (some ⟨.data, b1⟩) (('<' :: tag.toList ++ attrsL attrs.toList ++ ['>']) ++
        ((lfGuard tag kids).toList ++ (rIL [] kids.toList ++ closeL tag))) =
      some ⟨.data, withTop b1 (·.push (.elem (lower tag) (lowAttrs attrs) (fIL #[] kids.toList)))⟩ := by
  obtain ⟨hns, ht⟩ := contentOf_rcdata hc
  have htt : lower tag = "title" := by
    rcases ht with ht | ht
    · exact ht
    · exfalso
      have hst := h.start
      rcases hf1.mode with hm | hm
      · have hctx := ns_html_body hns hm
        simp only [startOk, hm, startAccepts, hctx, ite_true, ht, bodyAccepts_textarea] at hst
        exact absurd hst (by simp)
      · simp only [startOk, hm] at hst
        exact (headTags_not_lf _ hst).2.2 ht
  have htag : tag = "title" := by
    rcases h.same with h1 | h1
    · exact absurd hns h1
    · rw [← h1]; exact htt
  have hkids : kids.toList.all rcText = true := by
    have := h.kidsOk
    simp only [hnv, Bool.false_eq_true, ite_false, hc] at this
    rw [List.all_eq_true] at this ⊢
    intro k hk
    have := this k hk
    cases k <;> simp_all [rcText]
  have hguard : lfGuard tag kids = "" := by rw [htag]; simp [lfGuard, lfTags]
  rw [run_append, run_open b1 hf1 tag attrs kids h hnv, hc, hguard]
  simp only [after, String.toList_empty, List.nil_append]
  have hdl : (b1.mode == .inBody && nsIn b1.mode b1.stack (lower tag) == .html &&
      (lower tag == "pre" || lower tag == "listing")) = false := by
    rw [htt]; simp
  rw [hdl, hns, htt]
  let b2 : Builder := Builder.mk b1.mode (Frame.mk .html "title" (lowAttrs attrs) #[] :: b1.stack) false
  have hT : InText b2 := {
    text := by simp [b2, inText, currentIs]
    late := hf1.late
    nonempty := by simp [b2]
    noLF := rfl }
  rw [run_append, run_rcTexts "title" kids.toList hkids b2 hT]
  rw [show closeL tag = closeL "title" by rw [htag]]
  rw [raw_close .rcdata "title" (by decide) hT (.raw .rcdata "title") (textsOf kids.toList)
    (textsOf kids.toList) ⟨Or.inl rfl, by simp [pendOf]⟩]
  have hw : { withTop b2 (addL · (textsOf kids.toList)) with dropLF := false } =
      Builder.mk b1.mode (Frame.mk .html "title" (lowAttrs attrs) (addL #[] (textsOf kids.toList)) ::
        b1.stack) false := by simp [b2, withTop]
  rw [hw, stop_close b1 hf1.mode hf1.nonempty hd1 .html "title" _ _ (by decide),
    fIL_texts _ hkids]
  rfl

/-- An element whose children render as blocks, read from its start tag to its end tag. -/
theorem run_elemBlock (b1 : Builder) (hf1 : InFlow b1) (hd1 : b1.dropLF = false) (tag : String)
    (attrs : Array (String × String)) (kids : Array Node) (i : Nat)
    (h : ElemOk b1.mode b1.stack tag attrs kids) (hnv : Html.voidTags.contains tag = false)
    (hc : contentOf (nsIn b1.mode b1.stack (lower tag)) (lower tag) = .data)
    (hinl : inl tag kids = false)
    (ihBL : ∀ b', InFlow b' → b'.dropLF = false → AcceptsList b'.mode b'.stack kids.toList = true →
      run (some ⟨.data, b'⟩) (rBL [] kids.toList (i + 1)) =
        some ⟨.data, withTop b' (fBL · kids.toList (i + 1))⟩) :
    run (some ⟨.data, b1⟩) (('<' :: tag.toList ++ attrsL attrs.toList ++ ['>']) ++
        (['\n'] ++ (rBL [] kids.toList (i + 1) ++ (padL i ++ closeL tag)))) =
      some ⟨.data, withTop b1 (·.push (.elem (lower tag) (lowAttrs attrs)
        (addL (fBL (addL #[] ['\n']) kids.toList (i + 1)) (padL i))))⟩ := by
  have hkids : AcceptsList b1.mode (⟨nsIn b1.mode b1.stack (lower tag), lower tag, lowAttrs attrs, #[]⟩ ::
      b1.stack) kids.toList = true := by
    have := h.kidsOk
    simp only [hnv, Bool.false_eq_true, ite_false, hc] at this
    exact this
  have hdl : (b1.mode == .inBody && nsIn b1.mode b1.stack (lower tag) == .html &&
      (lower tag == "pre" || lower tag == "listing")) = false := by
    have hlf := lf_eq_dl h hf1.mode
    rw [← hlf]
    by_cases hl : lfTags.contains tag = true
    · exfalso
      have hmem : tag ∈ lfTags := by simpa using hl
      simp only [lfTags, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl
      · simp [inl, preserveTags] at hinl
      · rw [hlf] at hl
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hl
        obtain ⟨⟨hm, hns⟩, _⟩ := hl
        have hctx := ns_html_body hns hm
        have hst := h.start
        have ht : lower "listing" = "listing" := by decide
        simp only [startOk, hm, startAccepts, hctx, ite_true, ht, bodyAccepts_listing] at hst
        exact absurd hst (by simp)
      · simp [inl, preserveTags] at hinl
    · simpa using hl
  rw [run_append, run_open b1 hf1 tag attrs kids h hnv, hc, hdl]
  simp only [after]
  let b2 : Builder := Builder.mk b1.mode (Frame.mk (nsIn b1.mode b1.stack (lower tag)) (lower tag)
    (lowAttrs attrs) #[] :: b1.stack) false
  have hf2 : InFlow b2 := ⟨hf1.mode, by simp [b2]⟩
  rw [run_append, run_ws b2 ['\n'] rfl hf2.late hf2.nonempty (by simp), run_append,
    ihBL _ (hf2.top _) (by rw [withTop_dropLF]) (by
      rw [withTop_mode, AcceptsList_shape _ (withTop_shape b2 _)]; exact hkids),
    withTop_comp, run_append, run_ws _ _ (by rw [withTop_dropLF]) (by rw [withTop_mode]; exact hf2.late)
      (stack_ne_withTop hf2.nonempty _) (padL_ws i), withTop_comp]
  simp only [b2, withTop_mk, Function.comp]
  exact run_close b1 hf1 hd1 tag h.vtag ⟨h.skel.2.2, h.skel.2.1⟩ _ _ _ false

/-- A void element read from its start tag. -/
theorem run_elemVoid (b1 : Builder) (hf1 : InFlow b1) (hd1 : b1.dropLF = false) (tag : String)
    (attrs : Array (String × String)) (kids : Array Node) (h : ElemOk b1.mode b1.stack tag attrs kids)
    (hv : Html.voidTags.contains tag = true) :
    run (some ⟨.data, b1⟩) ('<' :: tag.toList ++ attrsL attrs.toList ++ ['>']) =
      some ⟨.data, withTop b1 (·.push (.elem (lower tag) (lowAttrs attrs) #[]))⟩ := by
  rw [run_startTag b1 tag attrs h.vtag h.vattrs,
    start_void b1 hf1.mode hf1.nonempty _ _ h.start (by rw [h.void, hv]), dropLF_false _ hd1]
  rfl

theorem pad_top (b : Builder) (hf : InFlow b) (hd : b.dropLF = false) (i : Nat) (rest : List Char) :
    run (some ⟨.data, b⟩) (padL i ++ rest) = run (some ⟨.data, withTop b (addL · (padL i))⟩) rest := by
  rw [run_append, run_ws b _ hd hf.late hf.nonempty (padL_ws i)]

theorem lf_top (b : Builder) (hf : InFlow b) (hd : b.dropLF = false) :
    run (some ⟨.data, b⟩) ['\n'] = some ⟨.data, withTop b (addL · ['\n'])⟩ :=
  run_ws b _ hd hf.late hf.nonempty (by simp)

theorem simB_elem (tag : String) (attrs : Array (String × String)) (kids : Array Node) (i : Nat)
    (b : Builder) (hf : InFlow b) (hd : b.dropLF = false)
    (h : Accepts b.mode b.stack (.elem tag attrs kids) = true)
    (ihBL : ∀ b', InFlow b' → b'.dropLF = false → AcceptsList b'.mode b'.stack kids.toList = true →
      run (some ⟨.data, b'⟩) (rBL [] kids.toList (i + 1)) =
        some ⟨.data, withTop b' (fBL · kids.toList (i + 1))⟩)
    (ihIL : ∀ b', InFlow b' → (b'.dropLF = true → leadsLF kids.toList = false) →
      AcceptsList b'.mode b'.stack kids.toList = true →
      run (some ⟨.data, b'⟩) (rIL [] kids.toList) =
        some ⟨.data, withTop { b' with dropLF := b'.dropLF && (rIL [] kids.toList).isEmpty }
          (fIL · kids.toList)⟩) :
    run (some ⟨.data, b⟩) (rB (.elem tag attrs kids) i) =
      some ⟨.data, withTop b (fB · (.elem tag attrs kids) i)⟩ := by
  have he := elem_parts h
  let b1 := withTop b (addL · (padL i))
  have hf1 : InFlow b1 := hf.top _
  have hd1 : b1.dropLF = false := by simp [b1, withTop_dropLF, hd]
  have he1 : ElemOk b1.mode b1.stack tag attrs kids := by
    have := he.shape (withTop_shape b (addL · (padL i)))
    have hb1m : b1.mode = b.mode := withTop_mode b _
    rw [hb1m]
    exact this
  have hlast : ∀ X : Array Dom, run (some ⟨.data, withTop b1 (·.push (.elem (lower tag) (lowAttrs attrs) X))⟩) ['\n'] =
      some ⟨.data, withTop b (fun K => addL ((addL K (padL i)).push (.elem (lower tag) (lowAttrs attrs) X)) ['\n'])⟩ := by
    intro X
    rw [lf_top _ (hf1.top _) (by rw [withTop_dropLF]; exact hd1), withTop_comp, withTop_comp]
    rfl
  by_cases hv : Html.voidTags.contains tag = true
  · have hv' : tag ∈ Html.voidTags := by simpa using hv
    have e : rB (.elem tag attrs kids) i = padL i ++ (('<' :: tag.toList ++ attrsL attrs.toList ++ ['>']) ++ ['\n']) := by
      simp [rB, hv']
    rw [e, pad_top b hf hd, run_append, run_elemVoid b1 hf1 hd1 tag attrs kids he1 hv, hlast]
    congr 3
    funext K
    simp [fB, hv']
  · have hnv : Html.voidTags.contains tag = false := by simpa using hv
    have hnv' : tag ∉ Html.voidTags := by simpa using hv
    by_cases hi : inl tag kids = true
    · have e : rB (.elem tag attrs kids) i = padL i ++ ((('<' :: tag.toList ++ attrsL attrs.toList ++ ['>']) ++
          ((lfGuard tag kids).toList ++ (rIL [] kids.toList ++ closeL tag))) ++ ['\n']) := by
        simp [rB, hnv', hi]
      rw [e, pad_top b hf hd, run_append]
      have hcase : contentOf (nsIn b1.mode b1.stack (lower tag)) (lower tag) = .data ∨
          contentOf (nsIn b1.mode b1.stack (lower tag)) (lower tag) = .rcdata := by
        have := he1.kidsOk
        simp only [hnv, Bool.false_eq_true, ite_false] at this
        cases hcc : contentOf (nsIn b1.mode b1.stack (lower tag)) (lower tag) <;> simp_all
      rcases hcase with hc | hc
      · rw [run_elemInline b1 hf1 hd1 tag attrs kids he1 hnv hc ihIL, hlast]
        congr 3; funext K; simp [fB, hnv', hi]
      · rw [run_elemRcdata b1 hf1 hd1 tag attrs kids he1 hnv hc, hlast]
        congr 3; funext K; simp [fB, hnv', hi]
    · have hi' : inl tag kids = false := by simpa using hi
      have e : rB (.elem tag attrs kids) i = padL i ++ ((('<' :: tag.toList ++ attrsL attrs.toList ++ ['>']) ++
          (['\n'] ++ (rBL [] kids.toList (i + 1) ++ (padL i ++ closeL tag)))) ++ ['\n']) := by
        simp [rB, hnv', hi']
      have hc : contentOf (nsIn b1.mode b1.stack (lower tag)) (lower tag) = .data := by
        have := he1.kidsOk
        simp only [hnv, Bool.false_eq_true, ite_false] at this
        cases hcc : contentOf (nsIn b1.mode b1.stack (lower tag)) (lower tag) with
        | data => rfl
        | rcdata =>
          exfalso
          obtain ⟨hns, ht⟩ := contentOf_rcdata hcc
          have htag : lower tag = tag := by
            rcases he1.same with h1 | h1
            · exact absurd hns h1
            · exact h1
          rcases ht with ht | ht
          · rw [htag] at ht; subst ht; simp [inl, phrasingTags] at hi'
          · rw [htag] at ht; subst ht; simp [inl, preserveTags] at hi'
        | _ => simp_all
      rw [e, pad_top b hf hd, run_append, run_elemBlock b1 hf1 hd1 tag attrs kids i he1 hnv hc hi' ihBL,
        hlast]
      congr 3; funext K; simp [fB, hnv', hi']

/-- A start tag is read the same whether or not a dropped line feed is pending. -/
theorem run_tag_dl (b : Builder) (tag : String) (attrs : Array (String × String))
    (hv : validTag tag = true) (ha : validAttrs attrs = true) (rest : List Char) :
    run (some ⟨.data, b⟩) (('<' :: tag.toList ++ attrsL attrs.toList ++ ['>']) ++ rest) =
      run (some ⟨.data, { b with dropLF := false }⟩) (('<' :: tag.toList ++ attrsL attrs.toList ++ ['>']) ++ rest) := by
  rw [run_append _ ('<' :: tag.toList ++ attrsL attrs.toList ++ ['>']) rest,
    run_append _ ('<' :: tag.toList ++ attrsL attrs.toList ++ ['>']) rest,
    run_startTag b tag attrs hv ha, run_startTag _ tag attrs hv ha]

theorem simI_elem (tag : String) (attrs : Array (String × String)) (kids : Array Node)
    (b : Builder) (hf : InFlow b) (h : Accepts b.mode b.stack (.elem tag attrs kids) = true)
    (ihIL : ∀ b', InFlow b' → (b'.dropLF = true → leadsLF kids.toList = false) →
      AcceptsList b'.mode b'.stack kids.toList = true →
      run (some ⟨.data, b'⟩) (rIL [] kids.toList) =
        some ⟨.data, withTop { b' with dropLF := b'.dropLF && (rIL [] kids.toList).isEmpty }
          (fIL · kids.toList)⟩) :
    run (some ⟨.data, b⟩) (rI (.elem tag attrs kids)) =
      some ⟨.data, withTop { b with dropLF := b.dropLF && (rI (.elem tag attrs kids)).isEmpty }
        (fI · (.elem tag attrs kids))⟩ := by
  have he := elem_parts h
  let b0 : Builder := { b with dropLF := false }
  have hf0 : InFlow b0 := ⟨hf.mode, hf.nonempty⟩
  have he0 : ElemOk b0.mode b0.stack tag attrs kids := he
  have hne : (rI (.elem tag attrs kids)).isEmpty = false := by
    unfold rI; split <;> simp
  rw [hne, Bool.and_false]
  by_cases hv : Html.voidTags.contains tag = true
  · have hv' : tag ∈ Html.voidTags := by simpa using hv
    have e : rI (.elem tag attrs kids) = ('<' :: tag.toList ++ attrsL attrs.toList ++ ['>']) ++ [] := by
      simp [rI, hv']
    rw [e, run_tag_dl b tag attrs he.vtag he.vattrs, List.append_nil,
      run_elemVoid b0 hf0 rfl tag attrs kids he0 hv]
    congr 3; funext K; simp [fI, hv']
  · have hnv : Html.voidTags.contains tag = false := by simpa using hv
    have hnv' : tag ∉ Html.voidTags := by simpa using hv
    have e : rI (.elem tag attrs kids) = ('<' :: tag.toList ++ attrsL attrs.toList ++ ['>']) ++
        ((lfGuard tag kids).toList ++ (rIL [] kids.toList ++ closeL tag)) := by
      simp [rI, hnv']
    rw [e, run_tag_dl b tag attrs he.vtag he.vattrs]
    have hcase : contentOf (nsIn b0.mode b0.stack (lower tag)) (lower tag) = .data ∨
        contentOf (nsIn b0.mode b0.stack (lower tag)) (lower tag) = .rcdata := by
      have := he0.kidsOk
      simp only [hnv, Bool.false_eq_true, ite_false] at this
      cases hcc : contentOf (nsIn b0.mode b0.stack (lower tag)) (lower tag) <;> simp_all
    rcases hcase with hc | hc
    · rw [run_elemInline b0 hf0 rfl tag attrs kids he0 hnv hc ihIL]
      congr 3; funext K; simp [fI, hnv']
    · rw [run_elemRcdata b0 hf0 rfl tag attrs kids he0 hnv hc]
      congr 3; funext K; simp [fI, hnv']

theorem simI_style (css : String) (b : Builder) (hf : InFlow b)
    (h : Accepts b.mode b.stack (.style css) = true) :
    run (some ⟨.data, b⟩) (rI (.style css)) =
      some ⟨.data, withTop { b with dropLF := b.dropLF && (rI (.style css)).isEmpty } (fI · (.style css))⟩ := by
  obtain ⟨hctx, hok, hpay⟩ := style_parts h
  obtain ⟨hz, _⟩ := payload_parts false _ hpay
  have hne : (rI (.style css)).isEmpty = false := by simp [rI]
  rw [hne, Bool.and_false]
  have e : rI (.style css) = ('<' :: "style".toList ++ attrsL (#[] : Array (String × String)).toList ++ ['>']) ++
      ((rawPayload "</style" css).toList ++ closeL "style") := by
    simp [rI, attrsL]
  rw [e, run_tag_dl b "style" #[] (by decide) (by simp [validAttrs]),
    run_rawNode { b with dropLF := false } ⟨hf.mode, hf.nonempty⟩ rfl "style" (Or.inl rfl) .rawtext rfl
      #[] (by simp [validAttrs]) hctx hok _ hz (style_no_term css) (by simp)]
  congr 3; funext K; simp [fI, lowAttrs]

theorem simB_script (attrs : Array (String × String)) (js : String) (i : Nat) (b : Builder)
    (hf : InFlow b) (hd : b.dropLF = false) (h : Accepts b.mode b.stack (.script attrs js) = true) :
    run (some ⟨.data, b⟩) (rB (.script attrs js) i) =
      some ⟨.data, withTop b (fB · (.script attrs js) i)⟩ := by
  obtain ⟨hctx, ha, hok, hpay⟩ := script_parts h
  obtain ⟨hz, hbang⟩ := block_payload_parts true _ i hpay
  have e : rB (.script attrs js) i = padL i ++ ((('<' :: "script".toList ++ attrsL attrs.toList ++ ['>']) ++
      (('\n' :: (rawPayload "</script" js).toList ++ '\n' :: padL i) ++ closeL "script")) ++ ['\n']) := by
    simp [rB]
  rw [e, pad_top b hf hd, run_append]
  have hf1 := hf.top (addL · (padL i))
  have hshape := withTop_shape b (addL · (padL i))
  rw [run_rawNode (withTop b (addL · (padL i))) hf1 (by rw [withTop_dropLF]; exact hd) "script"
    (Or.inr rfl) .script rfl attrs ha (by rw [htmlContext_shape hshape]; exact hctx)
    (by rw [withTop_mode, startOk_shape _ _ _ hshape]; exact hok) _ hz
    (no_term_block _ _ i (by decide) (by decide) (by simp) (script_no_term js)) (fun _ => hbang rfl),
    lf_top _ (hf1.top _) (by rw [withTop_dropLF, withTop_dropLF]; exact hd), withTop_comp, withTop_comp]
  rfl

theorem simI_script (attrs : Array (String × String)) (js : String) (b : Builder) (hf : InFlow b)
    (h : Accepts b.mode b.stack (.script attrs js) = true) :
    run (some ⟨.data, b⟩) (rI (.script attrs js)) =
      some ⟨.data, withTop { b with dropLF := b.dropLF && (rI (.script attrs js)).isEmpty }
        (fI · (.script attrs js))⟩ := by
  obtain ⟨hctx, ha, hok, hpay⟩ := script_parts h
  obtain ⟨hz, hbang⟩ := payload_parts true _ hpay
  have hne : (rI (.script attrs js)).isEmpty = false := by simp [rI]
  rw [hne, Bool.and_false]
  have e : rI (.script attrs js) = ('<' :: "script".toList ++ attrsL attrs.toList ++ ['>']) ++
      ((rawPayload "</script" js).toList ++ closeL "script") := by
    simp [rI]
  rw [e, run_tag_dl b "script" attrs (by decide) ha,
    run_rawNode { b with dropLF := false } ⟨hf.mode, hf.nonempty⟩ rfl "script" (Or.inr rfl) .script rfl
      attrs ha hctx hok _ hz (script_no_term js) (fun _ => hbang rfl)]
  rfl

theorem leadsLF_head (n : Node) (rest : List Node) (h : leadsLF (n :: rest) = false) :
    leadsLF [n] = false := by
  cases n with
  | text x =>
    unfold leadsLF at h ⊢
    by_cases hx : x.isEmpty = true
    · simp [hx, leadsLF]
    · simp only [hx, Bool.false_eq_true, ite_false] at h ⊢
      exact h
  | _ => rfl

theorem text_head_of_leadsLF (x : String) (h : leadsLF [.text x] = false) :
    x.toList.head? ≠ some '\n' := by
  unfold leadsLF at h
  by_cases hx : x.isEmpty = true
  · have : x = "" := by simpa using hx
    subst this; simp
  · simp only [hx, Bool.false_eq_true, ite_false, beq_eq_false_iff_ne, ne_eq] at h
    rw [String.front?_eq] at h
    exact h

theorem leadsLF_tail (n : Node) (rest : List Node) (h : leadsLF (n :: rest) = false)
    (he : (rI n).isEmpty = true) : leadsLF rest = false := by
  cases n with
  | text x =>
    have hx : x = "" := by
      have : escapeText.go x.toList = [] := by simpa [rI] using he
      cases hxl : x.toList with
      | nil => exact String.toList_eq_nil_iff.mp hxl
      | cons c cs =>
        rw [hxl, escapeText.go] at this
        unfold escapeCharText at this
        split at this <;> (try split at this) <;> (try split at this) <;> simp at this
    subst hx
    simpa [leadsLF] using h
  | style _ => simp [rI] at he
  | script _ _ => simp [rI] at he
  | elem tag attrs kids =>
    unfold rI at he
    split at he <;> simp at he

mutual

theorem simB : (n : Node) → (i : Nat) → (b : Builder) → InFlow b → b.dropLF = false →
    Accepts b.mode b.stack n = true →
    run (some ⟨.data, b⟩) (rB n i) = some ⟨.data, withTop b (fB · n i)⟩
  | .text t, i, b, hf, hd, h => simB_text t i b hf.mode hf.nonempty hd h
  | .style css, i, b, hf, hd, h => simB_style css i b hf hd h
  | .script attrs js, i, b, hf, hd, h => simB_script attrs js i b hf hd h
  | .elem tag attrs kids, i, b, hf, hd, h => simB_elem tag attrs kids i b hf hd h
      (fun b' hf' hd' h' => simBL kids.toList (i + 1) b' hf' hd' h')
      (fun b' hf' hd' h' => simIL kids.toList b' hf' hd' h')

theorem simI : (n : Node) → (b : Builder) → InFlow b → (b.dropLF = true → leadsLF [n] = false) →
    Accepts b.mode b.stack n = true →
    run (some ⟨.data, b⟩) (rI n) =
      some ⟨.data, withTop { b with dropLF := b.dropLF && (rI n).isEmpty } (fI · n)⟩
  | .text t, b, hf, hd, h => by
    have := simI_text t b hf.mode hf.nonempty (fun h1 => text_head_of_leadsLF t (hd h1)) h
    have he : (rI (.text t)).isEmpty = t.toList.isEmpty := by
      cases ht : t.toList with
      | nil => simp [rI, ht, escapeText.go]
      | cons c cs =>
        simp only [rI, ht, escapeText.go, List.isEmpty_cons]
        unfold escapeCharText
        split <;> (try split) <;> (try split) <;> simp
    rw [he]; exact this
  | .style css, b, hf, _, h => simI_style css b hf h
  | .script attrs js, b, hf, _, h => simI_script attrs js b hf h
  | .elem tag attrs kids, b, hf, _, h => simI_elem tag attrs kids b hf h
      (fun b' hf' hd' h' => simIL kids.toList b' hf' hd' h')

theorem simBL : (l : List Node) → (i : Nat) → (b : Builder) → InFlow b → b.dropLF = false →
    AcceptsList b.mode b.stack l = true →
    run (some ⟨.data, b⟩) (rBL [] l i) = some ⟨.data, withTop b (fBL · l i)⟩
  | [], _, b, _, _, _ => by simp [rBL, fBL, run_nil, withTop_id b _ (fun _ => rfl)]
  | n :: rest, i, b, hf, hd, h => by
    simp only [AcceptsList, Bool.and_eq_true] at h
    rw [rBL_cons, run_append, simB n i b hf hd h.1,
      simBL rest i (withTop b (fB · n i)) (hf.top _) (by rw [withTop_dropLF]; exact hd)
        (by rw [withTop_mode, AcceptsList_shape _ (withTop_shape b _)]; exact h.2),
      withTop_comp]
    rfl

theorem simIL : (l : List Node) → (b : Builder) → InFlow b → (b.dropLF = true → leadsLF l = false) →
    AcceptsList b.mode b.stack l = true →
    run (some ⟨.data, b⟩) (rIL [] l) =
      some ⟨.data, withTop { b with dropLF := b.dropLF && (rIL [] l).isEmpty } (fIL · l)⟩
  | [], b, _, _, _ => by
    simp [rIL, fIL, run_nil, withTop_id _ _ (fun _ => rfl)]
  | n :: rest, b, hf, hd, h => by
    simp only [AcceptsList, Bool.and_eq_true] at h
    rw [rIL_cons, run_append, simI n b hf (fun h1 => leadsLF_head n rest (hd h1)) h.1]
    let b' := withTop { b with dropLF := b.dropLF && (rI n).isEmpty } (fI · n)
    have hf' : InFlow b' :=
      InFlow.top (b := { b with dropLF := b.dropLF && (rI n).isEmpty }) ⟨hf.mode, hf.nonempty⟩ (fI · n)
    have hd' : b'.dropLF = true → leadsLF rest = false := by
      intro h1
      simp only [b', withTop_dropLF, Bool.and_eq_true] at h1
      exact leadsLF_tail n rest (hd h1.1) h1.2
    have hacc : AcceptsList b'.mode b'.stack rest = true := by
      simp only [b', withTop_mode]
      rw [AcceptsList_shape _ (withTop_shape _ _)]
      exact h.2
    rw [simIL rest b' hf' hd' hacc]
    have hie : ∀ (x y : List Char), (x ++ y).isEmpty = (x.isEmpty && y.isEmpty) := by
      intro x y; cases x <;> simp
    simp only [b', withTop_dropLF_comm, withTop_comp]
    rw [hie, Bool.and_assoc]
    rfl

end

/-! ### No carriage return is written -/

theorem escText_noCR (l : List Char) (h : '\r' ∉ l) : '\r' ∉ escapeText.go l := by
  induction l with
  | nil => simp [escapeText.go]
  | cons c rest ih =>
    simp only [List.mem_cons, not_or] at h
    simp only [escapeText.go, List.mem_append, not_or]
    refine ⟨?_, ih h.2⟩
    unfold escapeCharText
    split
    · decide
    · split
      · decide
      · split
        · decide
        · simp only [List.mem_singleton]; exact fun e => h.1 e

theorem escAttr_noCR (l : List Char) (h : '\r' ∉ l) : '\r' ∉ escapeAttr.go l := by
  induction l with
  | nil => simp [escapeAttr.go]
  | cons c rest ih =>
    simp only [List.mem_cons, not_or] at h
    simp only [escapeAttr.go, List.mem_append, not_or]
    refine ⟨?_, ih h.2⟩
    unfold escapeCharAttr
    split
    · decide
    · split
      · decide
      · split
        · decide
        · split
          · decide
          · split
            · decide
            · simp only [List.mem_singleton]; exact fun e => h.1 e

theorem pad_noCR (i : Nat) : '\r' ∉ padL i := by simp [padL]

theorem tag_noCR (tag : String) (h : validTag tag = true) : '\r' ∉ tag.toList := by
  unfold validTag at h
  cases ht : tag.toList with
  | nil => simp
  | cons c rest =>
    rw [ht] at h
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    simp only [List.mem_cons, not_or]
    refine ⟨fun e => ?_, fun hm => ?_⟩
    · subst e; simp [isAlpha] at h
    · have := h.2 _ hm; simp [nameChar] at this

theorem attrs_noCR (attrs : Array (String × String)) (h : validAttrs attrs = true) :
    '\r' ∉ attrsL attrs.toList := by
  obtain ⟨hall, _⟩ := validAttrs_parts attrs h
  generalize attrs.toList = l at hall ⊢
  induction l with
  | nil => simp [attrsL]
  | cons kv rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hall
    obtain ⟨⟨⟨_, hk⟩, hv⟩, hrest⟩ := hall
    have hkc : '\r' ∉ kv.1.toList := by
      intro hm
      have := List.all_eq_true.mp hk _ hm
      simp [keyChar, nameChar] at this
    have hvc : '\r' ∉ kv.2.toList := by
      intro hm
      have := List.all_eq_true.mp hv _ hm
      simp at this
    simp only [attrsL, List.flatMap_cons, List.mem_append, not_or]
    refine ⟨?_, by simpa [attrsL] using ih hrest⟩
    unfold attrL
    split
    · simp [hkc]
    · simp [hkc, escAttr_noCR _ hvc]

theorem guard_noCR (tag : String) (kids : Array Node) : '\r' ∉ (lfGuard tag kids).toList := by
  unfold lfGuard; split <;> simp

theorem payload_noCR (script : Bool) (p : String) (h : payloadOk script p = true) : '\r' ∉ p.toList := by
  intro hm
  simp only [payloadOk, Bool.and_eq_true, List.all_eq_true] at h
  have := h.1 _ hm
  simp at this

theorem texts_noCR (l : List Node) (hl : l.all rcText = true) :
    '\r' ∉ rIL [] l ∧ ∀ i, '\r' ∉ rBL [] l i := by
  induction l with
  | nil => simp [rIL, rBL]
  | cons n rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hl
    obtain ⟨ih1, ih2⟩ := ih hl.2
    cases n with
    | text x =>
      have hx : '\r' ∉ x.toList := by
        intro hm; have := hl.1; simp [rcText] at this; exact (this _ hm).2 rfl
      refine ⟨?_, fun i => ?_⟩
      · simp only [rIL_cons, rI, List.mem_append, not_or]; exact ⟨escText_noCR _ hx, ih1⟩
      · simp only [rBL_cons, rB, List.mem_append, List.mem_cons, not_or]
        exact ⟨⟨⟨pad_noCR i, escText_noCR _ hx⟩, by decide⟩, ih2 i⟩
    | _ => simp [rcText] at hl

mutual

theorem noCR_B : (n : Node) → (i : Nat) → (m : Mode) → (s : List Frame) →
    Accepts m s n = true → '\r' ∉ rB n i
  | .text t, i, m, s, h => by
    have ht : '\r' ∉ t.toList := by
      intro hm
      simp only [Accepts, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      exact (h _ hm).1.1 rfl
    simp only [rB, List.mem_append, List.mem_cons, not_or]
    exact ⟨⟨pad_noCR i, escText_noCR _ ht⟩, by decide⟩
  | .style css, i, m, s, h => by
    obtain ⟨_, _, hp⟩ := style_parts h
    have := payload_noCR _ _ hp
    simp only [rB, List.mem_append, List.mem_cons, not_or, closeL]
    simp [pad_noCR, this]
  | .script attrs js, i, m, s, h => by
    obtain ⟨_, ha, _, hp⟩ := script_parts h
    have := payload_noCR _ _ hp
    simp only [rB, List.mem_append, List.mem_cons, not_or, closeL]
    simp [pad_noCR, this, attrs_noCR _ ha]
  | .elem tag attrs kids, i, m, s, h => by
    have he := elem_parts h
    have hkids : '\r' ∉ rIL [] kids.toList ∧ '\r' ∉ rBL [] kids.toList (i + 1) := by
      have := he.kidsOk
      split at this
      · next hv =>
        have : kids.toList = [] := by simpa using this
        rw [this]; simp [rIL, rBL]
      · split at this
        · exact ⟨noCR_IL kids.toList m _ this, noCR_BL kids.toList (i + 1) m _ this⟩
        · have hl : kids.toList.all rcText = true := by
            rw [List.all_eq_true] at this ⊢
            intro k hk
            have := this k hk
            cases k <;> simp_all [rcText]
          exact ⟨(texts_noCR _ hl).1, (texts_noCR _ hl).2 _⟩
        · simp at this
    have htag := tag_noCR tag he.vtag
    have hatt := attrs_noCR attrs he.vattrs
    unfold rB
    split
    · simp [pad_noCR, htag, hatt]
    · split
      · simp [pad_noCR, htag, hatt, guard_noCR, hkids.1, closeL]
      · simp [pad_noCR, htag, hatt, hkids.2, closeL]

theorem noCR_I : (n : Node) → (m : Mode) → (s : List Frame) → Accepts m s n = true → '\r' ∉ rI n
  | .text t, m, s, h => by
    have ht : '\r' ∉ t.toList := by
      intro hm
      simp only [Accepts, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      exact (h _ hm).1.1 rfl
    exact escText_noCR _ ht
  | .style css, m, s, h => by
    obtain ⟨_, _, hp⟩ := style_parts h
    simp [rI, payload_noCR _ _ hp, closeL]
  | .script attrs js, m, s, h => by
    obtain ⟨_, ha, _, hp⟩ := script_parts h
    simp [rI, payload_noCR _ _ hp, attrs_noCR _ ha, closeL]
  | .elem tag attrs kids, m, s, h => by
    have he := elem_parts h
    have hkids : '\r' ∉ rIL [] kids.toList := by
      have := he.kidsOk
      split at this
      · next hv =>
        have : kids.toList = [] := by simpa using this
        rw [this]; simp [rIL]
      · split at this
        · exact noCR_IL kids.toList m _ this
        · have hl : kids.toList.all rcText = true := by
            rw [List.all_eq_true] at this ⊢
            intro k hk
            have := this k hk
            cases k <;> simp_all [rcText]
          exact (texts_noCR _ hl).1
        · simp at this
    have htag := tag_noCR tag he.vtag
    have hatt := attrs_noCR attrs he.vattrs
    unfold rI
    split
    · simp [htag, hatt]
    · simp [htag, hatt, guard_noCR, hkids, closeL]

theorem noCR_BL : (l : List Node) → (i : Nat) → (m : Mode) → (s : List Frame) →
    AcceptsList m s l = true → '\r' ∉ rBL [] l i
  | [], _, _, _, _ => by simp [rBL]
  | n :: rest, i, m, s, h => by
    simp only [AcceptsList, Bool.and_eq_true] at h
    simp only [rBL_cons, List.mem_append, not_or]
    exact ⟨noCR_B n i m s h.1, noCR_BL rest i m s h.2⟩

theorem noCR_IL : (l : List Node) → (m : Mode) → (s : List Frame) →
    AcceptsList m s l = true → '\r' ∉ rIL [] l
  | [], _, _, _ => by simp [rIL]
  | n :: rest, m, s, h => by
    simp only [AcceptsList, Bool.and_eq_true] at h
    simp only [rIL_cons, List.mem_append, not_or]
    exact ⟨noCR_I n m s h.1, noCR_IL rest m s h.2⟩

end

/-! ### The document -/

theorem run_doctype :
    run (some init) "<!DOCTYPE html>".toList =
      some ⟨.data, { mode := .beforeHtml, stack := [], dropLF := false }⟩ := by
  rfl

theorem run_ignoreWs (b : Builder) (hm : b.mode = .beforeHtml ∨ b.mode = .beforeHead)
    (hd : b.dropLF = false) (cs : List Char) (hw : ∀ c ∈ cs, c = ' ' ∨ c = '\n') :
    run (some ⟨.data, b⟩) cs = some ⟨.data, b⟩ := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
    have hc := hw c (by simp)
    have h1 : c ≠ '<' ∧ c ≠ '&' := by rcases hc with rfl | rfl <;> decide
    have hch : char b c = some b := by
      have hws : isWs c = true := by rcases hc with rfl | rfl <;> rfl
      rcases hm with hm | hm <;> simp [char, hm, hws]
    rw [run_cons, step_data b c h1.1 h1.2, emit_char _ c _ b hd hch]
    exact ih (fun d hd' => hw d (by simp [hd']))

theorem lowAttrs_lang (lang : String) : lowAttrs #[("lang", lang)] = #[("lang", lang)] := by
  simp [lowAttrs]; decide

theorem lowAttrs_empty : lowAttrs (#[] : Array (String × String)) = #[] := by simp [lowAttrs]

/-- A skeleton element's children read under its frame: as blocks or inline, ending in the data
state with the frame's children those `fKids` names. -/
theorem run_kids (m : Mode) (hm : m = .inBody ∨ m = .inHead) (F : Frame) (rest : List Frame)
    (tag : String) (kids : Array Node) (i : Nat)
    (h : AcceptsList m (F :: rest) kids.toList = true) (hlf : lfGuard tag kids = "") :
    run (some ⟨.data, Builder.mk m (F :: rest) false⟩)
        (if inl tag kids then (lfGuard tag kids).toList ++ rIL [] kids.toList
         else ['\n'] ++ rBL [] kids.toList (i + 1) ++ padL i) =
      some ⟨.data, Builder.mk m ({ F with kids := (if inl tag kids then fIL F.kids kids.toList
          else addL (fBL (addL F.kids ['\n']) kids.toList (i + 1)) (padL i)) } :: rest) false⟩ := by
  have hf : InFlow (Builder.mk m (F :: rest) false) := ⟨hm, by simp⟩
  split
  · rw [hlf]
    simp only [String.toList_empty, List.nil_append]
    rw [simIL kids.toList _ hf (by simp) h]
    rfl
  · rw [run_append, run_append, run_ws _ ['\n'] rfl hf.late hf.nonempty (by simp)]
    rw [simBL kids.toList (i + 1) _ (hf.top _) (by rw [withTop_dropLF]) (by
      rw [withTop_mode, AcceptsList_shape _ (withTop_shape _ _)]; exact h)]
    rw [withTop_comp, run_ws _ _ (by rw [withTop_dropLF]) (by rw [withTop_mode]; exact hf.late)
      (stack_ne_withTop hf.nonempty _) (padL_ws i), withTop_comp]
    rfl

theorem rB_skel (tag : String) (kids : Array Node) (i : Nat) (hv : Html.voidTags.contains tag = false) :
    rB (.elem tag #[] kids) i = padL i ++ (('<' :: tag.toList ++ attrsL [] ++ ['>']) ++
      ((if inl tag kids then (lfGuard tag kids).toList ++ rIL [] kids.toList
        else ['\n'] ++ rBL [] kids.toList (i + 1) ++ padL i) ++ (closeL tag ++ ['\n']))) := by
  unfold rB
  simp only [hv, Bool.false_eq_true, ite_false]
  split <;> simp

theorem document_toList (lang : String) (head body : Array Node) :
    (document lang head body).toList = "<!DOCTYPE html>".toList ++ (['\n'] ++
      (('<' :: "html".toList ++ attrsL [("lang", lang)] ++ ['>']) ++ (['\n'] ++
        (rB (.elem "head" #[] head) 1 ++ (rB (.elem "body" #[] body) 1 ++
          (closeL "html" ++ ['\n'])))))) := by
  simp only [document, document.inlineRenderTop]
  simp only [String.toList_append, render, ← renderInto_toList, String.toList_empty, List.nil_append]
  have hv : Html.voidTags.contains "html" = false := by decide
  have hi : inl "html" #[Node.elem "head" #[] head, Node.elem "body" #[] body] = false := by
    simp [inl, preserveTags, phrasingTags, isInlineOnly]
  simp only [elem]
  rw [rB.eq_4 (tag := "html")]
  simp only [hv, Bool.false_eq_true, ite_false, hi, rBL]
  simp [padL]

theorem skel_noCR (tag : String) (kids : Array Node) (i : Nat) (m : Mode) (s : List Frame)
    (hv : Html.voidTags.contains tag = false) (ht : '\r' ∉ tag.toList)
    (h : AcceptsList m s kids.toList = true) : '\r' ∉ rB (.elem tag #[] kids) i := by
  rw [rB_skel tag kids i hv]
  have h1 := noCR_IL kids.toList m s h
  have h2 := noCR_BL kids.toList (i + 1) m s h
  split
  · simp [pad_noCR, ht, attrsL, closeL, guard_noCR, h1]
  · simp [pad_noCR, ht, attrsL, closeL, h2]

theorem docOk_parts {lang : String} {head body : Array Node} (h : DocOk lang head body = true) :
    lang.toList.all (fun c => c != '\x00' && c != '\r') = true ∧
      AcceptsList .inHead [headFrame, htmlFrame lang] head.toList = true ∧
      AcceptsList .inBody [bodyFrame, htmlFrame lang] body.toList = true := by
  simp only [DocOk, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem lang_valid (lang : String) (h : lang.toList.all (fun c => c != '\x00' && c != '\r') = true) :
    validAttrs #[("lang", lang)] = true := by
  have hk : ("lang".isEmpty = false) ∧ "lang".toList.all keyChar = true := ⟨by decide, by decide⟩
  simp only [validAttrs, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, by simp⟩
  rw [← Array.all_toList]
  simp [hk.1, h]
  decide

theorem lfGuard_skel (tag : String) (kids : Array Node) (h : tag = "head" ∨ tag = "body") :
    lfGuard tag kids = "" := by
  rcases h with rfl | rfl <;> simp [lfGuard, lfTags]

theorem addL_html_ws (K : Array Dom) (e : Dom) (he : ∀ s, e ≠ .text s) :
    addL ((K.push e)) ['\n', ' ', ' '] = (K.push e).push (.text "\n  ") := by
  simp only [addL, List.foldl_cons, List.foldl_nil, addChar, Array.back?_push]
  cases e with
  | text s => exact absurd rfl (he s)
  | elem t a k =>
    simp [Array.back?_push, Array.pop_push]

theorem late_afterHead : Late .afterHead := ⟨by decide, by decide, by decide⟩

theorem late_afterBody : Late .afterBody := ⟨by decide, by decide, by decide⟩

theorem late_afterAfterBody : Late .afterAfterBody := ⟨by decide, by decide, by decide⟩

theorem seg_open (lang : String) (hl : lang.toList.all (fun c => c != '\x00' && c != '\r') = true) :
    run (some init) ("<!DOCTYPE html>".toList ++ (['\n'] ++
      (('<' :: "html".toList ++ attrsL [("lang", lang)] ++ ['>']) ++ ['\n']))) =
      some ⟨.data, ⟨.beforeHead, [htmlFrame lang], false⟩⟩ := by
  let B0 : Builder := { mode := .beforeHtml, stack := [], dropLF := false }
  rw [run_append, run_doctype, run_append, run_ignoreWs B0 (Or.inl rfl) rfl ['\n'] (by simp),
    run_append, run_startTag B0 "html" _ (by decide) (lang_valid lang hl), lowAttrs_lang]
  have hlow : lower "html" = "html" := by decide
  have hst0 : start { B0 with dropLF := false } "html" #[("lang", lang)] false =
      some (⟨.beforeHead, [htmlFrame lang], false⟩, .data) := by
    simp [start, B0, htmlFrame]
  rw [hlow, hst0]
  simp only [Option.map_some, after]
  exact run_ignoreWs _ (Or.inr rfl) rfl ['\n'] (by simp)

/-- The children of the document's head or body: the `fKids` they read as. -/
theorem seg_kids (m : Mode) (hm : m = .inBody ∨ m = .inHead) (F : Frame) (rest : List Frame)
    (tag : String) (ht : tag = "head" ∨ tag = "body") (kids : Array Node) (hF : F.kids = #[])
    (h : AcceptsList m (F :: rest) kids.toList = true) :
    run (some ⟨.data, Builder.mk m (F :: rest) false⟩)
        (if inl tag kids then (lfGuard tag kids).toList ++ rIL [] kids.toList
         else ['\n'] ++ rBL [] kids.toList (1 + 1) ++ padL 1) =
      some ⟨.data, Builder.mk m ({ F with kids := fKids tag kids 1 } :: rest) false⟩ := by
  rw [run_kids m hm F rest tag kids 1 h (lfGuard_skel tag kids ht), hF]
  rfl

theorem seg_head (lang : String) (head : Array Node)
    (hh : AcceptsList .inHead [headFrame, htmlFrame lang] head.toList = true) :
    run (some ⟨.data, ⟨.beforeHead, [htmlFrame lang], false⟩⟩) (rB (.elem "head" #[] head) 1) =
      some ⟨.data, ⟨.afterHead, [{ htmlFrame lang with
        kids := #[.elem "head" #[] (fKids "head" head 1), .text "\n"] }], false⟩⟩ := by
  let B1 : Builder := ⟨.beforeHead, [htmlFrame lang], false⟩
  rw [rB_skel "head" head 1 (by decide), run_append,
    run_ignoreWs B1 (Or.inr rfl) rfl (padL 1) (padL_ws 1), run_append,
    run_startTag B1 "head" #[] (by decide) (by simp [validAttrs])]
  have hlowh : lower "head" = "head" := by decide
  have hst : start { B1 with dropLF := false } "head" #[] false =
      some (⟨.inHead, [headFrame, htmlFrame lang], false⟩, .data) := by
    simp [start, B1, HtmlRead.insert, headFrame]
  rw [hlowh, lowAttrs_empty, hst]
  simp only [Option.map_some, after]
  rw [run_append, seg_kids .inHead (Or.inr rfl) headFrame [htmlFrame lang] "head" (Or.inl rfl) head rfl hh,
    run_append, run_stopTag _ "head" (by decide), hlowh]
  have hstop : stop { Builder.mk .inHead ({ headFrame with kids := fKids "head" head 1 } :: [htmlFrame lang])
      false with dropLF := false } "head" =
      some ⟨.afterHead, [{ htmlFrame lang with kids := #[.elem "head" #[] (fKids "head" head 1)] }], false⟩ := by
    simp [stop, closeCurrent, headFrame, htmlFrame, Frame.close]
  rw [hstop]
  simp only [Option.map_some]
  rw [run_ws _ ['\n'] rfl late_afterHead (by simp) (by simp)]
  simp [withTop, addL, addChar, htmlFrame]

theorem seg_body (lang : String) (body : Array Node) (H : Frame) (hH : H.ns = .html ∧ H.tag = "html" ∧
      H.attrs = #[("lang", lang)])
    (hb : AcceptsList .inBody [bodyFrame, htmlFrame lang] body.toList = true) :
    run (some ⟨.data, ⟨.afterHead, [H], false⟩⟩) (rB (.elem "body" #[] body) 1) =
      some ⟨.data, ⟨.afterBody, [{ bodyFrame with kids := addL (fKids "body" body 1) ['\n'] },
        { H with kids := addL H.kids (padL 1) }], false⟩⟩ := by
  let B3 : Builder := ⟨.afterHead, [H], false⟩
  rw [rB_skel "body" body 1 (by decide), run_append,
    run_ws B3 (padL 1) rfl late_afterHead (by simp [B3]) (padL_ws 1), run_append,
    run_startTag _ "body" #[] (by decide) (by simp [validAttrs])]
  have hlowb : lower "body" = "body" := by decide
  let H1 : Frame := { H with kids := addL H.kids (padL 1) }
  have hw : withTop B3 (addL · (padL 1)) = ⟨.afterHead, [H1], false⟩ := rfl
  have hst : start { withTop B3 (addL · (padL 1)) with dropLF := false } "body" #[] false =
      some (⟨.inBody, [bodyFrame, H1], false⟩, .data) := by
    rw [hw]; simp [start, HtmlRead.insert, bodyFrame]
  rw [hlowb, lowAttrs_empty, hst]
  simp only [Option.map_some, after]
  have hacc : AcceptsList .inBody (bodyFrame :: [H1]) body.toList = true := by
    rw [AcceptsList_shape _ (sameShape_push bodyFrame (show sameShape [H1] [htmlFrame lang] from
      ⟨hH.1, hH.2.1, hH.2.2, trivial⟩))]
    exact hb
  rw [run_append, seg_kids .inBody (Or.inl rfl) bodyFrame [H1] "body" (Or.inr rfl) body rfl hacc,
    run_append, run_stopTag _ "body" (by decide), hlowb]
  have hstop : stop { Builder.mk .inBody ({ bodyFrame with kids := fKids "body" body 1 } :: [H1])
      false with dropLF := false } "body" =
      some ⟨.afterBody, [{ bodyFrame with kids := fKids "body" body 1 }, H1], false⟩ := by
    simp [stop, currentIs, bodyFrame]
  rw [hstop]
  simp only [Option.map_some]
  rw [run_ws _ ['\n'] rfl late_afterBody (by simp) (by simp)]
  rfl

theorem seg_end (B : Frame) (H : Frame) :
    run (some ⟨.data, ⟨.afterBody, [B, H], false⟩⟩) (closeL "html" ++ ['\n']) =
      some ⟨.data, ⟨.afterAfterBody, [{ B with kids := addL B.kids ['\n'] }, H], false⟩⟩ := by
  rw [run_append, run_stopTag _ "html" (by decide)]
  have hlow : lower "html" = "html" := by decide
  rw [hlow]
  simp only [stop, beq_self_eq_true, ite_true, Option.map_some]
  rw [run_ws _ ['\n'] rfl late_afterAfterBody (by simp) (by simp)]
  rfl

theorem addL_head_ws (e : Dom) (he : ∀ s, e ≠ .text s) :
    addL #[e, .text "\n"] (padL 1) = #[e, .text "\n  "] := by
  cases e with
  | text s => exact absurd rfl (he s)
  | elem t a k => simp [addL, padL, addChar]

/-- The page `Html.document` writes parses, under the HTML Standard's parser as `HtmlRead` models
it, to `fDoc`: its head and body, the renderer's white space as text and names lower-cased,
whenever the head and body read as the stack builder they are (`DocOk`). -/
public theorem parse_render_exact (lang : String) (head body : Array Node)
    (h : DocOk lang head body = true) :
    HtmlRead.parse (document lang head body) = some (fDoc lang head body) := by
  obtain ⟨hl, hh, hb⟩ := docOk_parts h
  have hnv : ∀ t, t = "head" ∨ t = "body" → Html.voidTags.contains t = false := by
    intro t ht; rcases ht with rfl | rfl <;> decide
  have hcr : (document lang head body).toList.contains '\r' = false := by
    rw [document_toList]
    have h1 := skel_noCR "head" head 1 .inHead _ (hnv _ (Or.inl rfl)) (by decide) hh
    have h2 := skel_noCR "body" body 1 .inBody _ (hnv _ (Or.inr rfl)) (by decide) hb
    have h3 := attrs_noCR #[("lang", lang)] (lang_valid lang hl)
    simp only [List.contains_eq_any_beq, List.any_eq_false, beq_iff_eq]
    intro c hc heq
    subst heq
    simp only [List.mem_append, List.mem_cons] at hc
    simp_all [closeL]
  unfold HtmlRead.parse
  simp only [hcr, Bool.false_eq_true, ite_false]
  show (run (some init) (document lang head body).toList).bind finish = _
  rw [document_toList]
  have e : "<!DOCTYPE html>".toList ++ (['\n'] ++
      (('<' :: "html".toList ++ attrsL [("lang", lang)] ++ ['>']) ++ (['\n'] ++
        (rB (.elem "head" #[] head) 1 ++ (rB (.elem "body" #[] body) 1 ++
          (closeL "html" ++ ['\n'])))))) =
      ("<!DOCTYPE html>".toList ++ (['\n'] ++
        (('<' :: "html".toList ++ attrsL [("lang", lang)] ++ ['>']) ++ ['\n']))) ++
      (rB (.elem "head" #[] head) 1 ++ (rB (.elem "body" #[] body) 1 ++ (closeL "html" ++ ['\n']))) := by
    simp
  rw [e, run_append, seg_open lang hl, run_append, seg_head lang head hh, run_append,
    seg_body lang body _ ⟨rfl, rfl, rfl⟩ hb, seg_end]
  simp only [Option.bind_some, finish]
  simp only [fDoc, Frame.close, bodyFrame, htmlFrame]
  rw [addL_head_ws _ (fun _ => by simp), ← addL_append]
  rfl

mutual

theorem charsInto_acc (acc : String) : (d : Dom) →
    (Dom.charsInto acc d).toList = acc.toList ++ (Dom.chars d).toList
  | .text s => by simp [Dom.charsInto, Dom.chars, String.toList_append]
  | .elem tag a kids => by
    simp only [Dom.chars, Dom.charsInto]
    split
    · simp
    · rw [charsListInto_acc acc kids.toList, charsListInto_acc "" kids.toList]
      simp

theorem charsListInto_acc (acc : String) : (l : List Dom) →
    (Dom.charsListInto acc l).toList = acc.toList ++ (Dom.charsList l).toList
  | [] => by simp [Dom.charsListInto, Dom.charsList]
  | d :: rest => by
    simp only [Dom.charsListInto, Dom.charsList]
    rw [charsListInto_acc _ rest, charsListInto_acc (Dom.charsInto "" d) rest, charsInto_acc acc d,
      charsInto_acc "" d]
    simp

end

theorem charsList_nil : Dom.charsList [] = "" := rfl

theorem charsList_cons (d : Dom) (l : List Dom) :
    (Dom.charsList (d :: l)).toList = (Dom.chars d).toList ++ (Dom.charsList l).toList := by
  simp only [Dom.charsList, Dom.charsListInto]
  rw [charsListInto_acc]
  rfl

theorem chars_text (s : String) : Dom.chars (.text s) = s := by simp [Dom.chars, Dom.charsInto]

theorem chars_elem (tag : String) (a : Array (String × String)) (kids : Array Dom) :
    Dom.chars (.elem tag a kids) =
      if tag == "style" || tag == "script" then "" else Dom.charsList kids.toList := by
  simp only [Dom.chars, Dom.charsInto, Dom.charsList]

/-! ### The page's text -/

/-- The page text of a rendered page is the text of its body as the parser builds it. -/
public theorem pageText_render_exact (lang : String) (head body : Array Node)
    (h : DocOk lang head body = true) :
    HtmlRead.pageText (document lang head body) = some (bodyChars body) := by
  simp only [HtmlRead.pageText, parse_render_exact lang head body h, Option.bind_some, fDoc,
    Dom.bodyText]
  simp [List.find?, chars_elem, bodyChars]

public theorem inkInto_acc (l : List Node) : ∀ acc, Node.inkInto acc l = acc ++ Node.inkInto [] l := by
  induction l with
  | nil => intro acc; simp [Node.inkInto]
  | cons n rest ih =>
    intro acc
    simp only [Node.inkInto]
    rw [ih (acc ++ Node.ink n), ih ([] ++ Node.ink n)]
    simp

theorem inkList_nil : Node.inkList [] = [] := rfl

public theorem inkList_cons (n : Node) (rest : List Node) :
    Node.inkList (n :: rest) = Node.ink n ++ Node.inkList rest := by
  simp only [Node.inkList, Node.inkInto]
  rw [inkInto_acc, List.nil_append]

public theorem ink_elem (tag : String) (a : Array (String × String)) (kids : Array Node) :
    Node.ink (.elem tag a kids) =
      if lower tag == "style" || lower tag == "script" then [] else Node.inkList kids.toList := by
  simp only [Node.ink, Node.inkList]

theorem charsList_append (a b : List Dom) :
    (Dom.charsList (a ++ b)).toList = (Dom.charsList a).toList ++ (Dom.charsList b).toList := by
  induction a with
  | nil => simp [charsList_nil]
  | cons d rest ih => rw [List.cons_append, charsList_cons, charsList_cons, ih, List.append_assoc]

theorem charsList_addChar (K : Array Dom) (c : Char) :
    (Dom.charsList (addChar K c).toList).toList = (Dom.charsList K.toList).toList ++ [c] := by
  unfold addChar
  split
  · next s hb =>
    obtain ⟨ys, rfl⟩ := Array.back?_eq_some_iff.1 hb
    simp [Array.toList_push, charsList_append, charsList_cons, charsList_nil, chars_text,
      String.toList_push]
  · simp [Array.toList_push, charsList_append, charsList_cons, charsList_nil, chars_text]

theorem charsList_addL (K : Array Dom) (cs : List Char) :
    (Dom.charsList (addL K cs).toList).toList = (Dom.charsList K.toList).toList ++ cs := by
  induction cs generalizing K with
  | nil => simp [addL]
  | cons c rest ih =>
    simp only [addL, List.foldl_cons] at ih ⊢
    rw [ih, charsList_addChar, List.append_assoc]
    rfl

theorem charsList_push (K : Array Dom) (d : Dom) :
    (Dom.charsList (K.push d).toList).toList = (Dom.charsList K.toList).toList ++ (Dom.chars d).toList := by
  simp [Array.toList_push, charsList_append, charsList_cons, charsList_nil]

theorem pad_inked (i : Nat) : (padL i).filter inked = [] := by
  simp [padL, inked, isWs]

theorem lf_inked : (['\n'] : List Char).filter inked = [] := by decide

theorem raw_chars (t : String) (a : Array (String × String)) (X : Array Dom)
    (h : (t == "style" || t == "script") = true) : Dom.chars (.elem t a X) = "" := by
  simp [chars_elem, h]

theorem charsList_single (d : Dom) : (Dom.charsList [d]).toList = (Dom.chars d).toList := by
  rw [charsList_cons, charsList_nil]; simp

theorem chars_style (a : Array (String × String)) (X : Array Dom) :
    Dom.chars (.elem "style" a X) = "" := by simp [chars_elem]

theorem chars_script (a : Array (String × String)) (X : Array Dom) :
    Dom.chars (.elem "script" a X) = "" := by simp [chars_elem]

theorem ink_texts (l : List Node) (hl : l.all rcText = true) (K : Array Dom) :
    (Dom.charsList (fIL K l).toList).toList.filter inked =
      (Dom.charsList K.toList).toList.filter inked ++ (Node.inkList l).filter inked := by
  rw [fIL_texts l hl K, charsList_addL, List.filter_append]
  congr 1
  induction l with
  | nil => rfl
  | cons n rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hl
    cases n with
    | text x => simp [textsOf, textOf, inkList_cons, Node.ink, List.filter_append, ← ih hl.2]
    | _ => simp [rcText] at hl

theorem ink_fBL_texts (l : List Node) (hl : l.all rcText = true) (i : Nat) : ∀ K : Array Dom,
    (Dom.charsList (fBL K l i).toList).toList.filter inked =
      (Dom.charsList K.toList).toList.filter inked ++ (Node.inkList l).filter inked := by
  induction l with
  | nil => intro K; simp [fBL, inkList_nil]
  | cons n rest ih =>
    intro K
    simp only [List.all_cons, Bool.and_eq_true] at hl
    cases n with
    | text x =>
      simp only [fBL, inkList_cons, List.filter_append]
      rw [ih hl.2]
      simp [fB, charsList_addL, List.filter_append, pad_inked, Node.ink, inked, isWs]
    | _ => simp [rcText] at hl

/-- The children an accepted element's kids leave: none for a void element, accepted kids, or a
title's text. -/
theorem kids_cases {m : Mode} {s : List Frame} {tag : String} {attrs : Array (String × String)}
    {kids : Array Node} (he : ElemOk m s tag attrs kids) :
    (Html.voidTags.contains tag = true ∧ kids.toList = []) ∨
      (Html.voidTags.contains tag = false ∧
        AcceptsList m (⟨nsIn m s (lower tag), lower tag, lowAttrs attrs, #[]⟩ :: s) kids.toList = true) ∨
      (Html.voidTags.contains tag = false ∧ kids.toList.all rcText = true) := by
  have := he.kidsOk
  split at this
  · next hv => exact Or.inl ⟨hv, by simpa using this⟩
  · next hv =>
    have hv' : Html.voidTags.contains tag = false := by simpa using hv
    split at this
    · exact Or.inr (Or.inl ⟨hv', this⟩)
    · right; right
      refine ⟨hv', ?_⟩
      rw [List.all_eq_true] at this ⊢
      intro k hk
      have := this k hk
      cases k <;> simp_all [rcText]
    · simp at this

mutual

theorem ink_fB (K : Array Dom) : (n : Node) → (i : Nat) → (m : Mode) → (s : List Frame) →
    Accepts m s n = true →
    (Dom.charsList (fB K n i).toList).toList.filter inked =
      (Dom.charsList K.toList).toList.filter inked ++ (Node.ink n).filter inked
  | .text t, i, _, _, _ => by
    simp [fB, charsList_addL, List.filter_append, pad_inked, Node.ink, inked, isWs]
  | .style css, i, _, _, _ => by
    simp only [fB, charsList_addL, Array.toList_push, charsList_append, charsList_single,
      chars_style, List.filter_append, pad_inked, lf_inked, Node.ink]
    simp
  | .script attrs js, i, _, _, _ => by
    simp only [fB, charsList_addL, Array.toList_push, charsList_append, charsList_single,
      chars_script, List.filter_append, pad_inked, lf_inked, Node.ink]
    simp
  | .elem tag attrs kids, i, m, s, h => by
    have he := elem_parts h
    simp only [fB, charsList_addL, Array.toList_push, charsList_append, charsList_single,
      List.filter_append, pad_inked, lf_inked, List.append_nil]
    by_cases hr : (lower tag == "style" || lower tag == "script") = true
    · simp [ink_elem, hr, raw_chars _ _ _ hr]
    · have hr' : (lower tag == "style" || lower tag == "script") = false := by simpa using hr
      simp only [ink_elem, hr', Bool.false_eq_true, ite_false, chars_elem]
      have hinl : ∀ K', (Dom.charsList (fIL K' kids.toList).toList).toList.filter inked =
          (Dom.charsList K'.toList).toList.filter inked ++ (Node.inkList kids.toList).filter inked := by
        intro K'
        rcases kids_cases he with ⟨_, hk⟩ | ⟨_, hk⟩ | ⟨_, hk⟩
        · rw [hk]; simp [fIL, inkList_nil]
        · exact ink_fIL K' kids.toList m _ hk
        · exact ink_texts _ hk K'
      split
      · next hv =>
        rcases kids_cases he with ⟨_, hk⟩ | ⟨hv', _⟩ | ⟨hv', _⟩
        · rw [hk]; simp [charsList_nil, inkList_nil]
        · rw [hv] at hv'; exact absurd hv' (by decide)
        · rw [hv] at hv'; exact absurd hv' (by decide)
      · split
        · have := hinl #[]
          simp only [charsList_nil, String.toList_empty, List.filter_nil, List.nil_append] at this
          rw [this]
        · have hbl : (Dom.charsList (fBL (addL #[] ['\n']) kids.toList (i + 1)).toList).toList.filter inked =
              (Node.inkList kids.toList).filter inked := by
            rcases kids_cases he with ⟨_, hk⟩ | ⟨_, hk⟩ | ⟨_, hk⟩
            · rw [hk]; simp [fBL, inkList_nil, charsList_addL, charsList_nil, lf_inked]
            · rw [ink_fBL _ kids.toList (i + 1) m _ hk, charsList_addL]
              simp [charsList_nil, lf_inked]
            · rw [ink_fBL_texts kids.toList hk (i + 1), charsList_addL]
              simp [charsList_nil, lf_inked]
          rw [charsList_addL, List.filter_append, hbl, pad_inked, List.append_nil]

theorem ink_fI (K : Array Dom) : (n : Node) → (m : Mode) → (s : List Frame) →
    Accepts m s n = true →
    (Dom.charsList (fI K n).toList).toList.filter inked =
      (Dom.charsList K.toList).toList.filter inked ++ (Node.ink n).filter inked
  | .text t, _, _, _ => by simp [fI, charsList_addL, List.filter_append, Node.ink]
  | .style css, _, _, _ => by
    simp only [fI, Array.toList_push, charsList_append, charsList_single, chars_style, Node.ink]
    simp
  | .script attrs js, _, _, _ => by
    simp only [fI, Array.toList_push, charsList_append, charsList_single, chars_script, Node.ink]
    simp
  | .elem tag attrs kids, m, s, h => by
    have he := elem_parts h
    simp only [fI, Array.toList_push, charsList_append, charsList_single, List.filter_append]
    by_cases hr : (lower tag == "style" || lower tag == "script") = true
    · simp [ink_elem, hr, raw_chars _ _ _ hr]
    · have hr' : (lower tag == "style" || lower tag == "script") = false := by simpa using hr
      simp only [ink_elem, hr', Bool.false_eq_true, ite_false, chars_elem]
      split
      · next hv =>
        rcases kids_cases he with ⟨_, hk⟩ | ⟨hv', _⟩ | ⟨hv', _⟩
        · rw [hk]; simp [charsList_nil, inkList_nil]
        · rw [hv] at hv'; exact absurd hv' (by decide)
        · rw [hv] at hv'; exact absurd hv' (by decide)
      · have : (Dom.charsList (fIL #[] kids.toList).toList).toList.filter inked =
            (Node.inkList kids.toList).filter inked := by
          rcases kids_cases he with ⟨_, hk⟩ | ⟨_, hk⟩ | ⟨_, hk⟩
          · rw [hk]; simp [fIL, inkList_nil, charsList_nil]
          · simpa [charsList_nil] using ink_fIL #[] kids.toList m _ hk
          · simpa [charsList_nil] using ink_texts _ hk #[]
        rw [this]

theorem ink_fBL (K : Array Dom) : (l : List Node) → (i : Nat) → (m : Mode) → (s : List Frame) →
    AcceptsList m s l = true →
    (Dom.charsList (fBL K l i).toList).toList.filter inked =
      (Dom.charsList K.toList).toList.filter inked ++ (Node.inkList l).filter inked
  | [], _, _, _, _ => by simp [fBL, inkList_nil]
  | n :: rest, i, m, s, h => by
    simp only [AcceptsList, Bool.and_eq_true] at h
    simp only [fBL, inkList_cons, List.filter_append]
    rw [ink_fBL (fB K n i) rest i m s h.2, ink_fB K n i m s h.1, List.append_assoc]

theorem ink_fIL (K : Array Dom) : (l : List Node) → (m : Mode) → (s : List Frame) →
    AcceptsList m s l = true →
    (Dom.charsList (fIL K l).toList).toList.filter inked =
      (Dom.charsList K.toList).toList.filter inked ++ (Node.inkList l).filter inked
  | [], _, _, _ => by simp [fIL, inkList_nil]
  | n :: rest, m, s, h => by
    simp only [AcceptsList, Bool.and_eq_true] at h
    simp only [fIL, inkList_cons, List.filter_append]
    rw [ink_fIL (fI K n) rest m s h.2, ink_fI K n m s h.1, List.append_assoc]

end

/-- What a rendered page's text holds, white space aside, is what its body's text nodes hold
outside style sheets and scripts: the renderer adds only white space and drops no text. -/
public theorem pageText_render_ink (lang : String) (head body : Array Node)
    (h : DocOk lang head body = true) :
    ∃ t, HtmlRead.pageText (document lang head body) = some t ∧
      t.toList.filter inked = (Node.inkList body.toList).filter inked := by
  refine ⟨bodyChars body, pageText_render_exact lang head body h, ?_⟩
  obtain ⟨_, _, hb⟩ := docOk_parts h
  simp only [bodyChars, charsList_addL, List.filter_append]
  have hnl : (['\n', '\n'] : List Char).filter inked = [] := by decide
  rw [hnl, List.append_nil]
  unfold fKids
  split
  · simpa [charsList_nil] using ink_fIL #[] body.toList .inBody _ hb
  · rw [charsList_addL, List.filter_append, pad_inked, List.append_nil,
      ink_fBL _ body.toList 2 .inBody _ hb, charsList_addL]
    simp [charsList_nil, lf_inked]

end LeanTex.Core.Html
