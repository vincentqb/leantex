module

public import LeanTex.Core.Xml
public import LeanTex.Core.Css

/-!
# What an SVG may say: the resource boundary

The judge every SVG passes before anything reads it, a converter included,
evaluated over the parsed tree. A file is accepted when its root is an
`svg` element in the SVG namespace and nothing in it can reach outside the
file or run: no script, no foreign object, no event-handler or base-URI
attribute; every `href` or `src` a fragment reference — or, on an `image`
element, a `data:` URI declared PNG or JPEG or of no declared type, its
payload in any encoding, which carries its bytes and names nothing outside
the file; a function in an attribute only a fragment
`url(#id)` or, on a colour attribute, a wholly numeric `rgb()`/`rgba()`;
CSS within the subset `Css` reads; no animation that assigns a reference,
a style or an event. The XML reader has already refused DTD declarations,
external entities and processing instructions.

This is the boundary libxml's SAX events and an XPath over its tree used
to state, read the same way — names by their local part, values
whitespace-normalized as XPath's `normalize-space` normalizes them — with
two widenings: a `data:` image beyond the base64 PNG or JPEG reference the
XPath admitted, and CSS that spells a fragment `url(#id)` or a numeric
colour function, which only the attribute spelling admitted.
-/

namespace LeanTex.Core.Svg

open LeanTex.Core

@[expose] public def svgNs : String := "http://www.w3.org/2000/svg"
@[expose] public def xlinkNs : String := "http://www.w3.org/1999/xlink"

/-- XPath 1.0's `normalize-space` (§4.2): leading and trailing white space
gone, every inner run one space. -/
public def normalizeSpace (s : String) : String :=
  " ".intercalate ((s.split fun c => c == ' ' || c == '\t' || c == '\n' || c == '\r').toList.map
    (·.toString) |>.filter (!·.isEmpty))

/-- A character a local reference's id may hold: `Css.idChar`'s alphabet,
and `~` — the separator the engine's own figure ids hold (`GfxSvg.idSep`),
which closes no function and quotes nothing, so it can name nothing but a
fragment. -/
@[expose] public def refIdChar (c : Char) : Bool := Css.idChar c || c == '~'

/-- Exactly `url(#id)`, its id nonempty and drawn from `refIdChar`'s
alphabet, after normalization. -/
public def localUrl (v : String) : Bool :=
  let n := normalizeSpace v
  n.startsWith "url(#" && n.endsWith ")" && n.length > 6 &&
    ((n.drop 5).dropEnd 1).all refIdChar

/-- The attributes whose value is a colour. -/
@[expose] public def colorAttrs : List String :=
  ["fill", "stroke", "color", "stop-color", "flood-color", "lighting-color"]

/-- A colour attribute's wholly numeric `rgb()`/`rgba()`: its alphabet
cannot name a resource. -/
public def numericColor (attr v : String) : Bool :=
  colorAttrs.contains attr &&
    (let c := String.ofList ((normalizeSpace v).toList.map fun ch =>
        if ch == 'R' then 'r' else if ch == 'G' then 'g' else if ch == 'B' then 'b'
        else if ch == 'A' then 'a' else ch)
     let channels := match (c.splitOn "(") with
       | _ :: rest@(_ :: _) => ((("(".intercalate rest).splitOn ")").headD "")
       | _ => ""
     (c == "rgb(" ++ channels ++ ")" || c == "rgba(" ++ channels ++ ")") &&
       !channels.isEmpty && channels.all Css.channelChar)

/-- A value that spells CSS-like syntax: a call, an escape, an at-sign. -/
@[expose] public def cssSyntax (v : String) : Bool :=
  v.contains '(' || v.contains '\\' || v.contains '@'

/-- The attributes whose value is transform or timing syntax, which has
calls of its own and names no resource. -/
@[expose] public def callAttrs : List String :=
  ["transform", "gradientTransform", "patternTransform", "begin", "end"]

/-- The raster media types a `data:` image may declare: PNG and JPEG, or
none, when the bytes say which. -/
@[expose] public def rasterTypes : List String := ["image/png", "image/jpeg", "image/jpg", ""]

/-- A `data:` URI's media type and whether it is base64, when it is one. -/
public def dataUri (v : String) : Option (String × Bool × String) :=
  let n := normalizeSpace v
  if !(n.toLower.startsWith "data:") then none else
  match ((n.drop 5).toString).splitOn "," with
  | head :: rest@(_ :: _) =>
    let params := (head.splitOn ";").map (·.trimAscii.toString.toLower)
    let media := params.headD ""
    let b64 := params.contains "base64"
    some (media, b64, ",".intercalate rest)
  | _ => none

/-- A `data:` PNG or JPEG, which an `image` element may name. -/
public def dataRaster (v : String) : Bool :=
  match dataUri v with
  | some (media, _, _) => rasterTypes.contains media
  | none => false

/-- An attribute's value as a reference the boundary admits on element
`el`: a fragment, or an image's `data:` raster. -/
@[expose] public def refOk (el : String) (v : String) : Bool :=
  (normalizeSpace v).startsWith "#" || (el == "image" && dataRaster v)

/-- The values `attributeName` may not animate: a reference, a base, a
style, the timing of another animation, an event. -/
public def animatesRefused (v : String) : Bool :=
  let n := normalizeSpace v
  let local_ := match n.splitOn ":" with
    | [_, l] => l
    | _ => n
  ["href", "src", "base"].contains local_ ||
    ["style", "attributeName", "from", "to", "by", "values"].contains n || n.startsWith "on"

/-- Why the boundary refused a file. -/
public inductive Refused where
  | xml (r : Xml.Refusal)
  | names (why : String)
  | root
  | element (name : String)
  | attribute (el name : String)
  | style (why : String)
  | animation (target : String)
  deriving Repr, BEq, Inhabited

/-- One attribute where it stands: the element's local name, the
attribute. -/
public abbrev Site := String × Xml.Attr

mutual

-- conserves: none — a census of a tree's attributes, which the judge reads.
/-- Every attribute of a node and its descendants, with its element's local
name, in document order. -/
public def sitesOne (acc : Array Site) : Xml.Item → Array Site
  | .text _ => acc
  | .elem _ name attrs kids => sitesList (attrs.foldl (fun a at_ => a.push (name, at_)) acc) kids.toList

public def sitesList (acc : Array Site) : List Xml.Item → Array Site
  | [] => acc
  | n :: rest => sitesList (sitesOne acc n) rest

end

mutual

-- conserves: none — a census of a tree's elements, which the judge reads.
/-- Every element of a node and its descendants, in document order: its
local name, and a `style` element's text (what its sheet says; no other
element's text is read). -/
public def elemsOne (acc : Array (String × String)) : Xml.Item → Array (String × String)
  | .text _ => acc
  | n@(.elem _ name _ kids) =>
    elemsList (acc.push (name, if name == "style" then n.textOne "" else "")) kids.toList

public def elemsList (acc : Array (String × String)) : List Xml.Item → Array (String × String)
  | [] => acc
  | n :: rest => elemsList (elemsOne acc n) rest

end

/-- What the boundary refuses of one attribute, if anything. -/
public def attrRefusal (site : Site) : Option Refused :=
  let (el, a) := site
  let n := a.name
  if n == "base" || n.startsWith "on" then some (.attribute el n)
  else if (n == "href" || n == "src") && !refOk el a.value then some (.attribute el n)
  else if n == "style" then
    match Css.parseDecls a.value with
    | .error (.refused why) => some (.style why)
    | _ => none
  else if !(callAttrs.contains n) && cssSyntax a.value &&
      !(localUrl a.value || numericColor n a.value) then some (.attribute el n)
  else if n == "attributeName" && animatesRefused a.value then some (.animation (normalizeSpace a.value))
  else none

/-- What the boundary refuses of one element, if anything: a script, a
foreign object, a style sheet that spells what CSS here refuses. -/
public def elemRefusal (e : String × String) : Option Refused :=
  if e.1 == "script" || e.1 == "foreignObject" then some (.element e.1)
  else if e.1 == "style" then
    match Css.parseSheet e.2 with
    | .error why => some (.style why)
    | .ok _ => none
  else none

/-- Is the root an SVG `svg` element? -/
@[expose] public def svgRoot : Xml.Item → Bool
  | .elem ns name _ _ => ns == svgNs && name == "svg"
  | .text _ => false

/-- **The boundary's verdict on a parsed tree**: the first thing it refuses,
or nothing. -/
public def judgeTree (t : Xml.Item) : Option Refused :=
  if !svgRoot t then some .root
  else match (elemsOne #[] t).findSome? elemRefusal with
    | some r => some r
    | none => (sitesOne #[] t).findSome? attrRefusal

/-- **The boundary's verdict on bytes**: the tree, or what refused it. -/
public def judge (bytes : ByteArray) : Except Refused Xml.Item := do
  let node ← match Xml.parse bytes with
    | .ok n => pure n
    | .error r => throw (.xml r)
  let t ← match Xml.resolve node with
    | .ok t => pure t
    | .error why => throw (.names why)
  match judgeTree t with
  | some r => throw r
  | none => return t

/-- An admitted source's tree is the one its judge passed. -/
private theorem judge_tree (bytes : ByteArray) (t : Xml.Item) (h : judge bytes = .ok t) :
    judgeTree t = none := by
  unfold judge at h
  cases hp : Xml.parse bytes with
  | error r => simp [hp] at h <;> cases h
  | ok n =>
    cases hr : Xml.resolve n with
    | error w => simp [hp, hr] at h <;> cases h
    | ok t' =>
      cases hj : judgeTree t' with
      | some r => simp [hp, hr, hj] at h <;> cases h
      | none =>
        simp [hp, hr, hj] at h
        cases h
        exact hj

/-- A passed tree: an SVG root, no element the boundary refuses, no
attribute it refuses. -/
private theorem judgeTree_none (t : Xml.Item) (h : judgeTree t = none) :
    svgRoot t = true ∧ (∀ e ∈ elemsOne #[] t, elemRefusal e = none) ∧
      (∀ s ∈ sitesOne #[] t, attrRefusal s = none) := by
  unfold judgeTree at h
  by_cases hr : svgRoot t = true
  · simp only [hr, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    cases he : (elemsOne #[] t).findSome? elemRefusal with
    | some r => simp [he] at h
    | none =>
      simp only [he] at h
      exact ⟨hr, Array.findSome?_eq_none_iff.mp he, Array.findSome?_eq_none_iff.mp h⟩
  · simp [hr] at h

/-- What an admitted attribute is: no base, no event handler, and a
reference that is a fragment or an image's data raster. -/
private theorem attrRefusal_none (s : Site) (h : attrRefusal s = none) :
    s.2.name ≠ "base" ∧ s.2.name.startsWith "on" = false ∧
      ((s.2.name = "href" ∨ s.2.name = "src") → refOk s.1 s.2.value = true) := by
  obtain ⟨el, a⟩ := s
  unfold attrRefusal at h
  by_cases h1 : (a.name == "base" || a.name.startsWith "on") = true
  · simp [h1] at h
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
    simp only [Bool.or_eq_true, beq_iff_eq, not_or, Bool.not_eq_true] at h1
    refine ⟨h1.1, h1.2, ?_⟩
    intro hn
    by_cases h2 : ((a.name == "href" || a.name == "src") && !refOk el a.value) = true
    · simp [h2] at h
    · simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
        not_and, Bool.not_eq_false] at h2
      exact h2 hn

/-- What an admitted `style` attribute is: one the CSS reader does not
refuse. -/
private theorem attrRefusal_style (s : Site) (h : attrRefusal s = none) (hs : s.2.name = "style") :
    ∀ why, Css.parseDecls s.2.value ≠ .error (.refused why) := by
  obtain ⟨el, a⟩ := s
  simp only at hs ⊢
  intro why hw
  unfold attrRefusal at h
  by_cases h1 : (a.name == "base" || a.name.startsWith "on") = true
  · simp [h1] at h
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
    by_cases h2 : ((a.name == "href" || a.name == "src") && !refOk el a.value) = true
    · simp [h2] at h
    · simp only [↓reduceIte, hs, beq_self_eq_true, hw] at h
      cases h

/-- What any other admitted attribute is: a value that spells a call, an
escape or an at-sign is a local `url(#id)` or a colour attribute's numeric
`rgb()`/`rgba()`, unless the attribute's syntax is transform or timing. -/
private theorem attrRefusal_css (s : Site) (h : attrRefusal s = none) (hs : s.2.name ≠ "style")
    (hc : callAttrs.contains s.2.name = false) (hx : cssSyntax s.2.value = true) :
    localUrl s.2.value = true ∨ numericColor s.2.name s.2.value = true := by
  obtain ⟨el, a⟩ := s
  simp only at hs hc hx ⊢
  unfold attrRefusal at h
  by_cases h1 : (a.name == "base" || a.name.startsWith "on") = true
  · simp [h1] at h
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
    by_cases h2 : ((a.name == "href" || a.name == "src") && !refOk el a.value) = true
    · simp [h2] at h
    · simp only [h2, Bool.false_eq_true, ↓reduceIte] at h
      have h3 : (a.name == "style") = false := by simpa using hs
      simp only [h3, Bool.false_eq_true, ↓reduceIte, hc, Bool.not_false, hx, Bool.true_and] at h
      by_cases h4 : (localUrl a.value || numericColor a.name a.value) = true
      · simpa using h4
      · simp only [h4, Bool.not_false, ↓reduceIte] at h
        simp at h

/-- **Every reference an admitted SVG makes stays inside it** (`_covers`):
the source the native judge admits has an SVG root, no script and no
foreign object, no base URI and no event handler on any element, and every
`href` or `src` it carries is a fragment of its own tree or an image's
`data:` PNG or JPEG. A value that spells a call is a local `url(#id)` or a
colour's numeric `rgb()`/`rgba()`, unless it is transform or timing
syntax, and every `style` attribute and sheet passes the CSS reader's
refusals (`Css.refusedIn`: any function but those two, an escape, an
at-rule) — the judge's own checks, so a browser drawing it, or the
converter, is handed no reference the boundary did not read. -/
public theorem closure_covers (bytes : ByteArray) (t : Xml.Item) (h : judge bytes = .ok t) :
    svgRoot t = true ∧
    (∀ e ∈ elemsOne #[] t, e.1 ≠ "script" ∧ e.1 ≠ "foreignObject") ∧
    (∀ s ∈ sitesOne #[] t, s.2.name ≠ "base" ∧ s.2.name.startsWith "on" = false) ∧
    (∀ s ∈ sitesOne #[] t, (s.2.name = "href" ∨ s.2.name = "src") → refOk s.1 s.2.value = true) ∧
    (∀ s ∈ sitesOne #[] t, s.2.name ≠ "style" → callAttrs.contains s.2.name = false →
      cssSyntax s.2.value = true → localUrl s.2.value = true ∨ numericColor s.2.name s.2.value = true) ∧
    (∀ s ∈ sitesOne #[] t, s.2.name = "style" → ∀ why, Css.parseDecls s.2.value ≠ .error (.refused why)) ∧
    (∀ e ∈ elemsOne #[] t, e.1 = "style" → (Css.parseSheet e.2).toBool = true) := by
  obtain ⟨hr, he, ha⟩ := judgeTree_none t (judge_tree bytes t h)
  refine ⟨hr, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e hm
    have := he e hm
    unfold elemRefusal at this
    by_cases hs : (e.1 == "script" || e.1 == "foreignObject") = true
    · simp [hs] at this
    · simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hs
      exact hs
  · intro s hm
    obtain ⟨h1, h2, _⟩ := attrRefusal_none s (ha s hm)
    exact ⟨h1, h2⟩
  · intro s hm
    exact (attrRefusal_none s (ha s hm)).2.2
  · intro s hm hs hc hx
    exact attrRefusal_css s (ha s hm) hs hc hx
  · intro s hm hs
    exact attrRefusal_style s (ha s hm) hs
  · intro e hm hs
    have := he e hm
    unfold elemRefusal at this
    simp only [hs, ↓reduceIte, beq_self_eq_true] at this
    cases hp : Css.parseSheet e.2 with
    | error w => simp [hp] at this
    | ok _ => rfl

/-! ## The census reads the whole tree -/

/-- `e` is the tree `t` or an element below it: what the tree holds. -/
public inductive Holds : Xml.Item → Xml.Item → Prop
  | self (t : Xml.Item) : Holds t t
  | kid {e k : Xml.Item} {ns name : String} {attrs : Array Xml.Attr} {kids : Array Xml.Item} :
      k ∈ kids → Holds e k → Holds e (.elem ns name attrs kids)

private theorem foldlPush (name : String) (l : List Xml.Attr) (acc : Array Site) :
    l.foldl (fun a at_ => a.push (name, at_)) acc = acc ++ (l.map (name, ·)).toArray := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih => simp [List.foldl, ih]

mutual
private theorem sitesOne_acc (acc : Array Site) (n : Xml.Item) :
    sitesOne acc n = acc ++ sitesOne #[] n := by
  cases n with
  | text _ => simp [sitesOne]
  | elem ns name attrs kids =>
    simp only [sitesOne]
    rw [sitesList_acc _ kids.toList, sitesList_acc (Array.foldl _ #[] attrs) kids.toList,
      ← Array.foldl_toList, ← Array.foldl_toList, foldlPush, foldlPush]
    simp [Array.append_assoc]
private theorem sitesList_acc (acc : Array Site) (l : List Xml.Item) :
    sitesList acc l = acc ++ sitesList #[] l := by
  match l with
  | [] => simp [sitesList]
  | n :: rest =>
    simp only [sitesList]
    rw [sitesList_acc _ rest, sitesList_acc (sitesOne #[] n) rest, sitesOne_acc acc n,
      Array.append_assoc]
end

mutual
private theorem elemsOne_acc (acc : Array (String × String)) (n : Xml.Item) :
    elemsOne acc n = acc ++ elemsOne #[] n := by
  cases n with
  | text _ => simp [elemsOne]
  | elem ns name attrs kids =>
    simp only [elemsOne]
    rw [elemsList_acc _ kids.toList, elemsList_acc (#[].push _) kids.toList]
    simp
private theorem elemsList_acc (acc : Array (String × String)) (l : List Xml.Item) :
    elemsList acc l = acc ++ elemsList #[] l := by
  match l with
  | [] => simp [elemsList]
  | n :: rest =>
    simp only [elemsList]
    rw [elemsList_acc _ rest, elemsList_acc (elemsOne #[] n) rest, elemsOne_acc acc n,
      Array.append_assoc]
end

private theorem sitesList_mem (l : List Xml.Item) (k : Xml.Item) (hk : k ∈ l) (x : Site)
    (hx : x ∈ sitesOne #[] k) : x ∈ sitesList #[] l := by
  induction l with
  | nil => cases hk
  | cons n rest ih =>
    simp only [sitesList]
    rw [sitesList_acc]
    rcases List.mem_cons.mp hk with rfl | hr
    · exact Array.mem_append_left _ hx
    · exact Array.mem_append_right _ (ih hr)

private theorem elemsList_mem (l : List Xml.Item) (k : Xml.Item) (hk : k ∈ l)
    (x : String × String) (hx : x ∈ elemsOne #[] k) : x ∈ elemsList #[] l := by
  induction l with
  | nil => cases hk
  | cons n rest ih =>
    simp only [elemsList]
    rw [elemsList_acc]
    rcases List.mem_cons.mp hk with rfl | hr
    · exact Array.mem_append_left _ hx
    · exact Array.mem_append_right _ (ih hr)

/-- **The judge's attribute census holds every attribute of every element
the tree holds** (`_covers`), with its element's local name. -/
public theorem sites_covers {t e : Xml.Item} (h : Holds e t) :
    ∀ {ns name : String} {attrs : Array Xml.Attr} {kids : Array Xml.Item},
      e = .elem ns name attrs kids → ∀ a ∈ attrs, (name, a) ∈ sitesOne #[] t := by
  induction h with
  | self =>
    intro ns name attrs kids he a ha
    subst he
    simp only [sitesOne]
    rw [sitesList_acc, ← Array.foldl_toList, foldlPush]
    exact Array.mem_append_left _ (by simp [ha])
  | kid hk _ ih =>
    intro ns name attrs kids he a ha
    simp only [sitesOne]
    rw [sitesList_acc]
    exact Array.mem_append_right _ (sitesList_mem _ _ (Array.mem_toList_iff.mpr hk) _ (ih he a ha))

/-- **The judge's element census holds every element the tree holds**
(`_covers`): its local name, and a `style` element's text. -/
public theorem elems_covers {t e : Xml.Item} (h : Holds e t) :
    ∀ {ns name : String} {attrs : Array Xml.Attr} {kids : Array Xml.Item},
      e = .elem ns name attrs kids →
        (name, if name == "style" then e.textOne "" else "") ∈ elemsOne #[] t := by
  induction h with
  | self =>
    intro ns name attrs kids he
    subst he
    simp only [elemsOne]
    rw [elemsList_acc]
    exact Array.mem_append_left _ (by simp)
  | kid hk _ ih =>
    intro ns name attrs kids he
    simp only [elemsOne]
    rw [elemsList_acc]
    exact Array.mem_append_right _ (elemsList_mem _ _ (Array.mem_toList_iff.mpr hk) _ (ih he))

/-- **No element or attribute of an admitted SVG escapes the judge**
(`_covers`): every element the tree holds, wherever it stands, is no script
and no foreign object, a `style` element's sheet passes the CSS reader, and
every attribute it carries is no base or event handler, references a
fragment or an image's `data:` raster, and a `style` attribute passes the
CSS reader's refusals — `closure_covers`, carried from the judge's census
to the tree itself, which the census reads whole (`sites_covers`,
`elems_covers`). -/
public theorem closure_holds (bytes : ByteArray) (t : Xml.Item) (h : judge bytes = .ok t)
    (e : Xml.Item) (he : Holds e t) (ns name : String) (attrs : Array Xml.Attr)
    (kids : Array Xml.Item) (hel : e = .elem ns name attrs kids) :
    name ≠ "script" ∧ name ≠ "foreignObject" ∧
      (name = "style" → (Css.parseSheet (e.textOne "")).toBool = true) ∧
      ∀ a ∈ attrs, a.name ≠ "base" ∧ a.name.startsWith "on" = false ∧
        ((a.name = "href" ∨ a.name = "src") → refOk name a.value = true) ∧
        (a.name = "style" → ∀ why, Css.parseDecls a.value ≠ .error (.refused why)) := by
  obtain ⟨_, hel1, hat, href, _, hsty, hsheet⟩ := closure_covers bytes t h
  have hm := elems_covers he hel
  obtain ⟨hs, hf⟩ := hel1 _ hm
  refine ⟨hs, hf, ?_, ?_⟩
  · intro hn
    have := hsheet _ hm (by simpa using hn)
    simpa [hn] using this
  · intro a ha
    have hsite := sites_covers he hel a ha
    obtain ⟨hb, ho⟩ := hat _ hsite
    exact ⟨hb, ho, href _ hsite, hsty _ hsite⟩

/-- The words a refusal is reported in: the boundary's own, the construct
named. -/
public def Refused.message : Refused → String
  | .xml (.declaration what) =>
    s!"SVG resource boundary refuses DTD declarations and external entities ({what})"
  | .xml (.entity name) =>
    s!"SVG resource boundary refuses DTD declarations and external entities (the entity '{name}')"
  | .xml (.instruction target) =>
    s!"SVG resource boundary refuses processing instructions (<?{target} ...?>)"
  | .xml (.encoding name) =>
    s!"the SVG declares the encoding '{name}', which this reader does not read; save it as UTF-8"
  | .xml (.budget what) => s!"the SVG exceeds the reader's {what} budget"
  | .xml (.syntax pos what) => s!"SVG validation received an XML parser error at byte {pos}: {what}"
  | .names why => s!"SVG validation received an XML parser error: {why}"
  | .root => "SVG resource boundary requires an svg root element in the SVG namespace"
  | .element name =>
    s!"SVG resource boundary refuses the {name} element: scripts and foreign objects are unsupported"
  | .attribute el name =>
    s!"SVG resource boundary refuses the {name} attribute of {el}: references must be fragments \
(#id) or an image's data: PNG or JPEG, functions only url(#id) or a colour attribute's numeric \
rgb()/rgba(), and event handlers and base URIs are unsupported"
  | .style why =>
    s!"SVG resource boundary refuses {why} in CSS: CSS may spell only url(#id) and numeric \
rgb()/rgba(), with no escapes or at-rules"
  | .animation target =>
    s!"SVG resource boundary refuses an animation of '{target}': animated resource, style, \
timing and event assignments are unsupported"

/-! ## Font independence -/

/-- The element names that set text or name a font. -/
@[expose] public def textElems : List String :=
  ["text", "tspan", "textPath", "tref", "glyphRef"]

/-- Whether a converter's drawing of the tree can depend on host fonts: any
text, any font-naming element or attribute, any style, any font-relative
unit. Deliberately conservative: a `false` costs a cache slot, never a
conversion. -/
public def fontDependent (t : Xml.Item) : Bool :=
  let units := ["em", "ex", "ch", "ic", "lh", "cap"]
  (elemsOne #[] t).any (fun (n, txt) =>
      textElems.contains n || n.startsWith "altGlyph" || n.startsWith "font" ||
        (n == "style" && !(normalizeSpace txt).isEmpty)) ||
    (sitesOne #[] t).any fun (_, a) =>
      a.name.startsWith "font" || a.name == "style" ||
        (a.name == "attributeName" && (normalizeSpace a.value).startsWith "font") ||
        units.any fun u => (a.value.toLower.splitOn u).length > 1

end LeanTex.Core.Svg
