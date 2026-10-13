module

public import LeanTex.Core.Xml
public import LeanTex.Core.SvgJudge
import LeanTex.Core.PathData

/-!
# The pose at the end of an SVG animation

A static projection of synchronized SVG animation tracks, read from the
parsed tree: the pose approached at the end of one simple duration, before
repeat and fill handling (SVG 1.1 §19.2.9). It neither runs authored code
nor samples a timeline. Each `animate` names an attribute of its parent and
a `values` list; the projection writes the list's last value into that
attribute and drops the animation, and every other node stands as it is.

Only the timelines whose end is that last value are read: one linear or
discrete track per shape geometry or opacity attribute, starting at zero,
every track one finite duration in seconds, keyframes finite unitless
decimals (an absolute M/L path for `d`). Any other timeline — motion,
transforms, `set`, CSS, a delayed begin, a fractional repeat count — is refused with
the reason, never projected to a pose it does not reach. This is the
projection the XSLT stylesheet this module replaces stated, read the same
way.
-/

namespace LeanTex.Core.SvgPoster

open LeanTex.Core

/-- An XPath number's spelling: an optional `-`, digits, at most one point,
at least one digit — `number()` reads anything else as NaN. -/
public def scalar? (s : String) : Bool :=
  let cs := if s.startsWith "-" then (s.drop 1).toString.toList else s.toList
  let digits := cs.filter Char.isDigit
  !digits.isEmpty && cs.all (fun c => c.isDigit || c == '.') && (cs.filter (· == '.')).length ≤ 1

/-- An XPath number's value, for the spellings `scalar?` admits. -/
public def scalarValue (s : String) : Rat :=
  match PathData.number s.toList with
  | some (d, _) => d.toRat
  | none => 0

/-- What projecting a track can fail with: the boundary's own words. -/
@[expose] public def refusedTimeline : String :=
  "SVG last poster requires plain attribute animations without CSS, motion, transforms or set elements"

@[expose] public def refusedTrack : String :=
  "SVG last poster requires one linear/discrete values track per shape geometry or opacity attribute, starting at zero with the same finite duration in seconds; other targets or timing require a PDF frame sequence"

/-- Is the track's attribute a geometry of its parent element, or an
opacity of a graphical one? -/
public def geometryOf (parent attr : String) : Bool :=
  let isIn (xs : List String) := xs.contains attr
  (parent == "rect" && isIn ["x", "y", "width", "height", "rx", "ry"]) ||
  (parent == "circle" && isIn ["cx", "cy", "r"]) ||
  (parent == "ellipse" && isIn ["cx", "cy", "rx", "ry"]) ||
  (parent == "line" && isIn ["x1", "y1", "x2", "y2"]) ||
  (parent == "path" && isIn ["d", "stroke-dashoffset"]) ||
  ((parent == "text" || parent == "tspan") && isIn ["x", "y"]) ||
  (attr == "opacity" && ["g", "rect", "circle", "ellipse", "line", "path", "polygon", "polyline",
    "text", "tspan", "use", "image"].contains parent)

/-- The attributes a track may carry. -/
@[expose] public def trackAttrs : List String :=
  ["attributeName", "values", "keyTimes", "dur", "begin", "repeatCount", "fill", "calcMode",
   "attributeType"]

/-- A duration's seconds, when it is a finite positive decimal ending in `s`. -/
public def seconds? (dur : String) : Option Rat :=
  let d := Svg.normalizeSpace dur
  if !d.endsWith "s" then none else
  let n := (d.dropEnd 1).toString
  if n.isEmpty || !n.all (fun c => c.isDigit || c == '.') || (n.toList.filter (· == '.')).length > 1 then none
  else if !(n.any Char.isDigit) then none
  else
    let v := scalarValue n
    if v > 0 then some v else none

/-- The number of `L` commands a path value spells. -/
@[expose] public def lCount (s : String) : Nat := (s.toList.filter (· == 'L')).length

/-- An absolute M/L path's coordinate pairs, each a finite decimal. -/
public def pathPoints? (v : String) : Bool :=
  v.startsWith "M" &&
    (((v.drop 1).toString.splitOn "L").all fun pair =>
      match pair.splitOn "," with
      | [x, y] => scalar? (Svg.normalizeSpace x) && scalar? (Svg.normalizeSpace y)
      | _ => false)

/-- A track's values as the projection reads them: split on `;`, each
whitespace-normalized. -/
@[expose] public def trackValues (values : String) : List String :=
  (values.splitOn ";").map Svg.normalizeSpace

/-- The keyframes a track's terminal value is read from, checked: every
value and keyTime one the projection reads. -/
public def checkKeyframes (attr : String) (values : String) (times : Option String)
    (discrete : Bool) : Except String Unit := do
  let vs := trackValues values
  let shape := Svg.normalizeSpace ((values.splitOn ";").headD "")
  let ts : Option (List String) := times.map fun t => (t.splitOn ";").map Svg.normalizeSpace
  if vs.any (·.isEmpty) then
    throw "SVG last poster requires nonempty values and increasing keyTimes from zero"
  if let some ts := ts then
    if ts.length < vs.length then throw "SVG last poster requires one keyTime per value"
    if ts.length > vs.length then
      throw "SVG last poster requires one keyTime per value, ending at one for linear tracks or below one for discrete tracks"
    let nums := ts.map fun t => if scalar? t then some (scalarValue t) else none
    let mut prev : Option Rat := none
    for n in nums do
      match n with
      | none => throw "SVG last poster requires nonempty values and increasing keyTimes from zero"
      | some v =>
        let ok := 0 ≤ v && v ≤ 1 && (match prev with | some p => v > p | none => v == 0)
        unless ok do throw "SVG last poster requires nonempty values and increasing keyTimes from zero"
        prev := some v
    match prev with
    | some last =>
      if (!discrete && last != 1) || (discrete && last == 1) then
        throw "SVG last poster requires one keyTime per value, ending at one for linear tracks or below one for discrete tracks"
    | none => pure ()
  for v in vs do
    if attr == "d" then
      if !v.startsWith "M" || (!discrete && lCount v != lCount shape) then
        throw "SVG last poster requires absolute M/L comma-pair paths with matching commands across linear keyframes"
      unless pathPoints? v do
        throw "SVG last poster requires finite unitless decimal values in every keyframe"
    else
      unless scalar? v do throw "SVG last poster requires finite unitless decimal values in every keyframe"
      if ["width", "height", "r", "rx", "ry"].contains attr && scalarValue v < 0 then
        throw "SVG last poster requires nonnegative sizes in every keyframe"

/-- **A track's terminal value** (`terminal_exact`): its last value, when
every keyframe and keyTime is one the projection reads; else the reason. -/
public def terminalValue (attr : String) (values : String) (times : Option String)
    (discrete : Bool) : Except String String := do
  checkKeyframes attr values times discrete
  return (trackValues values).getLastD ""

/-- **The terminal value is the track's last value** (`_exact`): whatever a
projection writes into an animated attribute is the last of the track's
values, as written — the pose at the end of one simple duration (SVG 1.1
§19.2.9), never a sampled or interpolated one. -/
public theorem terminal_exact (attr values : String) (times : Option String) (discrete : Bool)
    (v : String) (h : terminalValue attr values times discrete = .ok v) :
    v = (trackValues values).getLastD "" := by
  unfold terminalValue at h
  cases hc : checkKeyframes attr values times discrete with
  | error e => simp [hc] at h; cases h
  | ok u =>
    simp only [hc] at h
    cases h
    rfl

/-- One track's checks, against the first track's duration. -/
public def checkTrack (parent : String) (earlier : List String) (firstDur : Option Rat)
    (attrs : Array Xml.Attr) : Except String Unit := do
  let get (n : String) := Xml.Attr.get? attrs "" n
  let attr := (get "attributeName").getD ""
  unless geometryOf parent attr do throw refusedTrack
  if attrs.any (fun a => a.ns != "" || !trackAttrs.contains a.name) then throw refusedTrack
  unless ((get "values").getD "").contains ';' do throw refusedTrack
  if earlier.contains attr then throw refusedTrack
  if let some b := get "begin" then
    let b := Svg.normalizeSpace b
    unless b == "0" || b == "0s" do throw refusedTrack
  if let some r := get "repeatCount" then
    unless r == "1" || r == "indefinite" do throw refusedTrack
  if let some f := get "fill" then
    unless f == "freeze" || f == "remove" do throw refusedTrack
  if let some c := get "calcMode" then
    unless c == "linear" || c == "discrete" do throw refusedTrack
  if let some t := get "attributeType" then
    unless t == "XML" || t == "auto" do throw refusedTrack
  let some secs := seconds? ((get "dur").getD "") | throw refusedTrack
  unless firstDur == some secs do throw refusedTrack

/-- Is a node an SVG `animate` element? -/
@[expose] public def isAnimate : Xml.Item → Bool
  | .elem ns name _ _ => ns == Svg.svgNs && name == "animate"
  | .text _ => false

/-- An element's tracks read in order: the attributes they animate (latest
first), and each one's terminal value to write; else the first track's
reason. -/
public def trackSets (name : String) (firstDur : Option Rat) (tracks : Array Xml.Item) :
    Except String (List String × Array Xml.Attr) := do
  let mut earlier : List String := []
  let mut set : Array Xml.Attr := #[]
  for t in tracks do
    let .elem _ _ tattrs _ := t | continue
    checkTrack name earlier firstDur tattrs
    let attr := (Xml.Attr.get? tattrs "" "attributeName").getD ""
    let discrete := Xml.Attr.get? tattrs "" "calcMode" == some "discrete"
    let v ← terminalValue attr ((Xml.Attr.get? tattrs "" "values").getD "")
      (Xml.Attr.get? tattrs "" "keyTimes") discrete
    earlier := attr :: earlier
    set := set.push { ns := "", name := attr, value := v }
  return (earlier, set)

/-- No track, nothing written. -/
private theorem trackSets_empty (name : String) (firstDur : Option Rat) :
    trackSets name firstDur #[] = .ok ([], #[]) := by
  simp [trackSets]
  rfl

mutual

-- conserves: none — a projection that writes each animated attribute's
-- terminal value; `terminal_fixed_point` and `terminal_exact` state it.
/-- One node projected: an element with `animate` children gets each
animated attribute's terminal value and loses the animations; every other
node stands, its children projected. -/
public def projectOne (firstDur : Option Rat) : Xml.Item → Except String Xml.Item
  | .text s => .ok (.text s)
  | .elem ns name attrs kids => do
    let (earlier, set) ← trackSets name firstDur (kids.filter isAnimate)
    let kept := attrs.filter fun a => !(a.ns == "" && earlier.contains a.name)
    let kids ← projectList firstDur #[] kids.toList
    return .elem ns name (kept ++ set) kids

public def projectList (firstDur : Option Rat) (acc : Array Xml.Item) :
    List Xml.Item → Except String (Array Xml.Item)
  | [] => .ok acc
  | n :: rest =>
    if isAnimate n then projectList firstDur acc rest
    else do projectList firstDur (acc.push (← projectOne firstDur n)) rest

end

mutual

-- conserves: none — a test: whether a tree holds an SVG `animate`.
/-- Whether a tree holds no SVG `animate` element: a pose. -/
public def stillOne : Xml.Item → Bool
  | .text _ => true
  | n@(.elem _ _ _ kids) => !isAnimate n && stillList kids.toList

public def stillList : List Xml.Item → Bool
  | [] => true
  | n :: rest => stillOne n && stillList rest

end

private theorem ok_bind {α β ε : Type} (x : α) (f : α → Except ε β) : (Except.ok x >>= f) = f x := rfl

/-- A list holds no animate exactly when none of its nodes is one. -/
private theorem stillList_iff (ns : List Xml.Item) :
    stillList ns = true ↔ ∀ n ∈ ns, stillOne n = true := by
  induction ns with
  | nil => simp [stillList]
  | cons n rest ih => simp [stillList, ih]

/-- A still node is no animate. -/
private theorem stillOne_not_animate (n : Xml.Item) (h : stillOne n = true) : isAnimate n = false := by
  cases n with
  | text s => rfl
  | elem ns name attrs kids =>
    simp only [stillOne, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact h.1

mutual

/-- **A pose projects to itself**: a tree holding no animation is its own
projection. -/
private theorem projectOne_still (fd : Option Rat) (n : Xml.Item) (h : stillOne n = true) :
    projectOne fd n = .ok n := by
  match n with
  | .text s => rfl
  | .elem ns name attrs kids =>
    simp only [stillOne, Bool.and_eq_true, Bool.not_eq_true'] at h
    have hk : kids.filter isAnimate = #[] := by
      rw [Array.filter_eq_empty_iff]
      intro x hx
      have := (stillList_iff kids.toList).mp h.2 x (Array.mem_toList_iff.mpr hx)
      simp [stillOne_not_animate x this]
    have hl := projectList_still fd #[] kids.toList h.2
    simp only [projectOne, hk, trackSets_empty, hl, ok_bind]
    have hf : attrs.filter (fun a => !(a.ns == "" && ([] : List String).contains a.name)) = attrs :=
      Array.filter_eq_self.mpr (fun a _ => by simp)
    simp only [hf, Array.append_empty, Array.empty_append]
    simp
    rfl

private theorem projectList_still (fd : Option Rat) (acc : Array Xml.Item) (ns : List Xml.Item)
    (h : stillList ns = true) : projectList fd acc ns = .ok (acc ++ ns.toArray) := by
  match ns with
  | [] => simp [projectList]
  | n :: rest =>
    simp only [stillList, Bool.and_eq_true] at h
    have ha := stillOne_not_animate n h.1
    simp only [projectList, ha, Bool.false_eq_true, ↓reduceIte, projectOne_still fd n h.1, ok_bind]
    rw [projectList_still fd (acc.push n) rest h.2]
    simp

end

mutual

-- conserves: none — a census of a tree's animations, in document order.
/-- Every SVG `animate` element's attributes, in document order. -/
public def tracksOne (acc : Array (Array Xml.Attr)) : Xml.Item → Array (Array Xml.Attr)
  | .text _ => acc
  | n@(.elem _ _ attrs kids) =>
    tracksList (if isAnimate n then acc.push attrs else acc) kids.toList

public def tracksList (acc : Array (Array Xml.Attr)) : List Xml.Item → Array (Array Xml.Attr)
  | [] => acc
  | n :: rest => tracksList (tracksOne acc n) rest

end

mutual

-- conserves: none — a census of a tree's elements by namespace and local
-- name, in document order, which the timeline checks read.
/-- Every element of a node and its descendants: its namespace and local
name. -/
public def kindsOne (acc : Array (String × String)) : Xml.Item → Array (String × String)
  | .text _ => acc
  | .elem ns name _ kids => kindsList (acc.push (ns, name)) kids.toList

public def kindsList (acc : Array (String × String)) : List Xml.Item → Array (String × String)
  | [] => acc
  | n :: rest => kindsList (kindsOne acc n) rest

end

/-! ### The projection's fixed point -/

mutual

private theorem kindsOne_acc (acc : Array (String × String)) (n : Xml.Item) :
    kindsOne acc n = acc ++ kindsOne #[] n := by
  match n with
  | .text _ => simp [kindsOne]
  | .elem ns name _ kids =>
    simp only [kindsOne]
    rw [kindsList_acc, kindsList_acc (#[].push (ns, name))]
    simp

private theorem kindsList_acc (acc : Array (String × String)) (ns : List Xml.Item) :
    kindsList acc ns = acc ++ kindsList #[] ns := by
  match ns with
  | [] => simp [kindsList]
  | n :: rest =>
    simp only [kindsList]
    rw [kindsList_acc _ rest, kindsList_acc (kindsOne #[] n) rest, kindsOne_acc acc n, Array.append_assoc]

end

mutual

private theorem tracksOne_acc (acc : Array (Array Xml.Attr)) (n : Xml.Item) :
    tracksOne acc n = acc ++ tracksOne #[] n := by
  match n with
  | .text _ => simp [tracksOne]
  | .elem ns name attrs kids =>
    simp only [tracksOne]
    rw [tracksList_acc]
    conv => rhs; rw [tracksList_acc]
    by_cases ha : isAnimate (.elem ns name attrs kids) = true <;> simp [ha]

private theorem tracksList_acc (acc : Array (Array Xml.Attr)) (ns : List Xml.Item) :
    tracksList acc ns = acc ++ tracksList #[] ns := by
  match ns with
  | [] => simp [tracksList]
  | n :: rest =>
    simp only [tracksList]
    rw [tracksList_acc _ rest, tracksList_acc (tracksOne #[] n) rest, tracksOne_acc acc n,
      Array.append_assoc]

end

private theorem kindsList_append (a b : List Xml.Item) :
    kindsList #[] (a ++ b) = kindsList #[] a ++ kindsList #[] b := by
  induction a with
  | nil => simp [kindsList]
  | cons n rest ih =>
    simp only [List.cons_append, kindsList]
    rw [kindsList_acc, ih, kindsList_acc (kindsOne #[] n) rest, Array.append_assoc]

mutual

/-- A pose holds no track and no SVG `animate` element. -/
private theorem still_kinds (n : Xml.Item) (h : stillOne n = true) :
    tracksOne #[] n = #[] ∧ ∀ k ∈ kindsOne #[] n, ¬(k.1 = Svg.svgNs ∧ k.2 = "animate") := by
  match n with
  | .text _ => simp [tracksOne, kindsOne]
  | .elem ns name attrs kids =>
    simp only [stillOne, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨hk, hl⟩ := still_kindsList kids.toList h.2
    refine ⟨?_, ?_⟩
    · simp only [tracksOne, h.1, Bool.false_eq_true, ↓reduceIte]
      exact hk
    · intro k hm
      simp only [kindsOne] at hm
      rw [kindsList_acc] at hm
      rcases Array.mem_append.mp hm with h0 | h1
      · simp only [List.push_toArray, List.nil_append, List.mem_toArray, List.mem_singleton] at h0
        subst h0
        intro ⟨e1, e2⟩
        simp only at e1 e2
        simp only [isAnimate, Bool.and_eq_false_imp, beq_iff_eq] at h
        exact absurd (by simpa using e2) (by simpa using h.1 e1)
      · exact hl k h1

private theorem still_kindsList (ns : List Xml.Item) (h : stillList ns = true) :
    tracksList #[] ns = #[] ∧ ∀ k ∈ kindsList #[] ns, ¬(k.1 = Svg.svgNs ∧ k.2 = "animate") := by
  match ns with
  | [] => simp [tracksList, kindsList]
  | n :: rest =>
    simp only [stillList, Bool.and_eq_true] at h
    obtain ⟨t1, k1⟩ := still_kinds n h.1
    obtain ⟨t2, k2⟩ := still_kindsList rest h.2
    refine ⟨?_, ?_⟩
    · simp only [tracksList]
      rw [tracksList_acc, t1, t2]
      rfl
    · intro k hm
      simp only [kindsList] at hm
      rw [kindsList_acc] at hm
      rcases Array.mem_append.mp hm with h0 | h1
      · exact k1 k h0
      · exact k2 k h1

end

mutual

/-- **What a projection leaves**: a node that is no animation projects to a
pose, every element of which was an element of the node. -/
private theorem projectOne_out (fd : Option Rat) (n p : Xml.Item) (hn : isAnimate n = false)
    (h : projectOne fd n = .ok p) :
    stillOne p = true ∧ ∀ k ∈ kindsOne #[] p, k ∈ kindsOne #[] n := by
  match n with
  | .text s =>
    simp only [projectOne] at h
    cases h
    simp [stillOne, kindsOne]
  | .elem ns name attrs kids =>
    simp only [projectOne] at h
    cases ht : trackSets name fd (kids.filter isAnimate) with
    | error e => simp [ht] at h; cases h
    | ok es =>
      cases hl : projectList fd #[] kids.toList with
      | error e => simp [ht, hl] at h; cases h
      | ok kids' =>
        simp [ht, hl] at h
        cases h
        obtain ⟨hs, hk⟩ := projectList_out fd #[] kids.toList kids' hl
        refine ⟨?_, ?_⟩
        · simp only [stillOne, Bool.and_eq_true, Bool.not_eq_true']
          refine ⟨by simpa [isAnimate] using hn, ?_⟩
          rw [stillList_iff]
          intro x hx
          rcases hs x (Array.mem_toList_iff.mp hx) with h0 | h1
          · simp at h0
          · exact h1
        · intro k hm
          simp only [kindsOne] at hm ⊢
          rw [kindsList_acc] at hm ⊢
          rcases Array.mem_append.mp hm with h0 | h1
          · exact Array.mem_append.mpr (.inl h0)
          · rcases hk k h1 with h2 | h3
            · simp [kindsList] at h2
            · exact Array.mem_append.mpr (.inr h3)

private theorem projectList_out (fd : Option Rat) (acc : Array Xml.Item) (ns : List Xml.Item)
    (out : Array Xml.Item) (h : projectList fd acc ns = .ok out) :
    (∀ x ∈ out, x ∈ acc ∨ stillOne x = true) ∧
      ∀ k ∈ kindsList #[] out.toList, k ∈ kindsList #[] acc.toList ∨ k ∈ kindsList #[] ns := by
  match ns with
  | [] =>
    simp only [projectList] at h
    cases h
    exact ⟨fun x hx => .inl hx, fun k hk => .inl hk⟩
  | n :: rest =>
    by_cases ha : isAnimate n = true
    · simp only [projectList, ha, ↓reduceIte] at h
      obtain ⟨hs, hk⟩ := projectList_out fd acc rest out h
      refine ⟨hs, fun k hm => ?_⟩
      rcases hk k hm with h0 | h1
      · exact .inl h0
      · refine .inr ?_
        simp only [kindsList]
        rw [kindsList_acc]
        exact Array.mem_append.mpr (.inr h1)
    · have ha' : isAnimate n = false := by simpa using ha
      simp only [projectList, ha', Bool.false_eq_true, ↓reduceIte] at h
      cases hp : projectOne fd n with
      | error e => simp [hp] at h; cases h
      | ok p0 =>
        simp only [hp, ok_bind] at h
        obtain ⟨hs, hk⟩ := projectList_out fd (acc.push p0) rest out h
        obtain ⟨ps, pk⟩ := projectOne_out fd n p0 ha' hp
        refine ⟨fun x hx => ?_, fun k hm => ?_⟩
        · rcases hs x hx with h0 | h1
          · rcases Array.mem_push.mp h0 with h2 | h3
            · exact .inl h2
            · subst h3; exact .inr ps
          · exact .inr h1
        · rcases hk k hm with h0 | h1
          · rw [Array.toList_push, kindsList_append] at h0
            rcases Array.mem_append.mp h0 with h2 | h3
            · exact .inl h2
            · simp only [kindsList] at h3
              refine .inr ?_
              simp only [kindsList]
              rw [kindsList_acc]
              exact Array.mem_append.mpr (.inl (pk k h3))
          · refine .inr ?_
            simp only [kindsList]
            rw [kindsList_acc]
            exact Array.mem_append.mpr (.inr h1)

end

/-- An animation element the projection does not read: motion, a
transform, a colour, a `set`, a `discard`. -/
@[expose] public def otherAnimationKind (k : String × String) : Bool :=
  (k.2.startsWith "animate" && k.2 != "animate") || k.2 == "set" || k.2 == "discard"

/-- An `animate` in another namespace: no SVG track — the stylesheet's
element test reads local names, so it refuses those too. -/
@[expose] public def foreignAnimateKind (k : String × String) : Bool :=
  k.2 == "animate" && k.1 != Svg.svgNs

/-- The duration every track must share: the first track's. -/
@[expose] public def firstDurOf (tracks : Array (Array Xml.Attr)) : Option Rat :=
  tracks[0]?.bind fun a => seconds? ((Xml.Attr.get? a "" "dur").getD "")

/-- **The terminal pose of a tree**, or why it has none this projection
reads. -/
public def terminal (t : Xml.Item) : Except String Xml.Item := do
  let kinds := kindsOne #[] t
  let tracks := tracksOne #[] t
  if kinds.any otherAnimationKind || kinds.any foreignAnimateKind then throw refusedTimeline
  if !tracks.isEmpty && (kinds.any (·.2 == "style") || (Svg.sitesOne #[] t).any (·.2.name == "style")) then
    throw refusedTimeline
  projectOne (firstDurOf tracks) t

/-- **The terminal pose is a fixed point** (`_fixed_point`): the pose of a
pose is itself — projected, a tree holds no SVG animation left to read, and
it passes every check the tree passed, since each of its elements was the
tree's. -/
public theorem terminal_fixed_point (t p : Xml.Item) (ht : isAnimate t = false)
    (h : terminal t = .ok p) : terminal p = .ok p := by
  simp only [terminal] at h
  split at h
  · cases h
  · next c1 =>
    split at h
    · cases h
    · next c2 =>
      obtain ⟨hs, hk⟩ := projectOne_out _ t p ht h
      obtain ⟨htr, _⟩ := still_kinds p hs
      have n1 : ((kindsOne #[] p).any otherAnimationKind ||
          (kindsOne #[] p).any foreignAnimateKind) = false := by
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at c1
        cases e1 : (kindsOne #[] p).any otherAnimationKind
        · cases e2 : (kindsOne #[] p).any foreignAnimateKind
          · rfl
          · obtain ⟨k, hm, hf⟩ := Array.any_eq_true'.mp e2
            have := Array.any_eq_true'.mpr ⟨k, hk k hm, hf⟩
            rw [c1.2] at this
            cases this
        · obtain ⟨k, hm, hf⟩ := Array.any_eq_true'.mp e1
          have := Array.any_eq_true'.mpr ⟨k, hk k hm, hf⟩
          rw [c1.1] at this
          cases this
      simp only [terminal, n1, htr, Bool.false_eq_true, ↓reduceIte, Array.isEmpty_empty,
        Bool.not_true, Bool.false_and]
      exact projectOne_still _ p hs

/-- A judged tree's pose: as authored, or its terminal pose at the end. -/
public def poseOf (tree : Xml.Item) (atEnd : Bool) : Except String Xml.Item :=
  if atEnd then terminal tree else pure tree

/-- **The pose a figure is drawn in**: its judged tree as authored, or —
where the request asks for the end of its animation — the terminal pose;
else the boundary's or the projection's reason. What both the PDF's
drawing and the browser's still face read, so the two draw one pose. -/
public def pose (bytes : ByteArray) (atEnd : Bool) : Except String Xml.Item := do
  let tree ← match Svg.judge bytes with
    | .ok t => pure t
    | .error r => throw r.message
  poseOf tree atEnd

end LeanTex.Core.SvgPoster
