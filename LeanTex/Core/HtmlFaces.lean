module

public import LeanTex.Core.Html
public import Std.Data.HashMap
public import Std.Data.HashSet
import LeanTex.Core.Css
import LeanTex.Core.Hex

/-! The font requests a web page's text makes, read from its typed tree and style sheets as a
browser's cascade (CSS Cascading 4 §6) sets `font-family`, `font-weight` and `font-style`, and the
face CSS Fonts 4 §5.2 selects for each. -/

namespace LeanTex.Core.HtmlFaces

open LeanTex.Core.Html

/-! ## Face selection -/

/-- How far a face's weight is from a requested one in the order CSS Fonts 4 §5.2 tries them. -/
public def weightRank (want face : Nat) : Nat :=
  if want < 400 then (if face ≤ want then want - face else 1000 + face)
  else if want ≤ 500 then
    (if want ≤ face && face ≤ 500 then face - want
     else if face < want then 1000 + (want - face) else 2000 + face)
  else (if want ≤ face then face - want else 1000 + (want - face))

/-- A face's rank for a request: style before weight. -/
public def rank (want face : Nat × Bool) : Nat :=
  (if face.2 == want.2 then 0 else 10000) + weightRank want.1 face.1

/-- The face a browser selects from a family's faces for a request: the least rank, the last
declared of equals. -/
public def select? {α : Type} (desc : α → Nat × Bool) (want : Nat × Bool) : List α → Option α
  | [] => none
  | f :: rest =>
    match select? desc want rest with
    | none => some f
    | some b => if rank want (desc b) ≤ rank want (desc f) then some b else some f

public theorem select?_nil {α : Type} (desc : α → Nat × Bool) (want : Nat × Bool) :
    select? desc want ([] : List α) = none := by
  simp [select?]

public theorem select?_none {α : Type} (desc : α → Nat × Bool) (want : Nat × Bool) :
    ∀ l : List α, select? desc want l = none → l = []
  | [], _ => rfl
  | _ :: rest, h => by
    simp only [select?] at h
    split at h
    · contradiction
    · split at h <;> contradiction

public theorem select?_mem {α : Type} (desc : α → Nat × Bool) (want : Nat × Bool) :
    ∀ (l : List α) (f : α), select? desc want l = some f → f ∈ l
  | [], _, h => by simp [select?] at h
  | x :: rest, f, h => by
    simp only [select?] at h
    split at h
    · simp_all
    · next b hb =>
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        exact List.mem_cons_of_mem _ (select?_mem desc want rest b hb)
      · simp_all

public theorem select?_le {α : Type} (desc : α → Nat × Bool) (want : Nat × Bool) :
    ∀ (l : List α) (f : α), select? desc want l = some f →
      ∀ g ∈ l, rank want (desc f) ≤ rank want (desc g)
  | [], _, h => by simp [select?] at h
  | x :: rest, f, h => by
    intro g hg
    simp only [select?] at h
    split at h
    · next hn =>
      simp only [Option.some.injEq] at h
      subst h
      rw [select?_none desc want rest hn] at hg
      simp_all
    · next b hb =>
      have hrest := select?_le desc want rest b hb
      split at h
      · next hle =>
        simp only [Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hg with rfl | hg
        · exact hle
        · exact hrest g hg
      · next hlt =>
        simp only [Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hg with rfl | hg
        · exact Nat.le_refl _
        · exact Nat.le_trans (Nat.le_of_lt (Nat.lt_of_not_le hlt)) (hrest g hg)

/-- Faces dropped around the selected one leave it selected: a browser picks from a subset holding
its choice what it picks from the whole family. -/
public theorem select?_filter {α : Type} (desc : α → Nat × Bool) (want : Nat × Bool) (p : α → Bool) :
    ∀ (l : List α) (f : α), select? desc want l = some f → p f = true →
      select? desc want (l.filter p) = some f
  | [], _, h, _ => by simp [select?] at h
  | x :: rest, f, h, hp => by
    simp only [select?] at h
    split at h
    · next hn =>
      simp only [Option.some.injEq] at h
      subst h
      rw [select?_none desc want rest hn]
      simp [hp, select?]
    · next b hb =>
      split at h
      · next hle =>
        simp only [Option.some.injEq] at h
        subst h
        have ih := select?_filter desc want p rest b hb hp
        by_cases hx : p x = true
        · simp [hx, select?, ih, hle]
        · simp [hx, ih]
      · next hlt =>
        simp only [Option.some.injEq] at h
        subst h
        simp only [List.filter_cons, hp, ite_true, select?]
        split
        · rfl
        · next b' hb' =>
          have hmem := List.mem_filter.mp (select?_mem desc want _ b' hb')
          have hle := select?_le desc want rest b hb b' hmem.1
          have : ¬ rank want (desc b') ≤ rank want (desc x) := by omega
          simp only [this, ite_false]

/-! ## Requests -/

/-- A family a browser tries for some text, at a weight and style. -/
public structure Use where
  family : String
  weight : Nat
  italic : Bool
  deriving Repr, DecidableEq, Hashable, Inhabited

/-- The font a run of text asks for: its family stacks, its weights (`none` for any) and styles
(`none` for either); a stack holding `*` names every family. -/
public structure Want where
  stacks : Array (List String)
  weights : Option (Array Nat)
  italics : Option (Array Bool)
  deriving Repr, BEq, Hashable, Inhabited

/-- Each request's characters. -/
public abbrev Requests := Std.HashMap Want (Std.HashSet Char)

/-- The families tried for one character, in stack order, until a selected face covers it. -/
public def tried {α : Type} (faces : String → List α) (desc : α → Nat × Bool)
    (covers : α → Char → Bool) (want : Nat × Bool) (c : Char) : List String → List Use
  | [] => []
  | g :: rest =>
    match select? desc want (faces g) with
    | none => tried faces desc covers want c rest
    | some f =>
      { family := g, weight := want.1, italic := want.2 } ::
        (if covers f c then [] else tried faces desc covers want c rest)

/-- Each character a request asks, with the weight and style it may be set at and the family stack
it is set from, a stack's `*` read as every family. -/
public def asks {α : Type} (families : List String) (faces : String → List α)
    (desc : α → Nat × Bool) (reqs : Requests) : List ((Nat × Bool) × Char × List String) :=
  reqs.toList.flatMap fun (w, cs) => w.stacks.toList.flatMap fun stack =>
    let stack := stack.flatMap fun g => if g == "*" then families else [g]
    let weights := w.weights.getD
      ((stack.flatMap fun g => (faces g).map (desc · |>.1)).eraseDups.toArray)
    let italics := w.italics.getD #[false, true]
    weights.toList.flatMap fun wt => italics.toList.flatMap fun it =>
      cs.toList.map fun c => ((wt, it), c, stack)

/-- Every family, weight and style the requests try. -/
public def uses {α : Type} (families : List String) (faces : String → List α)
    (desc : α → Nat × Bool) (covers : α → Char → Bool) (reqs : Requests) : Array Use :=
  ((asks families faces desc reqs).foldl (fun out (want, c, stack) =>
    (tried faces desc covers want c stack).foldl (·.insert ·) out) ({} : Std.HashSet Use)).toArray

/-- The face font fallback sets `c` in (CSS Fonts 4 §5.4): of the faces each family of the stack
selects, the first covering it. -/
public def fallback {α : Type} (faces : String → List α) (desc : α → Nat × Bool)
    (covers : α → Char → Bool) (want : Nat × Bool) (c : Char) : List String → Option α
  | [] => none
  | g :: rest =>
    match select? desc want (faces g) with
    | some f => if covers f c then some f else fallback faces desc covers want c rest
    | none => fallback faces desc covers want c rest

public theorem tried_want {α : Type} (faces : String → List α) (desc : α → Nat × Bool)
    (covers : α → Char → Bool) (want : Nat × Bool) (c : Char) :
    ∀ (stack : List String), ∀ u ∈ tried faces desc covers want c stack,
      (u.weight, u.italic) = want
  | [], u, h => by simp [tried] at h
  | g :: rest, u, h => by
    simp only [tried] at h
    split at h
    · exact tried_want faces desc covers want c rest u h
    · rcases List.mem_cons.mp h with rfl | h
      · rfl
      · split at h
        · simp at h
        · exact tried_want faces desc covers want c rest u h

/-- Faces that select in each family it tries what `faces` selects, and nothing where `faces`
selects nothing, set every character in the face `faces` sets it in. -/
public theorem fallback_exact {α : Type} (faces faces' : String → List α) (desc : α → Nat × Bool)
    (covers : α → Char → Bool) (want : Nat × Bool) (c : Char)
    (hnone : ∀ g, select? desc want (faces g) = none → select? desc want (faces' g) = none) :
    ∀ (stack : List String),
      (∀ u ∈ tried faces desc covers want c stack,
        select? desc want (faces' u.family) = select? desc want (faces u.family)) →
      fallback faces' desc covers want c stack = fallback faces desc covers want c stack
  | [], _ => rfl
  | g :: rest, h => by
    simp only [fallback]
    cases hs : select? desc want (faces g) with
    | none =>
      rw [hnone g hs]
      refine fallback_exact faces faces' desc covers want c hnone rest fun u hu => h u ?_
      simp only [tried, hs]
      exact hu
    | some f =>
      have hg := h { family := g, weight := want.1, italic := want.2 } (by simp [tried, hs])
      simp only at hg
      rw [hg, hs]
      by_cases hc : covers f c = true
      · simp [hc]
      · simp only [hc, Bool.false_eq_true, ↓reduceIte]
        refine fallback_exact faces faces' desc covers want c hnone rest fun u hu => h u ?_
        simp [tried, hs, hc, hu]

theorem mem_foldl_insert {β : Type} [BEq β] [Hashable β] [LawfulBEq β] (x : β) :
    ∀ (l : List β) (s : Std.HashSet β), x ∈ s ∨ x ∈ l → x ∈ l.foldl (·.insert ·) s
  | [], _, h => by simpa using h
  | y :: rest, s, h => by
    refine mem_foldl_insert x rest (s.insert y) ?_
    rcases h with h | h
    · exact Or.inl (Std.HashSet.mem_insert.mpr (Or.inr h))
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl (Std.HashSet.mem_insert.mpr (Or.inl (beq_self_eq_true _)))
      · exact Or.inr h

/-- Every family a request's character tries is one of the uses. -/
public theorem uses_covers {α : Type} (families : List String) (faces : String → List α)
    (desc : α → Nat × Bool) (covers : α → Char → Bool) (reqs : Requests) :
    ∀ a ∈ asks families faces desc reqs, ∀ u ∈ tried faces desc covers a.1 a.2.1 a.2.2,
      u ∈ uses families faces desc covers reqs := by
  intro a ha u hu
  simp only [uses]
  rw [Std.HashSet.mem_toArray]
  suffices h : ∀ (l : List ((Nat × Bool) × Char × List String)) (out : Std.HashSet Use),
      (u ∈ out ∨ ∃ b ∈ l, u ∈ tried faces desc covers b.1 b.2.1 b.2.2) →
        u ∈ l.foldl (fun out (want, c, stack) =>
          (tried faces desc covers want c stack).foldl (·.insert ·) out) out from
    h _ _ (Or.inr ⟨a, ha, hu⟩)
  intro l
  induction l with
  | nil => intro out h; simpa using h
  | cons b rest ih =>
    intro out h
    refine ih _ ?_
    rcases h with h | ⟨b', hb', hu'⟩
    · exact Or.inl (mem_foldl_insert u _ out (Or.inl h))
    · rcases List.mem_cons.mp hb' with rfl | hb'
      · exact Or.inl (mem_foldl_insert u _ out (Or.inr hu'))
      · exact Or.inr ⟨b', hb', hu'⟩

/-! ## Selectors -/

/-- A compound selector's tested part: type, classes and ids; `cond` when it holds a condition
this reading drops. -/
structure Comp where
  tag : Option String := none
  classes : Array String := #[]
  ids : Array String := #[]
  cond : Bool := false
  deriving Inhabited

/-- A complex selector: its subject, the compounds above it innermost first with whether each is a
parent (`true`) or an ancestor, its pseudo-element, and whether it states nothing this reading drops. -/
structure Sel where
  subject : Comp
  up : List (Bool × Comp)
  pe : Option String
  exact : Bool
  spec : Nat
  deriving Inhabited

/-- A rule's selectors and font-relevant declarations, whether a condition (a media query, a
support test) gates it, and its order. -/
structure FRule where
  sels : Array Sel
  decls : Array (String × String × Bool)
  gated : Bool
  order : Nat
  deriving Inhabited

private def identChar (c : Char) : Bool := Css.identChar c

private def legacyPe (n : String) : Bool :=
  n == "before" || n == "after" || n == "first-line" || n == "first-letter"

/-- A selector read from its text, `none` for a spelling this reading cannot follow, which then
selects every element. -/
def parseSel (text : String) : Option Sel := Id.run do
  let cs := text.trimAscii.toString.toList.toArray
  let mut i := 0
  let mut comps : Array (Option Bool × Comp) := #[]
  let mut cur : Comp := {}
  let mut pending : Option Bool := none
  let mut started := false
  let mut pe : Option String := none
  let mut exact := true
  let ident (j : Nat) : Nat := Id.run do
    let mut k := j
    for _ in [0:cs.size + 1] do
      match cs[k]? with
      | some c => if identChar c then k := k + 1 else break
      | none => break
    return k
  let word (a b : Nat) : String := String.ofList (cs.extract a b).toList
  for _ in [0:cs.size + 1] do
    let some c := cs[i]? | break
    if Css.isWs c || c == '>' || c == '+' || c == '~' then
      if started then
        comps := comps.push (pending, cur)
        cur := {}
        started := false
        pending := some false
      if c == '>' then pending := some true
      else if c == '+' || c == '~' then
        pending := none
        exact := false
      i := i + 1
    else if pe.isSome then return none
    else if c == '*' then
      started := true
      i := i + 1
    else if identChar c && !started then
      let k := ident i
      cur := { cur with tag := some (word i k).toLower }
      started := true
      i := k
    else if c == '.' || c == '#' then
      let k := ident (i + 1)
      if k == i + 1 then return none
      let n := word (i + 1) k
      cur := if c == '.' then { cur with classes := cur.classes.push n }
        else { cur with ids := cur.ids.push n }
      started := true
      i := k
    else if c == '\\' then
      cur := { cur with cond := true }
      exact := false
      started := true
      i := ident (i + 2)
    else if c == '[' || c == ':' then
      let elementPe := c == ':' && cs[i + 1]? == some ':'
      let a := if c == '[' then i else if elementPe then i + 2 else i + 1
      let k := if c == '[' then a else ident a
      let name := (word a k).toLower
      -- what follows the name: an argument or an attribute test, to its matching close
      let mut depth := 0
      let mut j := k
      let mut quote : Option Char := none
      if c == '[' || cs[k]? == some '(' then
        for _ in [0:cs.size + 1] do
          let some d := cs[j]? | break
          j := j + 1
          match quote with
          | some q => if d == q then quote := none
          | none =>
            if d == '"' || d == '\'' then quote := some d
            else if d == '(' || d == '[' then depth := depth + 1
            else if d == ')' || d == ']' then
              depth := depth - 1
              if depth == 0 then break
        if depth != 0 then return none
      if elementPe || (c == ':' && legacyPe name) then pe := some name
      else
        cur := { cur with cond := true }
        exact := false
      started := true
      i := j
    else return none
  if started then comps := comps.push (pending, cur)
  let some (_, subject) := comps.back? | return none
  -- above a sibling combinator nothing is read; the subject's ancestors innermost first
  let mut up : List (Bool × Comp) := []
  let mut k := comps.size - 1
  for _ in [0:comps.size] do
    if k == 0 then break
    match comps[k]?.map (·.1) with
    | some (some parent) =>
      up := up ++ [(parent, (comps[k - 1]?.getD (none, {})).2)]
      k := k - 1
    | _ => break
  let all := comps.map (·.2)
  let spec := all.foldl (fun n c => n + c.ids.size * 1048576 + c.classes.size * 1024 +
    (if c.tag.isSome then 1 else 0)) (if pe.isSome then 1 else 0)
  return some { subject, up := up, pe, exact := exact && !all.any (·.cond), spec }

/-- The selector matching everything, which an unreadable spelling stands for. -/
def anySel : Sel := { subject := { cond := true }, up := [], pe := some "*", exact := false, spec := 0 }

/-- What a selector reads of an element: its type, classes and id. -/
structure Subject where
  tag : String
  classes : Array String
  id : Option String
  deriving Inhabited

/-- Whether a compound may hold of an element; a class a script may set is assumed held. -/
def Comp.holds (dyn : Array String) (c : Comp) (e : Subject) : Bool :=
  c.tag.all (· == e.tag) && c.classes.all (fun k => e.classes.contains k || dyn.contains k) &&
    c.ids.all (some · == e.id)

/-- Whether the compounds above a subject may hold of its ancestors, innermost first. -/
def upHolds (dyn : Array String) : List (Bool × Comp) → List Subject → Bool
  | [], _ => true
  | (true, c) :: more, p :: ps => c.holds dyn p && upHolds dyn more ps
  | (true, _) :: _, [] => false
  | (false, c) :: more, ups => tryUp c more ups
where
  tryUp (c : Comp) (more : List (Bool × Comp)) : List Subject → Bool
    | [] => false
    | p :: ps => (c.holds dyn p && upHolds dyn more ps) || tryUp c more ps

/-- Whether a selector may match an element under its ancestors, and whether it surely does. -/
def Sel.test (dyn : Array String) (s : Sel) (e : Subject) (up : List Subject) : Option Bool :=
  if s.subject.holds dyn e && upHolds dyn s.up up then
    some (s.exact && !(s.subject.classes.any dyn.contains) &&
      !(s.up.any fun (_, c) => c.classes.any dyn.contains))
  else none

/-! ## Sheets -/

private def fontProp (p : String) : Bool :=
  p == "font-family" || p == "font-weight" || p == "font-style" || p == "font" ||
    p == "content" || p == "display" || p == "font-synthesis" || p == "list-style-type" ||
    p == "list-style"

/-- A declaration block's declarations: property, value and importance. -/
def declsOf (body : String) : Array (String × String × Bool) :=
  (Css.splitList ';' body).filterMap fun part =>
    match part.splitOn ":" with
    | prop :: rest@(_ :: _) =>
      let prop := prop.trimAscii.toString
      let (value, imp) := Css.importance (":".intercalate rest).trimAscii.toString
      some ((if prop.startsWith "--" then prop else prop.toLower), value, imp)
    | _ => none

/-- At-rules whose blocks set nothing on elements' text. -/
private def inertAt (name : String) : Bool :=
  ["@font-face", "@keyframes", "@-webkit-keyframes", "@page", "@property", "@counter-style",
   "@font-feature-values", "@font-palette-values", "@view-transition"].contains name

/-- Whether a style rule's block holds a nested rule (CSS Nesting), which this reading does not
model. -/
private def nestsRules (body : String) : Bool :=
  (Css.atoms body).any (·.head? == some '{')

/-- Whether an at-rule's block may set text's font in a way this reading does not model: a
registered property's initial value, or a page margin box's generated content. -/
private def unmodeledAt (name body : String) : Bool :=
  name == "@property" || (name == "@page" && (nestsRules body || (body.splitOn "content").length > 1))

/-- Whether a value rolls back to an earlier origin's, which this reading does not model. -/
private def reverts (v : String) : Bool :=
  (v.toLower.splitOn "revert").length > 1

/-- Whether a statement imports a sheet: an at-rule's name is ASCII case-insensitive, and the
sheet's end ends it as `;` does (CSS Syntax 3 §5.4.2). -/
private def importsSheet (prelude : String) : Bool :=
  prelude.trimAscii.toString.toLower.startsWith "@import"

structure Sheet where
  rules : Array FRule := #[]
  vars : Std.HashMap String (Array String) := {}
  /-- A sheet this reading does not see (an import) or a construct it does not model leaves every
  face possible. -/
  elsewhere : Bool := false

/-- A sheet's rules onto `sh`, a conditional group's rules gated. -/
def Sheet.read (sh : Sheet) (text : String) (gated : Bool) : Sheet := Id.run do
  let mut sh := sh
  let mut prelude := ""
  -- a block's text and gate, read in turn
  let mut todo : List (String × Bool) := [(Css.stripComments text, gated)]
  for _ in [0:text.length + 1] do
    match todo with
    | [] => break
    | (t, g) :: more =>
      todo := more
      for a in Css.atoms t do
        if a.head? == some ';' then
          if importsSheet prelude then sh := { sh with elsewhere := true }
          prelude := ""
        else if a.head? != some '{' then prelude := a.foldl String.push prelude
        else
          let body := String.ofList (if Css.closedAtom a then (a.drop 1).dropLast else a.drop 1)
          let pre := prelude.trimAscii.toString
          prelude := ""
          if pre.startsWith "@" then
            let name := (pre.takeWhile (fun c => !Css.isWs c && c != '(')).toString.toLower
            if unmodeledAt name body then sh := { sh with elsewhere := true }
            else unless inertAt name do todo := todo ++ [(body, true)]
          else
            if nestsRules body then sh := { sh with elsewhere := true }
            let decls := declsOf body
            if decls.any fun (p, v, _) => fontProp p && reverts v then
              sh := { sh with elsewhere := true }
            for (p, v, _) in decls do
              if p.startsWith "--" then
                sh := { sh with vars := sh.vars.insert p ((sh.vars.getD p #[]).push v) }
            let decls := decls.filter (fontProp ·.1)
            unless decls.isEmpty do
              let sels := (Css.splitList ',' pre).map fun s => (parseSel s).getD anySel
              let rule : FRule := { sels, decls, gated := g, order := sh.rules.size + 1 }
              sh := { sh with rules := sh.rules.push rule }
      if importsSheet prelude then sh := { sh with elsewhere := true }
      prelude := ""
  return sh

/-- A sheet's rules filed by the key their subject requires: an id, else a class, else a type,
else none. -/
structure Index where
  byKey : Std.HashMap String (Array (Nat × Nat)) := {}
  universal : Array (Nat × Nat) := #[]

def Comp.key (c : Comp) : Option String :=
  match c.ids[0]?, c.classes[0]?, c.tag with
  | some i, _, _ => some ("#" ++ i)
  | none, some k, _ => some ("." ++ k)
  | none, none, some t => some t
  | none, none, none => none

def Index.of (rules : Array FRule) : Index := Id.run do
  let mut ix : Index := {}
  for h : i in [0:rules.size] do
    for h2 : j in [0:rules[i].sels.size] do
      match rules[i].sels[j].subject.key with
      | some k => ix := { ix with byKey := ix.byKey.insert k ((ix.byKey.getD k #[]).push (i, j)) }
      | none => ix := { ix with universal := ix.universal.push (i, j) }
  return ix

def Index.candidates (ix : Index) (dyn : Array String) (e : Subject) : Array (Nat × Nat) :=
  let keys := (e.id.map ("#" ++ ·)).toList ++ (e.classes ++ dyn).toList.map ("." ++ ·) ++ [e.tag]
  keys.foldl (fun acc k => acc ++ ix.byKey.getD k #[]) ix.universal

/-! ## Cascade -/

/-- The font an element sets its text in: each component a set of what it may be. -/
structure FState where
  stacks : Array (List String)
  weights : Option (Array Nat)
  italics : Option (Array Bool)
  /-- The list styles a marker may set, `none` for any. -/
  lists : Option (Array String)
  deriving BEq, Hashable, Inhabited

def FState.want (s : FState) : Want := { stacks := s.stacks, weights := s.weights, italics := s.italics }

/-- A declaration that may set an element's property, its cascade key, and whether it surely
applies. -/
structure Cand where
  value : String
  key : Nat
  sure : Bool

private def keyOf (important : Bool) (level spec order : Nat) : Nat :=
  (if important then 1 else 0) * 2 ^ 90 + level * 2 ^ 80 + spec * 2 ^ 20 + order

/-- The values that may win a property: those of declarations at or above the highest that surely
applies, and the inherited one when none surely does. -/
def winners (cands : Array Cand) : Array String × Bool :=
  match cands.foldl (fun m c => if c.sure then some (max (m.getD 0) c.key) else m) none with
  | some top => ((cands.filter fun c => !c.sure || c.key ≥ top).map (·.value), false)
  | none => (cands.map (·.value), true)

/-- A value with each `var()` it starts with replaced by what the sheet declares for it, and
`none` past one substitution. -/
def expand (vars : Std.HashMap String (Array String)) (v : String) : Option (Array String) :=
  let v := v.trimAscii.toString
  if !(v.startsWith "var(") then (if (v.splitOn "var(").length > 1 then none else some #[v]) else
  let inner := ((v.drop 4).dropEnd 1).toString
  let parts := Css.splitList ',' inner
  let name := (parts[0]?.getD "").trimAscii.toString
  let fallback := if parts.size > 1 then
      #[(",".intercalate (parts.extract 1 parts.size).toList).trimAscii.toString] else #[]
  let all := vars.getD name #[] ++ fallback
  -- a property no sheet declares leaves the value invalid at computed-value time, so inherited
  let all := if all.isEmpty then #["inherit"] else all
  if all.any (fun s => (s.splitOn "var(").length > 1) || !v.endsWith ")" then none else some all

private def bolder (w : Nat) : Nat :=
  if w < 350 then 400 else if w < 550 then 700 else if w < 900 then 900 else w

private def lighter (w : Nat) : Nat :=
  if w < 100 then w else if w < 550 then 100 else if w < 750 then 400 else 700

private def inherits (v : String) : Bool :=
  v == "inherit" || v == "unset" || v == "revert" || v == "revert-layer"

def weightsOf (parent : Option (Array Nat)) (v : String) : Option (Array Nat) :=
  let v := v.toLower
  if inherits v then parent
  else if v == "normal" || v == "initial" then some #[400]
  else if v == "bold" then some #[700]
  else if v == "bolder" then parent.map (·.map bolder)
  else if v == "lighter" then parent.map (·.map lighter)
  else (v.toNat?.filter fun n => 1 ≤ n && n ≤ 1000).map (#[·])

def italicsOf (parent : Option (Array Bool)) (v : String) : Option (Array Bool) :=
  let v := v.toLower
  if inherits v then parent
  else if v == "normal" || v == "initial" then some #[false]
  else if v == "italic" || v.startsWith "oblique" then some #[true]
  else none

/-- The list style a `list-style` shorthand sets (CSS Lists 3 §3.4): its one style word or string,
`none` alone for both style and image, nothing but a position or an image for the initial `disc`. -/
def shorthandType (v : String) : String :=
  let word (w : String) := if w.startsWith "\"" || w.startsWith "'" then w else w.toLower
  let words := ((Css.splitList ' ' v.trimAscii.toString).toList.map (word ·.trimAscii.toString)).filter
    fun w => !w.isEmpty && w != "inside" && w != "outside" && !w.startsWith "url("
  match words with
  | [] => "initial"
  | ["none", "none"] => "none"
  | [w] => w
  | _ => "?"

def listsOf (parent : Option (Array String)) (v : String) : Option (Array String) :=
  let v := v.trimAscii.toString
  let v := if v.startsWith "\"" || v.startsWith "'" then v else v.toLower
  if inherits v then parent
  else if v.toLower == "initial" then some #["disc"]
  else if v.startsWith "\"" || v.startsWith "'" || v.all fun c => c.isAlphanum || c == '-' then
    some #[v]
  else none

def stacksOf (parent : Array (List String)) (v : String) : Array (List String) :=
  let l := v.toLower
  if inherits l then parent
  else if l == "initial" then #[["serif"]]
  else #[((Css.splitList ',' v).map fun n =>
      let n := n.trimAscii.toString
      let n := if (n.startsWith "\"" && n.endsWith "\"") || (n.startsWith "'" && n.endsWith "'")
        then ((n.drop 1).dropEnd 1).toString else n
      n.toLower).toList]

private def union {β : Type} [BEq β] (a b : Array β) : Array β :=
  b.foldl (fun acc x => if acc.contains x then acc else acc.push x) a

private def unionOpt {β : Type} [BEq β] : Option (Array β) → Option (Array β) → Option (Array β)
  | some a, some b => some (union a b)
  | _, _ => none

/-- An element's state from its parent's and the declarations that may set it. -/
def resolve (vars : Std.HashMap String (Array String)) (parent : FState)
    (cands : String → Array Cand) : FState :=
  let readAll (cs : Array Cand) : Option (Array String) × Bool :=
    let (vs, inh) := winners cs
    (vs.foldl (fun acc v => match acc, expand vars v with
      | some a, some e => some (a ++ e)
      | _, _ => none) (some #[]), inh)
  let read (prop : String) := readAll (cands prop)
  let (fam, famInh) := read "font-family"
  let (wt, wtInh) := read "font-weight"
  let (it, itInh) := read "font-style"
  let (ls, lsInh) := readAll (cands "list-style-type" ++
    (cands "list-style").map fun c => { c with value := shorthandType c.value })
  let stacks := match fam with
    | some vs => vs.foldl (fun acc v => union acc (stacksOf parent.stacks v))
        (if famInh then parent.stacks else #[])
    | none => #[["*"]]
  let weights := wt.bind fun vs => vs.foldl (fun acc v => unionOpt acc (weightsOf parent.weights v))
    (if wtInh then parent.weights else some #[])
  let italics := it.bind fun vs => vs.foldl (fun acc v => unionOpt acc (italicsOf parent.italics v))
    (if itInh then parent.italics else some #[])
  let lists := ls.bind fun vs => vs.foldl (fun acc v => unionOpt acc (listsOf parent.lists v))
    (if lsInh then parent.lists else some #[])
  -- a `font` shorthand may set any of the three
  if (cands "font").isEmpty then { stacks, weights, italics, lists }
  else { stacks := union stacks #[["*"]], weights := none, italics := none, lists }

/-- The user agent's own font declarations for an element (HTML §15.3, MathML Core §A). -/
def uaDecls (tag : String) : Array (String × String) :=
  if tag == "b" || tag == "strong" then #[("font-weight", "bolder")]
  else if ["h1", "h2", "h3", "h4", "h5", "h6", "th"].contains tag then #[("font-weight", "bold")]
  else if ["em", "i", "cite", "var", "dfn", "address"].contains tag then #[("font-style", "italic")]
  else if ["code", "kbd", "samp", "pre", "tt", "listing", "xmp", "plaintext"].contains tag then
    #[("font-family", "monospace")]
  else if tag == "math" then
    #[("font-family", "math"), ("font-style", "normal"), ("font-weight", "normal")]
  else #[]

/-- SVG's presentation attributes that set a font. -/
private def presentational (p : String) : Bool :=
  p == "font-family" || p == "font-weight" || p == "font-style"

/-- Characters a counter may print: ASCII letters and digits, a point and a hyphen. -/
private def counterChars : String :=
  String.ofList (((List.range 128).map Char.ofNat).filter Char.isAlphanum) ++ ".-"

/-- Characters a list item's or a disclosure's own marker may print. -/
private def markerChars : String := "•◦▪▸▾▶▼–-.()" ++ counterChars

/-- The user agent's list styles for an element under its ancestors (HTML §15.3.8), each with
whether it surely applies. -/
private def uaListStyles (tag : String) (up : List Subject) : Array (String × Bool) :=
  let lists := ["ul", "ol", "menu", "dir"]
  let depth := (up.filter fun p => lists.contains p.tag).length
  if ["ul", "menu", "dir"].contains tag then
    #[(if depth == 0 then "disc" else if depth == 1 then "circle" else "square", true)]
  else if tag == "ol" then #[("decimal", true)]
  else if tag == "summary" then #[("disclosure-closed", true), ("disclosure-open", false)]
  else #[]

/-- A CSS string's characters with its escapes read (CSS Syntax 3 §4.3.7): hex digits naming a code
point and one whitespace after them, an escaped line end dropped, any other character itself. -/
public def unescape (cs : List Char) : String := Id.run do
  let isHex (c : Char) : Bool := (Hex.digit? c).isSome
  let value (h : String) : Nat := (Hex.value? h.toList).getD 0
  let mut out := ""
  -- the hex digits after a backslash, `none` outside an escape
  let mut hex : Option String := none
  for c in cs do
    match hex with
    | none => if c == '\\' then hex := some "" else out := out.push c
    | some h =>
      if isHex c && h.length < 6 then hex := some (h.push c)
      else if h.isEmpty then
        unless Css.isLineEnd c do out := out.push c
        hex := none
      else
        out := out.push (Char.ofNat (value h))
        hex := if c == '\\' then some "" else none
        unless Css.isWs c || c == '\\' do out := out.push c
  if let some h := hex then
    unless h.isEmpty do out := out.push (Char.ofNat (value h))
  return out

/-- Characters a marker of the list style `v` prints: its symbol, its counter's digits and suffix, or
its string; any marker's for a style this reading does not know. -/
private def styleChars (v : String) : String :=
  if v == "disc" then "•" else if v == "circle" then "◦" else if v == "square" then "▪"
  else if v == "disclosure-open" then "▾▼" else if v == "disclosure-closed" then "▸▶"
  else if v == "none" then ""
  else if v.startsWith "\"" || v.startsWith "'" then unescape ((v.drop 1).dropEnd 1).toString.toList
  else if ["decimal", "decimal-leading-zero", "lower-alpha", "upper-alpha", "lower-latin",
      "upper-latin", "lower-roman", "upper-roman"].contains v then counterChars
  else markerChars

/-- The characters a `content` value may print: its strings, a counter's digits and letters, the
attributes it reads, and the quotation marks a quote keyword may set. -/
public def contentChars (attrs : Array (String × String)) (v : String) : String := Id.run do
  let mut out := ""
  for a in Css.atoms v do
    match a with
    | q :: rest =>
      if q == '"' || q == '\'' then
        out := out ++ unescape (if rest.getLast? == some q then rest.dropLast else rest)
    | [] => pure ()
  if (v.splitOn "counter").length > 1 then out := out ++ counterChars
  if (v.splitOn "open-quote").length > 1 || (v.splitOn "close-quote").length > 1 then
    out := out ++ "\"'“”‘’«»‹›„‚"
  for part in (v.splitOn "attr(").drop 1 do
    let name := (part.takeWhile (fun c => c != ')' && c != ',' && !Css.isWs c)).toString
    out := out ++ ((attrs.find? (·.1 == name)).map (·.2)).getD ""
  return out

/-- Mathematical italic for a character MathML Core's `math-auto` transforms (§5.1, its italic
table): Latin and Greek letters, dotless i and j, and the italic Greek symbols. -/
def mathItalic (c : Char) : Option Char :=
  let n := c.toNat
  if c == 'h' then some (Char.ofNat 0x210E)
  else if 'a'.toNat ≤ n && n ≤ 'z'.toNat then some (Char.ofNat (0x1D44E + n - 'a'.toNat))
  else if 'A'.toNat ≤ n && n ≤ 'Z'.toNat then some (Char.ofNat (0x1D434 + n - 'A'.toNat))
  else if 0x3B1 ≤ n && n ≤ 0x3C9 then some (Char.ofNat (0x1D6FC + n - 0x3B1))
  else if 0x391 ≤ n && n ≤ 0x3A9 && n != 0x3A2 then some (Char.ofNat (0x1D6E2 + n - 0x391))
  else if n == 0x3F4 then some (Char.ofNat 0x1D6F3)
  else if n == 0x2207 then some (Char.ofNat 0x1D6FB)
  else if n == 0x2202 then some (Char.ofNat 0x1D715)
  else if n == 0x3F5 then some (Char.ofNat 0x1D716)
  else if n == 0x3D1 then some (Char.ofNat 0x1D717)
  else if n == 0x3F0 then some (Char.ofNat 0x1D718)
  else if n == 0x3D5 then some (Char.ofNat 0x1D719)
  else if n == 0x3F1 then some (Char.ofNat 0x1D71A)
  else if n == 0x3D6 then some (Char.ofNat 0x1D71B)
  else if n == 0x131 then some (Char.ofNat 0x1D6A4)
  else if n == 0x237 then some (Char.ofNat 0x1D6A5)
  else none

/-- A character no font draws: a control, an ASCII blank, a zero-width mark or a soft hyphen. -/
private def inkless (c : Char) : Bool :=
  let n := c.toNat
  n < 0x21 || (0x7F ≤ n && n < 0xA0) || n == 0xAD || (0x200B ≤ n && n ≤ 0x200F) ||
    (0x2028 ≤ n && n ≤ 0x202E) || (0x2060 ≤ n && n ≤ 0x2064) || n == 0xFEFF

/-- What the walk carries: the element's subject chain, innermost first, and its state. -/
structure Ctx where
  up : List Subject
  state : FState
  cands : Array (Option String × String × Cand)
  /-- Inside a MathML `mi` with no `mathvariant`, whose single letter `math-auto` sets italic. -/
  autoItalic : Bool := false

/-- The analysis's fixed inputs. -/
structure Env where
  sheet : Sheet
  index : Index
  dyn : Array String

def subjectOf (tag : String) (attrs : Array (String × String)) : Subject :=
  { tag := tag.toLower
    classes := (((attrs.find? (·.1 == "class")).map (·.2)).getD "").splitOn " " |>.filter (!·.isEmpty)
      |>.toArray
    id := (attrs.find? (·.1 == "id")).map (·.2) }

/-- Each declaration that may set an element's font or its pseudo-elements', with the
pseudo-element it sets (`none` for the element's own text). -/
def candsFor (env : Env) (e : Subject) (up : List Subject) (attrs : Array (String × String)) :
    Array (Option String × String × Cand) := Id.run do
  let mut out : Array (Option String × String × Cand) := #[]
  for (p, v) in uaDecls e.tag do
    out := out.push (none, p, { value := v, key := keyOf false 0 0 0, sure := true })
  for (v, sure) in uaListStyles e.tag up do
    out := out.push (none, "list-style-type", { value := v, key := keyOf false 0 0 0, sure })
  for (p, v) in attrs do
    if presentational p then
      out := out.push (none, p, { value := v, key := keyOf false 1 0 0, sure := true })
  for (i, j) in env.index.candidates env.dyn e do
    let some r := env.sheet.rules[i]? | continue
    let some s := r.sels[j]? | continue
    match s.test env.dyn e up with
    | none => pure ()
    | some sure =>
      let pes : List (Option String) := match s.pe with
        | some "*" => [none, some "before", some "after", some "marker"]
        | some "first-line" | some "first-letter" => [none]
        | none | some "before" | some "after" | some "marker" => [s.pe]
        | some _ => [none, some "before", some "after", some "marker"]
      for pe in pes do
        for (p, v, imp) in r.decls do
          out := out.push (pe, p, { value := v, key := keyOf imp 2 s.spec r.order,
                                    sure := sure && !r.gated && pe == s.pe })
  if let some st := (attrs.find? (·.1 == "style")).map (·.2) then
    for (p, v, imp) in declsOf st do
      if fontProp p then
        out := out.push (none, p, { value := v, key := keyOf imp 3 0 0, sure := true })
  return out

def stateFor (env : Env) (parent : FState) (pe : Option String)
    (cands : Array (Option String × String × Cand)) : FState :=
  resolve env.sheet.vars parent fun p =>
    (cands.filter fun (q, p', _) => q == pe && p' == p).map (·.2.2)

/-- A box's first available font, the face holding U+0020 that sets its strut, `ex` and
underline (CSS Fonts 4 §5.4), asked as a request for the space. -/
private def addBox (reqs : Requests) (w : Want) : Requests :=
  reqs.insert w ((reqs.getD w {}).insert ' ')

/-- A space separator a shaper sets from the face's own U+0020 when the face lacks it. -/
private def spaceFallback (c : Char) : Bool :=
  let n := c.toNat
  n == 0xA0 || (0x2000 ≤ n && n ≤ 0x200A) || n == 0x202F || n == 0x205F || n == 0x3000

private def addChars (reqs : Requests) (w : Want) (s : String) : Requests :=
  let set := s.foldl (fun set c =>
    if inkless c then set
    else if spaceFallback c then set.insert ' '
    else (set.insert c).insert c.toUpper) (reqs.getD w {})
  reqs.insert w set

/-- The requests a tree's text makes, its elements' and their pseudo-elements'. -/
def walk (env : Env) : Walk Ctx Requests where
  text := fun ctx acc s =>
    let acc := addChars acc ctx.state.want s
    let t := s.trimAscii.toString
    match ctx.autoItalic, t.toList with
    | true, [c] => match mathItalic c with
      | some m => addChars acc ctx.state.want (String.singleton m)
      | none => acc
    | _, _ => acc
  inner := fun ctx tag attrs =>
    let e := subjectOf tag attrs
    let cands := candsFor env e ctx.up attrs
    some { up := e :: ctx.up, state := stateFor env ctx.state none cands, cands
           autoItalic := e.tag == "mi" && !(attrs.any (·.1 == "mathvariant")) }
  enter := fun ctx acc _ attrs _ =>
    match ctx.up with
    | [] => acc
    | e :: _ => Id.run do
      let mut acc := addBox acc ctx.state.want
      let listItem := e.tag == "li" || e.tag == "summary" ||
        ctx.cands.any fun (q, p, c) => q.isNone && p == "display" &&
          (c.value.splitOn "list-item").length > 1
      for pe in ["before", "after", "marker"] do
        let mine := ctx.cands.filter (·.1 == some pe)
        let (contents, unset) := winners ((mine.filter (·.2.1 == "content")).map (·.2.2))
        let normal (v : String) : Bool := v.trimAscii.toString == "normal"
        let shown := contents.filter fun v => v.trimAscii.toString != "none" && !normal v
        let chars := shown.foldl (fun s v => s ++ contentChars attrs v) ""
        -- a marker sets its list style's own marker only where `content` may stay `normal`
        let chars := if pe == "marker" && listItem && (unset || contents.any normal) then
          chars.append (match ctx.state.lists with
            | some vs => vs.foldl (fun s v => s ++ styleChars v) ""
            | none => markerChars)
          else chars
        unless chars.isEmpty && shown.isEmpty do
          let w := (stateFor env ctx.state (some pe) ctx.cands).want
          acc := addBox (addChars acc w chars) w
      return acc

/-- What a page loads its fonts' rules from: its style sheets, the custom properties its style
attributes declare, and whether it loads a sheet or a script from elsewhere. -/
def sources : Walk Unit (Array String × Array (String × String) × Bool) where
  style := fun _ (css, vs, o) s => (css.push s, vs, o)
  script := fun _ (css, vs, o) attrs _ => (css, vs, o || attrs.any (·.1 == "src"))
  enter := fun _ (css, vs, o) tag attrs _ =>
    let vs := match (attrs.find? (·.1 == "style")).map (·.2) with
      | some st => vs ++ ((declsOf st).filter (·.1.startsWith "--")).map fun (p, v, _) => (p, v)
      | none => vs
    (css, vs, o || (tag == "link" && attrs.any fun (k, v) =>
      k == "rel" && (v.splitOn "stylesheet").length > 1))

/-- The requests a page's text makes, read from its style sheets and its body; `none` when a
sheet or script the page loads from elsewhere may set any font. -/
public def requests (head body : Array Node) (dyn : Array String) : Option Requests := Id.run do
  let (css, vs, elsewhere) := sources.list () (#[], #[], false) (head ++ body).toList
  let sheet := css.foldl (fun sh t => sh.read t false) ({} : Sheet)
  if elsewhere || sheet.elsewhere then return none
  let vars := vs.foldl (fun m (p, v) => m.insert p ((m.getD p #[]).push v)) sheet.vars
  let sheet := { sheet with vars }
  let env : Env := { sheet, index := Index.of sheet.rules, dyn }
  let root := subjectOf "html" #[]
  let rootState := stateFor env
    { stacks := #[["serif"]], weights := some #[400], italics := some #[false]
      lists := some #["disc"] } none
    (candsFor env root [] #[])
  let bodyE := subjectOf "body" #[]
  let bodyCands := candsFor env bodyE [root] #[]
  let bodyState := stateFor env rootState none bodyCands
  return some ((walk env).list { up := [bodyE, root], state := bodyState, cands := bodyCands }
    (addBox (addBox {} rootState.want) bodyState.want) body.toList)

end LeanTex.Core.HtmlFaces
