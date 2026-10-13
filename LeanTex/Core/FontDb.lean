module

import Std.Data.HashSet

/-! Font selection over supplied face metadata; discovery and caching live in the CLI. -/

namespace LeanTex.Core.FontDb

/-- A face's classification, as metadata supplied by discovery or a caller. -/
public structure Face where
  path : String
  family : String
  subfamily : String
  bold : Bool
  italic : Bool
  fixedPitch : Bool
  /-- OS/2 usWeightClass: 400 is regular, 700 bold, 600 "Demi"/"Semibold". -/
  weight : Nat
  deriving Repr, Inhabited

/-- Which face of a family a piece of text wants. -/
public structure Variant where
  bold : Bool := false
  italic : Bool := false
  deriving Repr, BEq, Inhabited

/-- The standalone-font extensions recognized, lowercase. -/
public def fontExtensions : List String := ["ttf", "otf"]

/-- The font collection extensions recognized, lowercase. -/
public def collectionExtensions : List String := ["ttc", "otc"]

/-- A standalone-font extension, ignoring case, judged by the name alone. -/
public def hasFontExtension (p : String) : Bool :=
  match (p.splitOn ".").getLast? with
  | some ext => fontExtensions.contains ext.toLower
  | none => false

/-- A font collection's extension, ignoring case. -/
public def isCollectionFile (p : String) : Bool :=
  match (p.splitOn ".").getLast? with
  | some ext => collectionExtensions.contains ext.toLower
  | none => false

/-- The path a collection's face is known by: the file, `#`, and the face's index. -/
public def memberPath (file : String) (index : Nat) : String :=
  s!"{file}#{index}"

/-- The collection file and face index a `memberPath` names, or `none` for any other path. -/
public def splitMember (p : String) : Option (String × Nat) :=
  let parts := p.splitOn "#"
  if parts.length < 2 then none else
  let file := String.intercalate "#" parts.dropLast
  (parts.getLast?.bind String.toNat?).bind fun i =>
    if isCollectionFile file then some (file, i) else none

/-- The file a face's bytes are read from: a collection face's collection,
any other face's own path. -/
public def faceFile (p : String) : String :=
  ((splitMember p).map (·.1)).getD p

def norm (s : String) : String :=
  String.ofList ((s.toLower.toList).filter fun c => c.isAlphanum)

/-- Does `s` normalise to exactly `target`, without allocating the normalised string? -/
def normEq (s : String) (target : Array Char) : Bool :=
  let fin := s.foldl (init := some 0) fun i? c =>
    match i? with
    | none => none
    | some i =>
      let c := c.toLower
      if c.isAlphanum then
        if h : i < target.size then
          if target[i] == c then some (i + 1) else none
        else none
      else some i
  fin == some target.size

/-- Is `s` a canonical subfamily name, marking a family's plain face? -/
def canonicalSubfamily (s : String) : Bool :=
  ["regular", "bold", "italic", "oblique", "bolditalic", "boldoblique",
   "book", "normal"].contains (norm s)

def targetWeight (bold : Bool) : Nat := if bold then 700 else 400

def weightDist (target : Nat) (f : Face) : Nat :=
  max f.weight target - min f.weight target

/-- The face closest to `target`, the plain face winning a tie, then the earlier face. -/
public def pickWeighted (cands : Array Face) (target : Nat) : Option Face :=
  let better (a b : Face) : Bool :=
    let da := weightDist target a
    let db := weightDist target b
    if da != db then da < db
    else
      let ca := if canonicalSubfamily a.subfamily then 0 else 1
      let cb := if canonicalSubfamily b.subfamily then 0 else 1
      if ca != cb then ca < cb
      else a.subfamily.length < b.subfamily.length
  cands[0]?.map fun first =>
    cands.foldl (init := first) fun best c => if better c best then c else best

public theorem pickWeighted_total (cands : Array Face) (target : Nat)
    (h : 0 < cands.size) : (pickWeighted cands target).isSome := by
  unfold pickWeighted
  simp [h]

/-- The family a name denotes: itself, or a scanned font file name's family. -/
public def familyOf (faces : Array Face) (name : String) : String :=
  if hasFontExtension name then
    match faces.find? fun f => (f.path.splitOn "/").getLast? == some name with
    | some f => f.family
    | none => name
  else name

/-- Best face for a family name and variant, and whether the family offers what was asked; a
family-plus-subfamily name serves as that name's regular. -/
public def resolve (faces : Array Face) (family : String) (v : Variant) :
    Option (Face × Bool) :=
  let target := (norm (familyOf faces family)).toList.toArray
  let byFamily := faces.filter fun f => normEq f.family target
  let (inFamily, named) :=
    if byFamily.isEmpty then
      let targetItalic := target ++ "italic".toList.toArray
      (faces.filter fun f =>
        let key := f.family ++ f.subfamily
        normEq key target || normEq key targetItalic, true)
    else (byFamily, false)
  if inFamily.isEmpty then
    none
  else
    let want := if named then targetWeight false else targetWeight v.bold
    -- Italic is categorical: never substitute upright for italic silently.
    let matchingSlant := inFamily.filter fun f => f.italic == v.italic
    let pool := if matchingSlant.isEmpty then inFamily else matchingSlant
    match pickWeighted pool want with
    | none => none
    | some face =>
      let slantOk := face.italic == v.italic
      -- A named face is its name's regular, whatever its weight.
      let weightOk :=
        if named && !v.bold then true
        else if v.bold then face.weight ≥ 550 else face.weight ≤ 550
      some (face, slantOk && weightOk)

/-- The face a declared per-variant name denotes: a font file name is that
scanned file's own face; anything else resolves like a family or
family-plus-subfamily name. -/
public def resolveNamed (faces : Array Face) (name : String) : Option Face :=
  if hasFontExtension name then
    faces.find? fun f => (f.path.splitOn "/").getLast? == some name
  else
    (resolve faces name {}).map (·.1)

/-- The family stem and OS/2 weight a trailing weight word asks for; longer words match first. -/
public def nameWeight (name : String) : Option (String × Nat) :=
  let words : List (String × Nat) :=
    [("extralight", 200), ("ultralight", 200), ("semibold", 600),
     ("demibold", 600), ("extrabold", 800), ("ultrabold", 800),
     ("hairline", 100), ("medium", 500), ("light", 300), ("black", 900),
     ("heavy", 900), ("thin", 100), ("book", 400), ("demi", 600),
     ("bold", 700)]
  let low := name.toLower
  words.findSome? fun (w, k) =>
    if low.endsWith w && low.length > w.length then
      let stem := (name.dropEnd w.length).toString.trimAscii.toString
      let stem := if stem.endsWith "-" then
          (stem.dropEnd 1).toString.trimAscii.toString
        else stem
      if stem.isEmpty then none else some (stem, k)
    else none

/-- Nearest-weight resolution for a name asking a weight its family lacks; returns the face and
the weight asked. -/
public def resolveWeightName (faces : Array Face) (name : String) (v : Variant) :
    Option (Face × Nat) :=
  (nameWeight name).bind fun (fam, w) =>
    let target := (norm fam).toList.toArray
    let byFamily := faces.filter fun f => normEq f.family target
    let want := if v.bold then targetWeight true else w
    let matchingSlant := byFamily.filter fun f => f.italic == v.italic
    let pool := if matchingSlant.isEmpty then byFamily else matchingSlant
    (pickWeighted pool want).map fun face => (face, want)

/-- What a resolution substituted, when it did. -/
public inductive Substituted where
  | variant (msg : String)
  | weight (asked : String) (requested : Nat) (face : Face)

/-- The face for one slot variant and what substituted; a declared face wins, and `none` only
when the family has no face. -/
public def resolveVariant (faces : Array Face) (family : String) (declared : Option String)
    (v : Variant) : Option (Face × Option Substituted) :=
  let want :=
    if v.bold && v.italic then "bold italic"
    else if v.bold then "bold"
    else if v.italic then "italic"
    else "regular"
  match declared with
  | some name =>
    match resolveNamed faces name with
    | some face => some (face, none)
    | none =>
      match resolveWeightName faces name v with
      | some (face, req) =>
        some (face, if face.weight == req then none
          else some (.weight name req face))
      | none =>
        (resolve faces family v).map fun (face, _) =>
          (face, some (.variant s!"'{family}' declares '{name}' as its {want} face, \
            which is not installed; '{face.family} {face.subfamily}' substitutes"))
  | none =>
    match resolve faces family v with
    | some (face, satisfied) =>
      if satisfied then some (face, none)
      else some (face, some (.variant s!"'{family}' has no {want} face; \
        '{face.family} {face.subfamily}' substitutes"))
    | none =>
      -- A family name carrying a weight word answers at the base family's nearest weight.
      (resolveWeightName faces family v).map fun (face, req) =>
        (face, if face.weight == req then none
          else some (.weight family req face))

/-- `resolveVariant` on the weight axis: 400 and 700 resolve through it, any other weight by
nearest `usWeightClass` among the slant-matching faces. -/
public def resolveWeight (faces : Array Face) (family : String)
    (declared : Option String) (weight : Nat) (italic : Bool) :
    Option (Face × Option Substituted) :=
  if weight == 400 || weight == 700 then
    resolveVariant faces family declared { bold := weight == 700, italic }
  else
    let pick : Option (Face × Option Substituted) :=
      let target := (norm (familyOf faces family)).toList.toArray
      let byFamily := faces.filter fun f => normEq f.family target
      let matchingSlant := byFamily.filter fun f => f.italic == italic
      let pool := if matchingSlant.isEmpty then byFamily else matchingSlant
      (pickWeighted pool weight).map fun face =>
        (face, if face.weight == weight then none
          else some (.weight family weight face))
    match declared with
    | some name =>
      match resolveNamed faces name with
      | some face => some (face, none)
      | none => pick.map fun (face, _) =>
          (face, some (.variant s!"'{family}' declares '{name}' as its \
weight-{weight} face, which is not installed; \
'{face.family} {face.subfamily}' substitutes"))
    | none => pick

/-- The candidate order every scan-derived pick shares: family, upright first, weight nearest
regular, then subfamily and path. -/
public def faceLt (a b : Face) : Bool :=
  if norm a.family != norm b.family then norm a.family < norm b.family
  else if a.italic != b.italic then !a.italic && b.italic
  else
    let da := weightDist 400 a
    let db := weightDist 400 b
    if da != db then da < db
    else if a.subfamily != b.subfamily then a.subfamily < b.subfamily
    else a.path < b.path

/-- One fold step of `leastBy`: keep the lesser. -/
def leastStep (lt : Face → Face → Bool) (best : Option Face) (f : Face) :
    Option Face :=
  match best with
  | none => some f
  | some b => if lt f b then some f else some b

/-- The least face under `lt`, by one fold. -/
public def leastBy (lt : Face → Face → Bool) (xs : Array Face) : Option Face :=
  xs.toList.foldl (leastStep lt) none

theorem foldl_least (lt : Face → Face → Bool)
    (htrans : ∀ f g h, lt f g → lt g h → lt f h) :
    ∀ (l : List Face) (m0 : Face),
      (∀ f g, (f = m0 ∨ f ∈ l) → (g = m0 ∨ g ∈ l) → f = g ∨ lt f g ∨ lt g f) →
      ∃ m, List.foldl (leastStep lt) (some m0) l = some m ∧
        (m = m0 ∨ m ∈ l) ∧ ∀ f, (f = m0 ∨ f ∈ l) → f = m ∨ lt m f
  | [], m0, _ => ⟨m0, rfl, .inl rfl, fun f hf => by
      cases hf with
      | inl h => exact .inl h
      | inr h => cases h⟩
  | x :: rest, m0, htotal => by
    have lift : ∀ f, (f = x ∨ f ∈ rest) → (f = m0 ∨ f ∈ x :: rest) := fun f hf =>
      .inr (by cases hf with
        | inl h => exact h ▸ List.mem_cons_self
        | inr h => exact List.mem_cons_of_mem _ h)
    have liftM : ∀ f, (f = m0 ∨ f ∈ rest) → (f = m0 ∨ f ∈ x :: rest) := fun f hf =>
      hf.imp id (List.mem_cons_of_mem _)
    by_cases hx : lt x m0
    · obtain ⟨m, heq, hmem, hleast⟩ :=
        foldl_least lt htrans rest x
          (fun f g hf hg => htotal f g (lift f hf) (lift g hg))
      refine ⟨m, by simpa [leastStep, hx] using heq, lift m hmem, fun f hf => ?_⟩
      by_cases hfm : f = m
      · exact .inl hfm
      right
      cases hf with
      | inl hfm0 =>
        subst hfm0
        cases hleast x (.inl rfl) with
        | inl hxm => exact hxm ▸ hx
        | inr hmx => exact htrans m x f hmx hx
      | inr hfx =>
        cases List.mem_cons.mp hfx with
        | inl h =>
          cases hleast f (.inl h) with
          | inl h2 => exact absurd h2 hfm
          | inr h2 => exact h2
        | inr h =>
          cases hleast f (.inr h) with
          | inl h2 => exact absurd h2 hfm
          | inr h2 => exact h2
    · obtain ⟨m, heq, hmem, hleast⟩ :=
        foldl_least lt htrans rest m0
          (fun f g hf hg => htotal f g (liftM f hf) (liftM g hg))
      refine ⟨m, by simpa [leastStep, hx] using heq, liftM m hmem, fun f hf => ?_⟩
      by_cases hfm : f = m
      · exact .inl hfm
      right
      cases hf with
      | inl hfm0 =>
        cases hleast f (.inl hfm0) with
        | inl h2 => exact absurd h2 hfm
        | inr h2 => exact h2
      | inr hfx =>
        cases List.mem_cons.mp hfx with
        | inl hfx =>
          subst hfx
          cases htotal f m0 (.inr List.mem_cons_self) (.inl rfl) with
          | inl hfm0 =>
            cases hleast f (.inl hfm0) with
            | inl h2 => exact absurd h2 hfm
            | inr h2 => exact h2
          | inr hor =>
            cases hor with
            | inl hlt => exact absurd hlt hx
            | inr hgt =>
              cases hleast m0 (.inl rfl) with
              | inl hm0m => exact hm0m ▸ hgt
              | inr hmm0 => exact htrans m m0 f hmm0 hgt
        | inr hfr =>
          cases hleast f (.inr hfr) with
          | inl h2 => exact absurd h2 hfm
          | inr h2 => exact h2

theorem leastBy_spec (lt : Face → Face → Bool)
    (htrans : ∀ f g h, lt f g → lt g h → lt f h) (xs : Array Face)
    (htotal : ∀ f g, f ∈ xs → g ∈ xs → f = g ∨ lt f g ∨ lt g f) :
    (xs.toList = [] ∧ leastBy lt xs = none) ∨
      ∃ m, leastBy lt xs = some m ∧ m ∈ xs ∧
        ∀ f, f ∈ xs → f = m ∨ lt m f := by
  unfold leastBy
  match h : xs.toList with
  | [] => exact .inl ⟨rfl, rfl⟩
  | x :: rest =>
    have hxs : ∀ f, (f = x ∨ f ∈ rest) → f ∈ xs := fun f hf => by
      rw [← Array.mem_toList_iff, h]
      cases hf with
      | inl h2 => exact h2 ▸ List.mem_cons_self
      | inr h2 => exact List.mem_cons_of_mem _ h2
    obtain ⟨m, heq, hmem, hleast⟩ :=
      foldl_least lt htrans rest x
        (fun f g hf hg => htotal f g (hxs f hf) (hxs g hg))
    refine .inr ⟨m, ?_, hxs m hmem, fun f hf => ?_⟩
    · simpa [leastStep] using heq
    · have : f = x ∨ f ∈ rest := by
        have := (Array.mem_toList_iff).mpr hf
        rw [h] at this
        exact List.mem_cons.mp this
      exact hleast f this

public theorem leastBy_set_eq (lt : Face → Face → Bool)
    (htrans : ∀ f g h, lt f g → lt g h → lt f h)
    (hasym : ∀ f g, lt f g → ¬ lt g f)
    (a b : Array Face) (hmem : ∀ f, f ∈ a ↔ f ∈ b)
    (htotal : ∀ f g, f ∈ a → g ∈ a → f = g ∨ lt f g ∨ lt g f) :
    leastBy lt a = leastBy lt b := by
  have htotalB : ∀ f g, f ∈ b → g ∈ b → f = g ∨ lt f g ∨ lt g f := fun f g hf hg =>
    htotal f g ((hmem f).mpr hf) ((hmem g).mpr hg)
  cases leastBy_spec lt htrans a htotal with
  | inl ha =>
    cases leastBy_spec lt htrans b htotalB with
    | inl hb => rw [ha.2, hb.2]
    | inr hb =>
      obtain ⟨m, _, hmb, _⟩ := hb
      have : m ∈ a.toList := Array.mem_toList_iff.mpr ((hmem m).mpr hmb)
      rw [ha.1] at this
      cases this
  | inr ha =>
    obtain ⟨ma, heqa, hma, hlea⟩ := ha
    cases leastBy_spec lt htrans b htotalB with
    | inl hb =>
      have : ma ∈ b.toList := Array.mem_toList_iff.mpr ((hmem ma).mp hma)
      rw [hb.1] at this
      cases this
    | inr hb =>
      obtain ⟨mb, heqb, hmb, hleb⟩ := hb
      rw [heqa, heqb]
      by_cases hab : ma = mb
      · rw [hab]
      · cases hlea mb ((hmem mb).mpr hmb) with
        | inl h2 => exact absurd h2.symm hab
        | inr h2 =>
          cases hleb ma ((hmem ma).mp hma) with
          | inl h3 => exact absurd h3.symm (fun h => hab h.symm)
          | inr h3 => exact absurd h2 (hasym mb ma h3)

/-- One designed pairing of a text family with its companion face, with source and licence. -/
public structure Pairing where
  body : String
  companion : String
  source : String
  license : String
  /-- The text family's and the companion's measured x-heights, in thousandths of an em. -/
  xHeights : Option (Nat × Nat) := none
  deriving Repr, Inhabited

/-- The designed math companions, one sourced row per body family name. -/
public def mathCompanions : Array Pairing := #[
  { body := "Palatino", companion := "TeX Gyre Pagella Math"
    source := "gust.org.pl/projects/e-foundry/tg-math", license := "GUST Font License" },
  { body := "Palatino Linotype", companion := "TeX Gyre Pagella Math"
    source := "gust.org.pl/projects/e-foundry/tg-math", license := "GUST Font License" },
  { body := "URW Palladio L", companion := "TeX Gyre Pagella Math"
    source := "gust.org.pl/projects/e-foundry/tg-math", license := "GUST Font License" },
  { body := "P052", companion := "TeX Gyre Pagella Math"
    source := "gust.org.pl/projects/e-foundry/tg-math", license := "GUST Font License" },
  { body := "TeX Gyre Pagella", companion := "TeX Gyre Pagella Math"
    source := "gust.org.pl/projects/e-foundry/tg-math", license := "GUST Font License" },
  { body := "Times", companion := "TeX Gyre Termes Math"
    source := "gust.org.pl/projects/e-foundry/tg-math", license := "GUST Font License" },
  { body := "Times New Roman", companion := "TeX Gyre Termes Math"
    source := "gust.org.pl/projects/e-foundry/tg-math", license := "GUST Font License" },
  { body := "Nimbus Roman", companion := "TeX Gyre Termes Math"
    source := "gust.org.pl/projects/e-foundry/tg-math", license := "GUST Font License" },
  { body := "Nimbus Roman No9 L", companion := "TeX Gyre Termes Math"
    source := "gust.org.pl/projects/e-foundry/tg-math", license := "GUST Font License" },
  { body := "Liberation Serif", companion := "TeX Gyre Termes Math"
    source := "gust.org.pl/projects/e-foundry/tg-math", license := "GUST Font License" },
  { body := "TeX Gyre Termes", companion := "TeX Gyre Termes Math"
    source := "gust.org.pl/projects/e-foundry/tg-math", license := "GUST Font License" },
  { body := "STIX Two Text", companion := "STIX Two Math"
    source := "stixfonts.org", license := "SIL Open Font License" },
  { body := "Bookman", companion := "TeX Gyre Bonum Math"
    source := "gust.org.pl/projects/e-foundry/tg-math", license := "GUST Font License" },
  { body := "URW Bookman", companion := "TeX Gyre Bonum Math"
    source := "gust.org.pl/projects/e-foundry/tg-math", license := "GUST Font License" },
  { body := "Bookman Old Style", companion := "TeX Gyre Bonum Math"
    source := "gust.org.pl/projects/e-foundry/tg-math", license := "GUST Font License" },
  { body := "TeX Gyre Bonum", companion := "TeX Gyre Bonum Math"
    source := "gust.org.pl/projects/e-foundry/tg-math", license := "GUST Font License" },
  { body := "Century Schoolbook", companion := "TeX Gyre Schola Math"
    source := "gust.org.pl/projects/e-foundry/tg-math", license := "GUST Font License" },
  { body := "Century Schoolbook L", companion := "TeX Gyre Schola Math"
    source := "gust.org.pl/projects/e-foundry/tg-math", license := "GUST Font License" },
  { body := "C059", companion := "TeX Gyre Schola Math"
    source := "gust.org.pl/projects/e-foundry/tg-math", license := "GUST Font License" },
  { body := "New Century Schoolbook", companion := "TeX Gyre Schola Math"
    source := "gust.org.pl/projects/e-foundry/tg-math", license := "GUST Font License" },
  { body := "TeX Gyre Schola", companion := "TeX Gyre Schola Math"
    source := "gust.org.pl/projects/e-foundry/tg-math", license := "GUST Font License" },
  { body := "DejaVu Serif", companion := "TeX Gyre DejaVu Math"
    source := "gust.org.pl/projects/e-foundry/tg-math", license := "GUST Font License" },
  { body := "DejaVu Sans", companion := "TeX Gyre DejaVu Math"
    source := "gust.org.pl/projects/e-foundry/tg-math", license := "GUST Font License" },
  { body := "Libertinus Serif", companion := "Libertinus Math"
    source := "ctan.org/pkg/libertinus", license := "SIL Open Font License" },
  { body := "EB Garamond", companion := "Garamond-Math"
    source := "ctan.org/pkg/garamond-math", license := "SIL Open Font License" },
  { body := "Utopia", companion := "Erewhon Math"
    source := "ctan.org/pkg/erewhon-math", license := "SIL Open Font License" },
  { body := "Erewhon", companion := "Erewhon Math"
    source := "ctan.org/pkg/erewhon-math", license := "SIL Open Font License" },
  { body := "Fira Sans", companion := "Fira Math"
    source := "ctan.org/pkg/firamath", license := "SIL Open Font License" },
  { body := "Latin Modern Roman", companion := "Latin Modern Math"
    source := "gust.org.pl/projects/e-foundry/lm-math", license := "GUST Font License" },
  { body := "CMU Serif", companion := "Latin Modern Math"
    source := "gust.org.pl/projects/e-foundry/lm-math", license := "GUST Font License" }]

/-- The row of a pairing table that names `body`. -/
public def companionRow (table : Array Pairing) (body : String) : Option Pairing :=
  table.find? fun p => normEq body ((norm p.body).toList.toArray)

/-- The designed math companion of `body`: its row and the least supplied face of it. -/
public def pickCompanion (faces : Array Face) (body : String) : Option (Pairing × Face) := do
  let row ← companionRow mathCompanions body
  let face ← leastBy faceLt (faces.filter fun f =>
    normEq f.family ((norm row.companion).toList.toArray))
  return (row, face)

public theorem pickCompanion_set_eq (a b : Array Face) (body : String)
    (hmem : ∀ f, f ∈ a ↔ f ∈ b)
    (htrans : ∀ f g h, faceLt f g → faceLt g h → faceLt f h)
    (hasym : ∀ f g, faceLt f g → ¬ faceLt g f)
    (htotal : ∀ f g, f ∈ a → g ∈ a → f = g ∨ faceLt f g ∨ faceLt g f) :
    pickCompanion a body = pickCompanion b body := by
  unfold pickCompanion
  cases companionRow mathCompanions body with
  | none => rfl
  | some row =>
    have heq := leastBy_set_eq faceLt htrans hasym
      (a.filter fun f => normEq f.family ((norm row.companion).toList.toArray))
      (b.filter fun f => normEq f.family ((norm row.companion).toList.toArray))
      (fun f => by
        simp only [Array.mem_filter]
        exact and_congr_left fun _ => hmem f)
      (fun f g hf hg =>
        htotal f g (Array.mem_filter.mp hf).1 (Array.mem_filter.mp hg).1)
    show (leastBy faceLt (Array.filter (fun f => normEq f.family (norm row.companion).toList.toArray) a)).bind
        (fun face => some (row, face)) =
      (leastBy faceLt (Array.filter (fun f => normEq f.family (norm row.companion).toList.toArray) b)).bind
        (fun face => some (row, face))
    rw [heq]

/-- Installed families resembling a name, by a shared word or an edit or two; at most eight,
closest first. -/
public def nearest (families : Array String) (wanted : String) : Array String :=
  let words (s : String) : List String :=
    (s.toLower.splitOn " ").filter fun w => !w.isEmpty && w.length > 1
  let want := words wanted
  let score (fam : String) : Nat :=
    let got := words fam
    let shared := (want.filter got.contains).length
    let prefixHit := match want.head?, got.head? with
      | some a, some b => a.startsWith b || b.startsWith a
      | _, _ => false
    shared * 2 + (if prefixHit then 1 else 0)
  let scored := families.filterMap fun f =>
    let sc := score f
    if sc > 0 then some (sc, f) else none
  let sorted := scored.qsort fun a b => a.1 > b.1 || (a.1 == b.1 && a.2 < b.2)
  (sorted.extract 0 8).map (·.2)

/-- Family names present, sorted, for diagnostics. -/
public def families (faces : Array Face) : Array String := Id.run do
  let mut keys : Std.HashSet String := {}
  let mut out : Array String := #[]
  for f in faces do
    let k := norm f.family
    unless keys.contains k do
      keys := keys.insert k
      out := out.push f.family
  return out.qsort (· < ·)

/-- Families tried, in order, when a document declares no `\fonts`. -/
public def defaultFamilies : List String :=
  ["DejaVu Sans", "Helvetica Neue", "Helvetica", "Arial", "Liberation Sans",
   "Nimbus Sans", "Inter"]

/-- The first preferred family that resolves, else the first sans, else any face's family. -/
public def defaultFamily (faces : Array Face) : Option String :=
  match defaultFamilies.find? fun n => (resolve faces n {}).isSome with
  | some n => some n
  | none =>
    match faces.find? fun f => ((norm f.family).splitOn "sans").length > 1 with
    | some f => some f.family
    | none => faces[0]?.map (·.family)

/-- The designed typewriter companions, one sourced row per text family whose project ships
one. -/
public def monoCompanions : Array Pairing := #[
  { body := "DejaVu Sans", companion := "DejaVu Sans Mono"
    source := "github.com/dejavu-fonts/dejavu-fonts", license := "DejaVu fonts licence"
    xHeights := some (547, 547) },
  { body := "DejaVu Serif", companion := "DejaVu Sans Mono"
    source := "github.com/dejavu-fonts/dejavu-fonts", license := "DejaVu fonts licence"
    xHeights := some (519, 547) },
  { body := "Fira Sans", companion := "Fira Mono"
    source := "github.com/mozilla/Fira", license := "SIL Open Font License"
    xHeights := some (527, 527) },
  { body := "Source Sans Pro", companion := "Source Code Pro"
    source := "github.com/adobe-fonts/source-code-pro", license := "SIL Open Font License"
    xHeights := some (486, 486) },
  { body := "Source Serif Pro", companion := "Source Code Pro"
    source := "github.com/adobe-fonts/source-serif", license := "SIL Open Font License"
    xHeights := some (475, 486) },
  { body := "IBM Plex Sans", companion := "IBM Plex Mono"
    source := "github.com/IBM/plex", license := "SIL Open Font License"
    xHeights := some (516, 516) },
  { body := "IBM Plex Serif", companion := "IBM Plex Mono"
    source := "github.com/IBM/plex", license := "SIL Open Font License"
    xHeights := some (516, 516) },
  { body := "IBM Plex Sans Condensed", companion := "IBM Plex Mono"
    source := "github.com/IBM/plex", license := "SIL Open Font License"
    xHeights := some (516, 516) },
  { body := "Noto Sans", companion := "Noto Sans Mono"
    source := "github.com/notofonts/latin-greek-cyrillic", license := "SIL Open Font License"
    xHeights := some (536, 536) },
  { body := "Noto Serif", companion := "Noto Sans Mono"
    source := "github.com/notofonts/latin-greek-cyrillic", license := "SIL Open Font License"
    xHeights := some (536, 536) },
  { body := "Helvetica", companion := "Courier"
    source := "PostScript core set; psnfss2e", license := "vendor licence" },
  { body := "Arial", companion := "Courier New"
    source := "Microsoft core fonts for the web", license := "vendor licence" },
  { body := "Liberation Sans", companion := "Liberation Mono"
    source := "github.com/liberationfonts/liberation-fonts", license := "SIL Open Font License" },
  { body := "Nimbus Sans", companion := "Nimbus Mono PS"
    source := "github.com/ArtifexSoftware/urw-base35-fonts", license := "AGPL with font exception"
    xHeights := some (524, 419) }]

/-- Typewriter families whose project ships no italic face, per its sources
(github.com/notofonts/latin-greek-cyrillic holds upright masters only). -/
public def monoUprightOnly : List String := ["Noto Sans Mono"]

/-- The default text families no project ships a designed typewriter face beside. -/
public def monoUnpaired : List String := ["Helvetica Neue", "Inter"]

/-- The four corners NFSS names for every family — regular, bold, italic,
bold italic — at the weights the driver's assembly asks them at. -/
public def corners : List (Nat × Bool) := [(400, false), (700, false), (400, true), (700, true)]

/-- The upright corners, regular and bold: what a typewriter default must
serve with its own faces. -/
public def uprightCorners : List (Nat × Bool) := [(400, false), (700, false)]

/-- The italic corners, regular and bold: a typewriter default serves both or neither. -/
public def italicCorners : List (Nat × Bool) := [(400, true), (700, true)]

/-- Does the assembly's own resolver (`resolveWeight`, with nothing
declared) answer this corner of `family` with the family's own face,
unsubstituted and fixed-pitch? -/
public def cornerFixed (faces : Array Face) (family : String) (c : Nat × Bool) : Bool :=
  match resolveWeight faces family none c.1 c.2 with
  | some (f, none) => f.fixedPitch
  | _ => false

private theorem cornerFixed_fixedPitch (faces : Array Face) (family : String) (c : Nat × Bool)
    (h : cornerFixed faces family c = true) :
    ∃ f, resolveWeight faces family none c.1 c.2 = some (f, none) ∧ f.fixedPitch = true := by
  unfold cornerFixed at h
  split at h
  · rename_i f heq
    exact ⟨f, heq, h⟩
  · exact absurd h Bool.false_ne_true

/-- Does the same resolver answer this corner with an upright fixed-pitch face? -/
public def cornerUpright (faces : Array Face) (family : String) (c : Nat × Bool) : Bool :=
  match resolveWeight faces family none c.1 c.2 with
  | some (f, _) => !f.italic && f.fixedPitch
  | none => false

private theorem cornerUpright_upright (faces : Array Face) (family : String) (c : Nat × Bool)
    (h : cornerUpright faces family c = true) :
    ∃ f s, resolveWeight faces family none c.1 c.2 = some (f, s) ∧ f.italic = false ∧
      f.fixedPitch = true := by
  unfold cornerUpright at h
  split at h
  · rename_i f s heq
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ⟨f, s, heq, h.1, h.2⟩
  · exact absurd h Bool.false_ne_true

/-- Does the scan serve `family` as a typewriter family, its italics whole or upright? -/
public def servesMono (faces : Array Face) (family : String) : Bool :=
  uprightCorners.all (cornerFixed faces family) &&
    (italicCorners.all (cornerFixed faces family) || italicCorners.all (cornerUpright faces family))

/-- What a typewriter default serves: fixed-pitch faces of its own, unsubstituted, its italics
whole or upright. -/
public def MonoServed (faces : Array Face) (family : String) : Prop :=
  (∀ c ∈ uprightCorners, ∃ f, resolveWeight faces family none c.1 c.2 = some (f, none) ∧
      f.fixedPitch = true) ∧
    ((∀ c ∈ italicCorners, ∃ f, resolveWeight faces family none c.1 c.2 = some (f, none) ∧
        f.fixedPitch = true) ∨
      (∀ c ∈ italicCorners, ∃ f s, resolveWeight faces family none c.1 c.2 = some (f, s) ∧
        f.italic = false ∧ f.fixedPitch = true))

public theorem servesMono_contract (faces : Array Face) (family : String)
    (h : servesMono faces family = true) : MonoServed faces family := by
  unfold servesMono at h
  simp only [Bool.and_eq_true, Bool.or_eq_true] at h
  obtain ⟨hu, hi⟩ := h
  refine ⟨fun c hc => cornerFixed_fixedPitch faces family c (List.all_eq_true.mp hu c hc), ?_⟩
  rcases hi with hown | hup
  · exact Or.inl fun c hc => cornerFixed_fixedPitch faces family c (List.all_eq_true.mp hown c hc)
  · exact Or.inr fun c hc => cornerUpright_upright faces family c (List.all_eq_true.mp hup c hc)

/-- The text family's designed typewriter companion, when the scan serves it. -/
public def monoCompanion (faces : Array Face) (text : String) : Option String :=
  (companionRow monoCompanions text).bind fun row =>
    if servesMono faces row.companion then some row.companion else none

public theorem monoCompanion_contract (faces : Array Face) (text family : String)
    (h : monoCompanion faces text = some family) : MonoServed faces family := by
  unfold monoCompanion at h
  rcases Option.bind_eq_some_iff.mp h with ⟨row, _, hrow⟩
  split at hrow
  · rename_i hs
    cases hrow
    exact servesMono_contract faces _ hs
  · cases hrow

public theorem monoCompanion_mem (faces : Array Face) (text family : String)
    (h : monoCompanion faces text = some family) :
    ∃ row, companionRow monoCompanions text = some row ∧ row.companion = family := by
  unfold monoCompanion at h
  rcases Option.bind_eq_some_iff.mp h with ⟨row, hr, hrow⟩
  split at hrow
  · cases hrow
    exact ⟨row, hr, rfl⟩
  · cases hrow

/-- The platform monospace families an undeclared typewriter slot takes, in order. -/
public def monoDefaults : List String :=
  ["SF Mono", "Menlo", "DejaVu Sans Mono", "Liberation Mono"]

/-- The first platform monospace (`monoDefaults`) the scan serves as a
typewriter family (`servesMono`). -/
public def monoDefault (faces : Array Face) : Option String :=
  monoDefaults.find? (servesMono faces)

/-- An undeclared typewriter slot's family: the designed companion, else the first platform
monospace the scan serves. -/
public def monoFor (faces : Array Face) (text : Option String) : Option String :=
  (text.bind (monoCompanion faces ·)).orElse fun _ => monoDefault faces

public theorem monoDefault_contract (faces : Array Face) (family : String)
    (h : monoDefault faces = some family) : MonoServed faces family :=
  servesMono_contract faces family (List.find?_some h)

public theorem monoDefault_mem (faces : Array Face) (family : String)
    (h : monoDefault faces = some family) :
    family ∈ monoDefaults ∧ ∃ before after, monoDefaults = before ++ family :: after ∧
      ∀ g ∈ before, servesMono faces g = false := by
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  obtain ⟨before, after, hsplit, hbefore⟩ := List.find?_eq_some_iff_append.mp h |>.2
  exact ⟨before, after, hsplit, fun g hg => by simpa using hbefore g hg⟩

public theorem monoFor_contract (faces : Array Face) (text : Option String) (family : String)
    (h : monoFor faces text = some family) : MonoServed faces family := by
  unfold monoFor at h
  generalize hc : text.bind (monoCompanion faces ·) = pick at h
  match pick, hc, h with
  | some fam, hc, h =>
    have hf : fam = family := by simpa [Option.orElse] using h
    subst hf
    obtain ⟨t, _, ht⟩ := Option.bind_eq_some_iff.mp hc
    exact monoCompanion_contract faces t fam ht
  | none, _, h =>
    exact monoDefault_contract faces family (by simpa [Option.orElse] using h)

/-- The family lualatex's typewriter shapes are filed under. -/
public def latinModernMono : String := "Latin Modern Mono"

/-- lualatex's own typewriter shapes by corner file, as measured under lualatex; pending work:
the regular upright is the 10-point design at every size where lualatex takes LMMono8, 9 or 12 by
size, `\textsl` sets in the italic and `\textsc` in scaled capitals. -/
public def latinModernMonoFaces : List ((Nat × Bool) × String) :=
  [((400, false), "lmmono10-regular.otf"), ((700, false), "lmmonolt10-bold.otf"),
   ((400, true), "lmmono10-italic.otf"), ((700, true), "lmmonolt10-boldoblique.otf")]

/-- lualatex's shapes with each italic corner set in its upright's file. -/
public def latinModernMonoUpright : List ((Nat × Bool) × String) :=
  [((400, false), "lmmono10-regular.otf"), ((700, false), "lmmonolt10-bold.otf"),
   ((400, true), "lmmono10-regular.otf"), ((700, true), "lmmonolt10-bold.otf")]

/-- Does the resolver answer a corner declared by its file with that file's fixed-pitch face? -/
public def fileFixed (faces : Array Face) (c : (Nat × Bool) × String) : Bool :=
  match resolveWeight faces latinModernMono (some c.2) c.1.1 c.1.2 with
  | some (f, none) => f.fixedPitch
  | _ => false

/-- lualatex's shapes as the scan serves them: all four files, the upright two, or none. -/
public def latinModernMonoServed (faces : Array Face) :
    Option (List ((Nat × Bool) × String)) :=
  if latinModernMonoFaces.all (fileFixed faces) then some latinModernMonoFaces
  else if latinModernMonoUpright.all (fileFixed faces) &&
      (latinModernMonoFaces.filter (·.1.2)).all fun c => (resolveNamed faces c.2).isNone then
    some latinModernMonoUpright
  else none

private theorem latinModernMonoFaces_cover :
    ∀ k ∈ corners, ∃ c ∈ latinModernMonoFaces, c.1 = k := by decide

private theorem latinModernMonoUpright_cover :
    ∀ k ∈ corners, ∃ c ∈ latinModernMonoUpright, c.1 = k := by decide

public theorem latinModernMono_contract (faces : Array Face)
    (files : List ((Nat × Bool) × String)) (h : latinModernMonoServed faces = some files) :
    (∀ k ∈ corners, ∃ c ∈ files, c.1 = k) ∧
    ∀ c ∈ files, ∃ f, resolveWeight faces latinModernMono (some c.2) c.1.1 c.1.2 = some (f, none) ∧
      f.fixedPitch = true := by
  have fixed : ∀ c, fileFixed faces c = true →
      ∃ f, resolveWeight faces latinModernMono (some c.2) c.1.1 c.1.2 = some (f, none) ∧
        f.fixedPitch = true := by
    intro c hc
    unfold fileFixed at hc
    split at hc
    · rename_i f heq
      exact ⟨f, heq, hc⟩
    · exact absurd hc Bool.false_ne_true
  unfold latinModernMonoServed at h
  split at h
  · rename_i hall
    cases h
    exact ⟨latinModernMonoFaces_cover, fun c hc => fixed c (List.all_eq_true.mp hall c hc)⟩
  · split at h
    · rename_i hup
      cases h
      simp only [Bool.and_eq_true] at hup
      exact ⟨latinModernMonoUpright_cover, fun c hc => fixed c (List.all_eq_true.mp hup.1 c hc)⟩
    · cases h

/-- Latin Modern Mono's x-height in thousandths of an em, measured from lmmono10-regular.otf. -/
public def latinModernMonoXHeight : Nat := 431

/-- How far, in percent of the text's x-height, a companion's may stand and still lead: every
measured companion nearer than Latin Modern Mono stands within 5.4%, Latin Modern Mono 9 to 21%
below. -/
public def companionXHeightBound : Nat := 6

private def gapOf (a b : Nat) : Nat := if a ≥ b then a - b else b - a

/-- Does a declared text face's companion lead lualatex's shapes: its x-height nearer the text's
than Latin Modern Mono's, and within `companionXHeightBound`? -/
public def companionLeads (row : Pairing) : Bool :=
  match row.xHeights with
  | some (body, comp) =>
    0 < body && gapOf comp body < gapOf latinModernMonoXHeight body &&
      gapOf comp body * 100 ≤ companionXHeightBound * body
  | none => false

/-- What fills an undeclared typewriter slot: a family, and per-corner files where needed. -/
public structure MonoPick where
  family : String
  faces : List ((Nat × Bool) × String) := []
  deriving Repr, BEq

/-- lualatex's shapes as a pick, for a tex document. -/
private def lmPick (tex : Bool) (faces : Array Face) : Option MonoPick :=
  if tex then (latinModernMonoServed faces).map fun files => { family := latinModernMono, faces := files }
  else none

/-- The family `monoFor` answers, as a pick. -/
private def listedPick (faces : Array Face) (text : Option String) : Option MonoPick :=
  (monoFor faces text).map fun family => { family }

/-- The family the pool reports for a text face as a document names it. -/
public def textFamilyOf (faces : Array Face) (text : String) : String :=
  match resolveWeight faces text none 400 false with
  | some (f, _) => f.family
  | none => text

/-- The text family's companion as a pick, where it leads and the pool serves it. -/
private def leadPick (faces : Array Face) (text : Option String) : Option MonoPick :=
  text.bind fun t => (companionRow monoCompanions t).bind fun row =>
    -- premise: companionDepartureChecks — a row leads only nearer and inside the bound
    if companionLeads row && servesMono faces row.companion then some { family := row.companion }
    else none

/-- The typewriter default over one pool: a declared text family's leading companion, then
lualatex's shapes for tex, then `monoFor`'s family, which an undeclared one tries first. -/
public def monoPick (tex declared : Bool) (faces : Array Face) (text : Option String) :
    Option MonoPick :=
  let text := text.map (textFamilyOf faces)
  if declared then
    ((leadPick faces text).orElse fun _ => lmPick tex faces).orElse fun _ => listedPick faces text
  else (listedPick faces text).orElse fun _ => lmPick tex faces

private theorem orElse_some {α : Type} {o : Option α} {f : Unit → Option α} {a : α}
    (h : o.orElse f = some a) : o = some a ∨ f () = some a := by
  cases o with
  | some x => exact Or.inl (by simpa [Option.orElse] using h)
  | none => exact Or.inr (by simpa [Option.orElse] using h)

public theorem monoPick_contract (tex declared : Bool) (faces : Array Face)
    (text : Option String) (p : MonoPick) (h : monoPick tex declared faces text = some p) :
    (p.family = latinModernMono ∧ (∀ k ∈ corners, ∃ c ∈ p.faces, c.1 = k) ∧ ∀ c ∈ p.faces, ∃ f,
        resolveWeight faces p.family (some c.2) c.1.1 c.1.2 = some (f, none) ∧ f.fixedPitch = true) ∨
      (p.faces = [] ∧ MonoServed faces p.family) := by
  have lm : lmPick tex faces = some p → p.family = latinModernMono ∧
      (∀ k ∈ corners, ∃ c ∈ p.faces, c.1 = k) ∧ ∀ c ∈ p.faces, ∃ f,
      resolveWeight faces p.family (some c.2) c.1.1 c.1.2 = some (f, none) ∧
        f.fixedPitch = true := by
    intro hp
    unfold lmPick at hp
    split at hp
    · obtain ⟨files, hf, rfl⟩ := Option.map_eq_some_iff.mp hp
      exact ⟨rfl, latinModernMono_contract faces files hf⟩
    · cases hp
  have listed : ∀ text, listedPick faces text = some p → p.faces = [] ∧
      MonoServed faces p.family := by
    intro text hp
    unfold listedPick at hp
    obtain ⟨family, hm, rfl⟩ := Option.map_eq_some_iff.mp hp
    exact ⟨rfl, monoFor_contract faces text family hm⟩
  have lead : ∀ text, leadPick faces text = some p → p.faces = [] ∧
      MonoServed faces p.family := by
    intro text hp
    unfold leadPick at hp
    obtain ⟨t, _, ht⟩ := Option.bind_eq_some_iff.mp hp
    obtain ⟨row, _, hrow⟩ := Option.bind_eq_some_iff.mp ht
    split at hrow
    · rename_i hs
      cases hrow
      simp only [Bool.and_eq_true] at hs
      exact ⟨rfl, servesMono_contract faces row.companion hs.2⟩
    · cases hrow
  unfold monoPick at h
  split at h
  · rcases orElse_some h with hp | hp
    · rcases orElse_some hp with hl | hl
      · exact Or.inr (lead _ hl)
      · exact Or.inl (lm hl)
    · exact Or.inr (listed _ hp)
  · rcases orElse_some h with hp | hp
    · exact Or.inr (listed _ hp)
    · exact Or.inl (lm hp)

end LeanTex.Core.FontDb
