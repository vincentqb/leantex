module

import Std.Data.HashSet

/-! Pure selection over supplied font metadata. Discovery and cache policy
live in the CLI; this module never opens the paths it ranks. -/

namespace LeanTex.Core.FontDb

/-- A face's classification, supplied by discovery or a caller. Its fields
are metadata, not evidence that the path is readable, the bytes still match,
or any glyph paints ink. Selection contracts quantify over these values. -/
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

/-- A supported standalone-font extension, ignoring case. This recognizes
names used by selection and discovery; it does not inspect any bytes. Font
collections (`.ttc`, `.dfont`) are not supported. -/
public def hasFontExtension (p : String) : Bool :=
  let ext := (p.splitOn ".").getLast? |>.map String.toLower
  ext == some "ttf" || ext == some "otf"

def norm (s : String) : String :=
  String.ofList ((s.toLower.toList).filter fun c => c.isAlphanum)

/-- Does `s` normalise to exactly `target` (itself already normalised, as
chars)? The same answer as `norm s == String.ofList target.toList` without
the four intermediate structures `norm` allocates per name: `resolve` asks
this of every installed face, and a build resolves twelve slot–variant
pairs, so on a 2856-face host the `norm` form was ~15 ms of every build —
most of what resolution cost. -/
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

/-- Canonical subfamily names. A face whose subfamily is exactly one of these
is the family's plain face; anything else carries an extra descriptor
("Condensed Bold", "ExtraLight"), which must not win over the plain one —
condensed faces commonly share the typographic family name. -/
def canonicalSubfamily (s : String) : Bool :=
  ["regular", "bold", "italic", "oblique", "bolditalic", "boldoblique",
   "book", "normal"].contains (norm s)

/-- Target weight for the requested variant. Real families ship a weight
axis, so "bold" means "as close to 700 as this family gets". -/
def targetWeight (bold : Bool) : Nat := if bold then 700 else 400

/-- Distance from a target weight on the family's weight axis: the one
spelling of the fact both scan orderings rank by (`pickWeighted` toward
the requested variant's target, `faceLt` toward regular). -/
def weightDist (target : Nat) (f : Face) : Nat :=
  max f.weight target - min f.weight target

/-- Rank candidates for a target weight: closest weight wins; ties prefer the
plain face over one carrying an extra descriptor ("Condensed Bold"), because
condensed faces commonly share the typographic family name. A remaining tie
(the same family installed twice, e.g. a system copy and a TeX Live copy)
goes to the earlier supplied face — discovery preserves root order, so
the first search directory that holds a family owns it.
A fold-min, not a sort: only the best face is wanted, an earlier face
survives every tie by never being replaced, and the head of a nonempty
fold is a fact the totality theorem below can state. The picker is public
so a consumer can use `pickWeighted_total` without naming private state. -/
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

/-- The nearest rule is total: any candidates at all yield a face,
whatever weight was asked — the resolution half of `FontSet.index_total`,
so a family that exists never answers a weight request empty-handed. -/
public theorem pickWeighted_total (cands : Array Face) (target : Nat)
    (h : 0 < cands.size) : (pickWeighted cands target).isSome := by
  unfold pickWeighted
  simp [h]

/-- The family a name denotes. A family name denotes itself. A font file name
(`LibertinusSerif-Regular.otf`) — fontspec's way of naming a font that ships
beside the document — denotes the family of the scanned face with that file
name, so its bold and italic are found the way every other family's are. -/
public def familyOf (faces : Array Face) (name : String) : String :=
  if hasFontExtension name then
    match faces.find? fun f => (f.path.splitOn "/").getLast? == some name with
    | some f => f.family
    | none => name
  else name

/-- Best face for a family name and variant, plus whether the family really
offers what was asked for. A family whose heaviest face is "Demi" (600) is
serving a genuine bold, so that counts as satisfied; one with no italic at
all does not, and the caller warns.

A name that is no family may still name a face: fontspec documents ask for
"Fira Sans Light", the Light face of Fira Sans. Family plus subfamily
matches it exactly, the "… Italic" sibling comes along, and the named
weight serves as that name's regular — its bold stays unsatisfied and
warned, because picking a heavier face than the author named would be a
silent substitution. -/
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
      let weightOk :=
        if v.bold then face.weight ≥ 550 else face.weight ≤ 550
      some (face, slantOk && weightOk)

/-- The face a declared per-variant name denotes: a font file name is that
scanned file's own face; anything else resolves like a family or
family-plus-subfamily name. -/
public def resolveNamed (faces : Array Face) (name : String) : Option Face :=
  if hasFontExtension name then
    faces.find? fun f => (f.path.splitOn "/").getLast? == some name
  else
    (resolve faces name {}).map (·.1)

/-- The OS/2 weight a trailing weight word in a face name asks for
(OpenType spec, OS/2 `usWeightClass` table; the same words CSS
`font-weight` names): "Fira Sans Light" requests the family's 300 face.
Returns the family stem and the weight; `none` when the name carries no
weight word, or nothing but one. Longer words match first, so
"ExtraLight" is 200, never "Light"'s 300. -/
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

/-- Nearest-weight resolution for a name that denotes a weighted face of an
installed family, when the exact face is missing: "Fira Sans Light" on a
host with no Light picks Fira Sans's face nearest 300 and reports which
weight substitutes — never silently a heavier face for a lighter request.
A bold variant of the weighted name goes to the family's real bold
(`targetWeight`): a face heavier than the author named is a substitution,
and the caller says so exactly when the answer's weight differs from the
ask. Returns the face and the weight that was asked. -/
public def resolveWeightName (faces : Array Face) (name : String) (v : Variant) :
    Option (Face × Nat) :=
  (nameWeight name).bind fun (fam, w) =>
    let target := (norm fam).toList.toArray
    let byFamily := faces.filter fun f => normEq f.family target
    let want := if v.bold then targetWeight true else w
    let matchingSlant := byFamily.filter fun f => f.italic == v.italic
    let pool := if matchingSlant.isEmpty then byFamily else matchingSlant
    (pickWeighted pool want).map fun face => (face, want)

/-- What a resolution substituted, when it did. The driver renders each
arm under its own code: a missing variant of a served family (W0006), or
a missing weight with the nearest installed weight in its place (W0366) —
the requested and substituted weights ride along so the diagnostic can
name both numbers. -/
public inductive Substituted where
  | variant (msg : String)
  | weight (asked : String) (requested : Nat) (face : Face)

/-- The face for one slot variant, and what substituted when the answer is
not what the document asked for. A face the document declared (fontspec's
`BoldFont=` and siblings) wins over the family's own variant and is met by
definition; a declared face the host lacks degrades — through the nearest
installed weight when the name asks for one ("Inter-Medium" with no Medium
installed), else to the family's best variant — saying so either way.
`none` only when the family itself has no face at all — the caller's
E0403. -/
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
      -- The family name itself carries a weight word ("Fira Sans Light"
      -- with no such face installed): the base family answers at its
      -- nearest weight rather than not at all.
      (resolveWeightName faces family v).map fun (face, req) =>
        (face, if face.weight == req then none
          else some (.weight family req face))

/-- `resolveVariant` lifted onto the weight axis: the face for one
`(weight, italic)` key of a family. The corners LaTeX names — regular 400
and bold 700, whose naming conventions and satisfaction rules predate the
axis — go through `resolveVariant` unchanged; any other weight resolves
by nearest `usWeightClass` distance among the family's slant-matching
faces (italic stays categorical, never substituted silently), W0366 when
the answer's weight differs from the ask. A face the document declared
for the key (`FontFace={l}{n}{...}`, `\fonts{ body.l = ... }`) is met by
definition; a declared face the host lacks degrades through the same
nearest rule, saying so. -/
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

/-- The documented candidate order every scan-derived pick shares
(`fallbackPicks`, `pickCompanion`, `firstMathFace`): family name
(normalised), upright before italic, weight nearest regular, then subfamily
and path. One ordering rule, so a face picked from the scan is a function
of what is installed, never of scan luck. -/
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

/-- The least face under `lt`, by one fold. `leastBy_set_eq` is what it is
shaped for: the answer is a function of the set of faces, so a pick over it
cannot depend on scan order. -/
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

/-- Which face `leastBy` denotes is a function of the SET of faces: two
scans listing the same faces in any orders answer the same, provided the
order is transitive, asymmetric, and total on those faces. This is the
scan-order-independence core of `pickCompanion_set_eq`. -/
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

/-- One designed body↔math pairing, sourced: the body family a document
declares, its designed math companion, where the pairing is documented, and
the companion's licence (checked at the source). The engine ships none of
these faces — a row costs nothing until the host already has the face. -/
public structure Pairing where
  body : String
  companion : String
  source : String
  license : String
  deriving Repr, Inhabited

/-- The designed math companions, as data: one row per body family name the
scan may report, each row citing where the pairing is documented and the
companion's licence. Rows whose licence could not be verified are omitted
until sourced. Sources:
- gust.org.pl/projects/e-foundry/tg-math — the TeX Gyre math companions of
  Pagella (Palatino/URW Palladio), Termes (Times/Nimbus Roman), Bonum
  (Bookman), Schola (Century Schoolbook), and DejaVu; GUST Font License.
- gust.org.pl/projects/e-foundry/lm-math — Latin Modern Math, the companion
  of Latin Modern (and Computer Modern's lineage); GUST Font License.
- stixfonts.org — STIX Two Math beside STIX Two Text; SIL OFL.
- ctan.org/pkg/libertinus — Libertinus Math beside Libertinus Serif; OFL.
- ctan.org/pkg/garamond-math — "should be used together with EB Garamond";
  OFL.
- ctan.org/pkg/erewhon-math — "Utopia-based OpenType math font" beside
  Erewhon; OFL.
- ctan.org/pkg/firamath — Fira Math, the sans math face designed to match
  Fira Sans; OFL. -/
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

/-- The designed math companion of `body` in the supplied metadata: the sourced table
row naming the family, resolved against the scan as the least face (under
the one documented order) whose family is the row's companion. `none` when
no row names the family or no supplied face names the companion. This pure
decision neither reads nor validates that face's MATH table. -/
public def pickCompanion (faces : Array Face) (body : String) : Option (Pairing × Face) := do
  let row ← mathCompanions.find? fun p =>
    normEq body ((norm p.body).toList.toArray)
  let face ← leastBy faceLt (faces.filter fun f =>
    normEq f.family ((norm row.companion).toList.toArray))
  return (row, face)

/-- Scan-order independence: the companion pick is a function of the set of
installed faces — the row is data and the face is `leastBy`'s least member
of the matching faces (the engine's one documented order, `faceLt`), so two
scans listing the same faces in any orders pick the same companion. The
order axioms are hypotheses because `faceLt` bottoms out in string
comparison, whose order lemmas the library does not carry; the suite checks
them over the shipped faces, and `fontcache-check` stays the end-to-end
oracle. -/
public theorem pickCompanion_set_eq (a b : Array Face) (body : String)
    (hmem : ∀ f, f ∈ a ↔ f ∈ b)
    (htrans : ∀ f g h, faceLt f g → faceLt g h → faceLt f h)
    (hasym : ∀ f g, faceLt f g → ¬ faceLt g f)
    (htotal : ∀ f g, f ∈ a → g ∈ a → f = g ∨ faceLt f g ∨ faceLt g f) :
    pickCompanion a body = pickCompanion b body := by
  unfold pickCompanion
  cases mathCompanions.find? fun p => normEq body ((norm p.body).toList.toArray) with
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

/-- Installed families that resemble a name: sharing a word, or within an
edit or two of it. `Nimbus Roman` finds `Nimbus Sans L` and `Nimbus Mono`;
`Libertinus` finds every Libertinus face. At most eight, closest first. -/
public def nearest (families : Array String) (wanted : String) : Array String :=
  let words (s : String) : List String :=
    (s.toLower.splitOn " ").filter fun w => !w.isEmpty && w.length > 1
  let want := words wanted
  let score (fam : String) : Nat :=
    let got := words fam
    let shared := (want.filter got.contains).length
    -- Prefix of the first word counts too: `Nimbus` vs `NimbusSans`.
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
  -- One normalised key per face, kept in a set. The earlier `seen.any` with
  -- `norm` on both sides re-normalised every prior name for every face:
  -- four million string allocations and two seconds on a 2856-face host,
  -- paid on every failed font lookup.
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

/-- The family a document with no `\fonts` uses: the first preferred name
that resolves, else the first family calling itself sans, else the first
face of any kind. `none` only when no face is installed at all — so the
default exists on any host with any scannable font, by construction. -/
public def defaultFamily (faces : Array Face) : Option String :=
  match defaultFamilies.find? fun n => (resolve faces n {}).isSome with
  | some n => some n
  | none =>
    match faces.find? fun f => ((norm f.family).splitOn "sans").length > 1 with
    | some f => some f.family
    | none => faces[0]?.map (·.family)

end LeanTex.Core.FontDb
