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

/-- The standalone-font extensions selection and discovery recognize,
lowercase; a font collection's are `collectionExtensions`. -/
public def fontExtensions : List String := ["ttf", "otf"]

/-- The font collection extensions discovery recognizes, lowercase: one file
holding several faces (`.ttc`, `.otc`), the form macOS ships most of its
system faces in. A `.dfont` is neither a font file nor a collection here. -/
public def collectionExtensions : List String := ["ttc", "otc"]

/-- A supported standalone-font extension (`fontExtensions`), ignoring
case. This recognizes names used by selection and discovery; it does not
inspect any bytes. A collection is `isCollectionFile`'s. -/
public def hasFontExtension (p : String) : Bool :=
  match (p.splitOn ".").getLast? with
  | some ext => fontExtensions.contains ext.toLower
  | none => false

/-- An OpenType font collection's extension, ignoring case: one file
holding several faces (`.ttc`, `.otc`), the form macOS ships most of its
system faces in. -/
public def isCollectionFile (p : String) : Bool :=
  match (p.splitOn ".").getLast? with
  | some ext => collectionExtensions.contains ext.toLower
  | none => false

/-- The path a face of a collection is known by: the file, `#`, and the
face's index in it. No standalone font file is named so: its name would end
in no font extension, so the scan never lists one as a face. -/
public def memberPath (file : String) (index : Nat) : String :=
  s!"{file}#{index}"

/-- The collection file and face index a `memberPath` names, or `none` for
any other path: the text after the last `#` is the index, and the text
before it must name a collection. -/
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
      -- A named face is its name's regular, whatever its weight: "Fira Sans
      -- SemiBold" asked for upright is met by the SemiBold face itself.
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
installed weight when the name asks for one ("Ordwick-Semibold" with no
Semibold installed), else to the family's best variant — saying so either
way.
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

/-- One designed pairing, sourced: a text family, its designed companion —
a math face (`mathCompanions`) or a typewriter face (`monoCompanions`) —,
where the pairing is documented, and the companion's licence (checked at
the source). The engine ships none of these faces — a row costs nothing
until the host already has the face. -/
public structure Pairing where
  body : String
  companion : String
  source : String
  license : String
  /-- The text family's and the companion's x-heights, in thousandths of an
  em — the ink top of each regular face's own 'x', as the engine measures
  it (`Font.xInkTop`), from the files the row's source ships — where they
  were measured: what decides whether a typewriter companion leads
  lualatex's Latin Modern Mono beside a declared text face
  (`companionLeads`). -/
  xHeights : Option (Nat × Nat) := none
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

/-- The row of a sourced pairing table that names `body`: the one lookup
both companion tables share (`mathCompanions`, `monoCompanions`). -/
public def companionRow (table : Array Pairing) (body : String) : Option Pairing :=
  table.find? fun p => normEq body ((norm p.body).toList.toArray)

/-- The designed math companion of `body` in the supplied metadata: the sourced table
row naming the family, resolved against the scan as the least face (under
the one documented order) whose family is the row's companion. `none` when
no row names the family or no supplied face names the companion. This pure
decision neither reads nor validates that face's MATH table. -/
public def pickCompanion (faces : Array Face) (body : String) : Option (Pairing × Face) := do
  let row ← companionRow mathCompanions body
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

/-- The designed typewriter companions, as data: one row per
`defaultFamilies` entry whose own project or collection ships a monospaced
family beside it, where that is documented, and one per text family of a
superfamily whose project ships its monospace beside it (Fira, Adobe's
Source, IBM Plex, Noto, DejaVu's serif) under the name the family's files
declare; each with the companion's licence,
and the x-heights of the pair where they were measured (`companionLeads`).
A default family with none is on `monoUnpaired` instead, so every default
family is a decided row (`markdownMonoChecks`). The engine ships none of
these faces — a row costs nothing until the host already has the face.
Sources:
- github.com/mozilla/Fira — Fira Sans and Fira Mono, one family; SIL OFL.
- github.com/adobe-fonts/source-code-pro — Source Code Pro, the Source
  superfamily's monospace, drawn by Source Sans Pro's designer (Paul D.
  Hunt, in both families' name tables); Source Serif is drawn to complement
  Source Sans (github.com/adobe-fonts/source-serif); SIL OFL.
- github.com/IBM/plex — IBM Plex Sans, Sans Condensed, Serif and Mono, one
  superfamily;
  SIL OFL.
- github.com/notofonts/latin-greek-cyrillic — Noto Sans, Noto Serif and Noto
  Sans Mono, which ships no italic (`monoUprightOnly`); SIL OFL.
- github.com/dejavu-fonts/dejavu-fonts (README, "Available fonts") — DejaVu
  Sans, DejaVu Serif and DejaVu Sans Mono, one family; the DejaVu fonts
  licence (Bitstream Vera's, with public-domain changes).
- github.com/liberationfonts/liberation-fonts (README) — Liberation Sans,
  Serif and Mono, one collection, metric-compatible with Arial, Times New
  Roman and Courier New; SIL OFL.
- github.com/ArtifexSoftware/urw-base35-fonts — the PostScript base 35 set,
  Nimbus Sans (Helvetica) and Nimbus Mono PS (Courier) among them; AGPL with
  a font exception.
- the PostScript core set (PostScript Language Reference, the standard 35)
  and PSNFSS's standard sans and typewriter pairing (`helvet`, `courier`;
  psnfss2e) — Helvetica with Courier, and Microsoft's core fonts for the web
  the same way, Arial with Courier New (the correspondence the Liberation
  collection documents); vendor licences. -/
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

/-- Typewriter families whose project ships no italic face at all: an
italic code run set in one is upright for want of a face to install, so
the note naming it offers a declaration alone (`DriverDiag.monoUpright`).
Sources: github.com/notofonts/latin-greek-cyrillic, whose Noto Sans Mono
sources hold upright masters only. -/
public def monoUprightOnly : List String := ["Noto Sans Mono"]

/-- The default text families no project ships a designed typewriter face
beside: their documents' undeclared slot takes the first platform monospace
the scan serves (`monoDefault`) — a tex document's, where it serves none,
lualatex's own shapes (`monoPick`) — and keeps the text family, which W0390
names, where nothing serves. -/
public def monoUnpaired : List String := ["Helvetica Neue", "Inter"]

/-- The four corners NFSS names for every family — regular, bold, italic,
bold italic — at the weights the driver's assembly asks them at. -/
public def corners : List (Nat × Bool) := [(400, false), (700, false), (400, true), (700, true)]

/-- The upright corners, regular and bold: what a typewriter default must
serve with its own faces. -/
public def uprightCorners : List (Nat × Bool) := [(400, false), (700, false)]

/-- The italic corners, regular and bold: a typewriter default serves both
with its own faces, or holds no italic face at all — Debian's
`fonts-dejavu-core` ships DejaVu Sans Mono's Regular and Bold alone — and
sets both upright in it, never slanted, named once where a document sets
italic code (N0031). A family holding one italic of the two is no default:
the corner it lacks would set in its other italic, a substitution of a
family the document never named. -/
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

/-- Does the same resolver answer this corner with an upright fixed-pitch
face — its answer for an italic corner of a family holding no italic face,
since italic is categorical and only an italic-free family's upright faces
answer one? -/
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

/-- Does the scan serve `family` as a typewriter family: its upright
corners (`uprightCorners`) each its own face, unsubstituted and fixed-pitch
(`cornerFixed`), and its italic corners (`italicCorners`) both so, or both
upright in it (`cornerUpright`)? -/
public def servesMono (faces : Array Face) (family : String) : Bool :=
  uprightCorners.all (cornerFixed faces family) &&
    (italicCorners.all (cornerFixed faces family) || italicCorners.all (cornerUpright faces family))

/-- What a typewriter default serves, through the resolver call the
assembly makes for each corner: its upright corners each its own
fixed-pitch face, unsubstituted, and its italic corners both so, or both an
upright fixed-pitch face of it. It never sets code in a proportional face
or a substituted weight, and never in a family missing one italic of two. -/
public def MonoServed (faces : Array Face) (family : String) : Prop :=
  (∀ c ∈ uprightCorners, ∃ f, resolveWeight faces family none c.1 c.2 = some (f, none) ∧
      f.fixedPitch = true) ∧
    ((∀ c ∈ italicCorners, ∃ f, resolveWeight faces family none c.1 c.2 = some (f, none) ∧
        f.fixedPitch = true) ∨
      (∀ c ∈ italicCorners, ∃ f s, resolveWeight faces family none c.1 c.2 = some (f, s) ∧
        f.italic = false ∧ f.fixedPitch = true))

/-- **A family the scan serves as a typewriter family is served whole or
upright** (`MonoServed`). -/
public theorem servesMono_contract (faces : Array Face) (family : String)
    (h : servesMono faces family = true) : MonoServed faces family := by
  unfold servesMono at h
  simp only [Bool.and_eq_true, Bool.or_eq_true] at h
  obtain ⟨hu, hi⟩ := h
  refine ⟨fun c hc => cornerFixed_fixedPitch faces family c (List.all_eq_true.mp hu c hc), ?_⟩
  rcases hi with hown | hup
  · exact Or.inl fun c hc => cornerFixed_fixedPitch faces family c (List.all_eq_true.mp hown c hc)
  · exact Or.inr fun c hc => cornerUpright_upright faces family c (List.all_eq_true.mp hup c hc)

/-- The typewriter family an undeclared slot takes first (`monoFor`): its
text family's designed companion (`monoCompanions`), when the scan serves
the companion as a typewriter family (`servesMono`) — else none, and the
platform monospace answers (`monoDefault`). -/
public def monoCompanion (faces : Array Face) (text : String) : Option String :=
  (companionRow monoCompanions text).bind fun row =>
    if servesMono faces row.companion then some row.companion else none

/-- **The default sets no corner it cannot serve.** A family the default
picks is served (`MonoServed`) through the same resolver call the assembly
makes: it never sets code in a proportional face or a substituted weight,
and it is never a guess beyond the sourced rows. An italic it lacks sets
upright in it, named once (N0031). -/
public theorem monoCompanion_contract (faces : Array Face) (text family : String)
    (h : monoCompanion faces text = some family) : MonoServed faces family := by
  unfold monoCompanion at h
  rcases Option.bind_eq_some_iff.mp h with ⟨row, _, hrow⟩
  split at hrow
  · rename_i hs
    cases hrow
    exact servesMono_contract faces _ hs
  · cases hrow

/-- The default is drawn from the sourced rows: a family it picks is the
companion of the row naming the text family. -/
public theorem monoCompanion_mem (faces : Array Face) (text family : String)
    (h : monoCompanion faces text = some family) :
    ∃ row, companionRow monoCompanions text = some row ∧ row.companion = family := by
  unfold monoCompanion at h
  rcases Option.bind_eq_some_iff.mp h with ⟨row, hr, hrow⟩
  split at hrow
  · cases hrow
    exact ⟨row, hr, rfl⟩
  · cases hrow

/-- The monospaced families an undeclared typewriter slot takes, in order,
where the text family has no designed companion the scan serves: the
platforms' own system monospace faces, macOS's first. One list for every
host: a face is taken because the font environment holds it, never because
of the operating system's name, so the artifact stays a function of the
document and its font environment. The engine ships none of these faces.

A tex document declaring its text family reads lualatex's own shapes
before this list, and any other tex document after it (`monoPick`).
Sources:
- developer.apple.com/fonts — SF Mono, Apple's monospaced system family,
  where a user has installed it into a font directory.
- en.wikipedia.org/wiki/Menlo_(typeface) — Menlo, the monospaced face macOS
  has shipped since 10.6, as the system font collection `Menlo.ttc`; that
  file's layout is unverified here, since no Mac was available to read it.
- github.com/dejavu-fonts/dejavu-fonts — DejaVu Sans Mono, the monospace
  Linux distributions install and fontconfig's `monospace` alias resolves
  to on them (fontconfig, `conf.d/60-latin.conf`).
- github.com/liberationfonts/liberation-fonts — Liberation Mono, the
  distributions' metric-compatible Courier New. -/
public def monoDefaults : List String :=
  ["SF Mono", "Menlo", "DejaVu Sans Mono", "Liberation Mono"]

/-- The first platform monospace (`monoDefaults`) the scan serves as a
typewriter family (`servesMono`). -/
public def monoDefault (faces : Array Face) : Option String :=
  monoDefaults.find? (servesMono faces)

/-- The typewriter family an undeclared slot the document sets runs in
takes, on either surface: the text family's designed companion where the
scan serves it, else the first platform monospace it serves, else none —
and the slot falls to the text family, the loss W0390 names, unless a tex
document's lualatex shapes answer (`monoPick`). -/
public def monoFor (faces : Array Face) (text : Option String) : Option String :=
  (text.bind (monoCompanion faces ·)).orElse fun _ => monoDefault faces

/-- **The platform default sets no corner it cannot serve**, as the
companion does not (`monoCompanion_contract`): never a proportional face,
never a substituted weight, never one italic of two. -/
public theorem monoDefault_contract (faces : Array Face) (family : String)
    (h : monoDefault faces = some family) : MonoServed faces family :=
  servesMono_contract faces family (List.find?_some h)

/-- The platform default is drawn from the sourced list, and every family
listed before it is one the scan does not serve: the list is read in
order. -/
public theorem monoDefault_mem (faces : Array Face) (family : String)
    (h : monoDefault faces = some family) :
    family ∈ monoDefaults ∧ ∃ before after, monoDefaults = before ++ family :: after ∧
      ∀ g ∈ before, servesMono faces g = false := by
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  obtain ⟨before, after, hsplit, hbefore⟩ := List.find?_eq_some_iff_append.mp h |>.2
  exact ⟨before, after, hsplit, fun g hg => by simpa using hbefore g hg⟩

/-- **Whatever family `monoFor` answers is served** (`MonoServed`): the
companion's contract and the platform default's, one statement for the
assembly's one call. -/
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

/-- The family lualatex's typewriter shapes are filed under here: the
typographic family of the regular and italic files, whose bold is the
Light family's (`latinModernMonoFaces`). -/
public def latinModernMono : String := "Latin Modern Mono"

/-- lualatex's own typewriter shapes for a tex document that declares none,
measured under lualatex (TeX Live 2026, with and without fontspec's
`\setmainfont`; `\fontname\font` at each size and shape) and read in
`tulmtt.fd`: `\textit` over `\texttt` sets in LMMono10-Italic at every size,
`\textbf` in the Light family's bold, LMMonoLt10-Bold (`b/n`), and bold
italic in LMMonoLt10-BoldOblique (`tulmtt.fd` substitutes `b/sl` for
`b/it`), each at every size; the regular upright sets in LMMono10-Regular
from 9.5 pt up to 11 pt. The shapes span two families, so they are named by
their files, the files every TeX distribution installs: a corner's face
file, regular, bold, italic, bold italic.

Pending work, where the page departs from lualatex's: the regular upright
is the 10-point design at every size, where lualatex takes LMMono8-Regular
below 8.5 pt (a `\footnotesize` listing in a 10-point class), LMMono9-Regular
from 8.5 pt (a `\small` one) and LMMono12-Regular from 11 pt (the `12pt`
class option's text): each advance is 0.531 em, 0.525 em and 0.515 em of
its file's, against LMMono10's 0.525 em, so a line of code sets 1.1% narrower
than lualatex's below 8.5 pt, as wide from 8.5 pt to 11 pt, and 1.9% wider
from 11 pt, in the 10-point design's strokes throughout. `\textsl` over
`\texttt` sets in the italic, LMMono10-Italic, where lualatex takes
LMMonoSlant10-Regular (`m/sl`), on the same 0.525 em advance; and `\textsc`
in the regular's capitals scaled to a small capital's size
(`smallCapScaleFor`), their advance scaled with them, where lualatex takes
LMMonoCaps10-Regular (`m/sc`), whose small capitals keep the 0.525 em
advance: the engine's style carries no slanted shape beside the italic and
no small-capital face. -/
public def latinModernMonoFaces : List ((Nat × Bool) × String) :=
  [((400, false), "lmmono10-regular.otf"), ((700, false), "lmmonolt10-bold.otf"),
   ((400, true), "lmmono10-italic.otf"), ((700, true), "lmmonolt10-boldoblique.otf")]

/-- lualatex's shapes where neither italic file is installed: each italic
corner set in its upright's file, as a platform monospace with no italic
face sets its italic corners upright (`italicCorners`). -/
public def latinModernMonoUpright : List ((Nat × Bool) × String) :=
  [((400, false), "lmmono10-regular.otf"), ((700, false), "lmmonolt10-bold.otf"),
   ((400, true), "lmmono10-regular.otf"), ((700, true), "lmmonolt10-bold.otf")]

/-- Does the assembly's resolver answer a corner declared by its file — the
call it makes for each of a pick's files — with a fixed-pitch face,
unsubstituted: the file's own face (`resolveNamed`)? -/
public def fileFixed (faces : Array Face) (c : (Nat × Bool) × String) : Bool :=
  match resolveWeight faces latinModernMono (some c.2) c.1.1 c.1.2 with
  | some (f, none) => f.fixedPitch
  | _ => false

/-- lualatex's shapes as the scan serves them, corner by corner: all four
files (`latinModernMonoFaces`), or — where neither italic file is
installed — the upright two at every corner (`latinModernMonoUpright`);
none where an upright file is missing, or one italic file of the two. -/
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

/-- **lualatex's shapes are met where they are taken**: they name a file
for every corner, and every corner's file answers the resolver call the
assembly makes for it — the family, the file declared, the corner — with a
fixed-pitch face, unsubstituted. -/
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

/-- Latin Modern Mono's x-height, in thousandths of an em: the ink top of
its regular's 'x' (`Font.xInkTop`), 431 of lmmono10-regular.otf's 1000
units (TeX Live 2026), Latin Modern Roman's own — the text face lualatex
pairs it with. -/
public def latinModernMonoXHeight : Nat := 431

/-- How far, in percent of the text's x-height, a companion's x-height may
stand from it and still lead lualatex's shapes (`companionLeads`): the
measured companions stand within 5.4% of their text faces', where Latin
Modern Mono stands 9 to 21% below them. -/
public def companionXHeightBound : Nat := 6

/-- The distance between two measures. -/
private def gapOf (a b : Nat) : Nat := if a ≥ b then a - b else b - a

/-- **The companion-first departure, decided on its axis.** lualatex sets
Latin Modern Mono in the typewriter slot beside any text face a document
declares; a declared text face's designed companion leads it instead
(`monoPick`) only where the pairing is measurably better on the axis it is
drawn on, x-height: the companion's stands nearer the text's than Latin
Modern Mono's (`latinModernMonoXHeight`), and within
`companionXHeightBound` percent of it. A row with no measurement keeps
lualatex's order. The departure's cost, beside its gain: every companion
advances 0.600 em a character (DejaVu Sans Mono 0.602 em) against Latin
Modern Mono's 0.525 em, so a line of code sets 14% wider and a declared line
lualatex fits may run past the measure; and a companion with no italic face
(`monoUprightOnly`, or a host that installed none) still leads, its italic
code upright and named once (N0031), the trade an undeclared slot makes
with any monospace that lacks its italics. Measured, text and companion:
Fira Sans and Fira Mono at
527 and 527, Latin Modern Mono at 82% of the text; Source Sans Pro and
Source Code Pro at 486 and 486, Latin Modern Mono at 89%; Source Serif Pro
at 475, its companion at 102%, Latin Modern Mono at 91%; IBM Plex Sans and
Serif, IBM Plex Sans Condensed and IBM Plex Mono at 516, Latin Modern Mono at
84%; Noto Sans, Noto Serif and Noto Sans Mono at 536, Latin Modern Mono at
80%; DejaVu Sans and DejaVu Sans
Mono at 547, Latin Modern Mono at 79%; DejaVu Serif at 519, its companion
at 105%, Latin Modern Mono at 83%. Nimbus Sans and Nimbus Mono PS stand at
524 and 419, 80%, where Latin Modern Mono's 82% is nearer: lualatex's order
holds there (`companionDepartureChecks`). -/
public def companionLeads (row : Pairing) : Bool :=
  match row.xHeights with
  | some (body, comp) =>
    0 < body && gapOf comp body < gapOf latinModernMonoXHeight body &&
      gapOf comp body * 100 ≤ companionXHeightBound * body
  | none => false

/-- What fills an undeclared typewriter slot: a family, and the face files
it is set in corner by corner where the answer is a set of files rather than
one family's faces (lualatex's shapes, which span two families). -/
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

/-- The family the pool reports for a text face as a document names it — a
family, a file of it, or a family and a weight it holds or lacks — read by
the call the text slot's regular corner makes (`resolveWeight`), so a
companion row is found however the face was spelled and for the face the
text sets in. -/
public def textFamilyOf (faces : Array Face) (text : String) : String :=
  match resolveWeight faces text none 400 false with
  | some (f, _) => f.family
  | none => text

/-- The text family's designed companion as a pick, where it leads
lualatex's shapes (`companionLeads`) and the pool serves it as a
typewriter family. -/
private def leadPick (faces : Array Face) (text : Option String) : Option MonoPick :=
  text.bind fun t => (companionRow monoCompanions t).bind fun row =>
    -- premise: companionDepartureChecks — a row leads only where its companion's measured x-height stands nearer the text's than Latin Modern Mono's and inside the bound, the suite's pair re-measured by the engine to its row
    if companionLeads row && servesMono faces row.companion then some { family := row.companion }
    else none

/-- **The typewriter default, read over one pool of faces.** A document
that declares its text family takes that family's designed companion first
where it leads lualatex's shapes on x-height (`companionLeads`, the one
departure from lualatex here, which sets Latin Modern Mono beside a
`\setmainfont`), then, a tex document, lualatex's own shapes
(`latinModernMonoServed`), and then the family `monoFor` answers — a
companion that does not lead, else the first platform monospace the pool
serves. Any other document takes the family `monoFor` answers first, and a
tex document lualatex's shapes after it, the last answer before its slot
falls to the text face; a markdown document has no lualatex answer to
keep. A document whose text family is the engine's own (`defaultFamily`)
does not set its text in lualatex's Latin Modern Roman, so lualatex's
pairing is not its page's: its default's companion is drawn to the text it
sits beside — DejaVu Sans Mono's x-height is DejaVu Sans's own, 0.547 em,
where Latin Modern Mono's 0.431 em stands at 79% of it. -/
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

/-- A pick is lualatex's shapes, a file for every corner, each met by the
assembly's call for its corner, or a family served as a typewriter family
(`MonoServed`). -/
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
