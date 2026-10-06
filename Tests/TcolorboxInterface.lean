module

import LeanTex.Core.Tcolorbox

/-! Native lowering exposes its prepared content, capture boundary, and body
contract. Key scanning and selection state remain implementation details. -/

open LeanTex.Core
open LeanTex.Core.Parse
open LeanTex.Core.Tcolorbox

namespace Tests.TcolorboxInterface

example : String → String := bindingName
example : String → Option String := boundName?
example : Repr Lowered := inferInstance
example : Repr Prepared := inferInstance

example (raws : Array Raw) (unsupported : Array String) : Lowered :=
  { raws, unsupported }
example (title bodyDecls : Array Raw) (before after : Option String)
    (unsupported : Array String) : Prepared :=
  { title, bodyDecls, before, after, unsupported }
example (s : Prepared) :
    Array Raw × Array Raw × Option String × Option String × Array String :=
  (s.title, s.bodyDecls, s.before, s.after, s.unsupported)
example (s : Lowered) : Array Raw × Array String := (s.raws, s.unsupported)

example : Array Raw → Pos → Prepared := prepare
example {m : Type → Type} [Monad m]
    (capture : String → Array Raw → m (Option (Array Raw)))
    (options : Array Raw) (pos : Pos) : m Prepared :=
  prepareM capture options pos
example (s : Prepared) (body : Array Raw) (pos : Pos) : Lowered := s.lower body pos
example : Array Raw → Array Raw → Pos → Lowered := lower

example (options : Array Raw) (pos : Pos) :
    prepareM (m := Id) (fun _ rs => pure (some rs)) options pos =
      prepare options pos :=
  prepareM_identity_exact options pos
example (s : Prepared) (body : Array Raw) (pos : Pos) :
    CarriesBody (s.lower body pos).raws body pos :=
  s.lower_body_covers body pos
example (options body : Array Raw) (pos : Pos) :
    CarriesBody (lower options body pos).raws body pos :=
  lower_body_covers options body pos

-- A client can read the contract's witness without unfolding the lowerer.
example (options body : Array Raw) (pos : Pos) :
    ∃ title decls, Raw.env "block"
      #[.group title pos, .group (decls ++ body) pos] pos ∈
        (lower options body pos).raws.toList := by
  obtain ⟨title, decls, h⟩ := lower_body_covers options body pos
  exact ⟨title, decls, h⟩

example : True := by
  fail_if_success have := Tcolorbox.trim
  fail_if_success have := Tcolorbox.value
  fail_if_success have := Tcolorbox.entries
  fail_if_success have := Tcolorbox.entry
  fail_if_success have := Tcolorbox.Settings
  fail_if_success have := Tcolorbox.Settings.refuse
  fail_if_success have := Tcolorbox.gap?
  fail_if_success have := Tcolorbox.settings
  fail_if_success have := Tcolorbox.ink
  fail_if_success have := Tcolorbox.gap
  fail_if_success have := Tcolorbox.Settings.prepared
  trivial

end Tests.TcolorboxInterface
