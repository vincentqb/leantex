module

public import LeanTex.Core.Elab
import all LeanTex.Core.Elab

namespace LeanTex.Core.Elab

open Ir Parse

/-- Two contexts that resolve every command and environment alike. -/
private def SameScope (a b : Ctx) : Prop :=
  a.user = b.user ∧ a.userEnvs = b.userEnvs ∧ a.limit = b.limit ∧ a.envLimit = b.envLimit ∧
    a.kept = b.kept

private theorem lookupUser_scope {a b : Ctx} (h : SameScope a b) (name : String) :
    lookupUser a name = lookupUser b name := by
  obtain ⟨hu, _, hl, _, hk⟩ := h
  simp only [lookupUser, hu, hl, hk]

private theorem lookupUserEnv_scope {a b : Ctx} (h : SameScope a b) (name : String) :
    lookupUserEnv a name = lookupUserEnv b name := by
  obtain ⟨_, he, _, hl, hk⟩ := h
  simp only [lookupUserEnv, he, hl, hk]

private theorem nestedCalls_scope {n : Nat} {a b : Ctx} {names : List String}
    (h : SameScope a b) (hn : NestedCalls n a names) : NestedCalls n b names := by
  cases hn with
  | nil => exact .nil b
  | cmd hl hk he hr =>
    exact .cmd ((lookupUser_scope h _).symm.trans hl) hk (he.trans h.2.2.2.1) hr
  | env hl hk hn hr =>
    exact .env ((lookupUserEnv_scope h _).symm.trans hl) hk hn hr

/-- A context a definition's text expands under, one step of a chain below the context `ctx`
naming it. -/
private def Below (n : Nat) (ctx : Ctx) (name : String) (inner : Ctx) : Prop :=
  ∀ rest, NestedCalls n inner rest → NestedCalls n ctx (name :: rest)

private theorem below_scope {n : Nat} {ctx ctx' inner : Ctx} {name : String}
    (hs : SameScope ctx' ctx) (h : Below n ctx' name inner) : Below n ctx name inner :=
  fun rest hr => nestedCalls_scope hs (h rest hr)

private theorem callInto_below {n : Nat} {ctx : Ctx} {name : String} {pos : Pos} {k : Nat}
    {cmd : UserCmd} (args : Array (String × Option (Array Inline)))
    (hu : lookupUser ctx name = some (k, cmd)) : Below n ctx name (callInto ctx name pos k args) :=
  fun _ h => .cmd (inner := callInto ctx name pos k args) hu rfl rfl h

private theorem envInto_below {n : Nat} {ctx inner : Ctx} {name : String} {k : Nat} {env : UserEnv}
    (args : Array (String × Option (Array Inline))) (he : lookupUserEnv ctx name = some (k, env))
    (hn : ctx.user.size ≤ n) (hs : SameScope inner (envInto ctx k args)) :
    Below n ctx name inner :=
  fun _ h => .env (inner := envInto ctx k args) he rfl hn (nestedCalls_scope hs h)

/-- Whether the block knot's built-in arms take an environment name before a document's own. -/
private def blockEnvBuiltin (n : String) : Bool :=
  n == Parse.scopeEnv || n == Parse.linesEnv || (Parse.inputEnvFile? n).isSome ||
    (displayMathEnvs.lookup n).isSome || (alignEnvs.lookup n).isSome ||
    Compat.tableEnvs.contains n || n == Parse.markdownTableEnv || n == "thebibliography" ||
    n == "frame" || n == "itemize" || n == "enumerate" || n == "description" || n == "center" ||
    n == "trivlist" || (Ir.raggedSideOf? n).isSome || n == "minipage" || (titledKind? n).isSome ||
    n == "quote" || n == "quotation" || n == "verse" || n == "abstract" || n == "appendices" ||
    n == "figure" || n == "figure*" || n == "table" || n == "table*" || n == "algorithm" ||
    n == "algorithm*" || n == "algorithm2e" || n == "algorithmic" || n == "columns" ||
    n == "ifbackend" || n == "nav"

/-- Each expansion the knot makes, inline or block, elaborates a definition's text one step of an
`expandUser_depth_le` chain below the context naming it. -/
private theorem knot_calls_nest (n : Nat) :
    (∀ (ctx : Ctx) (raws : Array Raw) (i : Nat) (acc : Array Inline) (sb name : String) (pos : Pos)
        (k : Nat) (cmd : UserCmd) (h : i < raws.size), raws[i] = .ctrl name pos →
        ctx.args.find? (·.1 == name) = none → lookupUser ctx name = some (k, cmd) →
        let at' : Ctx := { ctx with macroRoles := (inlineMacroAt ctx.macroRoles raws i acc sb).1 }
        (∃ K : Array (String × Option (Array Inline)) × { j : Nat // i + 1 ≤ j } → Array Inline →
            EM (Array Inline), elabInlinesFrom ctx raws i acc sb =
          takeArgsFrom at' cmd.params 0 name raws (i + 1) pos #[] >>= fun r =>
            elabInlinesCore (callInto at' name pos k r.1) cmd.body >>= K r) ∧
        ∀ args, Below n ctx name (callInto at' name pos k args)) ∧
    (∀ (ctx : Ctx) (raws : Array Raw) (i : Nat) (acc : Array Inline) (sb name : String)
        (body : Array Raw) (pos : Pos) (k : Nat) (env : UserEnv) (h : i < raws.size),
        raws[i] = .env name body pos → (name == Parse.scopeEnv) = false →
        (name == Parse.modeEnv) = false → Parse.inputEnvFile? name = none →
        displayMathEnvs.lookup name = none → alignEnvs.lookup name = none →
        (name == "tikzpicture") = false → lookupUserEnv ctx name = some (k, env) →
        let at' : Ctx := { ctx with macroRoles := (inlineMacroAt ctx.macroRoles raws i acc sb).1 }
        let literal := declaresMono env.beginBody
        (∃ K : Array Inline → EM (Array Inline), elabInlinesFrom ctx raws i acc sb =
          takeArgsFrom at' env.params 0 name body 0 pos #[] >>= fun r =>
            withDefault env.params r.1
              (fun d => elabInlinesCore { envInto at' k r.1 with argBody := true } d) >>= fun b =>
            inlineGroup at'.palette (do
              let opened ← elabInlinesCore (halvesInto at' k b)
                (env.beginBody.push (.ctrl envContentArg { pos with origins := [] }))
              let content ← elabInlinesCore { at' with literalText := at'.literalText || literal }
                (envBody env body r.2.1)
              let closed ← elabInlinesCore
                { halvesInto at' k b with literalText := at'.literalText || literal } env.endBody
              pure (placeEnvContent opened (content ++ closed))) >>= K) ∧
        (ctx.user.size ≤ n → ∀ args lit, Below n ctx name { envInto at' k args with argBody := true } ∧
          Below n ctx name (halvesInto at' k args) ∧
          Below n ctx name { halvesInto at' k args with literalText := lit })) ∧
    (∀ (ctx : Ctx) (raws : Array Raw) (i : Nat) (h : i < raws.size) (name : String) (pos : Pos)
        (blocks : Array Block) (k : Nat) (cmd : UserCmd),
        Ir.boxCommands.contains (Compat.overlayName name) = false →
        declCtrl.contains (Compat.overlayName name) = false →
        runningCtrl.contains (Compat.overlayName name) = false → lookupUser ctx name = some (k, cmd) →
        (∃ K : Array (String × Option (Array Inline)) × { j : Nat // i + 1 ≤ j } → Array Block →
            EM (Array Block × { j : Nat // i < j }), elabCtrlArm ctx raws i h name pos blocks =
          takeArgsFrom ctx cmd.params 0 (Compat.overlayName name) raws (i + 1) pos #[] >>= fun r =>
            splicedFrameScope (some blocks.size)
              (elabBlockScope (callInto ctx name pos k r.1) cmd.body) >>= K r) ∧
        ∀ args, Below n ctx name (callInto ctx name pos k args)) ∧
    (∀ (ctx : Ctx) (name : String) (scope : Array Raw) (pos : Pos) (blocks : Array Block) (st : ESt)
        (k : Nat) (env : UserEnv), blockEnvBuiltin name = false →
        scopedEnv st.ctr.thm name = false → lookupUserEnv ctx name = some (k, env) →
        (∃ K : Array (String × Option (Array Inline)) × Nat → Array (String × Option (Array Inline)) →
            Array Block → Array Block → Array Block → EM (Array Block),
          (elabEnvArm ctx name scope pos blocks).run st =
            (let body := (openLengthScope ctx scope).2.1
            takeArgs ctx env.params name body 0 pos >>= fun r =>
              withDefault env.params r.1
                (fun d => elabInlinesCore { envInto ctx k r.1 with argBody := true } d) >>= fun b =>
              splicedFrameScope (some blocks.size) (elabBlockScope (envInto ctx k b) env.beginBody)
                >>= fun opened =>
              splicedFrameScope (some (blocks ++ opened).size)
                (elabBlockScope ctx (body.extract r.2 body.size)) >>= fun content =>
              splicedFrameScope (some (blocks ++ opened ++ content).size)
                (elabBlockScope (envInto ctx k b) env.endBody) >>= K r b opened content).run st) ∧
        (ctx.user.size ≤ n → ∀ args, Below n ctx name { envInto ctx k args with argBody := true } ∧
          Below n ctx name (envInto ctx k args))) := by
  have rolesScope : ∀ (ctx : Ctx) roles, SameScope { ctx with macroRoles := roles } ctx :=
    fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ctx raws i acc sb name pos k cmd h hr ha hu
    refine ⟨?_, fun args => below_scope (rolesScope ctx _)
      (callInto_below args ((lookupUser_scope (rolesScope ctx _) name).trans hu))⟩
    rw [elabInlinesFrom]
    generalize inlineMacroAt ctx.macroRoles raws i acc sb = state
    rcases state with ⟨roles, acc', sb'⟩
    dsimp only
    rw [dite_eq_left h, hr]
    simp only [ha]
    split
    · rename_i heq
      simp only [lookupUser] at hu heq
      rw [hu] at heq
      cases heq
      exact ⟨_, rfl⟩
    · rename_i heq
      simp only [lookupUser] at hu heq
      rw [hu] at heq
      cases heq
  · intro ctx raws i acc sb name body pos k env h hr h1 h2 h3 h4 h5 h6 he
    have he' := (lookupUserEnv_scope
      (rolesScope ctx (inlineMacroAt ctx.macroRoles raws i acc sb).1) name).trans he
    refine ⟨?_, fun hn args _ =>
      have b := fun inner (hs : SameScope inner
          (envInto { ctx with macroRoles := (inlineMacroAt ctx.macroRoles raws i acc sb).1 } k args)) =>
        below_scope (rolesScope ctx _) (envInto_below (inner := inner) args he' hn hs)
      ⟨b _ ⟨rfl, rfl, rfl, rfl, rfl⟩, b _ ⟨rfl, rfl, rfl, rfl, rfl⟩, b _ ⟨rfl, rfl, rfl, rfl, rfl⟩⟩⟩
    rw [elabInlinesFrom]
    generalize inlineMacroAt ctx.macroRoles raws i acc sb = state
    rcases state with ⟨roles, acc', sb'⟩
    dsimp only
    rw [dite_eq_left h, hr]
    simp only [h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i heq
      simp only [lookupUserEnv] at he heq
      rw [he] at heq
      cases heq
      exact ⟨_, rfl⟩
    · rename_i heq
      simp only [lookupUserEnv] at he heq
      rw [he] at heq
      cases heq
  · intro ctx raws i h name pos blocks k cmd hb hd hn hu
    refine ⟨?_, fun args => callInto_below args hu⟩
    rw [elabCtrlArm]
    simp only [boxBlockHead, hb, Bool.false_and, Bool.not_false, ↓reduceIte, hd, hn,
      Bool.false_eq_true, pure_bind, hu, Option.isNone_some, Bool.and_false]
    split
    · rename_i heq
      rw [hu] at heq
      cases heq
      exact ⟨_, rfl⟩
    · rename_i heq
      rw [hu] at heq
      cases heq
  · intro ctx name scope pos blocks st k env hb hs he
    refine ⟨?_, fun hn args =>
      have b := fun inner (hs : SameScope inner (envInto ctx k args)) =>
        envInto_below (inner := inner) args he hn hs
      ⟨b _ ⟨rfl, rfl, rfl, rfl, rfl⟩, b _ ⟨rfl, rfl, rfl, rfl, rfl⟩⟩⟩
    rw [elabEnvArm]
    generalize openLengthScope ctx scope = o
    rcases o with ⟨saved, body, h1, h2, h3⟩
    simp only [blockEnvBuiltin, Bool.or_eq_false_iff, Option.isSome_eq_false_iff,
      Option.isNone_iff_eq_none] at hb
    simp only [hb, Bool.false_eq_true, ↓reduceIte, Bool.or_false,
      Option.isSome_none, Option.isNone_none, Bool.true_and]
    rw [show ∀ f : ESt → EM (Array Block), StateT.run (get >>= f) st = StateT.run (f st) st
      from fun _ => rfl]
    simp only [hs, Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i hle
      have hg : (lookupUserEnv ctx name).get hle = (k, env) := by simp only [he, Option.get_some]
      simp only [hg, pure_bind]
      exact ⟨_, rfl⟩
    · rename_i hle
      simp [he] at hle

end LeanTex.Core.Elab
