module

public import LeanTex.Cli.PicCache

/-! The host as a vocabulary of questions. A `Prog` is a value: it asks, and
what it does next depends only on the replies, so one program runs against a
world given as a function (`Prog.run`) or against the machine (`Host.runIO`).
What a program learned from the world is the trace `Prog.record` keeps, and
`Prog.replay` answers it again from that trace alone. -/

namespace LeanTex.Cli.World

/-- Why the host could not answer: the path is not there, access was
refused, the path is not a regular file, or anything else, in the host's
words. -/
public inductive Failure where
  | absent
  | denied
  | notRegular
  | other (why : String)
  deriving DecidableEq, Repr

public inductive Kind where
  | file
  | dir
  | symlink
  | other
  deriving DecidableEq, Repr

/-- A path's metadata, symlinks followed, with its resolved real path. -/
public structure Stat where
  kind : Kind
  size : Nat
  mtimeSec : Int
  mtimeNsec : Nat
  real : String
  deriving DecidableEq, Repr

/-- One bounded tool run in a scratch directory of its own. `inputs` are
written there before the call and `outputs` read back after it, both named
relative to it; `env` changes the inherited environment. -/
public structure ToolCall where
  tool : String
  args : Array String
  inputs : Array (String × ByteArray) := #[]
  outputs : Array String := #[]
  budgetMs : Nat
  graceMs : Nat
  captureLimit : Nat
  env : Array (String × Option String) := #[]
  deriving DecidableEq

/-- How a run ended, what it printed, and each declared output (`none`
when it is not a regular file). `complete` is a run that exited within its
budget with both streams read to their end. -/
public structure Ended where
  ran : PicCache.Ran
  out : String
  err : String
  complete : Bool
  outputs : Array (String × Option ByteArray)
  deriving BEq

public inductive Ask where
  | env (name : String)
  | cwd
  | stat (path : String)
  | readFile (path : String)
  | listDir (path : String)
  | run (call : ToolCall)
  | writeAtomic (path : String) (bytes : ByteArray)
  | createDirAll (path : String)
  deriving DecidableEq

/-- What each question is answered with. A listing is sorted by name, and a
read refuses anything but a regular file. -/
@[expose, reducible] public def Reply : Ask → Type
  | .env _ => Option String
  | .cwd => Except Failure String
  | .stat _ => Except Failure Stat
  | .readFile _ => Except Failure ByteArray
  | .listDir _ => Except Failure (Array (String × Kind))
  | .run _ => Ended
  | .writeAtomic .. => Except Failure Unit
  | .createDirAll _ => Except Failure Unit

@[expose] public def Ask.isRun : Ask → Bool
  | .run _ => true
  | _ => false

/-- One answered question. -/
public abbrev Fact := (q : Ask) × Reply q

public inductive Prog (α : Type) where
  | pure (a : α)
  | ask (q : Ask) (k : Reply q → Prog α)

namespace Prog

@[expose] public def bind {α β : Type} : Prog α → (α → Prog β) → Prog β
  | .pure a, f => f a
  | .ask q k, f => .ask q fun r => bind (k r) f

public instance : Monad Prog where
  pure := Prog.pure
  bind := Prog.bind

public instance : LawfulMonad Prog := LawfulMonad.mk'
  (id_map := fun p => by
    induction p with
    | pure _ => rfl
    | ask q k ih => exact congrArg (Prog.ask q) (funext ih))
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun p f g => by
    induction p with
    | pure _ => rfl
    | ask q k ih => exact congrArg (Prog.ask q) (funext ih))

/-- The program's answer in a world given as a function. -/
@[expose] public def run {α : Type} (w : (q : Ask) → Reply q) : Prog α → α
  | .pure a => a
  | .ask q k => run w (k (w q))

/-- What the program asks that world, in order. -/
@[expose] public def asks {α : Type} (w : (q : Ask) → Reply q) : Prog α → List Ask
  | .pure _ => []
  | .ask q k => q :: asks w (k (w q))

/-- The program run by an interpreter: each question answered by `ans`. -/
@[expose] public def runM {m : Type → Type} [Monad m] {α : Type}
    (ans : (q : Ask) → m (Reply q)) : Prog α → m α
  | .pure a => Pure.pure a
  | .ask q k => ans q >>= fun r => runM ans (k r)

/-- `runM`, keeping every question with the reply it got. -/
@[expose] public def record {m : Type → Type} [Monad m] {α : Type}
    (ans : (q : Ask) → m (Reply q)) : Prog α → m (α × List Fact)
  | .pure a => Pure.pure (a, [])
  | .ask q k => ans q >>= fun r =>
    (fun (x : α × List Fact) => (x.1, ⟨q, r⟩ :: x.2)) <$> record ans (k r)

/-- The program answered from a trace, in order: a question the trace does
not hold next, or a trace that outlasts the program, is no answer. -/
@[expose] public def replay {α : Type} : Prog α → List Fact → Option α
  | .pure a, [] => some a
  | .pure _, _ :: _ => none
  | .ask _ _, [] => none
  | .ask q k, ⟨q', r⟩ :: tr => if h : q' = q then replay (k (h ▸ r)) tr else none

public theorem run_bind {α β : Type} (w : (q : Ask) → Reply q) (p : Prog α) (f : α → Prog β) :
    (p >>= f).run w = (f (p.run w)).run w := by
  induction p with
  | pure _ => rfl
  | ask q k ih => exact ih (w q)

public theorem run_map {α β : Type} (w : (q : Ask) → Reply q) (p : Prog α) (f : α → β) :
    (f <$> p).run w = f (p.run w) := by
  rw [← bind_pure_comp, run_bind]
  rfl

public theorem asks_bind {α β : Type} (w : (q : Ask) → Reply q) (p : Prog α) (f : α → Prog β) :
    (p >>= f).asks w = p.asks w ++ (f (p.run w)).asks w := by
  induction p with
  | pure _ => rfl
  | ask q k ih => exact congrArg (q :: ·) (ih (w q))

public theorem asks_map {α β : Type} (w : (q : Ask) → Reply q) (p : Prog α) (f : α → β) :
    (f <$> p).asks w = p.asks w := by
  rw [← bind_pure_comp, asks_bind]
  exact List.append_nil _

/-- **A program is determined by the replies it reads.** Two worlds that
agree on every question the program asks one of them give the same answer:
what the program never asked cannot move it. -/
public theorem run_replay_exact {α : Type} (p : Prog α) (w v : (q : Ask) → Reply q)
    (h : ∀ q ∈ p.asks w, v q = w q) : p.run v = p.run w := by
  induction p with
  | pure _ => rfl
  | ask q k ih =>
    have hq : v q = w q := h q List.mem_cons_self
    change (k (v q)).run v = (k (w q)).run w
    rw [hq]
    exact ih (w q) fun q' hq' => h q' (List.mem_cons_of_mem q hq')

/-- **The interpreter over a pure world is `run`.** Tests' worlds and the
host run one interpreter. -/
public theorem runM_exact {α : Type} (p : Prog α) (w : (q : Ask) → Reply q) :
    p.runM (m := Id) (fun q => Pure.pure (w q)) = p.run w := by
  induction p with
  | pure _ => rfl
  | ask q k ih => exact ih (w q)

public theorem replay_cons {α : Type} (q : Ask) (k : Reply q → Prog α) (r : Reply q)
    (tr : List Fact) : (Prog.ask q k).replay (⟨q, r⟩ :: tr) = (k r).replay tr := by
  simp [replay]

/-- **A recorded run is the replay of its own trace**, in any lawful monad:
every outcome `(a, tr)` of `record` satisfies `replay tr = some a`, stated as
the equation that pairs each outcome with that proposition. -/
public theorem record_replay_exact {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type}
    (ans : (q : Ask) → m (Reply q)) (p : Prog α) :
    (fun x => (x, p.replay x.2 = some x.1)) <$> p.record ans =
      (fun x => (x, True)) <$> p.record ans := by
  induction p with
  | pure a => simp [record, replay]
  | ask q k ih =>
    simp only [record, map_bind]
    refine congrArg (ans q >>= ·) (funext fun r => ?_)
    have h := congrArg
      (Functor.map fun (y : (α × List Fact) × Prop) =>
        ((y.1.1, (⟨q, r⟩ : Fact) :: y.1.2), y.2)) (ih r)
    simpa only [Functor.map_map, Function.comp_def, replay_cons] using h

end Prog

/-- One question as a program. -/
@[expose] public def ask (q : Ask) : Prog (Reply q) := .ask q .pure

namespace ToolPath

@[expose] public def isFile : Except Failure Stat → Bool
  | .ok st => st.kind == .file
  | .error _ => false

/-- A name inside a directory, with one separator between them. -/
@[expose] public def join (dir name : String) : String :=
  if dir.endsWith "/" then dir ++ name else dir ++ "/" ++ name

/-- The directory one PATH entry names: an empty entry is the working
directory, a relative one is joined to it, and both are skipped when the
working directory is unavailable. -/
@[expose] public def entryDir (cwd : Except Failure String) (entry : String) : Option String :=
  if entry.isEmpty then cwd.toOption
  else if entry.startsWith "/" then some entry
  else cwd.toOption.map (join · entry)

/-- POSIX's candidates for a command name: a name with a slash is itself,
an unset PATH names nothing, and otherwise each entry in order. -/
@[expose] public def candidates (tool : String) (path : Option String)
    (cwd : Except Failure String) : List String :=
  if tool.contains '/' then [tool]
  else match path with
    | none => []
    | some p => (p.splitOn ":").filterMap fun e => (entryDir cwd e).map (join · tool)

/-- The first candidate whose stat is a regular file, with that stat. -/
@[expose] public def firstFile : List String → Prog (Option (String × Stat))
  | [] => .pure none
  | c :: cs => .ask (.stat c) fun st =>
    match st with
    | .ok s => if s.kind == .file then .pure (some (c, s)) else firstFile cs
    | .error _ => firstFile cs

@[expose] public def locate (tool : String) : Prog (Option (String × Stat)) :=
  if tool.contains '/' then firstFile [tool]
  else .ask (.env "PATH") fun
    | none => .pure none
    | some p => .ask .cwd fun cwd => firstFile (candidates tool (some p) cwd)

/-- The first regular file the command name reaches. No process is started:
mode bits are not readable here, so a regular file the OS would refuse to
execute is still the answer (`probe` is execvp's whole rule). -/
@[expose] public def resolve (tool : String) : Prog (Option String) :=
  (·.map (·.1)) <$> locate tool

/-- The resolution decision as a function of what the host says. -/
@[expose] public def select (tool : String) (path : Option String) (cwd : Except Failure String)
    (stat : String → Except Failure Stat) : Option String :=
  (candidates tool path cwd).find? fun c => isFile (stat c)

/-- The executable's identity as the font cache keys a face: resolved path,
size and modification time. -/
@[expose] public def stamp (st : Stat) : String :=
  String.intercalate "\t" [st.real, toString st.size, toString st.mtimeSec, toString st.mtimeNsec]

/-- The stamp of `resolve`'s answer, empty when there is none. -/
@[expose] public def witness (tool : String) : Prog String :=
  (fun | none => "" | some (_, st) => stamp st) <$> locate tool

/-- Lean's spawn reports an exec that failed, before the tool ran at all, as
exit 255 with exactly this line on standard error. -/
@[expose] public def execFailed (exe : String) (e : Ended) : Bool :=
  e.ran == .exited 255 && e.err == "could not execute external process '" ++ exe ++ "'\n"

/-- Run each regular candidate in order until one starts, as execvp does:
a candidate the OS refuses to execute comes back with the exec-failure
signature, and the next is tried. -/
@[expose] public def probeGo (call : String → ToolCall) :
    List String → Prog (Option (String × Ended))
  | [] => .pure none
  | c :: cs => .ask (.stat c) fun st =>
    if isFile st then
      .ask (.run (call c)) fun e => if execFailed c e then probeGo call cs else .pure (some (c, e))
    else probeGo call cs

/-- `probeGo` over the command name's candidates. A run happens in its own
scratch directory, so a relative candidate is anchored to the working
directory first. -/
@[expose] public def probe (tool : String) (call : String → ToolCall) :
    Prog (Option (String × Ended)) :=
  if tool.contains '/' then
    if tool.startsWith "/" then probeGo call [tool]
    else .ask .cwd fun
      | .ok d => probeGo call [join d tool]
      | .error _ => .pure none
  else .ask (.env "PATH") fun
    | none => .pure none
    | some p => .ask .cwd fun cwd => probeGo call (candidates tool (some p) cwd)

/-- A version question's operational ceiling: two seconds, then 100 ms for
the process group to stop, and 64 KiB per stream. -/
public def versionBudgetMs : Nat := 2000

@[expose] public def versionCall (budgetMs : Nat) (exe : String) : ToolCall :=
  { tool := exe, args := #["--version"], budgetMs, graceMs := 100, captureLimit := 65536 }

/-- Ask the tool who it is, read as `PicCache.probed` reads one attempt:
the first line of what the candidate that started printed. -/
@[expose] public def version (tool : String) (budgetMs : Nat := versionBudgetMs) :
    Prog PicCache.Tool :=
  (fun
    | none => .absent "no executable file by this name on PATH"
    | some (_, e) => PicCache.probed e.ran ((e.out.splitOn "\n").headD "").trimAscii.toString)
  <$> probe tool (versionCall budgetMs)

public theorem firstFile_find (w : (q : Ask) → Reply q) (cs : List String) :
    ((firstFile cs).run w).map (·.1) = cs.find? fun c => isFile (w (.stat c)) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    change (Prog.run w (match w (.stat c) with
      | .ok s => if s.kind == .file then .pure (some (c, s)) else firstFile cs
      | .error _ => firstFile cs)).map (·.1) = _
    cases h : w (.stat c) with
    | ok s =>
      cases hk : s.kind == .file
      · simpa [h, hk, isFile, List.find?] using ih
      · simp [h, hk, isFile, Prog.run, List.find?]
    | error _ => simpa [h, isFile, List.find?] using ih

/-- **Resolution is the decision `select` names**, over whatever the host
says about PATH, the working directory and each candidate's stat. -/
public theorem resolve_select_exact (tool : String) (w : (q : Ask) → Reply q) :
    (resolve tool).run w = select tool (w (.env "PATH")) (w .cwd) (fun c => w (.stat c)) := by
  unfold resolve select
  rw [Prog.run_map]
  unfold locate
  by_cases hs : tool.contains '/' = true
  · simp only [hs, ite_true]
    rw [firstFile_find]
    simp [candidates, hs]
  · simp only [hs]
    change Option.map _ (Prog.run w (match w (.env "PATH") with
      | none => .pure none
      | some p => .ask .cwd fun cwd => firstFile (candidates tool (some p) cwd))) = _
    cases hp : w (.env "PATH") with
    | none => simp [candidates, hs, Prog.run]
    | some p =>
      change ((firstFile (candidates tool (some p) (w .cwd))).run w).map (·.1) = _
      rw [firstFile_find]

/-- **Resolution is the first PATH candidate whose stat is a regular file**,
under POSIX's splitting (`candidates`). With `probe`'s fall-through past a
candidate the OS refuses, this is execvp's choice. -/
public theorem select_exact (tool c : String) (w : (q : Ask) → Reply q) :
    (resolve tool).run w = some c ↔
      isFile (w (.stat c)) = true ∧ ∃ pre post,
        candidates tool (w (.env "PATH")) (w .cwd) = pre ++ c :: post ∧
        ∀ d ∈ pre, isFile (w (.stat d)) = false := by
  rw [resolve_select_exact, select, List.find?_eq_some_iff_append]
  simp

public theorem entryDir_error (e : Failure) (x : String) :
    entryDir (.error e) x = if x.startsWith "/" = true then some x else none := by
  unfold entryDir
  by_cases he : x.isEmpty = true
  · have hx : x = "" := String.isEmpty_iff.mp he
    subst hx
    have h0 : "".startsWith "/" = false := by simp
    simp only [he, h0, ite_true, Bool.false_eq_true, ite_false]
    rfl
  · simp only [he, Bool.false_eq_true, ite_false]
    by_cases hs : x.startsWith "/" = true
    · simp only [hs, ite_true]
    · simp only [hs, Bool.false_eq_true, ite_false]
      rfl

/-- **Without a working directory, only absolute entries are candidates.** -/
public theorem candidates_absolute_exact (tool p : String) (e : Failure)
    (h : tool.contains '/' = false) :
    candidates tool (some p) (.error e) =
      ((p.splitOn ":").filter (·.startsWith "/")).map (join · tool) := by
  simp only [candidates, h, Bool.false_eq_true, ite_false, entryDir_error]
  induction p.splitOn ":" with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : x.startsWith "/" = true
    · simp only [List.filterMap_cons, hx, ite_true, Option.map_some, List.filter_cons,
        List.map_cons, ih]
    · simp only [List.filterMap_cons, hx, Bool.false_eq_true, ite_false, Option.map_none,
        List.filter_cons, ih]

public theorem firstFile_asks_mem (w : (q : Ask) → Reply q) (cs : List String) (q : Ask)
    (h : q ∈ (firstFile cs).asks w) : ∃ p, q = .stat p := by
  induction cs with
  | nil => simp [firstFile, Prog.asks] at h
  | cons c cs ih =>
    change q ∈ .stat c :: Prog.asks w (match w (.stat c) with
      | .ok s => if s.kind == .file then .pure (some (c, s)) else firstFile cs
      | .error _ => firstFile cs) at h
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨c, rfl⟩
    · cases hw : w (.stat c) with
      | ok s =>
        rw [hw] at h
        by_cases hk : s.kind = .file
        · simp [hk, Prog.asks] at h
        · simp only [hk, beq_iff_eq, ite_false] at h
          exact ih h
      | error _ =>
        rw [hw] at h
        exact ih h

public theorem locate_asks_mem (tool : String) (w : (q : Ask) → Reply q) (q : Ask)
    (h : q ∈ (locate tool).asks w) : q = .env "PATH" ∨ q = .cwd ∨ ∃ p, q = .stat p := by
  unfold locate at h
  by_cases hs : tool.contains '/' = true
  · simp only [hs, ite_true] at h
    exact .inr (.inr (firstFile_asks_mem w _ q h))
  · simp only [hs] at h
    change q ∈ .env "PATH" :: Prog.asks w (match w (.env "PATH") with
      | none => .pure none
      | some p => .ask .cwd fun cwd => firstFile (candidates tool (some p) cwd)) at h
    rcases List.mem_cons.mp h with rfl | h
    · exact .inl rfl
    · cases hp : w (.env "PATH") with
      | none =>
        rw [hp] at h
        simp [Prog.asks] at h
      | some p =>
        rw [hp] at h
        change q ∈ .cwd :: (firstFile (candidates tool (some p) (w .cwd))).asks w at h
        rcases List.mem_cons.mp h with rfl | h
        · exact .inr (.inl rfl)
        · exact .inr (.inr (firstFile_asks_mem w _ q h))

/-- **Resolving starts no process**: every question it asks, in any world,
is PATH, the working directory, or a stat. -/
public theorem resolve_asks_mem (tool : String) (w : (q : Ask) → Reply q) (q : Ask)
    (h : q ∈ (resolve tool).asks w) : q = .env "PATH" ∨ q = .cwd ∨ ∃ p, q = .stat p := by
  rw [resolve, Prog.asks_map] at h
  exact locate_asks_mem tool w q h

/-- **Taking a witness starts no process**, for the same reason. -/
public theorem witness_asks_mem (tool : String) (w : (q : Ask) → Reply q) (q : Ask)
    (h : q ∈ (witness tool).asks w) : q = .env "PATH" ∨ q = .cwd ∨ ∃ p, q = .stat p := by
  rw [witness, Prog.asks_map] at h
  exact locate_asks_mem tool w q h

/-- **The probe answers with the first candidate that started**: a regular
file whose run is not the exec-failure signature, every candidate before it
either not a regular file or refused by the OS. -/
public theorem probeGo_exact (call : String → ToolCall) (w : (q : Ask) → Reply q)
    (cs : List String) (c : String) (e : Ended) :
    (probeGo call cs).run w = some (c, e) ↔
      ∃ pre post, cs = pre ++ c :: post ∧ isFile (w (.stat c)) = true ∧
        e = w (.run (call c)) ∧ execFailed c e = false ∧
        ∀ d ∈ pre, isFile (w (.stat d)) = false ∨ execFailed d (w (.run (call d))) = true := by
  induction cs with
  | nil => simp [probeGo, Prog.run]
  | cons d ds ih =>
    change Prog.run w (if isFile (w (.stat d)) then
        .ask (.run (call d)) fun e =>
          if execFailed d e then probeGo call ds else .pure (some (d, e))
      else probeGo call ds) = some (c, e) ↔ _
    constructor
    · intro hrun
      by_cases hf : isFile (w (.stat d)) = true
      · simp only [hf, ite_true] at hrun
        change Prog.run w (if execFailed d (w (.run (call d))) then probeGo call ds
          else .pure (some (d, w (.run (call d))))) = some (c, e) at hrun
        by_cases hx : execFailed d (w (.run (call d))) = true
        · simp only [hx, ite_true] at hrun
          obtain ⟨pre, post, hds, hc, he, hne, hpre⟩ := ih.mp hrun
          refine ⟨d :: pre, post, by simp [hds], hc, he, hne, ?_⟩
          intro d' hd'
          rcases List.mem_cons.mp hd' with rfl | hd'
          · exact .inr hx
          · exact hpre d' hd'
        · simp only [hx, Bool.false_eq_true, ite_false, Prog.run, Option.some.injEq,
            Prod.mk.injEq] at hrun
          obtain ⟨rfl, rfl⟩ := hrun
          exact ⟨[], ds, rfl, hf, rfl, by simpa using hx, by simp⟩
      · simp only [hf, Bool.false_eq_true, ite_false] at hrun
        obtain ⟨pre, post, hds, hc, he, hne, hpre⟩ := ih.mp hrun
        refine ⟨d :: pre, post, by simp [hds], hc, he, hne, ?_⟩
        intro d' hd'
        rcases List.mem_cons.mp hd' with rfl | hd'
        · exact .inl (by simpa using hf)
        · exact hpre d' hd'
    · rintro ⟨pre, post, hcs, hc, he, hne, hpre⟩
      cases pre with
      | nil =>
        obtain ⟨rfl, rfl⟩ := List.cons.inj hcs
        subst he
        simp [hc, hne, Prog.run]
      | cons d0 pre =>
        have hd : d = d0 := (List.cons.inj hcs).1
        have hds : ds = pre ++ c :: post := (List.cons.inj hcs).2
        have hrest : (probeGo call ds).run w = some (c, e) :=
          ih.mpr ⟨pre, post, hds, hc, he, hne, fun x hx => hpre x (List.mem_cons_of_mem _ hx)⟩
        have hhead := hpre d0 List.mem_cons_self
        rw [← hd] at hhead
        rcases hhead with hf | hx
        · simp only [hf, Bool.false_eq_true, ite_false]
          exact hrest
        · by_cases hf : isFile (w (.stat d)) = true
          · simp only [hf, ite_true]
            change Prog.run w (if execFailed d (w (.run (call d))) then probeGo call ds
              else .pure (some (d, w (.run (call d))))) = some (c, e)
            simp only [hx, ite_true]
            exact hrest
          · simp only [hf, Bool.false_eq_true, ite_false]
            exact hrest

end ToolPath

end LeanTex.Cli.World
