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

/-- **Recording changes no result**: in any lawful monad, `record`'s answer
is `runM`'s, so the result of a run that kept no trace is still the replay
of the trace it would have kept (`record_replay_exact`). -/
public theorem record_fst_exact {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type}
    (ans : (q : Ask) → m (Reply q)) (p : Prog α) :
    Prod.fst <$> p.record ans = p.runM ans := by
  induction p with
  | pure a => simp [record, runM]
  | ask q k ih =>
    simp only [record, runM, map_bind, Functor.map_map]
    exact congrArg (ans q >>= ·) (funext ih)

/-- Every question the program can ask, whatever the replies before it,
satisfies `P`: a property of the whole tree, so it holds of every
interpreter, including a host that answers one question twice and
differently. -/
public inductive Only {α : Type} (P : Ask → Prop) : Prog α → Prop where
  | pure (a : α) : Only P (.pure a)
  | ask (q : Ask) (k : Reply q → Prog α) : P q → (∀ r, Only P (k r)) → Only P (.ask q k)

public theorem Only.bind {α β : Type} {P : Ask → Prop} {p : Prog α} {f : α → Prog β}
    (hp : p.Only P) (hf : ∀ a, (f a).Only P) : (p >>= f).Only P := by
  induction hp with
  | pure a => exact hf a
  | ask q k hq _ ih => exact .ask q (fun r => k r >>= f) hq ih

public theorem Only.map {α β : Type} {P : Ask → Prop} {p : Prog α} (f : α → β)
    (hp : p.Only P) : (f <$> p).Only P := by
  rw [← bind_pure_comp]
  exact hp.bind fun a => .pure (f a)

/-- In a world given as a function, every question asked satisfies `P`. -/
public theorem Only.asks {α : Type} {P : Ask → Prop} {p : Prog α} (h : p.Only P)
    (w : (q : Ask) → Reply q) : ∀ q ∈ p.asks w, P q := by
  induction h with
  | pure a => simp [Prog.asks]
  | ask q k hq _ ih =>
    intro q' hq'
    rcases List.mem_cons.mp hq' with rfl | hq'
    · exact hq
    · exact ih (w q) q' hq'

/-- **An interpreter is read only where the program can ask.** Two
interpreters that agree on every question satisfying `P` run a program that
asks only such questions as the same action. -/
public theorem runM_only_exact {m : Type → Type} [Monad m] {α : Type} {P : Ask → Prop}
    {p : Prog α} (h : p.Only P) (ans ans' : (q : Ask) → m (Reply q))
    (hag : ∀ q, P q → ans q = ans' q) : p.runM ans = p.runM ans' := by
  induction h with
  | pure a => rfl
  | ask q k hq _ ih =>
    change ans q >>= (fun r => runM ans (k r)) = ans' q >>= (fun r => runM ans' (k r))
    rw [hag q hq]
    exact congrArg (ans' q >>= ·) (funext ih)

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

/-- The paths execvp tries for a command name, anchored to the working
directory: a name with a slash is the one candidate, and otherwise each PATH
entry in order. An unset PATH is a search path the C library chooses — POSIX
leaves it to the implementation, and glibc's is `/bin:/usr/bin` — so it names
no candidate here: `probe` runs the bare name and lets that default decide
(`probe_unset_exact`). -/
@[expose] public def candidates (tool : String) (path : Option String)
    (cwd : Except Failure String) : List String :=
  if tool.contains '/' then (entryDir cwd tool).toList
  else match path with
    | none => []
    | some p => (p.splitOn ":").filterMap fun e => (entryDir cwd e).map (join · tool)

/-- The candidate with its stat, when that shows a regular file: the only
kind of file execve can start. -/
@[expose] public def regular (c : String) : Except Failure Stat → Option (String × Stat)
  | .ok s => if s.kind == .file then some (c, s) else none
  | .error _ => none

@[expose] public def regularGo (acc : Array (String × Stat)) :
    List String → Prog (Array (String × Stat))
  | [] => .pure acc
  | c :: cs => .ask (.stat c) fun st => regularGo (match regular c st with
      | some f => acc.push f
      | none => acc) cs

/-- A lookup's first questions: PATH unless the name has a slash, then the
working directory; the candidates follow from both, and `unset` is the
program for an unset PATH. -/
@[expose] public def lookup {β : Type} (tool : String) (unset : Prog β)
    (go : List String → Prog β) : Prog β :=
  if tool.contains '/' then .ask .cwd fun cwd => go (candidates tool none cwd)
  else .ask (.env "PATH") fun
    | none => unset
    | some p => .ask .cwd fun cwd => go (candidates tool (some p) cwd)

/-- Every regular file the command name reaches, in PATH order: the files
execvp could start. Mode bits are not readable here, so which of them starts
is `probe`'s question, and taking these starts no process
(`Host.located_runless_exact`). -/
@[expose] public def located (tool : String) : Prog (List (String × Stat)) :=
  (·.toList) <$> lookup tool (.pure #[]) (regularGo #[])

/-- The first of them: the file execvp starts unless the OS refuses it. -/
@[expose] public def resolve (tool : String) : Prog (Option String) :=
  (fun fs => fs.head?.map (·.1)) <$> located tool

/-- The resolution decision as a function of what the host says. -/
@[expose] public def select (tool : String) (path : Option String) (cwd : Except Failure String)
    (stat : String → Except Failure Stat) : Option String :=
  (candidates tool path cwd).find? fun c => isFile (stat c)

/-- One file's identity as the font cache keys a face: resolved path, size
and modification time. -/
@[expose] public def stamp (st : Stat) : String :=
  String.intercalate "\t" [st.real, toString st.size, toString st.mtimeSec, toString st.mtimeNsec]

/-- The identity of whichever file runs: the stamp of every regular file the
name reaches, in order. Any of them may be the one execvp starts
(`probe_located_mem`), so a change to any moves the witness; with exactly
one, it is that file's stamp. Empty when the name reaches none, or when PATH
is unset (`witness_unset_exact`). -/
@[expose] public def witness (tool : String) : Prog String :=
  (fun fs => "\t".intercalate (fs.map (stamp ·.2))) <$> located tool

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

/-- The bare name, run as it is: with PATH unset, the C library's default
search path decides. -/
@[expose] public def bare (tool : String) (call : String → ToolCall) :
    Prog (Option (String × Ended)) :=
  .ask (.run (call tool)) fun e => .pure (if execFailed tool e then none else some (tool, e))

/-- execvp's rule over `located`'s lookup: each regular candidate in order,
passing over one the OS refuses (`probeGo_exact`), or the bare name when
PATH is unset (`probe_unset_exact`). A run happens in a scratch directory of
its own, which is why the candidates are anchored to the working directory. -/
@[expose] public def probe (tool : String) (call : String → ToolCall) :
    Prog (Option (String × Ended)) :=
  lookup tool (bare tool call) (probeGo call)

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

/-- The regular files among the candidates, in order, each with its stat. -/
@[expose] public def found (w : (q : Ask) → Reply q) (cs : List String) : List (String × Stat) :=
  cs.filterMap fun c => regular c (w (.stat c))

public theorem regularGo_exact (w : (q : Ask) → Reply q) (acc : Array (String × Stat))
    (cs : List String) : ((regularGo acc cs).run w).toList = acc.toList ++ found w cs := by
  induction cs generalizing acc with
  | nil => simp [regularGo, found, Prog.run]
  | cons c cs ih =>
    change ((regularGo (match regular c (w (.stat c)) with
      | some f => acc.push f
      | none => acc) cs).run w).toList = _
    rw [ih]
    cases h : regular c (w (.stat c)) with
    | none => simp [found, h]
    | some f => simp [found, h]

public theorem candidates_slash_exact (tool : String) (p p' : Option String) (cwd : Except Failure String)
    (h : tool.contains '/' = true) : candidates tool p cwd = candidates tool p' cwd := by
  simp [candidates, h]

/-- **The lookup reads PATH, the working directory and one stat per
candidate**, and finds exactly the candidates' regular files. -/
public theorem located_exact (tool : String) (w : (q : Ask) → Reply q) :
    (located tool).run w = found w (candidates tool (w (.env "PATH")) (w .cwd)) := by
  unfold located lookup
  rw [Prog.run_map]
  by_cases hs : tool.contains '/' = true
  · simp only [hs, ite_true]
    change ((regularGo #[] (candidates tool none (w .cwd))).run w).toList = _
    rw [regularGo_exact, candidates_slash_exact tool none (w (.env "PATH")) _ hs]
    simp
  · simp only [hs, Bool.false_eq_true, ite_false]
    change (Prog.run w (match w (.env "PATH") with
      | none => .pure #[]
      | some p => .ask .cwd fun cwd => regularGo #[] (candidates tool (some p) cwd))).toList = _
    cases hp : w (.env "PATH") with
    | none => simp [Prog.run, candidates, hs, found]
    | some p =>
      change ((regularGo #[] (candidates tool (some p) (w .cwd))).run w).toList = _
      rw [regularGo_exact]
      simp

public theorem found_head_exact (w : (q : Ask) → Reply q) (cs : List String) :
    (found w cs).head?.map (·.1) = cs.find? fun c => isFile (w (.stat c)) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have hf : found w (c :: cs) = (match regular c (w (.stat c)) with
        | some f => f :: found w cs
        | none => found w cs) := by
      unfold found
      rw [List.filterMap_cons]
      cases regular c (w (.stat c)) <;> rfl
    rw [hf, List.find?_cons]
    cases h : w (.stat c) with
    | ok s =>
      by_cases hk : s.kind = .file
      · have hr : regular c (.ok s) = some (c, s) := by simp [regular, hk]
        have hi : isFile (.ok s) = true := by simp [isFile, hk]
        rw [hr, hi]
        rfl
      · have hr : regular c (.ok s) = none := by simp [regular, hk]
        have hi : isFile (.ok s) = false := by simp [isFile, hk]
        rw [hr, hi]
        exact ih
    | error _ => exact ih

/-- **Resolution is the decision `select` names**, over whatever the host
says about PATH, the working directory and each candidate's stat. -/
public theorem resolve_select_exact (tool : String) (w : (q : Ask) → Reply q) :
    (resolve tool).run w = select tool (w (.env "PATH")) (w .cwd) (fun c => w (.stat c)) := by
  simp only [resolve, select, Prog.run_map, located_exact, found_head_exact]

/-- **Resolution is the first candidate whose stat is a regular file**, under
POSIX's splitting (`candidates`). With `probe`'s fall-through past a
candidate the OS refuses, this is execvp's choice. -/
public theorem select_exact (tool c : String) (w : (q : Ask) → Reply q) :
    (resolve tool).run w = some c ↔
      isFile (w (.stat c)) = true ∧ ∃ pre post,
        candidates tool (w (.env "PATH")) (w .cwd) = pre ++ c :: post ∧
        ∀ d ∈ pre, isFile (w (.stat d)) = false := by
  rw [resolve_select_exact, select, List.find?_eq_some_iff_append]
  simp

/-- **The witness is the stamps of every regular file the name reaches.** -/
public theorem witness_exact (tool : String) (w : (q : Ask) → Reply q) :
    (witness tool).run w =
      "\t".intercalate ((found w (candidates tool (w (.env "PATH")) (w .cwd))).map (stamp ·.2)) := by
  unfold witness
  rw [Prog.run_map, located_exact]

/-- **An unset PATH gives no witness**: the default search path is the C
library's, and no stat can say which file it reaches. -/
public theorem witness_unset_exact (tool : String) (w : (q : Ask) → Reply q)
    (hs : tool.contains '/' = false) (hp : w (.env "PATH") = none) : (witness tool).run w = "" := by
  rw [witness_exact, hp]
  simp [candidates, hs, found]

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

/-- **The probe runs over `located`'s candidates** whenever PATH is set or
the name has a slash. -/
public theorem probe_exact (tool : String) (call : String → ToolCall) (w : (q : Ask) → Reply q)
    (h : tool.contains '/' = true ∨ (w (.env "PATH")).isSome = true) :
    (probe tool call).run w = (probeGo call (candidates tool (w (.env "PATH")) (w .cwd))).run w := by
  unfold probe lookup
  by_cases hs : tool.contains '/' = true
  · simp only [hs, ite_true]
    change (probeGo call (candidates tool none (w .cwd))).run w = _
    rw [candidates_slash_exact tool none (w (.env "PATH")) _ hs]
  · simp only [hs, Bool.false_eq_true, ite_false]
    have hp : (w (.env "PATH")).isSome = true := h.resolve_left hs
    change Prog.run w (match w (.env "PATH") with
      | none => bare tool call
      | some p => .ask .cwd fun cwd => probeGo call (candidates tool (some p) cwd)) = _
    cases hw : w (.env "PATH") with
    | none => simp [hw] at hp
    | some p => rfl

/-- **With PATH unset, the probe is the bare name's run**, so execvp's own
default search path decides, as it decides for every spawn by name. -/
public theorem probe_unset_exact (tool : String) (call : String → ToolCall)
    (w : (q : Ask) → Reply q) (hs : tool.contains '/' = false) (hp : w (.env "PATH") = none) :
    (probe tool call).run w =
      if execFailed tool (w (.run (call tool))) then none else some (tool, w (.run (call tool))) := by
  unfold probe lookup
  simp only [hs, Bool.false_eq_true, ite_false]
  change Prog.run w (match w (.env "PATH") with
    | none => bare tool call
    | some p => .ask .cwd fun cwd => probeGo call (candidates tool (some p) cwd)) = _
  rw [hp]
  rfl

/-- **Whatever the probe starts is among the located files**, so its stamp
is in the witness: the identity a memo or slot is keyed by covers the file
that ran, whichever regular file the OS accepted. -/
public theorem probe_located_mem (tool : String) (call : String → ToolCall)
    (w : (q : Ask) → Reply q) (c : String) (e : Ended)
    (h : tool.contains '/' = true ∨ (w (.env "PATH")).isSome = true)
    (hr : (probe tool call).run w = some (c, e)) :
    ∃ s, w (.stat c) = .ok s ∧ (c, s) ∈ (located tool).run w := by
  rw [probe_exact tool call w h, probeGo_exact] at hr
  obtain ⟨pre, post, hcs, hc, -, -, -⟩ := hr
  cases hw : w (.stat c) with
  | error _ => simp [isFile, hw] at hc
  | ok s =>
    refine ⟨s, rfl, ?_⟩
    have hk : s.kind = .file := by simpa [isFile, hw] using hc
    rw [located_exact, found, hcs]
    exact List.mem_filterMap.mpr ⟨c, by simp, by simp [regular, hw, hk]⟩

/-- A question a lookup may ask: PATH, the working directory, or a stat. -/
@[expose] public def Lookup : Ask → Prop
  | .env name => name = "PATH"
  | .cwd => True
  | .stat _ => True
  | _ => False

public theorem regularGo_only (acc : Array (String × Stat)) (cs : List String) :
    (regularGo acc cs).Only Lookup := by
  induction cs generalizing acc with
  | nil => exact .pure acc
  | cons c cs ih => exact .ask (.stat c) _ trivial fun _ => ih _

public theorem located_only (tool : String) : (located tool).Only Lookup := by
  unfold located lookup
  refine Prog.Only.map _ ?_
  by_cases hs : tool.contains '/' = true
  · simp only [hs, ite_true]
    exact .ask .cwd _ trivial fun _ => regularGo_only _ _
  · simp only [hs, Bool.false_eq_true, ite_false]
    refine .ask (.env "PATH") _ rfl fun r => ?_
    cases r with
    | none => exact .pure _
    | some p => exact .ask .cwd _ trivial fun _ => regularGo_only _ _

public theorem resolve_only (tool : String) : (resolve tool).Only Lookup :=
  (located_only tool).map _

public theorem witness_only (tool : String) : (witness tool).Only Lookup :=
  (located_only tool).map _

end ToolPath

end LeanTex.Cli.World
