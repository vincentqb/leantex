module

/-! How a boundary tool's attempt ended and what it answered, and the memo of the tool's
version. -/

namespace LeanTex.Cli.PicCache

/-- How one boundary process ended: its own exit, a budget overrun with the process
killed, or a spawn that raised. -/
public inductive Ran where
  | exited (code : Nat)
  | overran (seconds : Nat)
  | unstarted (err : String)
  deriving BEq, Repr

/-- What the tool left of one attempt: its log's last words, or no log, the evidence that
the tool reached an answer. -/
public inductive Log where
  | absent
  | says (tail : String)
  deriving BEq, Repr

/-- The log's last words, empty when there is no log. -/
@[expose] public def Log.tail : Log → String
  | .absent => ""
  | .says t => t

/-- What the tool answered about one request: a PDF, its own refusal in its last words, or
no answer. -/
public inductive Outcome where
  | drawn
  | refused (says : String)
  | inconclusive (says : String)
  deriving BEq, Repr

/-- One attempt read as a verdict: an exit the tool chose and left a log for is one; a
kill, a failed spawn or a nonzero exit without a log is inconclusive. -/
@[expose] public def outcome (ran : Ran) (drew : Bool) (log : Log) : Outcome :=
  let said (fallback : String) : String :=
    if log.tail.isEmpty then fallback else log.tail
  match ran with
  | .exited 0 => if drew then .drawn else .refused "no PDF was produced"
  | .exited c =>
    match log with
    | .absent => .inconclusive s!"exit code {c}"
    | .says _ => .refused (said s!"exit code {c}")
  | .overran s => .inconclusive (said s!"no result within {s} s; killed")
  | .unstarted e => .inconclusive (said e)

/-- The longest line of a tool's own words a reason carries. -/
public def saidLimit : Nat := 200

/-- The last nonblank line of `err`, cut at `saidLimit` characters and
marked: the tool's own words, for a reason that has no log to quote. -/
public def saidOf (err : String) : String :=
  let said := (((err.splitOn "\n").map (·.trimAscii.toString)).filter (!·.isEmpty)).getLastD ""
  if said.length > saidLimit then (said.take saidLimit).toString ++ "…" else said

/-- An attempt that reached no verdict and left no log also names `said`, the words its
tool wrote last; every other outcome is unchanged. -/
@[expose] public def annotate (o : Outcome) (log : Log) (said : String) : Outcome :=
  match o, log with
  | .inconclusive why, .absent => if said.isEmpty then o else .inconclusive s!"{why}: {said}"
  | o, _ => o

/-- What asking the tool its version came back with: its own answer, or an absence with
its reason. -/
public inductive Tool where
  | absent (why : String)
  | present (version : String)
  deriving BEq, Repr

/-- One `--version` attempt read as the tool's identity: only a clean exit naming
something is the tool. -/
public def probed (ran : Ran) (firstLine : String) (said : String := "") : Tool :=
  match ran with
  | .exited 0 =>
    if firstLine = "" then .absent "no version line" else .present firstLine
  | .exited c =>
    .absent (if said.isEmpty then s!"'--version' exited {c}" else s!"'--version' exited {c}: {said}")
  | .overran s => .absent s!"no version within {s} s; killed"
  | .unstarted e => .absent e

public theorem probed_present_exact (ran : Ran) (firstLine version said : String) :
    probed ran firstLine said = .present version ↔
      (ran = .exited 0 ∧ firstLine = version ∧ firstLine ≠ "") := by
  cases ran with
  | exited c =>
    cases c with
    | zero =>
      by_cases h : firstLine = ""
      · simp [probed, h]
      · simp [probed, h]
    | succ n => simp [probed]
  | overran _ => simp [probed]
  | unstarted _ => simp [probed]

public theorem probed_absent_exact (c : Nat) (hc : c ≠ 0) (firstLine said : String) :
    probed (.exited c) firstLine said = .absent (if said.isEmpty then s!"'--version' exited {c}"
      else s!"'--version' exited {c}: {said}") := by
  unfold probed
  cases c with
  | zero => exact absurd rfl hc
  | succ _ => rfl

/-- Whether this run has to ask the tool who it is. -/
public inductive VersionStep where
  | remembered (version : String)
  | probe
  deriving BEq, Repr

/-- Reuse a version only under its recorded, nonempty witness (resolved path, size,
modification time). -/
public def versionStep (memo : Option (String × String)) (witness : String) : VersionStep :=
  match memo with
  | some (w, v) =>
    if w = witness ∧ w ≠ "" ∧ v ≠ "" then .remembered v else .probe
  | none => .probe

public theorem versionStep_remembered_exact (memo : Option (String × String))
    (witness version : String) :
    versionStep memo witness = .remembered version ↔
      (memo = some (witness, version) ∧ witness ≠ "" ∧ version ≠ "") := by
  cases memo with
  | none => simp [versionStep]
  | some p =>
    obtain ⟨w, v⟩ := p
    by_cases hc : w = witness ∧ w ≠ "" ∧ v ≠ ""
    · obtain ⟨hw, hne, hvne⟩ := hc
      subst hw
      constructor
      · intro h
        have hv : v = version := by simpa [versionStep, hne, hvne] using h
        exact ⟨by rw [hv], hne, by rw [← hv]; exact hvne⟩
      · rintro ⟨he, -, -⟩
        have hv : v = version := by simpa using Option.some.inj he
        subst hv
        simp [versionStep, hne, hvne]
    · refine ⟨fun h => absurd h (by simp [versionStep, hc]), fun h => absurd ?_ hc⟩
      obtain ⟨he, hw, hv⟩ := h
      have hp : w = witness ∧ v = version := by simpa using Option.some.inj he
      exact ⟨hp.1, by rw [hp.1]; exact hw, by rw [hp.2]; exact hv⟩

public theorem versionStep_changed_exact (w witness version : String) (h : w ≠ witness) :
    versionStep (some (w, version)) witness = .probe := by
  simp [versionStep, h]

/-- The remembered version as its file's two lines: the witness it was
recorded under, then the version the tool gave. -/
public def versionMemo (witness version : String) : String := witness ++ "\n" ++ version

/-- The memo's two lines back, or nothing when the file is not those two lines. -/
public def readVersionMemo (text : String) : Option (String × String) :=
  match text.splitOn "\n" with
  | w :: v :: _ => if w = "" ∨ v = "" then none else some (w, v)
  | _ => none

/-- Where the remembered version lives, beside the slots it names. -/
public def versionName (toolKey : String) : String := "tool-" ++ toolKey ++ ".ver"

end LeanTex.Cli.PicCache
