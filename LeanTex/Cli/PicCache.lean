import LeanTex.Core.Diag

/-! Pure boundary outcomes and tool-version memo policy. `PictureAssets`
captures process results; `ConvCache` stores complete drawings or refusals.
Unfinished attempts are retried. -/

namespace LeanTex.Cli.PicCache

/-- How one boundary process ended. `exited` is the tool's own exit — it
ran to a decision; `overran` is the wall-clock budget spent with the
process killed; `unstarted` is a spawn that raised. The last two say
nothing about the request, only about the machine. -/
inductive Ran where
  | exited (code : Nat)
  | overran (seconds : Nat)
  | unstarted (err : String)
  deriving BEq, Repr

/-- What the tool left behind of one attempt: its log's last words, or no
log at all. A tool that never ran writes nothing — a spawn that reached
`exec` and failed there still comes back as an exit code — so the log's
presence is the platform-independent evidence that the tool formed an
opinion rather than that the machine lacks it. -/
inductive Log where
  | absent
  | says (tail : String)
  deriving BEq, Repr

/-- The log's last words, empty when there is no log. -/
def Log.tail : Log → String
  | .absent => ""
  | .says t => t

/-- What the tool answered about one request. `drawn` is a PDF; `refused`
is the tool's own no, carrying its last words verbatim; `inconclusive` is
an attempt that never reached an answer. -/
inductive Outcome where
  | drawn
  | refused (says : String)
  | inconclusive (says : String)
  deriving BEq, Repr

/-- One attempt read as a verdict: the process's ending, whether a PDF
landed, and what the tool left in its log. An exit the tool chose *and
left a log for* is a verdict — nonzero with its last words, or zero with
nothing drawn. A budget kill, a failed spawn, and a nonzero exit that left
no log at all are not: each says something about the machine, and a machine
without the tool installed must not be able to make a picture look
unrenderable. -/
def outcome (ran : Ran) (drew : Bool) (log : Log) : Outcome :=
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

/-- What the cache keeps of an outcome: the tool's own refusal, and
nothing else. A drawn picture is kept as its PDF, and an inconclusive
attempt is kept not at all — so the next build retries it. -/
def remembers : Outcome → Option String
  | .drawn => none
  | .refused says => some says
  | .inconclusive _ => none

/-- What asking the tool who it is came back with. `present` is the tool's
own answer — it ran and named a version; `absent` is every other ending,
because none of them identifies a tool: a machine with nothing installed
still reaches `exec` and comes back as a nonzero exit, and its stdout is
not empty but whatever the forked child inherited, so the exit code is the
only signal worth reading. A tool that cannot say who it is cannot have a
slot keyed by its version, and a request it never saw is not a request it
refused. -/
inductive Tool where
  | absent (why : String)
  | present (version : String)
  deriving BEq, Repr

/-- One `--version` attempt read as the tool's identity: a clean exit that
named something is the tool, and nothing else is. `firstLine` is the first
line of what the probe wrote — trusted only on a clean exit, since a failed
`exec` hands back a child's inherited buffer rather than silence. -/
def probed (ran : Ran) (firstLine : String) : Tool :=
  match ran with
  | .exited 0 =>
    if firstLine = "" then .absent "no version line" else .present firstLine
  | .exited c => .absent s!"'--version' exited {c}"
  | .overran s => .absent s!"no version within {s} s; killed"
  | .unstarted e => .absent e

/-- **A tool that did not exit cleanly is not an identified tool.** The
statement whose absence sent a machine with no boundary tool installed down
the *refused* path: the probe read a nonzero exit as a version string, so a
picture no tool had ever looked at was reported as one the tool drew
nothing for — a dropped loss that fails the run, where the honest answer is
the degraded one, a placeholder and a warning naming the missing tool. -/
theorem probed_present_exact (ran : Ran) (firstLine version : String) :
    probed ran firstLine = .present version ↔
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

/-- **A nonzero exit names no version.** The half of `probed_present_exact`
the missing-tool machine lands on, spelled as the equation the driver's
routing reads. -/
theorem probed_absent_exact (c : Nat) (hc : c ≠ 0) (firstLine : String) :
    probed (.exited c) firstLine = .absent s!"'--version' exited {c}" := by
  unfold probed
  cases c with
  | zero => exact absurd rfl hc
  | succ _ => rfl

/-- Whether this run has to ask the tool who it is. -/
inductive VersionStep where
  | remembered (version : String)
  | probe
  deriving BEq, Repr

/-- Reuse a version only for its recorded, nonempty executable witness.
The witness comprises resolved path, size and modification time; this
assumes replacements change those observations. Result caches include both
the witness and version, so different executables reporting the same version
do not share answers. -/
def versionStep (memo : Option (String × String)) (witness : String) : VersionStep :=
  match memo with
  | some (w, v) =>
    if w = witness ∧ w ≠ "" ∧ v ≠ "" then .remembered v else .probe
  | none => .probe

/-- **A version is reused only for the witness it was recorded under.** -/
theorem versionStep_remembered_exact (memo : Option (String × String))
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

/-- **A tool that changed is asked again.** The upgrade half, stated as the
equation: a witness that does not match the recorded one sends the run back
to the tool, whose version then names fresh slots and re-renders every
picture. -/
theorem versionStep_changed_exact (w witness version : String) (h : w ≠ witness) :
    versionStep (some (w, version)) witness = .probe := by
  simp [versionStep, h]

/-- The remembered version as its file's two lines: the witness it was
recorded under, then the version the tool gave. -/
def versionMemo (witness version : String) : String := witness ++ "\n" ++ version

/-- The two lines back, or nothing when the file is not those two lines —
an unreadable memo asks the tool rather than guessing. -/
def readVersionMemo (text : String) : Option (String × String) :=
  match text.splitOn "\n" with
  | w :: v :: _ => if w = "" ∨ v = "" then none else some (w, v)
  | _ => none

/-- Where the remembered version lives, beside the slots it names. -/
def versionName (toolKey : String) : String := "tool-" ++ toolKey ++ ".ver"

/-- The cache slot one request takes: its content hash and the tool's
version, so an edited picture reads a different slot and is retried, and a
tool upgrade retries every one. -/
def stem (key version : String) : String := key ++ "-" ++ version

/-- The drawn PDF's name in the slot. -/
def pdfName (key version : String) : String := stem key version ++ ".pdf"

/-- The remembered refusal's name in the slot, beside the PDF: one slot
per request, whichever way the tool answered. -/
def failName (key version : String) : String := stem key version ++ ".fail"

/-- What a run does about one request. -/
inductive Step where
  | serve
  | replay (says : String)
  | run
  deriving BEq, Repr

/-- The cache decides in one place: a drawn PDF serves, else a remembered
refusal replays with the tool's own words, else the tool runs. -/
def step (drawn : Bool) (refusal : Option String) : Step :=
  if drawn then .serve
  else match refusal with
    | some says => .replay says
    | none => .run

/-- **A remembered verdict is never re-attempted.** The tool runs exactly
when the slot holds neither a drawn PDF nor a remembered refusal — the
invariant whose absence made every unrenderable picture pay a fresh
process on every build, forever, while a renderable one paid once. -/
theorem step_cold_exact (drawn : Bool) (refusal : Option String) :
    step drawn refusal = .run ↔ (drawn = false ∧ refusal = none) := by
  unfold step
  cases drawn with
  | true => simp
  | false => cases refusal <;> simp

/-- **A replay carries the tool's own words.** What a remembered refusal
reports is the string the tool gave, never a stand-in: the diagnostic
reads the same on the second build as on the first. -/
theorem replay_says_exact (says : String) :
    step false (some says) = .replay says := rfl

/-- **Only the tool's own refusal is remembered.** A verdict is written
exactly when the tool reached one and said no; a kill and a failed spawn
write nothing, so nothing the machine did can be mistaken for something
the request is. -/
theorem remembers_verdict_exact (o : Outcome) (says : String) :
    remembers o = some says ↔ o = .refused says := by
  cases o <;> simp [remembers]

/-- **A killed attempt is retried.** The composition of the two halves, at
the shape that matters: a budget overrun leaves the slot as it found it, so
the next build runs the tool again. -/
theorem overrun_retried_exact (s : Nat) (drew : Bool) (log : Log) :
    remembers (outcome (.overran s) drew log) = none := rfl

/-- **A tool that left no log is retried.** The other half of the same
guard, and the one a machine without the tool installed lands on: a spawn
that reached `exec` and failed there comes back as an exit code like any
other failure, so the absent log is what separates it from a verdict. Its
diagnostic still fires — the loss is named on every build — but the slot
stays empty, so installing the tool is all it takes. -/
theorem unlogged_retried_exact (c : Nat) (hc : c ≠ 0) (drew : Bool) :
    remembers (outcome (.exited c) drew .absent) = none := by
  unfold outcome remembers
  cases c with
  | zero => exact absurd rfl hc
  | succ _ => rfl

end LeanTex.Cli.PicCache
