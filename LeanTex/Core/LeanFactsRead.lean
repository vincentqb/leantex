module

public import LeanTex.Core.LeanFacts
public import LeanTex.Core.Diag
import LeanTex.Core.Json

/-! A page's facts as read: kept only where they line up with its file, else the code alone, with
the one note or warning that names what to run. -/

namespace LeanTex.Core.LeanFacts

open LeanTex.Core.JsonText (Json)

/-- What to run where a page's facts stand absent, no longer line up, or are of an older or a newer
schema than this leantex reads. -/
public structure Help where
  absent : String
  again : String
  update : String
  newer : String
  deriving Repr, Inhabited

/-- The note a page owes when no facts file stands where its facts are read from. -/
public def missing (file path help : String) : Diag :=
  Diag.of .N0032 (Diag.say .N0032 .facts path) (some ⟨file, {}⟩)
    (help := help) (subject := some s!"lean:{file}")

/-- The warning a page owes when its facts no longer line up with its file, or do not read. -/
public def stale (file path why help : String) : Diag :=
  Diag.of .W0433 (Diag.say .W0433 .facts path) (some ⟨file, {}⟩) (detail := some why)
    (help := help) (subject := some s!"lean:{file}")

/-- The schema a facts file's first line names, where it reads. -/
public def schemaOf (body : String) : Option Nat :=
  (body.splitOn "\n").head?.bind fun line =>
    (Json.parse line).toOption.bind fun h => (h.getObjValAs? Nat "leantex-lean-export").toOption

/-- The facts the bytes read at `path` give a page of `text`, if they read and line up with it,
with the note an absent file owes or the warning one that does not read or line up owes. -/
public def judge (file path text : String) (help : Help) (read : Option ByteArray) :
    Option Facts × Array Diag :=
  match read with
  | none => (none, #[missing file path help.absent])
  | some bytes =>
    match String.fromUTF8? bytes with
    | none => (none, #[stale file path "not UTF-8" help.again])
    | some body =>
      match decode body with
      | .ok facts =>
        if alignedWith facts text then (some facts, #[])
        else (none, #[stale file path "does not match the file" help.again])
      | .error why =>
        match schemaOf body with
        | some n =>
          if n < schemaVersion then
            (none, #[stale file path s!"schema {n}, older than this leantex's {schemaVersion}"
              help.update])
          else if n > schemaVersion then
            (none, #[stale file path s!"schema {n}, newer than this leantex's {schemaVersion}"
              help.newer])
          else (none, #[stale file path s!"unreadable: {why}" help.again])
        | none => (none, #[stale file path s!"unreadable: {why}" help.again])

/-- A page keeps facts only where they line up with its text. -/
public theorem judge_aligned {file path text : String} {help : Help}
    {read : Option ByteArray} {f : Facts} (h : (judge file path text help read).1 = some f) :
    alignedWith f text = true := by
  unfold judge at h
  repeat' split at h
  all_goals simp_all

end LeanTex.Core.LeanFacts
