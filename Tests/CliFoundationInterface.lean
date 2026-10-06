module

import LeanTex.Cli.Args
import LeanTex.Cli.AtomicFile
import LeanTex.Cli.Batch
import LeanTex.Cli.PublicationPaths
import LeanTex.Cli.SvgPoster

/-! Ordinary imports expose the command and executor APIs, without their
parser helpers, staging operation, or batching accumulator. -/

example : List String → Except String LeanTex.Cli.Config := LeanTex.Cli.parse
example : System.FilePath → ByteArray → IO Unit := LeanTex.Cli.AtomicFile.write
example : Array (String × String) → IO (Option String) :=
  LeanTex.Cli.PublicationPaths.conflict
example : String := LeanTex.Cli.SvgPoster.stylesheet

example [DecidableEq κ] (extra : Nat) (key : α → κ) (xs : List α) :
    (LeanTex.Cli.Batch.plan extra key xs).flatten = xs :=
  LeanTex.Cli.Batch.plan_exact extra key xs

example : True := by
  fail_if_success have := LeanTex.Cli.emitOne
  fail_if_success have := LeanTex.Cli.cssChoice
  fail_if_success have := LeanTex.Cli.colorMode
  fail_if_success have := LeanTex.Cli.AtomicFile.stage
  fail_if_success have := LeanTex.Cli.PublicationPaths.canonical
  fail_if_success have := LeanTex.Cli.Batch.takeBatch
  trivial
