module

import Std.Async.Process

namespace LeanTex.Cli.RunCost

/-- The `VmHWM` line of a Linux `/proc/self/status`, in KiB. -/
def highWaterKiB (status : String) : Option Nat :=
  (status.splitOn "\n").findSome? fun line =>
    if line.startsWith "VmHWM:" then
      match ((line.drop 6).toString.trimAscii.toString.splitOn " ") with
      | [n, "kB"] => n.toNat?
      | _ => none
    else none

/-- The most memory this process has held resident, in KiB, since it started or since the
last successful `resetPeak`; spawned tools are excluded, and `none` means the platform
cannot say. -/
public def peakKiB : IO (Option Nat) := do
  if let .ok status ← (IO.FS.readFile "/proc/self/status").toBaseIO then
    if let some kib := highWaterKiB status then return some kib
  try
    let kib := (← Std.IO.Process.getResourceUsage).peakResidentSetSizeKb.toNat
    return if kib == 0 then none else some kib
  catch _ =>
    return none

/-- Start a new peak by lowering the high-water mark to the current resident set; `false`
where the platform has no such reset. -/
public def resetPeak : IO Bool := do
  try
    IO.FS.writeFile "/proc/self/clear_refs" "5"
    return true
  catch _ =>
    return false

end LeanTex.Cli.RunCost
