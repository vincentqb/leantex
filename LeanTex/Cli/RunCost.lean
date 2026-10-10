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

/-- The most memory this process has held resident, in KiB: since it started,
or since the last `resetPeak` that succeeded. On Linux that is the high-water
mark of the image's own address space (`VmHWM`): `getrusage`'s maximum carries
the spawning process's resident set across fork and exec, so a run started by
a 300 MB parent read 314 MB there. Elsewhere it is the maximum the toolchain's
resource usage reports, in KiB. Tools the run spawns are not included. `none`
when the platform answers neither, so a summary never states a zero it did not
measure. -/
public def peakKiB : IO (Option Nat) := do
  if let .ok status ← (IO.FS.readFile "/proc/self/status").toBaseIO then
    if let some kib := highWaterKiB status then return some kib
  try
    let kib := (← Std.IO.Process.getResourceUsage).peakResidentSetSizeKb.toNat
    return if kib == 0 then none else some kib
  catch _ =>
    return none

/-- Start a new peak: on Linux, lower the high-water mark to what the process
holds now (`/proc/self/clear_refs`, value 5), so the next `peakKiB` is the most
it held from here on. What it holds now counts: memory earlier work freed stays
resident for reuse. `false` where the platform has no such reset, and the peak
stays the process's lifetime one. -/
public def resetPeak : IO Bool := do
  try
    IO.FS.writeFile "/proc/self/clear_refs" "5"
    return true
  catch _ =>
    return false

end LeanTex.Cli.RunCost
