module

import Init.System.IO

namespace LeanTex.Cli.AtomicFile

private def stage (part : System.FilePath) (bytes : ByteArray) : IO Unit := do
  let file ← IO.FS.Handle.mk part .writeNew
  try
    file.write bytes
    file.flush
  catch error =>
    discard <| (IO.FS.removeFile part).toBaseIO
    throw error

/-- Write `bytes` to `target` atomically, staged beside it and renamed; the parent must
exist. -/
public def write (target : System.FilePath) (bytes : ByteArray) : IO Unit := do
  let pid ← IO.Process.getPID
  let nonce ← IO.monoNanosNow
  let part := (target.parent.getD ".") / s!".leantex-{pid}-{nonce}.part"
  stage part bytes
  try
    IO.FS.rename part target
  catch error =>
    discard <| (IO.FS.removeFile part).toBaseIO
    throw error

end LeanTex.Cli.AtomicFile
