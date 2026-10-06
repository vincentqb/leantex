module

import Init.System.IO

namespace LeanTex.Cli.AtomicFile

private def stage (part : System.FilePath) (bytes : ByteArray) : IO Unit := do
  -- Ownership starts only after the exclusive open succeeds. The handle
  -- closes when this helper returns, before the destination is replaced.
  let file ← IO.FS.Handle.mk part .writeNew
  try
    file.write bytes
    file.flush
  catch error =>
    discard <| (IO.FS.removeFile part).toBaseIO
    throw error

/-- Stage beside the destination, then rename. The destination's parent
must already exist. A name collision leaves the other writer's file intact. -/
public def write (target : System.FilePath) (bytes : ByteArray) : IO Unit := do
  let pid ← IO.Process.getPID
  let nonce ← IO.monoNanosNow
  let part := (target.parent.getD ".") / s!".leantex-{pid}-{nonce}.part"
  stage part bytes
  try
    IO.FS.rename part target
  catch error =>
    -- After a successful rename the name is free for another writer;
    -- cleanup belongs only to failures while this attempt still owns it.
    discard <| (IO.FS.removeFile part).toBaseIO
    throw error

end LeanTex.Cli.AtomicFile
