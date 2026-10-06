import Init.System.IO

namespace LeanTex.Cli.AtomicFile

/-- Stage beside the destination, then rename. The destination's parent
must already exist; cleanup removes only this attempt's staging directory. -/
def write (target : System.FilePath) (bytes : ByteArray) : IO Unit :=
  IO.FS.withTempDir fun nonce => do
    let part := (target.parent.getD ".") / ("." ++ nonce.fileName.getD "tmp" ++ ".part")
    -- createDir is exclusive. Even a stale name collision fails closed.
    IO.FS.createDir part
    try
      let value := part / "value"
      IO.FS.writeBinFile value bytes
      IO.FS.rename value target
    finally
      IO.FS.removeDirAll part

end LeanTex.Cli.AtomicFile
