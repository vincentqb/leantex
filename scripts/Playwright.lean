/-
The host's cached Playwright module and the Chromium it launches, for the scripts that drive a
browser.
-/

/-- The Playwright module directories to try: `LEANTEX_PLAYWRIGHT`, then every
`~/.npm/_npx/*/node_modules/playwright`. -/
def playwrightCandidates : IO (Array String) := do
  let mut out : Array String := #[]
  if let some p ← IO.getEnv "LEANTEX_PLAYWRIGHT" then out := out.push p
  if let some home ← IO.getEnv "HOME" then
    let npx : System.FilePath := home / ".npm" / "_npx"
    if ← npx.isDir then
      for e in (← npx.readDir).qsort (·.fileName < ·.fileName) do
        let m := e.path / "node_modules" / "playwright"
        if ← (m / "package.json").pathExists then out := out.push m.toString
  return out

/-- The module's declared version, from its package.json. -/
def moduleVersion (m : String) : IO String := do
  let pkg ← IO.FS.readFile (m ++ "/package.json")
  match (pkg.splitOn "\"version\": \"").drop 1 with
  | v :: _ => return ((v.splitOn "\"").headD "?")
  | [] => return "?"

/-- The first module whose Chromium launches on this host, with the version it reports. -/
def findChromium (node : String) : IO (Option (String × String)) := do
  for m in ← playwrightCandidates do
    let launch := "require(process.env.PW_MODULE).chromium.launch({headless:true,args:['--no-sandbox','--disable-gpu']})" ++
      ".then(b=>{console.log(b.version());return b.close()})" ++
      ".catch(e=>{console.error(String(e.message).split('\\n')[0]);process.exit(1)})"
    let out ← IO.Process.output
      { cmd := node
        args := #["-e", launch]
        env := #[("PW_MODULE", some m)] }
    if out.exitCode == 0 then
      return some (m, out.stdout.trimAscii.toString)
  return none
