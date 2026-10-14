module

public import Tests.Support

public section

namespace Tests

/-- The text of a call's last argument, from just inside its opening parenthesis to its closing
one: what follows its last top-level comma. -/
def lastArgument (call : String) : String := Id.run do
  let mut depth : Nat := 0
  let mut quote : Option Char := none
  let mut escaped := false
  let mut acc : List Char := []
  for c in call.toList do
    match quote with
    | some q =>
      acc := c :: acc
      if escaped then escaped := false
      else if c == '\\' then escaped := true
      else if c == q then quote := none
    | none =>
      if c == ')' || c == ']' || c == '}' then
        if depth == 0 then return (String.ofList acc.reverse).trimAscii.toString
        depth := depth - 1
        acc := c :: acc
      else if c == ',' && depth == 0 then acc := []
      else
        if c == '(' || c == '[' || c == '{' then depth := depth + 1
        if c == '"' || c == '\'' || c == '`' then quote := some c
        acc := c :: acc
  return ""

/-- The fixed wall-clock waits in a browser script's text: a `timeout` option or a `setTimeout`
delay given as a number, and every `waitForTimeout` sleep. -/
def fixedWaits (js : String) : Array String := Id.run do
  let rest (s : String) : List Char := s.toList.dropWhile (· == ' ')
  let numeric (cs : List Char) : Bool :=
    match cs.dropWhile (· == ' ') with
    | c :: _ => c.isDigit
    | [] => false
  let mut acc : Array String := #[]
  for piece in (js.splitOn "timeout").drop 1 do
    if let ':' :: cs := rest piece then
      if numeric cs then
        acc := acc.push s!"timeout:{(String.ofList ((cs.takeWhile (· != '}')).take 12)).trimAsciiEnd}"
  for _ in (js.splitOn "waitForTimeout").drop 1 do
    acc := acc.push "waitForTimeout"
  for piece in (js.splitOn "setTimeout").drop 1 do
    if let '(' :: cs := rest piece then
      let delay := lastArgument (String.ofList cs)
      if numeric delay.toList then acc := acc.push s!"setTimeout(…, {delay})"
  return acc

/-- The body of the raw string a source binds after `opener`, up to the first `"#`. -/
def rawStringAfter (src opener : String) : String :=
  match src.splitOn opener with
  | _ :: rest :: _ => (rest.splitOn "\"#").headD ""
  | _ => ""

/-- The browser oracle's probe judges a page by its events under budgets its run declares: no
wait in it is a fixed wall-clock time, each context it opens takes its waits' budget, and its
browser's launch is held to the same. -/
def oracleWaitChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let probe := rawStringAfter (← IO.FS.readFile "scripts/html-oracle.lean") "def probeJs : String := r#\""
  t "oracle waits: the probe is found" (hasStr probe "deckLinks")
  t s!"oracle waits: no wait in the probe is a fixed wall-clock time ({fixedWaits probe})"
    (fixedWaits probe).isEmpty
  let count (needle : String) : Nat := (probe.splitOn needle).length - 1
  t "oracle waits: every context the probe opens takes its waits' budget"
    (count "newContext(" > 0 && count "newContext(" == count "budgeted(await browser.newContext(" &&
      count "browser.newPage(" == 0 && hasStr probe "ctx.setDefaultTimeout(STEP_MS);" &&
      hasStr probe "ctx.setDefaultNavigationTimeout(STEP_MS);")
  t "oracle waits: the browser's launch is held to the waits' budget"
    (count ".launch(" == 1 && count "launch({ headless: true, timeout: STEP_MS," == 1)
  for (js, want) in [
      ("page.waitForFunction(f, x, {timeout: 2500});", 1),
      ("page.goto(u, { waitUntil: 'load', timeout:30000 });", 1),
      ("await page.waitForTimeout(100);", 1),
      ("await new Promise(r => setTimeout(r, 100));", 1),
      ("setTimeout(() => { f(a, ')'); g([1, 2]); }, 2500);", 1),
      ("page.goto(u, { timeout : 30000 }); setTimeout (r, 50); page.waitForTimeout (9);", 3),
      ("out('error', 'hard timeout'); out('x', 'a timeout: of 9');", 0),
      ("setTimeout(() => { out('budget', String(HARD_MS)); }, HARD_MS);", 0),
      ("pw.chromium.launch({ headless: true, timeout: STEP_MS });", 0),
      ("clearTimeout(watchdog); ctx.setDefaultTimeout(STEP_MS);", 0)] do
    t s!"oracle waits: the judge finds {want} fixed waits in {js}" ((fixedWaits js).size == want)

end Tests
