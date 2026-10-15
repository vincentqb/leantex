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

/-- A browser script's text with its comments and every string and template literal's
contents blanked. -/
def jsCode (js : String) : String := Id.run do
  let mut quote : Option Char := none
  let mut escaped := false
  let mut line := false
  let mut block := false
  let mut prev := ' '
  let mut acc : List Char := []
  for c in js.toList do
    if line then
      if c == '\n' then line := false; acc := c :: acc else acc := ' ' :: acc
    else if block then
      if prev == '*' && c == '/' then block := false
      acc := (if c == '\n' then c else ' ') :: acc
    else match quote with
      | some q =>
        if c == '\n' then
          if q != '`' then quote := none
          escaped := false
        else if escaped then escaped := false
        else if c == '\\' then escaped := true
        else if c == q then quote := none
        acc := (if quote.isNone || c == '\n' then c else ' ') :: acc
      | none =>
        if prev == '/' && c == '/' then line := true; acc := ' ' :: ' ' :: acc.drop 1
        else if prev == '/' && c == '*' then block := true; acc := ' ' :: ' ' :: acc.drop 1
        else
          if c == '"' || c == '\'' || c == '`' then quote := some c
          acc := c :: acc
    prev := c
  return String.ofList acc.reverse

/-- The waits in a browser script whose time its run's budget does not set: a `timeout` option, a
delay or default timeout not written in `STEP_MS` or `HARD_MS`, a numeric `polling`, a
`networkidle` wait, and every `waitForTimeout` sleep. -/
def fixedWaits (js : String) : Array String := Id.run do
  let budgeted (e : String) : Bool := hasStr e "STEP_MS" || hasStr e "HARD_MS"
  let rest (s : String) : List Char := s.toList.dropWhile (· == ' ')
  let code := jsCode js
  let mut acc : Array String := #[]
  for piece in (code.splitOn "timeout").drop 1 do
    if let ':' :: cs := rest piece then
      let value := String.ofList (cs.takeWhile fun c => c != ',' && c != '}' && c != ')' && c != '\n')
      unless budgeted value do acc := acc.push s!"timeout:{value.trimAscii}"
  for name in ["setTimeout", "setInterval", "setDefaultTimeout", "setDefaultNavigationTimeout"] do
    for piece in (code.splitOn name).drop 1 do
      if let '(' :: cs := rest piece then
        let delay := lastArgument (String.ofList cs)
        unless budgeted delay do acc := acc.push s!"{name}(…, {delay})"
  for piece in (code.splitOn "polling").drop 1 do
    if let ':' :: cs := rest piece then
      if (cs.dropWhile (· == ' ')).head?.any Char.isDigit then acc := acc.push "polling"
  for _ in (js.splitOn "networkidle").drop 1 do
    acc := acc.push "networkidle"
  for _ in (js.splitOn "waitForTimeout").drop 1 do
    acc := acc.push "waitForTimeout"
  return acc

/-- The bodies of every raw string literal in a source, in order. -/
def rawStrings (src : String) : Array String :=
  ((src.splitOn "r#\"").drop 1).toArray.map fun piece => (piece.splitOn "\"#").headD ""

/-- The browser oracle's probe judges a page by its events under budgets its run declares: no
wait in it is a fixed wall-clock time, each context it opens takes its waits' budget, and its
browser's launch is held to the same. -/
def oracleWaitChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let src ← IO.FS.readFile "scripts/html-oracle.lean"
  let probe := ((src.splitOn "def probeJs : String := ").getD 1 "" |> rawStrings).getD 0 ""
  let js := String.intercalate "\n" (rawStrings src).toList
  t "oracle waits: the probe is found" (hasStr probe "deckLinks")
  t s!"oracle waits: no wait in the oracle's browser scripts is a fixed wall-clock time ({fixedWaits js})"
    ((fixedWaits js).isEmpty && hasStr js probe)
  let count (needle : String) : Nat := (probe.splitOn needle).length - 1
  t "oracle waits: every context the probe opens takes its waits' budget"
    (count "newContext(" > 0 && count "newContext(" == count "budgeted(await browser.newContext(" &&
      count "browser.newPage(" == 0 && hasStr probe "ctx.setDefaultTimeout(STEP_MS);" &&
      hasStr probe "ctx.setDefaultNavigationTimeout(STEP_MS);")
  t "oracle waits: the browser's launch is held to the waits' budget"
    (count ".launch(" == 1 && count "launch({ headless: true, timeout: 2 * STEP_MS," == 1)
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
      ("clearTimeout(watchdog); ctx.setDefaultTimeout(STEP_MS);", 0),
      ("page.setDefaultTimeout(2500); ctx.setDefaultNavigationTimeout(30000);", 2),
      ("const T = 2500; page.waitForFunction(f, x, {timeout: T});", 1),
      ("setInterval(f, 100); setTimeout(r, .5);", 2),
      ("page.waitForFunction(f, x, {polling: 2500});", 1),
      ("page.goto(u, {waitUntil: 'networkidle'});", 1),
      ("setTimeout(r, STEP_MS / 100); out('t', `timeout: ${n}`);", 0)] do
    t s!"oracle waits: the judge finds {want} fixed waits in {js}" ((fixedWaits js).size == want)

end Tests
