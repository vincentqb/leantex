module

public import LeanTex.Cli.World
public import LeanTex.Cli.Host

/-! The font directories of the TeX distribution first on `PATH`, found without running
TeX or reading its configuration. -/

namespace LeanTex.Cli.TexFontTrees

open LeanTex.Cli.World

/-- The programs whose location names the distribution, in lookup order. -/
public def programs : List String := ["lualatex", "luatex", "tex"]

/-- The directory holding an absolute path; the root holds itself. -/
public def parent (p : String) : String :=
  let upTo := (p.toList.reverse.dropWhile (· != '/')).reverse
  let trimmed := (upTo.reverse.dropWhile (· == '/')).reverse
  if trimmed.isEmpty then "/" else String.ofList trimmed

/-- The trees of the distribution whose program's real path is `program`, in TeX's search
order: the user's (under `home`), the site's, then the distribution's, for the TeX Live,
packaged and MacPorts layouts. -/
public def trees (program : String) (home : Option String) : List String :=
  let pfx := parent (parent program)
  let root := parent pfx
  let up := parent root
  let user := ((home.filter (!·.isEmpty)).map fun h =>
    [ToolPath.join h "texmf", ToolPath.join h "Library/texmf"]).getD []
  user ++
    [ToolPath.join up "texmf-local", ToolPath.join pfx "share/texlive/texmf-local",
     ToolPath.join pfx "share/texmf-local", ToolPath.join pfx "local/share/texmf",
     ToolPath.join up "share/texmf-local",
     ToolPath.join pfx "share/texmf", ToolPath.join up "share/texmf",
     ToolPath.join root "texmf-dist", ToolPath.join pfx "share/texmf-dist",
     ToolPath.join pfx "share/texlive/texmf-dist", ToolPath.join up "share/texmf-texlive"]

/-- Every tree's OpenType directory, then every TrueType one, in kpathsea's order. -/
public def fontDirs (trees : List String) : List String :=
  trees.map (ToolPath.join · "fonts/opentype") ++ trees.map (ToolPath.join · "fonts/truetype")

/-- The colorprofiles package's directory in each tree, where l3pdfmeta finds the profiles it
describes. -/
public def profileDirs (trees : List String) : List String :=
  trees.map (ToolPath.join · "tex/generic/colorprofiles")

/-- The real path of the first of `names` that `PATH` reaches as a regular
file. -/
@[expose] public def programIn : List String → Prog (Option String)
  | [] => .pure none
  | name :: rest => ToolPath.located name >>= fun
    | (_, st) :: _ => .pure (some st.real)
    | [] => programIn rest

/-- The directories among `cs`, each spelled as first met, a directory two
of them reach through links searched once, in order. -/
@[expose] public def dirsGo (acc : Array (String × String)) : List String → Prog (Array (String × String))
  | [] => .pure acc
  | c :: cs => .ask (.stat c) fun st =>
    dirsGo (match st with
      | .ok s => if s.kind == .dir && !acc.any (·.2 == s.real) then acc.push (c, s.real) else acc
      | .error _ => acc) cs

/-- The first regular file named `name` in one of `dirs`, in order. -/
@[expose] public def firstFileIn (name : String) : List String → Prog (Option String)
  | [] => .pure none
  | d :: ds =>
    let p := ToolPath.join d name
    .ask (.stat p) fun st => match ToolPath.regular p st with
      | some _ => .pure (some p)
      | none => firstFileIn name ds

/-- The colorprofiles package's profile `name` in the TeX distribution on `PATH`, in its trees'
search order, the user's under `HOME` first; none when `PATH` reaches no TeX program or no tree
holds it. -/
@[expose] public def colorProfile (name : String) : Prog (Option String) :=
  .ask (.env "HOME") fun home => programIn programs >>= fun
    | none => .pure none
    | some program => firstFileIn name (profileDirs (trees program home))

/-- The font directories of the TeX distribution on `PATH` that exist, in
search order; none when `PATH` reaches no TeX program. -/
@[expose] public def roots (home : Option String) : Prog (List String) :=
  programIn programs >>= fun
    | none => .pure []
    | some program => (fun ds => ds.toList.map (·.1)) <$> dirsGo #[] (fontDirs (trees program home))

public theorem programIn_only (names : List String) : (programIn names).Only ToolPath.Lookup := by
  induction names with
  | nil => exact .pure _
  | cons name rest ih =>
    refine (ToolPath.located_only name).bind fun found => ?_
    cases found with
    | nil => exact ih
    | cons f _ => exact .pure _

public theorem dirsGo_only (acc : Array (String × String)) (cs : List String) :
    (dirsGo acc cs).Only ToolPath.Lookup := by
  induction cs generalizing acc with
  | nil => exact .pure acc
  | cons c cs ih => exact .ask (.stat c) _ trivial fun _ => ih _

public theorem roots_only (home : Option String) : (roots home).Only ToolPath.Lookup := by
  refine (programIn_only programs).bind fun program => ?_
  cases program with
  | none => exact .pure _
  | some p => exact (dirsGo_only #[] _).map _

/-- Finding the font directories starts no process. -/
public theorem roots_runless_exact (home : Option String) :
    (roots home).runM Host.answer = (roots home).runM Host.answerRunless :=
  Prog.runM_only_exact (roots_only home) Host.answer Host.answerRunless Host.answer_runless_exact

/-- A question finding a colour profile asks: a lookup's, or the user's home. -/
@[expose] public def ProfileAsk (q : Ask) : Prop := ToolPath.Lookup q ∨ q = .env "HOME"

private theorem onlyProfile {α : Type} {p : Prog α} (h : p.Only ToolPath.Lookup) :
    p.Only ProfileAsk := by
  induction h with
  | pure a => exact .pure a
  | ask q k hq _ ih => exact .ask q k (.inl hq) ih

public theorem firstFileIn_only (name : String) (ds : List String) :
    (firstFileIn name ds).Only ToolPath.Lookup := by
  induction ds with
  | nil => exact .pure _
  | cons d ds ih =>
    refine .ask (.stat (ToolPath.join d name)) _ trivial fun st => ?_
    cases ToolPath.regular (ToolPath.join d name) st with
    | some _ => exact .pure _
    | none => exact ih

public theorem colorProfile_only (name : String) : (colorProfile name).Only ProfileAsk := by
  refine .ask (.env "HOME") _ (.inr rfl) fun home => ?_
  refine (onlyProfile (programIn_only programs)).bind fun program => ?_
  cases program with
  | none => exact .pure _
  | some p => exact onlyProfile (firstFileIn_only name _)

/-- Finding a colour profile starts no process. -/
public theorem colorProfile_runless_exact (name : String) :
    (colorProfile name).runM Host.answer = (colorProfile name).runM Host.answerRunless :=
  Prog.runM_only_exact (colorProfile_only name) Host.answer Host.answerRunless fun q h => by
    rcases h with h | rfl
    · exact Host.answer_runless_exact q h
    · exact Host.answer_runless_of_ask _ rfl

/-- The font directories of the TeX distribution on this host's `PATH`. -/
public def hostRoots : IO (List String) := do
  let home ← IO.getEnv "HOME"
  ((roots home).runM Host.answer : BaseIO (List String))

end LeanTex.Cli.TexFontTrees
