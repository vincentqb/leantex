module

public import LeanTex.Core.Parse
public import LeanTex.Core.Ir

public section

namespace LeanTex.Core.PackageEnvs

open Parse

/-- framed.sty's hooks a document may redefine, which the template reads none of. -/
def framedHooks : List String :=
  ["FrameCommand", "FirstFrameCommand", "MidFrameCommand", "LastFrameCommand", "FrameRestore"]

/-- The framed.sty environments this module sets: the ruled frames and the shaded grounds. -/
def envs : List String := ["framed", "oframed", "shaded", "shaded*", "snugshade", "snugshade*"]

/-- latex.ltx's `\topsep` at the first list level of a standard class at `pt` points, as framed.sty's
`\OuterFrameSep` takes it. -/
def outerSep (pt : Nat) : String :=
  match Ir.listSkips .sizeFile (Dim.pt pt) 1 with
  | some s => s!"{s.topsep.width.fixed.toPtString}pt plus {s.topsep.stretch.fixed.toPtString}pt \
minus {s.topsep.shrink.fixed.toPtString}pt"
  | none => "0pt"

/-- What framed.sty's `\MakeFramed` sets for environment `n`: a box of `\fbox` (a 0.4pt rule
`\FrameSep` 9pt out) or `\colorbox{shadecolor}`, `snugshade`'s on the default `\fboxsep`, around a
minipage of the measure less the box's sides, `\OuterFrameSep` above and below. -/
def template (n : String) (pt : Nat) (bodySep : String) : String :=
  let outer := outerSep pt
  let framedLike := n == "framed" || n == "oframed"
  let box := if framedLike then "\\fbox" else "\\colorbox{shadecolor}"
  let sep := if n.startsWith "snugshade" then "3pt" else "9pt"
  -- the box stands within the measure, its text inset by its sides: shaded and snugshade's
  -- ground, which framed.sty bleeds into the margins around text at the measure, does not bleed
  let width := if framedLike then "18.8pt" else if sep == "3pt" then "6pt" else "18pt"
  s!"\\par\\vspace\{{outer}}\\noindent\{\\setlength\{\\fboxsep}\{{sep}}{box}\{\\begin\{minipage}\{\\dimexpr\\linewidth-{width}\\relax}\
\\setlength\{\\fboxsep}\{{bodySep}}\\zzframedbody\\end\{minipage}}}\\par\\vspace\{{outer}}"

private theorem toList_sizeOf_lt (b : Array Raw) : sizeOf b.toList < sizeOf b := by
  cases b; simp

/-- The template's raws at the environment's site `site`, its body mark replaced by `body`, at every
depth. -/
def fill (site : Pos) (body : Array Raw) (out : Array Raw) : List Raw → Array Raw
  | [] => out
  | .ctrl n _ :: rest => if n == "zzframedbody" then fill site body (out ++ body) rest
      else fill site body (out.push (.ctrl n site)) rest
  | .group b _ :: rest => fill site body (out.push (.group (fill site body #[] b.toList) site)) rest
  | .env n b _ :: rest => fill site body (out.push (.env n (fill site body #[] b.toList) site)) rest
  | .word w _ :: rest => fill site body (out.push (.word w site)) rest
  | .sym c _ :: rest => fill site body (out.push (.sym c site)) rest
  | .par _ :: rest => fill site body (out.push (.par site)) rest
  | r :: rest => fill site body (out.push r) rest
termination_by l => sizeOf l
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have := toList_sizeOf_lt b; omega)

/-- The template for `n` at `pt` points around `body`, its source read by `read`. -/
def raws (read : String → Array Raw) (n : String) (pt : Nat) (bodySep : String) (body : Array Raw)
    (site : Pos) : Array Raw :=
  fill site body #[] (read (template n pt bodySep)).toList

/-- The longtable markers that close a head or foot part: the first head, the head, the foot and the
last foot. -/
def longtableMarks : List String := ["endfirsthead", "endhead", "endfoot", "endlastfoot"]

/-- A longtable body's rows as one tabular sets them once: its first head (or its head), its rows
and its last foot (or its foot), the repeated parts a page break would set again dropped. -/
def longtableRows (body : Array Raw) : Array Raw := Id.run do
  let mut parts : Array (String × Array Raw) := #[]
  let mut cur : Array Raw := #[]
  for r in body do
    match r with
    | .ctrl n _ =>
      if longtableMarks.contains n then
        parts := parts.push (n, cur)
        cur := #[]
      -- a row `\kill` ends sizes the columns and sets nothing
      else if n == "kill" then
        let back := (cur.toList.reverse.dropWhile (!· matches .ctrl "\\" _)).reverse
        cur := back.toArray
      else cur := cur.push r
    | r => cur := cur.push r
  let part (n : String) : Option (Array Raw) := (parts.find? (·.1 == n)).map (·.2)
  let head := (part "endfirsthead").orElse fun _ => part "endhead"
  let foot := (part "endlastfoot").orElse fun _ => part "endfoot"
  return head.getD #[] ++ cur ++ foot.getD #[]

/-- A longtable as LaTeX sets it on one page: a centred tabular of its column spec and its rows. -/
def longtableRaws (body : Array Raw) (p : Pos) : Array Raw :=
  -- the optional `[c]`, `[l]` or `[r]` placement before the spec
  let (place, body) := if body[0]? matches some (Raw.sym '[' _) then
      let close := (body.findIdx? fun (r : Raw) => r matches Raw.sym ']' _).getD 0
      (rawSrc (body.extract 1 close), body.extract (close + 1) body.size)
    else ("c", body)
  let k := (body.findIdx? fun (r : Raw) => r matches Raw.group _ _).getD body.size
  let spec := body.extract 0 (k + 1)
  let env := match place.trimAscii.toString with
    | "l" => "flushleft"
    | "r" => "flushright"
    | _ => "center"
  #[.env env #[.env "tabular" (spec ++ longtableRows (body.extract (k + 1) body.size)) p] p]

/-- A document's framed.sty and longtable environments as their templates set them, at every depth,
where `pkgs` loads their package: its class at `pt` points, a frame's body at `\fboxsep` `bodySep`,
templates read by `read`. -/
def lower (read : String → Array Raw) (pkgs : List String) (pt : Nat) (bodySep : String)
    (out : Array Raw) : List Raw → Array Raw
  | [] => out
  | .env n b p :: rest =>
    let inner := lower read pkgs pt bodySep #[] b.toList
    if envs.contains n && pkgs.contains "framed" then
      lower read pkgs pt bodySep (out ++ raws read n pt bodySep inner p) rest
    else if n == "longtable" && pkgs.contains "longtable" then
      lower read pkgs pt bodySep (out ++ longtableRaws inner p) rest
    else lower read pkgs pt bodySep (out.push (.env n inner p)) rest
  | .group b p :: rest =>
    lower read pkgs pt bodySep (out.push (.group (lower read pkgs pt bodySep #[] b.toList) p)) rest
  | r :: rest => lower read pkgs pt bodySep (out.push r) rest
termination_by l => sizeOf l
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have := toList_sizeOf_lt b; omega)

/-- A command and a one-word group, as a package load stands, hold no environment to lower. -/
theorem lower_command_word (read : String → Array Raw) (pkgs : List String) (pt : Nat)
    (bodySep c w : String) (p q g : Pos) :
    lower read pkgs pt bodySep #[] [.ctrl c p, .group #[.word w q] g] =
      #[.ctrl c p, .group #[.word w q] g] := by
  simp [lower]

end LeanTex.Core.PackageEnvs
