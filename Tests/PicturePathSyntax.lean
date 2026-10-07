import Tests.Support

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-- Endpoint spelling conserves the shipped path: foreach substitution,
relative coordinates and additive calc coordinates agree with their explicit
coordinates. A midway label stays attached to its segment on either side of
the endpoint; a trailing label without a position stands at the endpoint.
An orthogonal midway label stays at the corner even when a leg has zero length.
Unsupported operations and options still name their losses.
All content is invented; the witnesses read Layout.Out and typed SVG. -/
def picturePathSyntaxChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let nodes :=
    "\\node[draw,minimum width=10mm,minimum height=8mm,inner sep=0pt,outer sep=0pt] (n) at (0,0) {N};\n" ++
    "\\node[draw,minimum width=10mm,minimum height=8mm,inner sep=0pt,outer sep=0pt] (e) at (3,0) {E};\n" ++
    "\\node[draw,minimum width=10mm,minimum height=8mm,inner sep=0pt,outer sep=0pt] (s) at (3,2) {S};\n" ++
    "\\node[draw,minimum width=10mm,minimum height=8mm,inner sep=0pt,outer sep=0pt] (w) at (0,2) {W};\n"
  let src (body : String) (opts : String := "") :=
    "\\documentclass{article}\\pictures{tool=none}\\begin{document}\n" ++
    "\\begin{tikzpicture}" ++ opts ++ "\n" ++ nodes ++ body ++
    "\n\\useasboundingbox (-4,-3) rectangle (7,5);\n\\end{tikzpicture}\n\\end{document}"
  let page (body : String) (opts : String := "") := layoutOf oneFace (elabStr (src body opts)).1
  let points (out : Layout.Out) : Array (Nat × Array Int) :=
    out.pages.flatMap fun p => p.paths.filterMap fun q => match q.path with
      | .segs ss => some (0, ss.flatMap fun seg => match seg with
        | .line x y u v => #[x, y, u, v]
        | .cubic x y a b c d u v => #[x, y, a, b, c, d, u, v])
      | .tri x y u v a b => some (1, #[x, y, u, v, a, b])
      | .rect .. | .circle .. => none
  let counts (out : Layout.Out) : Nat × Nat :=
    out.pages.foldl (fun acc p => p.paths.foldl (fun (acc : Nat × Nat) q => match q.path with
      | .segs ss => (acc.1 + ss.size, acc.2)
      | .tri .. => (acc.1, acc.2 + 1)
      | .rect .. | .circle .. => acc) acc) (0, 0)
  let close (a b : Array (Nat × Array Int)) : Bool :=
    a.size == b.size && (a.zip b).all fun ((ka, xs), (kb, ys)) =>
      ka == kb && xs.size == ys.size && (xs.zip ys).all fun (x, y) =>
        -- Two separately rounded offsets differ from one rounded sum by
        -- at most two sp; the page's y flip preserves that bound.
        decide (x - y ≤ 2 ∧ y - x ≤ 2)
  let svg (body : String) (opts : String := "") : Array String :=
    (elabStr (src body opts)).1.body.foldl (fun acc b =>
      acc ++ attrValuesOf (· == "path") "d" (HtmlDoc.blockNode {} b)) #[]
  let losses (body : String) : Array Diag :=
    (elabStr (src body)).2.filter fun d => d.code == "E0333" || d.code == "W0334"
  let cases : Array (String × String × String × Nat × Nat) := #[
    ("word tuple bindings",
      "\\foreach \\u/\\v in {n/e,e/s,s/w} \\draw[->] (\\u) -- (\\v);",
      "\\draw[->] (n) -- (e);\\draw[->] (e) -- (s);\\draw[->] (s) -- (w);", 3, 3),
    ("word tuple anchor suffixes",
      "\\foreach \\u/\\v in {n/e,w/s} \\draw (\\u.west) -- (\\v.east);",
      "\\draw (n.west) -- (e.east);\\draw (w.west) -- (s.east);", 2, 0),
    ("anchor names as tuple values",
      "\\foreach \\u/\\v in {n.west/e.east,w.west/s.east} \\draw (\\u) -- (\\v);",
      "\\draw (n.west) -- (e.east);\\draw (w.west) -- (s.east);", 2, 0),
    ("mixed symbolic and numeric tuples",
      "\\foreach \\u/\\v/\\d in {n/e/1,w/s/2} \\draw (\\u.west) -- ++(-\\d,0) |- (\\v.west);",
      "\\draw (n.west) -- (-1.5,0) -- (e.west);\\draw (w.west) -- (-2.5,2) -- (s.west);", 4, 0),
    ("numeric tuple expressions",
      "\\foreach \\u/\\v in {0/0,3/2} \\draw (\\u,\\v) -- (\\u+1,\\v+1);",
      "\\draw (0,0) -- (1,1);\\draw (3,2) -- (4,3);", 2, 0),
    ("numeric macros and nested arithmetic",
      "\\pgfmathsetmacro{\\u}{2}\\pgfmathsetmacro{\\v}{1}\\draw (min(\\u,3),\\v) -- (\\u+1,\\v*2);",
      "\\draw (2,1) -- (3,2);", 1, 0),
    ("relative then vertical-horizontal",
      "\\draw[->] (n.west) -- ++(-0.7,0) |- (w.west);",
      "\\draw[->] (n.west) -- (-1.2,0) -- (-1.2,2) -- (w.west);", 3, 1),
    ("relative then horizontal-vertical",
      "\\draw[->] (n.north) -- ++(0,0.6) -| (e.north);",
      "\\draw[->] (n.north) -- (0,1) -- (3,1) -- (e.north);", 3, 1),
    ("single plus preserves relative base",
      "\\draw (1,1) -- +(1,0) -- +(0,1) -- ++(-1,0) -- +(0,-1);",
      "\\draw (1,1) -- (2,1) -- (1,2) -- (0,1) -- (0,0);", 4, 0),
    ("absolute endpoint resets relative base",
      "\\draw (1,1) -- ++(1,0) -- (4,3) -- ++(-1,-1);",
      "\\draw (1,1) -- (2,1) -- (4,3) -- (3,2);", 3, 0),
    ("initial relative coordinate",
      "\\draw ++(1,2) -- ++(2,0);", "\\draw (1,2) -- (3,2);", 1, 0),
    ("relative numeric tuple",
      "\\foreach \\u/\\v in {1/2,2/1} \\draw (0,0) -- ++(\\u,\\v) |- ++(1,1);",
      "\\draw (0,0) -- (1,2) -- (1,3) -- (2,3);\\draw (0,0) -- (2,1) -- (2,2) -- (3,2);", 6, 0),
    ("orthogonal node borders",
      "\\draw[->] (n) |- (s);", "\\draw[->] (n) -- (0,2) -- (s);", 2, 1),
    ("orthogonal zero final leg keeps arrow",
      "\\draw[->] (0,0) |- (0,2);", "\\draw[->] (0,0) -- (0,2);", 1, 1),
    ("orthogonal zero initial leg keeps node borders",
      "\\draw[->] (n) |- (e);", "\\draw[->] (n) -- (e);", 1, 1),
    ("calc named anchor offsets",
      "\\draw[->] ($(n.west)+(-0.7,0)$) -- ($(w.west)+(-0.7,0)$);",
      "\\draw[->] (-1.2,0) -- (-1.2,2);", 1, 1),
    ("calc numeric sum and subtraction",
      "\\draw ($(1,2)+(2,-1)-(1,0)$) -- ($(3,1)+(1,2)$);",
      "\\draw (2,1) -- (4,3);", 1, 0),
    ("calc bindings and relative chaining",
      "\\pgfmathsetmacro{\\d}{0.7}\\foreach \\u/\\v in {n/w} " ++
        "\\draw ($(\\u.west)+(-\\d,0)$) -- ++(0,1) |- ($(\\v.west)+(-\\d,0)$);",
      "\\draw (-1.2,0) -- (-1.2,1) -- (-1.2,2);", 2, 0),
    ("trailing midway label",
      "\\draw (0,0) -- (3,2) node[midway,above] {Tag};",
      "\\draw (0,0) -- node[above] {Tag} (3,2);", 1, 0),
    ("calc trailing midway label",
      "\\draw[->] ($(n.west)+(-0.7,0)$) -- ($(w.west)+(-0.7,0)$) node[midway,above] {Tag};",
      "\\draw[->] (-1.2,0) -- node[above] {Tag} (-1.2,2);", 1, 1)]
  for (name, written, explicit, segments, tips) in cases do
    let got := page written
    let want := page explicit
    t s!"path syntax: {name} ships its segments and tips"
      (counts got == (segments, tips) && counts want == (segments, tips) &&
        close (points got) (points want))
    t s!"path syntax: {name} agrees in typed SVG"
      (!(svg explicit).isEmpty && svg written == svg explicit)
    t s!"path syntax: {name} names no unsupported syntax" (losses written).isEmpty
    if name.contains "label" then
      let labels (out : Layout.Out) := (bodyLines out).filter (lineText · == "Tag")
      t s!"path syntax: {name} ships its text at the segment"
        (match (labels got).toList, (labels want).toList with
         | [a], [b] => decide (a.x - b.x ≤ 2 ∧ b.x - a.x ≤ 2 ∧ a.y - b.y ≤ 2 ∧ b.y - a.y ≤ 2)
         | _, _ => false)
  let labelPoints (body : String) :=
    ((bodyLines (page body)).filter (lineText · == "Tag")).map fun line => (line.x, line.y)
  let svgLabel (body : String) :=
    ((elabStr (src body)).1.body.flatMap fun b =>
      elemNodesOne (· == "text") #[] (HtmlDoc.blockNode {} b)).filterMap fun n =>
        if nodeTextOne "" n != "Tag" then none else
        match n with
        | .elem _ attrs _ => some attrs
        | .text _ | .style _ | .script _ _ => none
  -- PGF §17.8 and tikz@timer@vhline/hvline: pos=.5 is the corner,
  -- irrespective of either leg's length. A LuaLaTeX probe confirms every
  -- corner below, including the reversals and the zero-leg endpoints.
  for (name, start, op, finish, corner) in #[
      ("vh", "(0,0)", "|-", "(3,2)", "(0,2)"),
      ("vh reverse", "(3,2)", "|-", "(0,0)", "(3,0)"),
      ("hv", "(0,0)", "-|", "(3,2)", "(3,0)"),
      ("hv reverse", "(3,2)", "-|", "(0,0)", "(0,2)"),
      ("vh zero first", "(0,0)", "|-", "(3,0)", "(0,0)"),
      ("vh zero first reverse", "(3,0)", "|-", "(0,0)", "(3,0)"),
      ("vh zero final", "(0,0)", "|-", "(0,2)", "(0,2)"),
      ("vh zero final reverse", "(0,2)", "|-", "(0,0)", "(0,0)"),
      ("hv zero first", "(0,0)", "-|", "(0,2)", "(0,0)"),
      ("hv zero first reverse", "(0,2)", "-|", "(0,0)", "(0,2)"),
      ("hv zero final", "(0,0)", "-|", "(3,0)", "(3,0)"),
      ("hv zero final reverse", "(3,0)", "-|", "(0,0)", "(0,0)")] do
    for trailing in [false, true] do
      let tag := " node[midway,above] {Tag} "
      let written := "\\draw " ++ start ++ " " ++ op ++
        (if trailing then " " else tag) ++ finish ++ (if trailing then tag else "") ++ ";"
      -- An explicit endpoint fixes the expected position independently of
      -- the orthogonal operation's interpolation and leg simplification.
      let explicit := "\\path (0,0) -- " ++ corner ++ " node[above] {Tag};"
      t s!"path syntax: orthogonal {name}, trailing={trailing}, Layout.Out corner"
        ((labelPoints written).size == 1 && (labelPoints explicit).size == 1 &&
          labelPoints written == labelPoints explicit && (losses written).isEmpty)
      t s!"path syntax: orthogonal {name}, trailing={trailing}, typed SVG corner"
        ((svgLabel written).size == 1 && (svgLabel explicit).size == 1 &&
          svgLabel written == svgLabel explicit)
  let scaled := "\\draw ($(1,1)+(1,0)$) -- ++(1,1) |- (4,1);"
  let scaledExplicit := "\\draw (2,1) -- (3,2) -- (3,1) -- (4,1);"
  t "path syntax: calc and relative offsets scale once"
    (counts (page scaled "[scale=0.8]") == (3, 0) &&
      close (points (page scaled "[scale=0.8]")) (points (page scaledExplicit "[scale=0.8]")) &&
      svg scaled "[scale=0.8]" == svg scaledExplicit "[scale=0.8]")
  let scaledNamed := "\\draw[->] ($(n.west)+(-1,0)$) -- ($(w.west)+(-1,0)$);"
  let scaledNamedExplicit := "\\draw[->] (-1.625,0) -- (-1.625,2);"
  t "path syntax: scaled calc does not rescale named anchors"
    (counts (page scaledNamed "[scale=0.8]") == (1, 1) &&
      close (points (page scaledNamed "[scale=0.8]")) (points (page scaledNamedExplicit "[scale=0.8]")) &&
      svg scaledNamed "[scale=0.8]" == svg scaledNamedExplicit "[scale=0.8]")
  let endLabel := "\\draw (0,0) -- (3,2) node[above] {Tag};"
  let halfwayLabel := "\\draw (0,0) -- node[above] {Tag} (6,4);"
  t "path syntax: trailing label defaults to endpoint"
    (counts (page endLabel) == (1, 0) && (losses endLabel).isEmpty &&
      match ((bodyLines (page endLabel)).filter (lineText · == "Tag")).toList,
          ((bodyLines (page halfwayLabel)).filter (lineText · == "Tag")).toList with
      | [a], [b] => a.x == b.x && a.y == b.y
      | _, _ => false)
  let rotated := "\\draw[->] ($(n.west)+(-0.7,0)$) -- ($(w.west)+(-0.7,0)$) " ++
    "node[midway,rotate=90,above] {Tag};"
  t "path syntax: unsupported rotation still names its loss and keeps edge and label"
    (counts (page rotated) == (1, 1) &&
      (bodyLines (page rotated)).any (lineText · == "Tag") &&
      (losses rotated).any (fun d => d.code == "W0334" && hasStr d.message "'rotate'") &&
      !((losses rotated).any (·.code == "E0333")))
  for (body, code, word) in #[
      ("\\draw (absent) -- (e);", "E0333", "absent"),
      ("\\draw (n.mystery) -- (e);", "W0334", "mystery"),
      ("\\draw (\\missing) -- (e);", "E0333", "missing"),
      ("\\draw (0,0) -- (1/0,2);", "E0333", "zero"),
      ("\\draw (n) arc (e);", "W0334", "arc"),
      ("\\draw ($(n)!0.5!(e)$) -- (s);", "W0334", "calc"),
      ("\\draw ($(n)+(0,1)*2$) -- (s);", "W0334", "calc"),
      ("\\draw (0,0) -- node {One} (2,1) node[midway] {Two};", "W0334", "multiple")] do
    t s!"path syntax: unsupported {word} stays diagnosed without a partial edge"
      ((losses body).any (fun d => d.code == code && hasStr d.message word) &&
        counts (page body) == (0, 0))
