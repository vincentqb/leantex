/-
Regenerates bench/lorem.tex: a deterministic, lualatex-compatible document
of justified prose, large enough to make timing differences visible. Run with:

  lake env lean --run scripts/gen-lorem.lean
-/

def words : Array String := #[
  "typesetting", "algorithm", "paragraph", "internationalization",
  "demonstration", "hyphenation", "measurement", "considerable",
  "arrangement", "optimization", "representation", "understanding",
  "development", "infrastructure", "characteristic", "responsibility",
  "configuration", "transformation", "implementation", "documentation"]

def main : IO Unit := do
  IO.FS.createDirAll "bench"
  let mut lines : Array String := #["\\documentclass{article}", "\\begin{document}", ""]
  for p in [1:151] do
    let mut line := "The quick brown fox says:"
    for s in [1:61] do
      line := line ++ " " ++ words.getD ((p * 7 + s * 13) % 20) ""
    lines := lines.push (line ++ " again and again.")
    lines := lines.push ""
  lines := lines.push "\\end{document}"
  let content := String.intercalate "\n" lines.toList ++ "\n"
  IO.FS.writeFile "bench/lorem.tex" content
  IO.println s!"{content.utf8ByteSize} bench/lorem.tex"
