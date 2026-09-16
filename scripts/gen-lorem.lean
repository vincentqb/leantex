/-
Regenerates bench/lorem.tex — a deterministic, lualatex-compatible document
of justified prose, large enough to make timing differences visible — and
bench/underline.tex, the same prose with every word underlined, so the
per-glyph ink decode sits on the measured path. Run with:

  lake env lean --run scripts/gen-lorem.lean
-/

def words : Array String := #[
  "typesetting", "algorithm", "paragraph", "internationalization",
  "demonstration", "hyphenation", "measurement", "considerable",
  "arrangement", "optimization", "representation", "understanding",
  "development", "infrastructure", "characteristic", "responsibility",
  "configuration", "transformation", "implementation", "documentation"]

def gen (wrap : String → String) : String := Id.run do
  let mut lines : Array String := #["\\documentclass{article}", "\\begin{document}", ""]
  for p in [1:151] do
    let mut line := "The quick brown fox says:"
    for s in [1:61] do
      line := line ++ " " ++ wrap (words.getD ((p * 7 + s * 13) % 20) "")
    lines := lines.push (line ++ " again and again.")
    lines := lines.push ""
  lines := lines.push "\\end{document}"
  return String.intercalate "\n" lines.toList ++ "\n"

def main : IO Unit := do
  IO.FS.createDirAll "bench"
  let lorem := gen id
  IO.FS.writeFile "bench/lorem.tex" lorem
  IO.println s!"{lorem.utf8ByteSize} bench/lorem.tex"
  let underline := gen fun w => "\\underline{" ++ w ++ "}"
  IO.FS.writeFile "bench/underline.tex" underline
  IO.println s!"{underline.utf8ByteSize} bench/underline.tex"
