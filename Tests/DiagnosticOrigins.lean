import Tests.Support

open LeanTex.Core LeanTex.Cli

namespace Tests

/-- Delayed glyph diagnostics name the actual failing source occurrence. A
covered occurrence of the same scalar is not evidence for the later loss.
The glyph census also checks that locating a fallback never changes its ink. -/
def diagnosticOriginChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let load (name : String) : IO Font.Font := do
    match Font.parse (← IO.FS.readBinFile (testFonts ++ "/" ++ name)) with
    | .ok f => pure f
    | .error e => throw (IO.userError s!"origins: {name}: {e}")
  let sans ← load "OpenSans-Regular.ttf"
  let code ← load "SourceCodePro-Regular.otf"
  let variants (slot idx : Nat) : List ((Nat × Nat × Bool) × Nat) :=
    [((slot, 400, false), idx), ((slot, 700, false), idx),
     ((slot, 400, true), idx), ((slot, 700, true), idx)]
  let fs : Font.FontSet := {
    fonts := #[sans, code]
    index := (variants 0 0 ++ variants 1 0 ++ variants 2 1).toArray
    fallback := #[('∀', 1)] }
  let parse (file text : String) : Array Parse.Raw :=
    (Parse.parse file (Lex.lex file text).1).1
  let sourceDoc (file text : String) : Ir.Doc :=
    (Elab.runRawsSpanned file (parse file text)).1
  let atSource (ds : Array Diag) (code file : String) (line : Nat) : Bool :=
    ds.any fun d => d.code == code && d.span.any fun s => s.file == file && s.pos.line == line
  let text := "\\texttt{∀}\n\nlater ∀ here"
  let doc := sourceDoc "chapters/example.tex" text
  let out := layoutOf fs doc
  t "glyph origin: fallback points past an earlier covered occurrence"
    (atSource out.diags "W0009" "chapters/example.tex" 3)
  t "glyph origin: the fallback glyph actually ships from its mapped face"
    (((out.pages.flatMap (·.lines)).flatMap (·.segs)).any fun s => match s with
      | .run 1 _ _ _ gs _ _ _ _ _ _ => gs.any (·.2.1 == '∀')
      | _ => false)
  let plain := (Elab.run "chapters/example.tex" text).1
  t "glyph origin: provenance leaves the emitted PDF unchanged"
    (Pdf.write (Layout.Geom.ofPage doc.page) fs out.pages ==
      Pdf.write (Layout.Geom.ofPage plain.page) fs (layoutOf fs plain).pages)
  let missing := layoutOf fs (sourceDoc "chapters/missing.tex" "first\n\nlost ⟨ here")
  t "glyph origin: an absent scalar keeps its source line"
    (atSource missing.diags "E0405" "chapters/missing.tex" 3)
  let child := parse "chapters/included.tex" "first\n\nlater ∀ here"
  let included : Array Parse.Raw := #[.env (Parse.inputEnv "chapters/included.tex") child {}]
  let imported := layoutOf fs (Elab.runRawsSpanned "root.tex" included).1
  t "glyph origin: included text names the included file"
    (atSource imported.diags "W0009" "chapters/included.tex" 3)
  let lines := sourceDoc "chapters/listing.tex"
    "first\n\n\\begin{verbatim}\na = 1\nlost ⟨ here\n\\end{verbatim}"
  t "glyph origin: listing losses point to their content line"
    (atSource (layoutOf fs lines).diags "E0405" "chapters/listing.tex" 5)

end Tests
