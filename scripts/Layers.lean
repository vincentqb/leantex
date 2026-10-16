module

/-! The engine's layers as its import checks read them. -/

public section

/-- The surface modules: tex's lexer, parser, elaborator and compatibility layer, markdown's reader
and desugaring, the code-file reader, and their door. -/
def surfaceModules : List String :=
  ["Lex", "Parse", "Elab", "Compat", "MdParse", "MdDesugar", "CodeDoc", "Surface"].map
    ("LeanTex.Core." ++ ·)

/-- The backends, which read the IR alone. -/
def backendModules : List String :=
  ["Layout", "Pdf", "PdfContent", "PdfStruct", "Html", "HtmlDoc", "MathMl", "MarkdownDoc"].map
    ("LeanTex.Core." ++ ·)
