module

public import LeanTex.Core.Parse
import all LeanTex.Core.CiteDecl
import all LeanTex.Core.Parse

/-! Kernel checks of the citation setup's carrier: what a surface writes, the elaborator reads. -/

namespace LeanTex.Core

/-- Every declaration reads back from the word that carries it. -/
public theorem CiteDecl.spelling_read_exact (d : CiteDecl) :
    CiteDecl.ofSpelling? d.spelling = some d := by
  cases d with
  | word w =>
    have h : '=' ∉ w.name.toList := by cases w <;> decide +kernel
    have hl : CiteDecl.Word.names.lookup w.name = some w := by cases w <;> decide +kernel
    have hs := KeyVal.cutAt_append '=' _ [] h
    simp only [List.append_nil, KeyVal.cutAt] at hs
    simp [CiteDecl.spelling, CiteDecl.ofSpelling?, hs, hl]
  | set k v =>
    have h : '=' ∉ k.name.toList := by cases k <;> decide +kernel
    have hk : (k.name == "option") = false := by cases k <;> decide +kernel
    have hl : CiteDecl.Key.names.lookup k.name = some k := by cases k <;> decide +kernel
    simp [CiteDecl.spelling, CiteDecl.ofSpelling?, String.toList_append,
      KeyVal.cutAt_append '=' _ _ h, KeyVal.cutAt, hk, hl]
  | option o =>
    have hl : CiteDecl.Opt.names.lookup o.name = some o := by cases o <;> decide +kernel
    simp [CiteDecl.spelling, CiteDecl.ofSpelling?, String.toList_append, KeyVal.cutAt, hl]

/-- The setup a surface carries is its mark and a group the elaborator reads back as the setup. -/
public theorem Parse.citeSetupRaws_read_exact (ds : Array CiteDecl) (pos : Pos) :
    ∃ body, Parse.citeSetupRaws ds pos = #[.ctrl Parse.citeSetupMark pos, .group body pos] ∧
      Parse.citeSetupOf body = ds := by
  refine ⟨_, rfl, ?_⟩
  unfold Parse.citeSetupOf
  rw [Array.filterMap_map]
  simp [Function.comp_def, CiteDecl.spelling_read_exact]

end LeanTex.Core
