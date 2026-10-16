-- leantex: bibliography = lean-cite.bib
/-! # Citing from Lean documentation

A module doc cites a work as doc-gen4 does, [ash2001], and a second one in the
collapsed form, [birch2002][]; a key the bibliography lacks, [unknown1999],
stays as written, as does `[ash2001]` in code. Pandoc's spelling cites too:
[@roe2020, p. 3], and in the sentence @birch2002, while @List.map stays text. -/

/-- The successor, as [ash2001] defines it. -/
def succ' (n : Nat) : Nat := n + 1
