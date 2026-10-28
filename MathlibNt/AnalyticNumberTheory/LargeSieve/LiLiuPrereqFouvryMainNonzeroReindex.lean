import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryMainNonzero
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvrySecondaryResonanceReindex

/-!
# Main nonzero occupied labels, with the common index and r varying

Only the two ordered inner triples are fixed. The original beta/zeta weight
is independent of both averaged coordinates; the shared k multiplicity
remains in the already constructed Gram section.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

abbrev WGramMainBase := (ℕ × ℕ × ℤ) × (ℕ × ℕ × ℤ)


def wGramMainLabels (K : WExtractedKey) (a : ℤ)
    (V : Finset (WExtractedTuple × ℤ)) : Finset WGramLabel :=
  (wGramLabels V).filter
    (fun L => wGramNumerator K a L ≠ 0 ∧ ¬ wGramSecondaryResonant L)


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
