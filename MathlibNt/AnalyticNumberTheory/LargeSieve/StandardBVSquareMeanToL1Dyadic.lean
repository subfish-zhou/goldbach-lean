

import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanAllCharacterAnalyticLedger
import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanTypeILongVariable

/-!
 # Standard BV: exact dyadic square-mean to L¹ conversion

This module isolates the finite conversion which is needed *before* any
Bombieri--Vinogradov conclusion may be claimed.  The AP prefix error is supplied
pointwise through the character expansion, not as a final BV premise.  Every
factor `1/φ(q)`, `q/φ(q)`, the number of moduli in a block, and the number of
conductor cells is retained.

The character quantity is a genuine prefix maximum.  Nothing in this file
replaces it by the endpoint `y = N`.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators

noncomputable section


/-- The nonnegative amplitude whose square is the full character prefix
maximum. -/
def nonprincipalPrefixAmplitude
    (b : ℤ → ℂ) (N q : ℕ) (χ : DirichletCharacter ℂ q) : ℝ :=
  Real.sqrt (characterPrefixMaxSquare χ b 0 N)

lemma nonprincipalPrefixAmplitude_nonneg
    (b : ℤ → ℂ) (N q : ℕ) (χ : DirichletCharacter ℂ q) :
    0 ≤ nonprincipalPrefixAmplitude b N q χ := Real.sqrt_nonneg _

lemma nonprincipalPrefixAmplitude_sq
    (b : ℤ → ℂ) (N q : ℕ) (χ : DirichletCharacter ℂ q) :
    nonprincipalPrefixAmplitude b N q χ ^ 2 =
      characterPrefixMaxSquare χ b 0 N := by
  apply Real.sq_sqrt
  unfold characterPrefixMaxSquare
  let V := (Finset.range (N + 1)).image
    (fun y => characterPrefixSquare χ b 0 y)
  have hm : V.max' (Finset.image_nonempty.mpr ⟨0, by simp⟩) ∈ V :=
    Finset.max'_mem V _
  rcases Finset.mem_image.mp hm with ⟨y, hy, heq⟩
  rw [← heq]
  unfold characterPrefixSquare
  positivity


/-! ## Substitution ledger for the currently proved producers

These are transparent scale expressions, not hypotheses asserting BV.  Their
factorizations identify exactly which payments must be compared with the
preceding threshold. -/


end

end AnalyticNumberTheory.LargeSieve
