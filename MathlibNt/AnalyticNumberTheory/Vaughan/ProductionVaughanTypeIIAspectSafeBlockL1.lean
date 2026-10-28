import MathlibNt.AnalyticNumberTheory.Vaughan.ProductionVaughanTypeIIRectangularExplicitShell
import MathlibNt.AnalyticNumberTheory.LargeSieve.ProductionDyadicConductorGeometry

/-!
# Conductor-cell local actual Vaughan Type-II shells

This checker leaf performs only the finite conductor-cell compilation needed to
apply the rectangular aspect gate at `Q = 2 * i`.  In particular, the
coefficient-`L¹` family term remains the literal term over the actual cell, and
the complementary filtered family is called residual rather than extreme.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators ArithmeticFunction

noncomputable section

/-- The AP-normalized actual collected-shell mean restricted to an arbitrary
finite conductor set. -/
def apNormalizedVaughanActualCollectedShellMeanOn
    (N u v k l : ℕ) (S : Finset ℕ) : ℝ :=
  ∑ q ∈ S, ((q.totient : ℝ)⁻¹) *
    ∑ χ : PrimitiveCharacter q,
      Real.sqrt (vaughanCanonicalCollectedPrefixMaxSquare N u v k l q χ)

/-- Exact block normalization: on a conductor cell with lower endpoint `i`,
`1 / φ(q) = (1 / q) (q / φ(q))` pays at most `1 / i`. -/
theorem apNormalizedVaughanActualCollectedShellMeanOn_le_inv_mul_weightedMean
    (N u v k l i : ℕ) (S : Finset ℕ) (hi : 0 < i)
    (hlevels : ∀ q ∈ S, i ≤ q) :
    apNormalizedVaughanActualCollectedShellMeanOn N u v k l S ≤
      (1 / (i : ℝ)) *
        vaughanActualCanonicalCollectedShellWeightedMean N u v k l S := by
  unfold apNormalizedVaughanActualCollectedShellMeanOn
    vaughanActualCanonicalCollectedShellWeightedMean
    vaughanActualCanonicalCollectedShellAmplitude
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  have hq0 : 0 < q := hi.trans_le (hlevels q hq)
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr hq0
  have hsum : 0 ≤ ∑ χ : PrimitiveCharacter q,
      Real.sqrt (vaughanCanonicalCollectedPrefixMaxSquare N u v k l q χ) := by
    positivity
  have hinv : (1 / (q : ℝ)) ≤ 1 / (i : ℝ) :=
    one_div_le_one_div_of_le (by exact_mod_cast hi)
      (by exact_mod_cast hlevels q hq)
  calc
    ((q.totient : ℝ)⁻¹) *
        (∑ χ : PrimitiveCharacter q,
          Real.sqrt (vaughanCanonicalCollectedPrefixMaxSquare N u v k l q χ)) =
      (1 / (q : ℝ)) *
        (((q : ℝ) / (q.totient : ℝ)) *
          (∑ χ : PrimitiveCharacter q,
            Real.sqrt (vaughanCanonicalCollectedPrefixMaxSquare N u v k l q χ))) := by
        field_simp
    _ ≤ (1 / (i : ℝ)) *
        (((q : ℝ) / (q.totient : ℝ)) *
          (∑ χ : PrimitiveCharacter q,
            Real.sqrt (vaughanCanonicalCollectedPrefixMaxSquare N u v k l q χ))) := by
      exact mul_le_mul_of_nonneg_right hinv
        (mul_nonneg (div_nonneg (by positivity) (by positivity)) hsum)


end
end AnalyticNumberTheory.LargeSieve
