import MathlibNt.SieveTheory.Selberg.Liu.LiuSelbergMainTerm
import MathlibNt.SieveTheory.Selberg.SelbergUpperBound

/-!
# Liu's source Selberg coefficient

This module identifies the legacy Selberg-weight API with Liu's source modulus
and finite coefficient carrier.  The optimized numerical estimate is kept as a
transparent eventual input; the legacy pointwise existence theorem does not
provide it.
-/

open scoped BigOperators

namespace MathlibNt.SieveTheory.LiuWeight

open Filter Finset

namespace LegacySelberg

open MathlibNt.SieveTheory.SelbergUpperBound

/-- The legacy modulus is exactly Liu's source modulus.  Both use the
non-strict real cutoff `p ≤ N^(1/4-epsilon/2)`, represented by the same floor. -/
theorem selbergQ_eq_liuPaperQModulus (N : ℕ) (epsilon : ℝ) :
    selbergQ N epsilon = liuPaperQModulus N epsilon := by
  rw [liuPaperQModulus_eq_paperQStyleModulus]
  rfl

/-- Every legacy Selberg weight has Liu's source support and absolute bound. -/
theorem SelbergWeights.liuSelbergLambdaAdmissible
    {N : ℕ} {epsilon : ℝ} (SW : SelbergWeights N epsilon) :
    LiuSelbergLambdaAdmissible N epsilon SW.lambda := by
  refine ⟨?_, SW.lambda_bounded⟩
  intro d hd
  rw [← selbergQ_eq_liuPaperQModulus]
  constructor
  · by_contra hdiv
    exact hd (SW.lambda_support d (Or.inr hdiv))
  · by_contra hcutoff
    exact hd (SW.lambda_support d (Or.inl (lt_of_not_ge hcutoff)))



/-- The actual sharp input missing from the legacy development: for every
sufficiently large even source parameter whose cutoff contains `1`, an optimized
Selberg weight exists.  The conditional formulation avoids demanding impossible
weights at small parameters with cutoff zero. -/
def LiuOptimizedSelbergCoefficientEstimate
    (delta epsilon : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    Even N → 1 ≤ paperQSourceCutoff N epsilon →
      ∃ SW : SelbergWeights N epsilon,
        LiuSelbergCoefficientFactorBound delta N epsilon SW.lambda

/-- Source-faithful optimized Selberg input: an error tolerance first fixes a
small epsilon range, and every epsilon in that range has an eventual family of
optimized coefficients. -/
def LiuOptimizedSelbergCoefficientInput : Prop :=
  ∀ delta > 0, ∃ epsilon0 > 0, ∀ epsilon, 0 < epsilon → epsilon ≤ epsilon0 →
    LiuOptimizedSelbergCoefficientEstimate delta epsilon

end LegacySelberg

end MathlibNt.SieveTheory.LiuWeight
