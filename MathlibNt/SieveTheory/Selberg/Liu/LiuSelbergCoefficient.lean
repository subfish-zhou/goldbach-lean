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
  have hsupport :
      ¬(d > paperQSourceCutoff N epsilon ∨ ¬d ∣ selbergQ N epsilon) := by
    intro h
    exact hd (SW.lambda_support d h)
  rw [← selbergQ_eq_liuPaperQModulus]
  exact ⟨not_not.mp (not_or.mp hsupport).2, by
    simpa [paperQSourceCutoff] using (not_lt.mp (not_or.mp hsupport).1)⟩

/-- The source normalization is separate from admissibility because the latter
is exactly the support-and-size interface needed by the remainder argument. -/
theorem SelbergWeights.lambda_one_source
    {N : ℕ} {epsilon : ℝ} (SW : SelbergWeights N epsilon) :
    SW.lambda 1 = 1 :=
  SW.lambda_one

/-- Restricting the legacy divisor quadratic sum to Liu's filtered source
carrier is exact.  Terms outside the cutoff vanish by the legacy support
condition; they are not silently discarded. -/
theorem SelbergWeights.divisors_quadraticSum_eq_liuSelbergCoefficientFactor
    {N : ℕ} {epsilon : ℝ} (SW : SelbergWeights N epsilon) :
    (selbergQ N epsilon).divisors.sum (fun d1 =>
      (selbergQ N epsilon).divisors.sum (fun d2 =>
        SW.lambda d1 * SW.lambda d2 / Nat.totient (Nat.lcm d1 d2))) =
      liuSelbergCoefficientFactor N epsilon SW.lambda := by
  classical
  rw [selbergQ_eq_liuPaperQModulus]
  unfold liuSelbergCoefficientFactor liuSelbergLambdaSourceCarrier
  simp_rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d1 hd1
  by_cases h1 : d1 ≤ paperQSourceCutoff N epsilon
  · simp only [h1, if_true]
    apply Finset.sum_congr rfl
    intro d2 hd2
    by_cases h2 : d2 ≤ paperQSourceCutoff N epsilon
    · simp [h2]
    · have hzero : SW.lambda d2 = 0 := by
        apply SW.lambda_support d2
        exact Or.inl (lt_of_not_ge h2)
      simp [h2, hzero]
  · have hzero : SW.lambda d1 = 0 := by
      apply SW.lambda_support d1
      exact Or.inl (lt_of_not_ge h1)
    simp [h1, hzero]

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
