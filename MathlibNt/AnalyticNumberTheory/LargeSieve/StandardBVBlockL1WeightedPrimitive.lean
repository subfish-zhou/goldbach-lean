

import MathlibNt.AnalyticNumberTheory.Vaughan.StandardBVHighActualVaughanRows
import MathlibNt.AnalyticNumberTheory.LargeSieve.ProductionDyadicConductorGeometry

/-!
 # Block-L¹ weighted primitive consumers for the production Vaughan rows

The analytic hypotheses in this file are block-local first-moment estimates for
exactly the production Type-I and Type-II coefficients.  The finite consumer
converts `d / φ(d)` to the AP normalization on each block, reindexes a disjoint
finite block partition exactly, and then uses only the two scalar geometric
ledgers.  The small lane is the production coefficient at
`standardBVBalancedSmallCutoff`, hence is retained and paid through its square
ledger plus high-conductor Cauchy.  The former `v = min N 1` path remains only
as an explicitly named compatibility wrapper.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset Filter
open scoped BigOperators ArithmeticFunction Topology

noncomputable section


/-- Consume the actual high-conductor square payment for any coefficient.
The factor three is the existing ledger reserve, not a new triangle bound.
Only the target needs to be nonnegative; the multiplier may be signed. -/
theorem apNormalizedPrimitiveMeanOn_high_le_of_square_payment
    (a : ℤ → ℂ) (N Q C : ℕ) (P Z : ℝ)
    (hR : 1 ≤ logConductorThreshold N C) (hZ : 0 ≤ Z)
    (hpay : P ^ 2 * (3 * highConductorHarmonicFactor Q
        (logConductorThreshold N C) *
        primitivePrefixSquareLedgerOn a N (highConductorSet N Q C)) ≤ Z ^ 2) :
    P * apNormalizedPrimitiveMeanOn a N (highConductorSet N Q C) ≤ Z := by
  have hcard : ∀ d ∈ Finset.Icc (logConductorThreshold N C + 1) Q,
      Fintype.card (PrimitiveCharacter d) ≤ d.totient := by
    intro d hd
    exact card_primitiveCharacter_le_totient d (by
      have hdR := (Finset.mem_Icc.mp hd).1
      omega)
  have hc := apNormalizedPrimitiveMeanOn_high_sq_le a N Q
    (logConductorThreshold N C) hcard
  rw [← highConductorSet_eq_interval N Q C hR] at hc
  have hw := mul_le_mul_of_nonneg_left hc (sq_nonneg P)
  apply le_of_sq_le_sq _ hZ
  nlinarith only [hw, hpay,
    sq_nonneg (P * apNormalizedPrimitiveMeanOn a N (highConductorSet N Q C))]


/-- The common quadratic envelope used by chosen Type-I/II payments and by
bare block sources. The modulus is the actual Pan cutoff, including `Q = 0`. -/
theorem productionAbelConductorEnvelope_le_logPow_two (B N : ℕ) (hN : 3 ≤ N) :
    let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
    4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2 ≤
      48 * Real.log (N : ℝ) ^ 2 := by
  dsimp only
  let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
  have hlog : 1 ≤ Real.log (N : ℝ) := by
    have he1 : Real.exp 1 < (3 : ℝ) :=
      Real.exp_one_lt_d9.trans (by norm_num)
    exact (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < N)).2
      (he1.trans_le (by exact_mod_cast hN)) |>.le
  have habel : discreteAbelAmplifierPrefixMax N ≤ 3 := by
    refine (discreteAbelAmplifierPrefixMax_le_two_inv_log_two N).trans ?_
    have htwo : (2 / 3 : ℝ) < Real.log 2 := by
      linarith [Real.log_two_gt_d9]
    rw [mul_inv_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
    linarith
  by_cases hQ0 : Q = 0
  · simp [Q, hQ0, conductorHarmonicFactor]
    exact pow_nonneg (zero_le_one.trans hlog) 2
  · have hQpos : 0 < Q := Nat.pos_of_ne_zero hQ0
    have hQsq : Q ^ 2 ≤ N := by
      simpa [Q] using MathlibNt.SieveTheory.LiuWeight.panModulusCutoff_sq_le
        N (B : ℝ) (by omega) (by positivity : 0 ≤ (B : ℝ))
    have hQle : Q ≤ N := by
      calc
        Q = Q * 1 := by simp
        _ ≤ Q * Q := Nat.mul_le_mul_left Q (Nat.succ_le_iff.mpr hQpos)
        _ = Q ^ 2 := by ring
        _ ≤ N := hQsq
    have hlogQ : Real.log (Q : ℝ) ≤ Real.log (N : ℝ) :=
      Real.log_le_log (by exact_mod_cast hQpos) (by exact_mod_cast hQle)
    have hH : conductorHarmonicFactor Q ≤ 2 * Real.log (N : ℝ) :=
      (conductorHarmonicFactor_le Q).trans (by linarith)
    have hH0 : 0 ≤ conductorHarmonicFactor Q := conductorHarmonicFactor_nonneg Q
    calc
      _ ≤ 4 * 3 * (2 * Real.log (N : ℝ)) ^ 2 := by gcongr
      _ = 48 * Real.log (N : ℝ) ^ 2 := by ring


end
end AnalyticNumberTheory.LargeSieve
