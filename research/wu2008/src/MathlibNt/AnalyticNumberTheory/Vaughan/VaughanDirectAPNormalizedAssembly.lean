

import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanDirectTypeIPhysicalScale
import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanTypeILongCoeffMomentExplicit

/-!
 # AP-normalized direct Vaughan assembly

This module is the direct L¹ route with the literal arithmetic-progression
weight `1 / φ(q)`.  The historical `q / φ(q)` unsquared mean remains available
only as a compatibility majorant in `VaughanDirectL1Physical`.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators

noncomputable section

/-- AP-normalized Type-II direct Vaughan mean. -/
def apNormalizedVaughanTypeIIMean (N Q u v : ℕ) : ℝ :=
  apNormalizedPrimitiveMean
    (vaughanTypeIICoeff vaughanUnitIntegerCoeff u v) N Q

/-- AP-normalized small-range direct Vaughan mean. -/
def apNormalizedVaughanSmallMean (N Q v : ℕ) : ℝ :=
  apNormalizedPrimitiveMean
    (vaughanSmallCoeff vaughanUnitIntegerCoeff v) N Q



private lemma apNormalized_amplitude_three_piece
    {x a b c : ℝ} (hx : 0 ≤ x) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : x ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2)) :
    x ≤ 2 * (a + b + c) := by
  nlinarith [sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)]

/-- Vaughan's exact three-piece identity assembled directly in the
AP-normalized primitive L¹ mean. -/
theorem apNormalizedPrimitiveMean_vaughan_le
    (N Q u v : ℕ) :
    apNormalizedPrimitiveMean vonMangoldtIntegerCoeff N Q ≤
      2 * (apNormalizedVaughanTypeIMean N Q u v +
        apNormalizedVaughanTypeIIMean N Q u v +
        apNormalizedVaughanSmallMean N Q v) := by
  unfold apNormalizedVaughanTypeIMean apNormalizedVaughanTypeIIMean
    apNormalizedVaughanSmallMean apNormalizedPrimitiveMean
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℝ)⁻¹) *
        ∑ χ : PrimitiveCharacter q,
          2 * (primitivePrefixAmplitude
              (vaughanTypeICoeff vaughanUnitIntegerCoeff u v) N q χ +
            primitivePrefixAmplitude
              (vaughanTypeIICoeff vaughanUnitIntegerCoeff u v) N q χ +
            primitivePrefixAmplitude
              (vaughanSmallCoeff vaughanUnitIntegerCoeff v) N q χ) := by
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro χ hχ
        apply apNormalized_amplitude_three_piece
        · exact primitivePrefixAmplitude_nonneg _ _ _ _
        · exact primitivePrefixAmplitude_nonneg _ _ _ _
        · exact primitivePrefixAmplitude_nonneg _ _ _ _
        · exact primitivePrefixAmplitude_nonneg _ _ _ _
        · rw [primitivePrefixAmplitude_sq, primitivePrefixAmplitude_sq,
            primitivePrefixAmplitude_sq, primitivePrefixAmplitude_sq]
          exact primitiveCharacterPrefixMaxSquare_le_three _ _ _ _ N q χ
            (fun n _ => (vaughanLambdaCoeff_unit_eq n).symm.trans
              (vaughanLambdaCoeff_eq vaughanUnitIntegerCoeff u v n))
      · positivity
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      ring

/-- Strong conductor transport.  The exact reciprocal-totient conductor bound
lands on the AP-normalized primitive mean, with no `q / φ(q)` inflation. -/
theorem direct_conductor_sum_le_apNormalizedPrimitive
    (a : ℤ → ℂ) (N Q : ℕ) :
    (∑ d ∈ Finset.Icc 2 Q, directConductorWeight Q d *
      ∑ ψ : PrimitiveCharacter d, primitivePrefixAmplitude a N d ψ) ≤
      conductorHarmonicFactor Q ^ 2 * apNormalizedPrimitiveMean a N Q := by
  unfold apNormalizedPrimitiveMean
  calc
    _ ≤ ∑ d ∈ Finset.Icc 2 Q,
        (conductorHarmonicFactor Q ^ 2 / (d.totient : ℝ)) *
          ∑ ψ : PrimitiveCharacter d, primitivePrefixAmplitude a N d ψ := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_right (directConductorWeight_le Q d)
        (Finset.sum_nonneg fun ψ _ => primitivePrefixAmplitude_nonneg a N d ψ)
    _ = ∑ d ∈ Finset.Icc 2 Q,
        conductorHarmonicFactor Q ^ 2 *
          (((d.totient : ℝ)⁻¹) *
            ∑ ψ : PrimitiveCharacter d, primitivePrefixAmplitude a N d ψ) := by
      simp only [div_eq_mul_inv, mul_assoc]
    _ ≤ ∑ d ∈ Finset.Icc 1 Q,
        conductorHarmonicFactor Q ^ 2 *
          (((d.totient : ℝ)⁻¹) *
            ∑ ψ : PrimitiveCharacter d, primitivePrefixAmplitude a N d ψ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.Icc_subset_Icc_left (by omega)
      · intro d hd hnot
        exact mul_nonneg (sq_nonneg _)
          (mul_nonneg (by positivity)
            (Finset.sum_nonneg fun ψ _ => primitivePrefixAmplitude_nonneg a N d ψ))
    _ = _ := by rw [Finset.mul_sum]

/-- All nonprincipal characters transported to the AP-normalized primitive
mean.  The change-of-level correction remains explicit. -/
theorem directAllCharacterMean_le_apNormalizedPrimitive
    (a : ℤ → ℂ) (N Q : ℕ) :
    directAllCharacterMean a N Q ≤
      2 * conductorHarmonicFactor Q ^ 2 * apNormalizedPrimitiveMean a N Q +
      2 * directConductorCorrectionMean a N Q := by
  calc
    _ ≤ 2 * (∑ d ∈ Finset.Icc 2 Q, directConductorWeight Q d *
          ∑ ψ : PrimitiveCharacter d, primitivePrefixAmplitude a N d ψ) +
        2 * directConductorCorrectionMean a N Q :=
      directAllCharacterMean_le_conductor a N Q
    _ ≤ 2 * (conductorHarmonicFactor Q ^ 2 *
          apNormalizedPrimitiveMean a N Q) +
        2 * directConductorCorrectionMean a N Q := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          (direct_conductor_sum_le_apNormalizedPrimitive a N Q) (by positivity))
        le_rfl
    _ = _ := by ring

/-- Largest short-variable scale occurring in the two Type-I lanes. -/
def vaughanTypeIShortScale (u v : ℕ) : ℕ := max u (u * v)

/-- AP-normalized Type-I physical-scale input, retaining the exact
`Q*sqrt(N*D)` dependence of the shell square ledger. -/
def VaughanDirectAPNormalizedTypeIInput
    (N Q u v : ℕ) (K logPay : ℝ) : Prop :=
  apNormalizedVaughanTypeIMean N Q u v ≤
    K * logPay * ((N : ℝ) + (Q : ℝ) ^ 2 * Real.sqrt N)

/-- AP-normalized Type-II physical-scale input. -/
def VaughanDirectAPNormalizedTypeIIInput
    (N Q u v : ℕ) (K logPay : ℝ) : Prop :=
  apNormalizedVaughanTypeIIMean N Q u v ≤
    K * logPay * ((N : ℝ) +
      (Q : ℝ) * N / Real.sqrt (u + 1 : ℕ))


end

end AnalyticNumberTheory.LargeSieve
