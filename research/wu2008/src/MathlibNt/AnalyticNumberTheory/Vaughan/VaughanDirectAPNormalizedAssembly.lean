

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

lemma apNormalizedPrimitiveMean_nonneg (a : ℤ → ℂ) (N Q : ℕ) :
    0 ≤ apNormalizedPrimitiveMean a N Q := by
  unfold apNormalizedPrimitiveMean
  apply Finset.sum_nonneg
  intro q hq
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg fun χ _ => primitivePrefixAmplitude_nonneg a N q χ)

/-- Weighted Cauchy in the modulus variable.  The reciprocal square roots
produce the harmonic factor, while the second factor is exactly the usual
`q / φ(q)` square-large-sieve ledger.  Thus `q / φ(q)` appears only inside the
proved square estimate, never as the direct unsquared mean. -/
theorem apNormalizedPrimitiveMean_sq_le_harmonic_weightedSquare
    (a : ℤ → ℂ) (N Q : ℕ)
    (hcard : ∀ q ∈ Finset.Icc 1 Q,
      Fintype.card (PrimitiveCharacter q) ≤ q.totient) :
    apNormalizedPrimitiveMean a N Q ^ 2 ≤
      conductorHarmonicFactor Q *
        (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter q,
            primitiveCharacterPrefixMaxSquare a 0 N q χ) := by
  let T : ℕ → ℝ := fun q => ((q.totient : ℝ)⁻¹) *
    ∑ χ : PrimitiveCharacter q, primitivePrefixAmplitude a N q χ
  let B : ℕ → ℝ := fun q => ((q : ℝ) / (q.totient : ℝ)) *
    ∑ χ : PrimitiveCharacter q,
      primitiveCharacterPrefixMaxSquare a 0 N q χ
  have hT (q : ℕ) (hq : q ∈ Finset.Icc 1 Q) : (q : ℝ) * T q ^ 2 ≤ B q := by
    have hq0 : 0 < q := (Finset.mem_Icc.mp hq).1
    have hφ : (0 : ℝ) < q.totient := by
      exact_mod_cast Nat.totient_pos.mpr hq0
    let A : PrimitiveCharacter q → ℝ := fun χ => primitivePrefixAmplitude a N q χ
    have hchars := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (PrimitiveCharacter q))) (f := A)
    have hsq : (∑ χ : PrimitiveCharacter q, A χ) ^ 2 ≤
        (q.totient : ℝ) * ∑ χ : PrimitiveCharacter q, A χ ^ 2 := by
      refine hchars.trans ?_
      gcongr
      exact_mod_cast hcard q hq
    have hamp : (∑ χ : PrimitiveCharacter q, A χ ^ 2) =
        ∑ χ : PrimitiveCharacter q,
          primitiveCharacterPrefixMaxSquare a 0 N q χ := by
      apply Finset.sum_congr rfl
      intro χ hχ
      exact primitivePrefixAmplitude_sq a N q χ
    dsimp [T, B]
    rw [hamp] at hsq
    rw [div_eq_mul_inv]
    have hφne : (q.totient : ℝ) ≠ 0 := ne_of_gt hφ
    field_simp
    nlinarith
  have hsplit : apNormalizedPrimitiveMean a N Q =
      ∑ q ∈ Finset.Icc 1 Q,
        (Real.sqrt (q : ℝ))⁻¹ * (Real.sqrt (q : ℝ) * T q) := by
    unfold apNormalizedPrimitiveMean
    apply Finset.sum_congr rfl
    intro q hq
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
    have hsne : Real.sqrt (q : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hq0
    dsimp [T]
    field_simp
  rw [hsplit]
  refine (Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 Q)
    (fun q => (Real.sqrt (q : ℝ))⁻¹)
    (fun q => Real.sqrt (q : ℝ) * T q)).trans ?_
  have hfirst : (∑ q ∈ Finset.Icc 1 Q, (Real.sqrt (q : ℝ))⁻¹ ^ 2) =
      conductorHarmonicFactor Q := by
    unfold conductorHarmonicFactor
    apply Finset.sum_congr rfl
    intro q hq
    rw [inv_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ q)]
  rw [hfirst]
  apply mul_le_mul_of_nonneg_left
  · apply Finset.sum_le_sum
    intro q hq
    have hq0 : (0 : ℝ) ≤ q := by positivity
    rw [mul_pow, Real.sq_sqrt hq0]
    exact hT q hq
  · exact conductorHarmonicFactor_nonneg Q

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

/-- Physical direct assembly through the AP-normalized primitive mean.  In
particular, conductor transport never invokes the compatibility
`q / φ(q)` unsquared mean. -/
theorem direct_L1_vaughan_apNormalized_physical_assembly
    (E : ℕ → ℝ) (N Q u v : ℕ) (K logPay : ℝ)
    (hK : 0 ≤ K) (hlogPay : 0 ≤ logPay)
    (hE : ∀ q ∈ Finset.Icc 1 Q, E q ≤ ((q.totient : ℝ)⁻¹) *
      ∑ χ ∈ nonprincipalCharacters q,
        nonprincipalPrefixAmplitude vonMangoldtIntegerCoeff N q χ)
    (hI : VaughanDirectAPNormalizedTypeIInput N Q u v K logPay)
    (hII : VaughanDirectAPNormalizedTypeIIInput N Q u v K logPay) :
    (∑ q ∈ Finset.Icc 1 Q, E q) ≤
      4 * conductorHarmonicFactor Q ^ 2 *
        (2 * vaughanDirectPhysicalMajorant N Q u K logPay +
          apNormalizedVaughanSmallMean N Q v) +
      2 * directConductorCorrectionMean vonMangoldtIntegerCoeff N Q := by
  have hstart := residue_errors_le_directAllCharacterMean E N Q hE
  have hcond := directAllCharacterMean_le_apNormalizedPrimitive
    vonMangoldtIntegerCoeff N Q
  have hv := apNormalizedPrimitiveMean_vaughan_le N Q u v
  have hlanes :
      apNormalizedVaughanTypeIMean N Q u v +
          apNormalizedVaughanTypeIIMean N Q u v ≤
        2 * vaughanDirectPhysicalMajorant N Q u K logPay := by
    unfold VaughanDirectAPNormalizedTypeIInput at hI
    unfold VaughanDirectAPNormalizedTypeIIInput at hII
    unfold vaughanDirectPhysicalMajorant
    have hKL : 0 ≤ K * logPay := mul_nonneg hK hlogPay
    calc
      _ ≤ K * logPay * ((N : ℝ) + (Q : ℝ) ^ 2 * Real.sqrt N) +
          K * logPay * ((N : ℝ) +
            (Q : ℝ) * N / Real.sqrt (u + 1 : ℕ)) := add_le_add hI hII
      _ ≤ 2 * (K * logPay * ((N : ℝ) + (Q : ℝ) ^ 2 * Real.sqrt N +
            (Q : ℝ) * N / Real.sqrt (u + 1 : ℕ))) := by
        rw [two_mul]
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) hKL
        · apply mul_le_mul_of_nonneg_left _ hKL
          exact add_le_add (le_add_of_nonneg_right (by positivity)) le_rfl
  calc
    _ ≤ directAllCharacterMean vonMangoldtIntegerCoeff N Q := hstart
    _ ≤ 2 * conductorHarmonicFactor Q ^ 2 *
          apNormalizedPrimitiveMean vonMangoldtIntegerCoeff N Q +
        2 * directConductorCorrectionMean vonMangoldtIntegerCoeff N Q := hcond
    _ ≤ 2 * conductorHarmonicFactor Q ^ 2 *
          (2 * (apNormalizedVaughanTypeIMean N Q u v +
            apNormalizedVaughanTypeIIMean N Q u v +
            apNormalizedVaughanSmallMean N Q v)) +
        2 * directConductorCorrectionMean vonMangoldtIntegerCoeff N Q := by
      gcongr
    _ = 4 * conductorHarmonicFactor Q ^ 2 *
          (apNormalizedVaughanTypeIMean N Q u v +
            apNormalizedVaughanTypeIIMean N Q u v +
            apNormalizedVaughanSmallMean N Q v) +
        2 * directConductorCorrectionMean vonMangoldtIntegerCoeff N Q := by ring
    _ ≤ _ := by
      apply add_le_add _ le_rfl
      exact mul_le_mul_of_nonneg_left (add_le_add hlanes le_rfl) (by positivity)

end

end AnalyticNumberTheory.LargeSieve
