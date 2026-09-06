

import MathlibNt.AnalyticNumberTheory.LargeSieve.StandardBVExactLowHighConnector
import MathlibNt.AnalyticNumberTheory.LargeSieve.StandardBVPayload

/-!
 # Narrow sufficient assembly for Standard Bombieri--Vinogradov

The finite lambda/conductor connector and the elementary payload are consumed
internally.  The publication-facing theorem retains only a low-conductor
Siegel--Walfisz/PNT source and the exact high-conductor Vaughan hybrid source.
Neither source contains a Standard-BV conclusion.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset Filter
open scoped BigOperators ArithmeticFunction Topology

noncomputable section

/-- The genuine low-conductor analytic source after finite character and
conductor bookkeeping.  It consists only of the low primitive-conductor lane
and the modulus-one PNT/partial-summation lane. -/
def StandardBVLowSiegelWalfiszSource : Prop :=
  ∀ A C B : ℕ, ∃ K : ℝ, 0 < K ∧
    ∀ᶠ N : ℕ in Filter.atTop,
      let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
      2 * discreteAbelAmplifierPrefixMax N * lowConductorPhysical N Q C +
          discreteAbelAmplifierPrefixMax N * principalGlobalPhysical N Q +
          chebyshevToLiPhysical N Q ≤
        K * (N : ℝ) / Real.log N ^ A

/-- The genuine high-conductor analytic source.  Its left side is exactly the
Vaughan Type-I/II/small hybrid on the high conductor Finset, multiplied only by
the proved conductor transport and Abel factors.  The small lane is elementary
and may be bounded independently by `highConductorVaughanSmallMean_le_explicit`;
no Standard-BV assertion occurs here. -/
def StandardBVHighTypeITypeIIHybridSource : Prop :=
  ∀ A C B : ℕ, ∃ u v : ℕ, ∃ K : ℝ, 0 < K ∧
    ∀ᶠ N : ℕ in Filter.atTop,
      let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
      4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2 *
          (highConductorVaughanTypeIMean N Q C u v +
            highConductorVaughanTypeIIMean N Q C u v +
            highConductorVaughanSmallMean N Q C v) ≤
        K * (N : ℝ) / Real.log N ^ A

private lemma amplitude_three_piece
    {x a b c : ℝ} (hx : 0 ≤ x) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : x ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2)) :
    x ≤ 2 * (a + b + c) := by
  nlinarith [sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)]

/-- Vaughan's exact prefix decomposition restricted to an arbitrary conductor
Finset. -/
theorem apNormalizedPrimitiveMeanOn_vaughan_le
    (N : ℕ) (S : Finset ℕ) (u v : ℕ) :
    apNormalizedPrimitiveMeanOn vonMangoldtIntegerCoeff N S ≤
      2 * (apNormalizedPrimitiveMeanOn
          (vaughanTypeICoeff vaughanUnitIntegerCoeff u v) N S +
        apNormalizedPrimitiveMeanOn
          (vaughanTypeIICoeff vaughanUnitIntegerCoeff u v) N S +
        apNormalizedPrimitiveMeanOn
          (vaughanSmallCoeff vaughanUnitIntegerCoeff v) N S) := by
  unfold apNormalizedPrimitiveMeanOn
  calc
    _ ≤ ∑ q ∈ S, ((q.totient : ℝ)⁻¹) *
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
        apply amplitude_three_piece
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

/-- Direct conductor weight on any subset is controlled by the AP-normalized
primitive mean on that same subset. -/
theorem directConductorMeanOn_le_apNormalizedPrimitiveMeanOn
    (a : ℤ → ℂ) (N Q : ℕ) (S : Finset ℕ) :
    directConductorMeanOn a N Q S ≤
      conductorHarmonicFactor Q ^ 2 * apNormalizedPrimitiveMeanOn a N S := by
  unfold directConductorMeanOn apNormalizedPrimitiveMeanOn
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  calc
    directConductorWeight Q d *
        (∑ ψ : PrimitiveCharacter d, primitivePrefixAmplitude a N d ψ) ≤
      (conductorHarmonicFactor Q ^ 2 / (d.totient : ℝ)) *
        (∑ ψ : PrimitiveCharacter d, primitivePrefixAmplitude a N d ψ) :=
      mul_le_mul_of_nonneg_right (directConductorWeight_le Q d)
        (Finset.sum_nonneg fun ψ _ => primitivePrefixAmplitude_nonneg a N d ψ)
    _ = conductorHarmonicFactor Q ^ 2 *
        (((d.totient : ℝ)⁻¹) *
          ∑ ψ : PrimitiveCharacter d, primitivePrefixAmplitude a N d ψ) := by
      rw [div_eq_mul_inv]
      ring

/-- The exact high physical conductor lane is controlled by the exact Vaughan
hybrid appearing in `StandardBVHighTypeITypeIIHybridSource`. -/
theorem highConductorPhysical_le_vaughanHybrid
    (N Q C u v : ℕ) :
    highConductorPhysical N Q C ≤
      2 * conductorHarmonicFactor Q ^ 2 *
        (highConductorVaughanTypeIMean N Q C u v +
          highConductorVaughanTypeIIMean N Q C u v +
          highConductorVaughanSmallMean N Q C v) := by
  refine (directConductorMeanOn_le_apNormalizedPrimitiveMeanOn
    vonMangoldtIntegerCoeff N Q (highConductorSet N Q C)).trans ?_
  have hv := mul_le_mul_of_nonneg_left
    (apNormalizedPrimitiveMeanOn_vaughan_le N (highConductorSet N Q C) u v)
    (sq_nonneg (conductorHarmonicFactor Q))
  unfold highConductorVaughanTypeIMean highConductorVaughanTypeIIMean
    highConductorVaughanSmallMean
  nlinarith only [hv]

/-- Closed finite sufficient assembly.  The connector is a theorem, and the
only third budget is the already-proved `StandardBVPayload`. -/
theorem standardBV_sufficient_at_closed
    (A : ℕ) (B C N Q u v : ℕ) (KL KH : ℝ)
    (hN : 2 ≤ N)
    (hQ : Q = MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ))
    (hlow :
      2 * discreteAbelAmplifierPrefixMax N * lowConductorPhysical N Q C +
          discreteAbelAmplifierPrefixMax N * principalGlobalPhysical N Q +
          chebyshevToLiPhysical N Q ≤
        KL * (N : ℝ) / Real.log N ^ A)
    (hhigh :
      4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2 *
          (highConductorVaughanTypeIMean N Q C u v +
            highConductorVaughanTypeIIMean N Q C u v +
            highConductorVaughanSmallMean N Q C v) ≤
        KH * (N : ℝ) / Real.log N ^ A)
    (hpayload : StandardBVPayload N Q ≤
      180 * (N : ℝ) / Real.log N ^ A) :
    (∑ q ∈ Finset.Icc 1
        (MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)),
      MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPPrefixMaxError N q) ≤
      (KL + KH + 180) * (N : ℝ) / Real.log N ^ A := by
  subst Q
  let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
  have habel : 0 ≤ discreteAbelAmplifierPrefixMax N := by
    have h0 : 0 ≤ discreteAbelAmplifier 0 := by unfold discreteAbelAmplifier; positivity
    exact h0.trans (by
      unfold discreteAbelAmplifierPrefixMax
      exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨0, by simp, rfl⟩))
  have hconnector := lambdaToLowHighConductorConnector N Q C
  have hhighPhysical := highConductorPhysical_le_vaughanHybrid N Q C u v
  have hpacket := sum_standardPrimeAPPrefixMaxError_le_concretePhysical N Q hN
  have hnon :
      discreteAbelAmplifierPrefixMax N * nonprincipalLambdaPhysical N Q ≤
        2 * discreteAbelAmplifierPrefixMax N *
            (lowConductorPhysical N Q C + highConductorPhysical N Q C) +
          discreteAbelAmplifierPrefixMax N *
            (2 * directConductorCorrectionMean vonMangoldtIntegerCoeff N Q) := by
    have hscaled := mul_le_mul_of_nonneg_left hconnector habel
    nlinarith only [hscaled]
  have hhigh' :
      2 * discreteAbelAmplifierPrefixMax N * highConductorPhysical N Q C ≤
        KH * (N : ℝ) / Real.log N ^ A := by
    refine (mul_le_mul_of_nonneg_left hhighPhysical
      (mul_nonneg (by norm_num) habel)).trans ?_
    change 2 * discreteAbelAmplifierPrefixMax N *
        (2 * conductorHarmonicFactor Q ^ 2 *
          (highConductorVaughanTypeIMean N Q C u v +
            highConductorVaughanTypeIIMean N Q C u v +
            highConductorVaughanSmallMean N Q C v)) ≤ _
    nlinarith only [hhigh]
  have htotal :
      (concreteStandardBVPhysicalTerms N Q).total
          (discreteAbelAmplifierPrefixMax N) ≤
        (KL + KH + 180) * (N : ℝ) / Real.log N ^ A := by
    unfold StandardBVPhysicalTerms.total concreteStandardBVPhysicalTerms
    calc
      _ ≤ (2 * discreteAbelAmplifierPrefixMax N * lowConductorPhysical N Q C +
            discreteAbelAmplifierPrefixMax N * principalGlobalPhysical N Q +
            chebyshevToLiPhysical N Q) +
          (2 * discreteAbelAmplifierPrefixMax N * highConductorPhysical N Q C) +
          discreteAbelAmplifierPrefixMax N *
            (principalBadPhysical N Q + primePowerPhysical N Q +
              2 * directConductorCorrectionMean vonMangoldtIntegerCoeff N Q) := by
        nlinarith only [hnon]
      _ ≤ KL * (N : ℝ) / Real.log N ^ A +
          KH * (N : ℝ) / Real.log N ^ A +
          180 * (N : ℝ) / Real.log N ^ A :=
        add_le_add (add_le_add hlow hhigh') (by
          simpa [StandardBVPayload] using hpayload)
      _ = (KL + KH + 180) * (N : ℝ) / Real.log N ^ A := by ring
  exact hpacket.trans htotal

/-- Narrow Standard-BV endpoint.  Its only premises are the genuine low SW/PNT
source and the genuine high Vaughan hybrid source; all finite connectors and
all elementary payment premises have disappeared. -/
theorem standardBV_of_lowSW_highTypeITypeII
    (hlow : StandardBVLowSiegelWalfiszSource)
    (hhigh : StandardBVHighTypeITypeIIHybridSource) :
    ∀ A : ℕ, ∃ B : ℕ, ∃ K : ℝ, 0 < K ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        (∑ q ∈ Finset.Icc 1
            (MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)),
          MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPPrefixMaxError N q) ≤
          K * (N : ℝ) / Real.log N ^ A := by
  intro A
  let B : ℕ := A + 3
  let C : ℕ := 1
  obtain ⟨KL, hKL, hlowN⟩ := hlow A C B
  obtain ⟨u, v, KH, hKH, hhighN⟩ := hhigh A C B
  refine ⟨B, KL + KH + 180, by positivity, ?_⟩
  filter_upwards [hlowN, hhighN, StandardBVPayload_payable A,
    eventually_ge_atTop (3 : ℕ)] with N hLN hHN hpayload hN
  let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
  have hlog0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ N by omega))
  have hcut : (Q : ℝ) ≤ Real.sqrt N / Real.log N ^ (A + 3) := by
    calc
      (Q : ℝ) =
          (Nat.floor ((N : ℝ) ^ (1 / 2 : ℝ) /
            Real.log N ^ ((A + 3 : ℕ) : ℝ)) : ℝ) := by
              simp [Q, MathlibNt.SieveTheory.LiuWeight.panModulusCutoff, B]
      _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) /
            Real.log N ^ ((A + 3 : ℕ) : ℝ) :=
        Nat.floor_le (div_nonneg
          (Real.rpow_nonneg (by positivity) _)
          (Real.rpow_nonneg hlog0 _))
      _ = Real.sqrt N / Real.log N ^ (A + 3) := by
        rw [Real.sqrt_eq_rpow, Real.rpow_natCast]
  exact standardBV_sufficient_at_closed A B C N Q u v KL KH
    (by omega) rfl hLN hHN (hpayload Q hcut)

end

end AnalyticNumberTheory.LargeSieve
