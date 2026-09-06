

import MathlibNt.AnalyticNumberTheory.LargeSieve.StandardBVSufficientAssembly
import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanTypeIActualDyadicClosure
import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanDirectAPNormalizedTypeIIActualPhysical

/-!
 # Feasibility boundary for the Standard-BV high-conductor Vaughan source

The unconditional Type-I/II physical inputs are full-conductor estimates with
an `N + Q^2 sqrt N` (and, for Type II, `Q N / sqrt (u+1)`) scale.  Restricting
the nonnegative conductor sum to `d > log(N)^C` preserves that same upper
bound; it does not manufacture an inverse-logarithmic saving.

This file records (1) the scalar obstruction, (2) a finite delta-mass witness
showing that deletion of low conductors alone has no `1/R` gain, and (3) the
narrow exact high-conductor contract, with moving Vaughan cutoffs, which the
existing Standard-BV consumer really needs.  No inhabitant of that analytic
contract is asserted here.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset Filter
open scoped BigOperators ArithmeticFunction Topology

noncomputable section

/-- A positive `L*N` lane cannot fit inside `K*N/logPow` once
`K < L*logPow`.  The modulus data `Q,B` are deliberately present but absent
from the hypotheses and conclusion: changing them cannot alter this lane. -/
theorem positive_N_lane_not_paid_by_modulus_cutoff
    (N L K logPow _Q _B : ℝ) (hN : 0 < N) (_hL : 0 < L)
    (hlogPow : 0 < logPow) (hgap : K < L * logPow) :
    K * N / logPow < L * N := by
  rw [div_lt_iff₀ hlogPow]
  nlinarith [mul_lt_mul_of_pos_right hgap hN]

/-- Formal contradiction certificate for any physical majorant which retains a
positive multiple of `N` but is advertised at inverse-logarithmic scale. -/
theorem physical_majorant_with_positive_N_lane_obstructed
    (N L K logPow Q B physical : ℝ) (hN : 0 < N) (hL : 0 < L)
    (hlogPow : 0 < logPow) (hgap : K < L * logPow)
    (hNlane : L * N ≤ physical)
    (hbudget : physical ≤ K * N / logPow) : False := by
  have hstrict := positive_N_lane_not_paid_by_modulus_cutoff
    N L K logPow Q B hN hL hlogPow hgap
  exact (not_lt_of_ge (hNlane.trans hbudget)) hstrict

/-- A delta mass at the top conductor.  It is the generic obstruction to
extracting an `R^{-1}` gain merely by deleting `d ≤ R`. -/
def topConductorDelta (Q d : ℕ) : ℝ := if d = Q then 1 else 0

lemma topConductorDelta_nonneg (Q d : ℕ) : 0 ≤ topConductorDelta Q d := by
  unfold topConductorDelta
  split_ifs <;> positivity

/-- If the high interval is nonempty, a nonnegative lane can be concentrated
entirely at its top conductor, so its high-conductor mass is still exactly one. -/
theorem sum_topConductorDelta_high (Q R : ℕ) (hRQ : R < Q) :
    (∑ d ∈ Finset.Icc (R + 1) Q, topConductorDelta Q d) = 1 := by
  simp [topConductorDelta, Finset.sum_ite_eq', Nat.succ_le_iff.mpr hRQ]

/-- Consequently no universal `high mass ≤ full mass / R` inequality follows
from positivity and the cutoff alone when `R>1`. -/
theorem no_inverse_cutoff_gain_from_restriction
    (Q R : ℕ) (hR : 1 < R) (hRQ : R < Q) :
    ¬ ((∑ d ∈ Finset.Icc (R + 1) Q, topConductorDelta Q d) ≤ (1 : ℝ) / R) := by
  rw [sum_topConductorDelta_high Q R hRQ]
  have hRreal : (1 : ℝ) < R := by exact_mod_cast hR
  have hinv : (1 : ℝ) / R < 1 := by
    rw [div_lt_one (by positivity : (0 : ℝ) < R)]
    exact hRreal
  exact not_le_of_gt hinv

/-- Positivity restricts either Vaughan coefficient family to high conductors
without improving the full-conductor bound. -/
private theorem highConductor_primitiveMean_le_full
    (a : ℤ → ℂ) (N Q C : ℕ) :
    apNormalizedPrimitiveMeanOn a N (highConductorSet N Q C) ≤
      apNormalizedPrimitiveMean a N Q := by
  unfold apNormalizedPrimitiveMeanOn apNormalizedPrimitiveMean
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    simp only [highConductorSet, Finset.mem_filter] at hd
    exact Finset.mem_Icc.mpr ⟨by omega, (Finset.mem_Icc.mp hd.1).2⟩
  · intro d hd hnot
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun ψ _ => primitivePrefixAmplitude_nonneg _ _ _ _)

/-- Restricting Type I to high conductors uses only positivity and therefore
retains the full-conductor right-hand side. -/
theorem highConductorVaughanTypeIMean_le_full
    (N Q C u v : ℕ) :
    highConductorVaughanTypeIMean N Q C u v ≤
      apNormalizedVaughanTypeIMean N Q u v := by
  exact highConductor_primitiveMean_le_full _ N Q C

/-- The identical monotonicity restriction for Type II.  This is the strongest
automatic bridge from the current full-range physical producer; it gives no
factor depending on the lower conductor cutoff. -/
theorem highConductorVaughanTypeIIMean_le_full
    (N Q C u v : ℕ) :
    highConductorVaughanTypeIIMean N Q C u v ≤
      apNormalizedVaughanTypeIIMean N Q u v := by
  exact highConductor_primitiveMean_le_full _ N Q C

/-- Narrowest honest missing analytic contract.  It asks only for the exact
post-conductor-transport high Vaughan hybrid, not for a BV conclusion.  The
Vaughan cutoffs may vary with `N`; fixing them before `N` would leave the
`Q*N/sqrt(u+1)` lane quantitatively unusable. -/
def StandardBVHighTypeITypeIIHybridMovingSource : Prop :=
  ∀ A C B : ℕ, ∃ u v : ℕ → ℕ, ∃ K : ℝ, 0 < K ∧
    ∀ᶠ N : ℕ in Filter.atTop,
      let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
      4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2 *
          (highConductorVaughanTypeIMean N Q C (u N) (v N) +
            highConductorVaughanTypeIIMean N Q C (u N) (v N) +
            highConductorVaughanSmallMean N Q C (v N)) ≤
        K * (N : ℝ) / Real.log N ^ A

/-- Source-faithful chosen-cutoff high-conductor interface.  For each requested
`A`, the source first chooses the Pan exponent `B` and separator exponent `C`;
only then does it choose moving Vaughan cutoffs and the implicit constant.
Unlike the legacy all-`B,C` interface, this does not demand estimates for
irrelevant choices such as `B = 0`. -/
def StandardBVHighTypeITypeIIHybridChosenSource : Prop :=
  ∀ A : ℕ, ∃ B C : ℕ, A + 3 ≤ B ∧
    ∃ u v : ℕ → ℕ, ∃ K : ℝ, 0 < K ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
        4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2 *
            (highConductorVaughanTypeIMean N Q C (u N) (v N) +
              highConductorVaughanTypeIIMean N Q C (u N) (v N) +
              highConductorVaughanSmallMean N Q C (v N)) ≤
          K * (N : ℝ) / Real.log N ^ A

/-- Compatibility adapter from the legacy uniformly quantified interface. -/
theorem standardBVHighTypeITypeIIHybridChosenSource_of_legacy
    (hhigh : StandardBVHighTypeITypeIIHybridMovingSource) :
    StandardBVHighTypeITypeIIHybridChosenSource := by
  intro A
  refine ⟨A + 3, 1, le_rfl, ?_⟩
  exact hhigh A 1 (A + 3)

/-- Pan's cutoff at a chosen `B ≥ A+3` meets the elementary payload margin. -/
private theorem panModulusCutoff_le_standardBVMargin
    (A B N : ℕ) (hAB : A + 3 ≤ B) (hN : 3 ≤ N) :
    (MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ) : ℝ) ≤
      Real.sqrt N / Real.log N ^ (A + 3) := by
  have hlog : 1 ≤ Real.log (N : ℝ) := by
    have he1 : Real.exp 1 < (3 : ℝ) :=
      Real.exp_one_lt_d9.trans (by norm_num)
    exact (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < N)).2
      (he1.trans_le (by exact_mod_cast hN)) |>.le
  have hlog0 : 0 ≤ Real.log (N : ℝ) := by positivity
  have hpow : Real.log (N : ℝ) ^ ((A + 3 : ℕ) : ℝ) ≤
      Real.log (N : ℝ) ^ (B : ℝ) := by
    exact Real.rpow_le_rpow_of_exponent_le hlog (by exact_mod_cast hAB)
  calc
    (MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ) : ℝ) ≤
        (N : ℝ) ^ (1 / 2 : ℝ) / Real.log N ^ (B : ℝ) := by
      exact Nat.floor_le (div_nonneg
        (Real.rpow_nonneg (by positivity) _)
        (Real.rpow_nonneg hlog0 _))
    _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) /
        Real.log N ^ ((A + 3 : ℕ) : ℝ) := by
      exact div_le_div_of_nonneg_left (Real.rpow_nonneg (by positivity) _)
        (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hlog) _) hpow
    _ = Real.sqrt N / Real.log N ^ (A + 3) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_natCast]

/-- Canonical sufficient assembly.  It consumes the chosen-cutoff high source
and specializes the low source only after `B,C` have been selected. -/
theorem standardBV_of_lowSW_highTypeITypeII_chosen
    (hlow : StandardBVLowSiegelWalfiszSource)
    (hhigh : StandardBVHighTypeITypeIIHybridChosenSource) :
    ∀ A : ℕ, ∃ B : ℕ, ∃ K : ℝ, 0 < K ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        (∑ q ∈ Finset.Icc 1
            (MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)),
          MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPPrefixMaxError N q) ≤
          K * (N : ℝ) / Real.log N ^ A := by
  intro A
  obtain ⟨B, C, hAB, u, v, KH, hKH, hhighN⟩ := hhigh A
  obtain ⟨KL, hKL, hlowN⟩ := hlow A C B
  refine ⟨B, KL + KH + 180, by positivity, ?_⟩
  filter_upwards [hlowN, hhighN, StandardBVPayload_payable A,
    eventually_ge_atTop (3 : ℕ)] with N hLN hHN hpayload hN
  let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
  have hcut : (Q : ℝ) ≤ Real.sqrt N / Real.log N ^ (A + 3) := by
    simpa [Q] using panModulusCutoff_le_standardBVMargin A B N hAB hN
  exact standardBV_sufficient_at_closed A B C N Q (u N) (v N) KL KH
    (by omega) rfl hLN hHN (hpayload Q hcut)

/-- Real consumer for the moving-cutoff high-conductor contract.  All finite
connectors and elementary lanes remain internal, exactly as in the fixed-cutoff
consumer; only the pointwise Vaughan cutoffs are instantiated after `N`. -/
theorem standardBV_of_lowSW_highTypeITypeII_moving
    (hlow : StandardBVLowSiegelWalfiszSource)
    (hhigh : StandardBVHighTypeITypeIIHybridMovingSource) :
    ∀ A : ℕ, ∃ B : ℕ, ∃ K : ℝ, 0 < K ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        (∑ q ∈ Finset.Icc 1
            (MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)),
          MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPPrefixMaxError N q) ≤
          K * (N : ℝ) / Real.log N ^ A := by
  exact standardBV_of_lowSW_highTypeITypeII_chosen hlow
    (standardBVHighTypeITypeIIHybridChosenSource_of_legacy hhigh)

end

end AnalyticNumberTheory.LargeSieve
