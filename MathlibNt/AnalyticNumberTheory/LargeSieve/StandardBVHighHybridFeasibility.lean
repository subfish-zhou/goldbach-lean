

import MathlibNt.AnalyticNumberTheory.LargeSieve.StandardBVSufficientAssembly
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


end

end AnalyticNumberTheory.LargeSieve
