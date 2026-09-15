

import MathlibNt.AnalyticNumberTheory.LargeSieve.StandardBVLowSiegelWalfiszProducer
import MathlibNt.AnalyticNumberTheory.LargeSieve.StandardBVHighChosenUnconditional

/-!
 # Final low-only producer for Standard Bombieri--Vinogradov

The chosen high-conductor source is unconditional, so the final assembly retains
only the genuine low-end input.  At source level this is exactly the
nonprincipal primitive Siegel--Walfisz source together with the modulus-one
global principal PNT source.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset Filter
open scoped BigOperators ArithmeticFunction Topology

noncomputable section

/-- Once the low Siegel--Walfisz contract is supplied, the unconditional chosen
high source closes Standard Bombieri--Vinogradov. -/
theorem standardBombieriVinogradov_of_lowSiegelWalfiszSource
    (hlow : StandardBVLowSiegelWalfiszSource) :
    MathlibNt.SieveTheory.BombieriVinogradov.StandardBombieriVinogradov := by
  have hnat := standardBV_of_lowSW_highTypeITypeII_chosen
    hlow standardBVHighChosenUnconditional
  intro A hA
  let An : ℕ := Nat.ceil A
  obtain ⟨B, K, hK, hN⟩ := hnat An
  refine ⟨(B : ℝ), by positivity, K, hK, ?_⟩
  filter_upwards [hN, eventually_ge_atTop (3 : ℕ)] with N hBN hN3
  intro _hN2
  have hlog : 1 ≤ Real.log (N : ℝ) := by
    exact ((Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < N)).2
      (Real.exp_one_lt_three.trans_le (by exact_mod_cast hN3))).le
  have hAceil : A ≤ (An : ℝ) := Nat.le_ceil A
  have hpow : Real.log (N : ℝ) ^ A ≤ Real.log (N : ℝ) ^ An := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hlog hAceil
  -- The natural-exponent estimate implies the requested real-exponent bound:
  -- increasing the exponent enlarges the positive denominator because log N ≥ 1.
  calc
    _ ≤ K * (N : ℝ) / Real.log (N : ℝ) ^ An := hBN
    _ ≤ K * (N : ℝ) / Real.log (N : ℝ) ^ A :=
      div_le_div_of_nonneg_left (mul_nonneg hK.le (by positivity))
        (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hlog) A) hpow

/-- Final source-level low-only producer.  There is no historical Vaughan-row
premise: the high source is `standardBVHighChosenUnconditional`. -/
theorem standardBombieriVinogradov_of_nonprincipalPrimitivePsi_lowOnly
    (hSW : NonprincipalPrimitivePsiSiegelWalfiszSource)
    (hPNT : GlobalChebyshevToLiPrincipalPNTSourceContract) :
    MathlibNt.SieveTheory.BombieriVinogradov.StandardBombieriVinogradov := by
  exact standardBombieriVinogradov_of_lowSiegelWalfiszSource
    (standardBVLowSiegelWalfiszSource_of_nonprincipalPrimitivePsi hSW hPNT)

end

end AnalyticNumberTheory.LargeSieve
