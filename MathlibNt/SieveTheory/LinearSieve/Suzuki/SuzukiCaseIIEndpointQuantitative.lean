import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIILambdaShortInterval
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIIEndpointTransport

open scoped Classical BigOperators Interval
open MeasureTheory Set

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

/-- Uniform lower bound for the odd Case-II error envelope on `1 < s ≤ 3`.
This is what allows all fixed finite endpoint terms divided by `log D` to be
absorbed uniformly as `D → ∞`. -/
theorem one_third_le_errorEnvelope_caseII
    {H : Section13HatLayers} {N : ℕ} {D d s : ℝ}
    (hH : Section13HatContract H 2) (hN : Odd N)
    (hD : 1 < D) (hs1 : 1 < s) (hs3 : s ≤ 3) :
    (1 / 3 : ℝ) ≤ errorEnvelope H N D d s := by
  have hs : 0 < s := zero_lt_one.trans hs1
  have hlog : 0 < Real.log D := Real.log_pos hD
  have hbase : 1 ≤ 1 + s ^ d / Real.log D := by
    have hq : 0 ≤ s ^ d / Real.log D :=
      div_nonneg (Real.rpow_nonneg hs.le d) hlog.le
    linarith
  have hpert : 1 ≤ perturbation D d 0 s := by
    rw [perturbation]
    norm_num
    exact Real.one_le_rpow hbase hs.le
  have hinit := hH.initial_plus s hs (by norm_num at hs3 ⊢; exact hs3)
  norm_num at hinit
  rw [errorEnvelope_eq_lambda_div H hs,
      lambda_eq_perturb_mul_weightedHat,
      ErrorSign.ofDepth_of_odd hN, hinit]
  have hinv : (1 / 3 : ℝ) ≤ 1 / s := by
    exact one_div_le_one_div_of_le hs hs3
  have hmul : 1 / s ≤ perturbation D d 0 s / s := by
    exact (div_le_div_iff_of_pos_right hs).2 hpert
  exact hinv.trans (by simpa only [perturbation, zero_add, mul_one] using hmul)

/-- At the cubic endpoint the opposite-sign `q_D` is completely explicit from
Section 13 initial data. -/
theorem qD_minus_three_eq
    {H : Section13HatLayers} {D d Δ : ℝ}
    (hH : Section13HatContract H 2) :
    qD H .minus D d Δ 3 =
      (1 + (3 : ℝ) ^ d / Real.log D) ^ (2 : ℕ) * ((3 : ℝ) / 2) ^ Δ := by
  have hinit := hH.initial_minus 2 (by norm_num) (by norm_num)
  simp only [qD, Section13HatLayers.kappaHat]
  norm_num [Real.rpow_one]
  have hT : H.T .minus 2 = 1 / 2 := by
    rw [weightedHat] at hinit
    norm_num [Real.rpow_two] at hinit ⊢
    linarith
  rw [hT]
  have hc : (1 + (3 : ℝ) ^ d / Real.log D) ^ (2 : ℕ) * 2 * (1 / 2) =
      (1 + (3 : ℝ) ^ d / Real.log D) ^ (2 : ℕ) := by ring
  exact Or.inl hc

/-- In odd Case II, the endpoint `q_D` in the transported Case-I remainder is
the explicit minus-sign cubic value. -/
theorem qD_opposite_three_eq_of_odd
    {H : Section13HatLayers} {N : ℕ} {D d Δ : ℝ}
    (hH : Section13HatContract H 2) (hN : Odd N) :
    qD H (ErrorSign.ofDepth N).opposite D d Δ 3 =
      (1 + (3 : ℝ) ^ d / Real.log D) ^ (2 : ℕ) * ((3 : ℝ) / 2) ^ Δ := by
  rw [ErrorSign.ofDepth_of_odd hN]
  exact qD_minus_three_eq hH


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
