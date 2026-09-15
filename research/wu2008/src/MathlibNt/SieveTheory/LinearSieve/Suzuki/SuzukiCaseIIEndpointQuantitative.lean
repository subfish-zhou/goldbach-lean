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

/-- Exact reciprocal logarithm at the cubic cutoff. -/
theorem one_div_log_cubic_endpoint
    {D y : ℝ} (hD : 1 < D) (hy : y = D ^ (1 / (3 : ℝ))) :
    1 / Real.log y = 3 / Real.log D := by
  rw [SuzukiPowerCoordinates.log_upper_endpoint hD (by norm_num) hy, one_div_div]

/-- Exact reciprocal logarithm at the lower `σ` power coordinate. -/
theorem one_div_log_sigma_endpoint
    {D w σ : ℝ} (hD : 1 < D) (hσ : 0 < σ)
    (hw : w = D ^ (1 / σ)) :
    1 / Real.log w = σ / Real.log D := by
  rw [SuzukiPowerCoordinates.log_lower_endpoint hD hσ hw, one_div_div]

/-- Cubic perturbation is quantitatively `1 + O(3^d / log D)`. -/
theorem perturbation_three_le_one_add_seven_ratio
    {D d : ℝ} (hD : 1 < D) (hsmall : (3 : ℝ) ^ d ≤ Real.log D) :
    perturbation D d 0 3 ≤ 1 + 7 * ((3 : ℝ) ^ d / Real.log D) := by
  let x : ℝ := (3 : ℝ) ^ d / Real.log D
  have hlog : 0 < Real.log D := Real.log_pos hD
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact div_nonneg (Real.rpow_nonneg (by norm_num) d) hlog.le
  have hx1 : x ≤ 1 := by
    dsimp [x]
    exact (div_le_one hlog).2 hsmall
  have hx2 : x ^ 2 ≤ x := by
    simpa only [pow_two, mul_one] using mul_le_mul_of_nonneg_left hx1 hx0
  have hx3 : x ^ 3 ≤ x := by
    calc
      x ^ 3 = x ^ 2 * x := pow_succ x 2
      _ ≤ x * x := mul_le_mul_of_nonneg_right hx2 hx0
      _ ≤ x := by simpa only [pow_two] using hx2
  rw [perturbation]
  norm_num [Real.rpow_natCast]
  change (1 + x) ^ 3 ≤ 1 + 7 * x
  nlinarith [hx2, hx3]

/-- Once the cubic perturbation is smaller than half the strict Claim-14.6(iii)
margin, its product with the contraction coefficient still leaves half of that
margin for all finite endpoint terms. -/
theorem caseII_contraction_with_cubic_perturbation
    {D d Δ σ : ℝ}
    (hσ : 1 < σ) (_hΔ : Δ < 1)
    (hpert : perturbation D d 0 3 ≤
      1 + (1 - (1 - 1 / σ) ^ (1 - Δ)) /
        (2 * (1 - 1 / σ) ^ (1 - Δ))) :
    (1 - 1 / σ) ^ (1 - Δ) * perturbation D d 0 3 ≤
      (1 + (1 - 1 / σ) ^ (1 - Δ)) / 2 := by
  let c : ℝ := (1 - 1 / σ) ^ (1 - Δ)
  have hbase : 0 < 1 - 1 / σ := by
    exact sub_pos.mpr ((div_lt_one (zero_lt_one.trans hσ)).2 hσ)
  have hc0 : 0 < c := Real.rpow_pos_of_pos hbase _
  have hpert' : perturbation D d 0 3 ≤ 1 + (1 - c) / (2 * c) := by
    simpa only [c] using hpert
  have hm := mul_le_mul_of_nonneg_left hpert' hc0.le
  have halg : c * (1 + (1 - c) / (2 * c)) = (1 + c) / 2 := by
    field_simp [ne_of_gt hc0]
    ring
  have hfinal : c * perturbation D d 0 3 ≤ (1 + c) / 2 :=
    hm.trans_eq halg
  simpa only [c] using hfinal

end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
