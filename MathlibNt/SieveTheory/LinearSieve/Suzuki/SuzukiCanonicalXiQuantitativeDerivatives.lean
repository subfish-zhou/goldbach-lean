import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCanonicalXiConstruction

open Set Filter Topology

namespace Section10CanonicalXi

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable def xiSlope (s : ℝ) : ℝ :=
  s - (s - 1) / xi s

lemma xi_hasDerivAt {s : ℝ} (hs : 1 < s) :
    HasDerivAt xi (xiSlope s)⁻¹ s := by
  have hxp := xi_pos hs
  have hd := eta_hasDerivAt hxp
  have hi := hd.of_local_left_inverse xi_continuous.continuousAt
    (by linarith [eta_slope_gt_half hxp]) (by
      filter_upwards [Ioi_mem_nhds hs] with y hy
      rw [eta_xi, max_eq_left hy.le])
  apply hi.congr_deriv
  change (eta (xi s) - (eta (xi s) - 1) / xi s)⁻¹ =
    (xiSlope s)⁻¹
  rw [eta_xi, max_eq_left hs.le]
  rfl

lemma xi_deriv {s : ℝ} (hs : 1 < s) :
    deriv xi s = (xiSlope s)⁻¹ :=
  (xi_hasDerivAt hs).deriv


lemma xiSlope_pos {s : ℝ} (hs : 1 < s) : 0 < xiSlope s := by
  dsimp only [xiSlope]
  linarith [xi_etaSlopeLower hs]


lemma xi_gt_one {s : ℝ} (hs : Real.exp 1 ≤ s) : 1 < xi s := by
  have hs1 : 1 < s := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by norm_num)) hs
  have hx0 : 0 ≤ xi s := (xi_pos hs1).le
  by_contra h
  have hx1 : xi s ≤ 1 := le_of_not_gt h
  have heta_le := eta_strictMonoOn.monotoneOn hx0 (by norm_num : (0 : ℝ) ≤ 1) hx1
  have heta_s : eta (xi s) = s := by rw [eta_xi, max_eq_left hs1.le]
  have heta_one : eta 1 = Real.exp 1 - 1 := by
    rw [eta_eq_div (by norm_num : (1 : ℝ) ≠ 0)]
    ring
  rw [heta_s, heta_one] at heta_le
  linarith

lemma log_lt_xi {s : ℝ} (hs : Real.exp 1 ≤ s) : Real.log s < xi s := by
  have hspos : 0 < s := lt_of_lt_of_le (Real.exp_pos 1) hs
  have hs1 : 1 < s := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by norm_num)) hs
  have hx1 := xi_gt_one hs
  have heq := xi_equation hs1
  have hexp : s < Real.exp (xi s) := by nlinarith
  exact Real.exp_lt_exp.mp (by simpa only [Real.exp_log hspos] using hexp)

private lemma one_lt_of_exp_two_le {s : ℝ} (hs : Real.exp 2 ≤ s) : 1 < s :=
  (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 2)).trans_le hs

lemma two_le_log {s : ℝ} (hs : Real.exp 2 ≤ s) : 2 ≤ Real.log s := by
  have hspos : 0 < s := lt_of_lt_of_le (Real.exp_pos 2) hs
  rw [← Real.exp_log hspos] at hs
  exact Real.exp_le_exp.mp hs

lemma two_lt_xi {s : ℝ} (hs : Real.exp 2 ≤ s) : 2 < xi s := by
  have he21 : Real.exp 1 ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
  exact lt_of_le_of_lt (two_le_log hs) (log_lt_xi (he21.trans hs))

lemma xiSlope_eq {s : ℝ} (hs : 1 < s) :
    xiSlope s = (s * (xi s - 1) + 1) / xi s := by
  have hx0 : xi s ≠ 0 := ne_of_gt (xi_pos hs)
  dsimp only [xiSlope]
  field_simp [hx0]
  ring

lemma xi_deriv_sub_reciprocal_eq {s : ℝ} (hs : 1 < s) :
    deriv xi s - 1 / s =
      (s - 1) / (s * (s * (xi s - 1) + 1)) := by
  have hs0 : s ≠ 0 := by linarith
  have hx0 : xi s ≠ 0 := ne_of_gt (xi_pos hs)
  have hB : s * (xi s - 1) + 1 ≠ 0 := by
    intro h
    have := xiSlope_pos hs
    rw [xiSlope_eq hs, h] at this
    simp at this
  rw [xi_deriv hs, xiSlope_eq hs]
  field_simp [hs0, hx0, hB]
  ring


lemma xiSlope_ge_half {s : ℝ} (hs : Real.exp 2 ≤ s) : s / 2 ≤ xiSlope s := by
  have hspos : 0 < s := lt_of_lt_of_le (Real.exp_pos 2) hs
  have hs1 : 1 < s := one_lt_of_exp_two_le hs
  have hx2 : 2 < xi s := two_lt_xi hs
  rw [xiSlope_eq hs1]
  apply (le_div_iff₀ (by linarith : 0 < xi s)).2
  nlinarith


lemma xi_deriv_le_two_div {s : ℝ} (hs : Real.exp 2 ≤ s) :
    deriv xi s ≤ 2 / s := by
  have hspos : 0 < s := lt_of_lt_of_le (Real.exp_pos 2) hs
  have hs1 : 1 < s := one_lt_of_exp_two_le hs
  rw [xi_deriv hs1]
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ (xiSlope_pos hs1) hspos).2
  nlinarith [xiSlope_ge_half hs]


end Section10CanonicalXi
