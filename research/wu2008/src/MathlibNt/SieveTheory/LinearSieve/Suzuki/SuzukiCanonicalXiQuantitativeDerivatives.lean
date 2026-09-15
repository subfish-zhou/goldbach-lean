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

lemma xiSlope_hasDerivAt {s : ℝ} (hs : 1 < s) :
    HasDerivAt xiSlope
      (1 - 1 / xi s + (s - 1) * (xiSlope s)⁻¹ / (xi s) ^ 2) s := by
  have hx0 : xi s ≠ 0 := ne_of_gt (xi_pos hs)
  have hq := ((hasDerivAt_id s).sub_const 1).div (xi_hasDerivAt hs) hx0
  have hout := (hasDerivAt_id s).sub hq
  change HasDerivAt (fun u => u - (u - 1) / xi u) _ s
  apply hout.congr_deriv
  simp only [id_eq]
  field_simp [hx0]
  ring

lemma xiSlope_pos {s : ℝ} (hs : 1 < s) : 0 < xiSlope s := by
  dsimp only [xiSlope]
  linarith [xi_etaSlopeLower hs]

/-- Exact second implicit-derivative formula for the canonical inverse. -/
lemma xi_hasDerivAt_deriv {s : ℝ} (hs : 1 < s) :
    HasDerivAt (deriv xi)
      (-(1 - 1 / xi s + (s - 1) * (xiSlope s)⁻¹ / (xi s) ^ 2) /
        (xiSlope s) ^ 2) s := by
  have hD : xiSlope s ≠ 0 := (xiSlope_pos hs).ne'
  have hi := (xiSlope_hasDerivAt hs).inv hD
  have hevent : deriv xi =ᶠ[𝓝 s] fun u => (xiSlope u)⁻¹ := by
    filter_upwards [Ioi_mem_nhds hs] with u hu
    exact xi_deriv hu
  exact hi.congr_of_eventuallyEq hevent

lemma xi_twiceDifferentiableAt {s : ℝ} (hs : 1 < s) :
    DifferentiableAt ℝ (deriv xi) s :=
  (xi_hasDerivAt_deriv hs).differentiableAt

lemma xi_secondDeriv {s : ℝ} (hs : 1 < s) :
    deriv (deriv xi) s =
      -(1 - 1 / xi s + (s - 1) * (xiSlope s)⁻¹ / (xi s) ^ 2) /
        (xiSlope s) ^ 2 :=
  (xi_hasDerivAt_deriv hs).deriv

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

/-- Quantitative first-order asymptotic, with explicit threshold and constant. -/
theorem xi_deriv_asymptotic {s : ℝ} (hs : Real.exp 2 ≤ s) :
    |deriv xi s - 1 / s| ≤ 2 / (s * Real.log s) := by
  have hspos : 0 < s := lt_of_lt_of_le (Real.exp_pos 2) hs
  have hs1 : 1 < s := one_lt_of_exp_two_le hs
  have hlog : 2 ≤ Real.log s := two_le_log hs
  have hlogpos : 0 < Real.log s := by linarith
  have hxlog : Real.log s < xi s := by
    exact log_lt_xi ((Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 2)).trans hs)
  have hmul : s * Real.log s ≤ s * xi s :=
    mul_le_mul_of_nonneg_left hxlog.le hspos.le
  have hBpos : 0 < s * (xi s - 1) + 1 := by nlinarith
  have hinner : (s - 1) * Real.log s ≤ 2 * (s * (xi s - 1) + 1) := by
    nlinarith
  have hcross := mul_le_mul_of_nonneg_left hinner hspos.le
  rw [xi_deriv_sub_reciprocal_eq hs1, abs_of_nonneg]
  · apply (div_le_div_iff₀ (mul_pos hspos hBpos) (mul_pos hspos hlogpos)).2
    nlinarith [hcross]
  · exact div_nonneg (by linarith) (mul_nonneg hspos.le hBpos.le)

lemma xiSlope_ge_half {s : ℝ} (hs : Real.exp 2 ≤ s) : s / 2 ≤ xiSlope s := by
  have hspos : 0 < s := lt_of_lt_of_le (Real.exp_pos 2) hs
  have hs1 : 1 < s := one_lt_of_exp_two_le hs
  have hx2 : 2 < xi s := two_lt_xi hs
  rw [xiSlope_eq hs1]
  apply (le_div_iff₀ (by linarith : 0 < xi s)).2
  nlinarith

lemma xi_deriv_nonneg {s : ℝ} (hs : 1 < s) : 0 ≤ deriv xi s := by
  rw [xi_deriv hs]
  exact inv_nonneg.mpr (xiSlope_pos hs).le

lemma xi_deriv_le_two_div {s : ℝ} (hs : Real.exp 2 ≤ s) :
    deriv xi s ≤ 2 / s := by
  have hspos : 0 < s := lt_of_lt_of_le (Real.exp_pos 2) hs
  have hs1 : 1 < s := one_lt_of_exp_two_le hs
  rw [xi_deriv hs1]
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ (xiSlope_pos hs1) hspos).2
  nlinarith [xiSlope_ge_half hs]

noncomputable def xiCurvatureFactor (s : ℝ) : ℝ :=
  1 - 1 / xi s + (s - 1) * (xiSlope s)⁻¹ / (xi s) ^ 2

lemma xiCurvatureFactor_nonneg {s : ℝ} (hs : Real.exp 2 ≤ s) :
    0 ≤ xiCurvatureFactor s := by
  have hs1 : 1 < s := one_lt_of_exp_two_le hs
  have hx2 : 2 < xi s := two_lt_xi hs
  have hxi_inv : 0 ≤ 1 / xi s := by positivity
  have hterm : 0 ≤ (s - 1) * (xiSlope s)⁻¹ / (xi s) ^ 2 := by
    exact div_nonneg (mul_nonneg (by linarith)
      (inv_nonneg.mpr (xiSlope_pos hs1).le)) (sq_nonneg (xi s))
  dsimp only [xiCurvatureFactor]
  have : 1 / xi s ≤ 1 := (div_le_one (by linarith : 0 < xi s)).2 (by linarith)
  linarith

lemma xiCurvatureFactor_le_three_halves {s : ℝ} (hs : Real.exp 2 ≤ s) :
    xiCurvatureFactor s ≤ 3 / 2 := by
  have hspos : 0 < s := lt_of_lt_of_le (Real.exp_pos 2) hs
  have hs1 : 1 < s := one_lt_of_exp_two_le hs
  have hx2 : 2 < xi s := two_lt_xi hs
  have hdinv0 : 0 ≤ (xiSlope s)⁻¹ := inv_nonneg.mpr (xiSlope_pos hs1).le
  have hdinv : (xiSlope s)⁻¹ ≤ 2 / s := by
    rw [← xi_deriv hs1]
    exact xi_deriv_le_two_div hs
  have hp1 : (s - 1) * (xiSlope s)⁻¹ ≤ s * (xiSlope s)⁻¹ := by
    exact mul_le_mul_of_nonneg_right (by linarith) hdinv0
  have hp2 : s * (xiSlope s)⁻¹ ≤ 2 := by
    have := mul_le_mul_of_nonneg_left hdinv hspos.le
    field_simp [ne_of_gt hspos] at this
    exact this
  have hx_sq : 4 ≤ (xi s) ^ 2 := by nlinarith
  have hterm : (s - 1) * (xiSlope s)⁻¹ / (xi s) ^ 2 ≤ 1 / 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < xi s))).2
    nlinarith
  have hinv0 : 0 ≤ 1 / xi s := by positivity
  dsimp only [xiCurvatureFactor]
  linarith

/-- Quantitative second-order asymptotic, with explicit threshold and constant. -/
theorem xi_secondDeriv_asymptotic {s : ℝ} (hs : Real.exp 2 ≤ s) :
    |deriv (deriv xi) s| ≤ 6 / s ^ 2 := by
  have hspos : 0 < s := lt_of_lt_of_le (Real.exp_pos 2) hs
  have hs1 : 1 < s := one_lt_of_exp_two_le hs
  have hDpos := xiSlope_pos hs1
  have hE0 := xiCurvatureFactor_nonneg hs
  have hE := xiCurvatureFactor_le_three_halves hs
  have hD := xiSlope_ge_half hs
  have hDsq : s ^ 2 / 4 ≤ (xiSlope s) ^ 2 := by nlinarith
  have hleft := mul_le_mul_of_nonneg_right hE (sq_nonneg s)
  have hcross : xiCurvatureFactor s * s ^ 2 ≤ 6 * (xiSlope s) ^ 2 := by
    nlinarith
  rw [xi_secondDeriv hs1]
  change |-(xiCurvatureFactor s) / (xiSlope s) ^ 2| ≤ 6 / s ^ 2
  rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hE0)
    (sq_nonneg (xiSlope s)))]
  rw [neg_div, neg_neg]
  apply (div_le_div_iff₀ (sq_pos_of_pos hDpos) (sq_pos_of_pos hspos)).2
  nlinarith [hcross]

/-- First-derivative estimate uniformly on the unit window `[s,s+1]`. -/
theorem xi_deriv_asymptotic_unitWindow {s t : ℝ} (hs : Real.exp 2 ≤ s)
    (ht : t ∈ Icc s (s + 1)) :
    |deriv xi t - 1 / t| ≤ 2 / (s * Real.log s) := by
  have hspos : 0 < s := lt_of_lt_of_le (Real.exp_pos 2) hs
  have htpos : 0 < t := lt_of_lt_of_le hspos ht.1
  have hlogs : 0 < Real.log s := lt_of_lt_of_le (by norm_num) (two_le_log hs)
  have hlogmono : Real.log s ≤ Real.log t := Real.log_le_log hspos ht.1
  have hprod : s * Real.log s ≤ t * Real.log t :=
    mul_le_mul ht.1 hlogmono hlogs.le htpos.le
  calc
    |deriv xi t - 1 / t| ≤ 2 / (t * Real.log t) :=
      xi_deriv_asymptotic (hs.trans ht.1)
    _ ≤ 2 / (s * Real.log s) :=
      div_le_div_of_nonneg_left (by norm_num) (mul_pos hspos hlogs) hprod

/-- Second-derivative estimate uniformly on the unit window `[s,s+1]`. -/
theorem xi_secondDeriv_asymptotic_unitWindow {s t : ℝ} (hs : Real.exp 2 ≤ s)
    (ht : t ∈ Icc s (s + 1)) :
    |deriv (deriv xi) t| ≤ 6 / s ^ 2 := by
  have hspos : 0 < s := lt_of_lt_of_le (Real.exp_pos 2) hs
  have htpos : 0 < t := lt_of_lt_of_le hspos ht.1
  have hsq : s ^ 2 ≤ t ^ 2 := (sq_le_sq₀ hspos.le htpos.le).2 ht.1
  calc
    |deriv (deriv xi) t| ≤ 6 / t ^ 2 := xi_secondDeriv_asymptotic (hs.trans ht.1)
    _ ≤ 6 / s ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hspos) hsq

end Section10CanonicalXi
