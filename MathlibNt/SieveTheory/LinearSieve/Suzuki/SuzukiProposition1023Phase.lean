import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCanonicalXiQuantitativeDerivatives

open Set Filter Topology MeasureTheory intervalIntegral
open scoped Interval

namespace Section10CanonicalXi

set_option autoImplicit false
set_option maxHeartbeats 800000

private noncomputable def phaseThreshold : ℝ := Real.exp 2
private noncomputable def phaseLogConstant : ℝ := xi phaseThreshold + 3
private noncomputable def phaseConstant : ℝ :=
  xi phaseThreshold + Real.log phaseLogConstant

lemma xi_monotone : Monotone xi := by
  intro a b hab
  change ((etaOrderIso.symm ⟨max a 1, le_max_right a 1⟩ : Ici (0 : ℝ)) : ℝ) ≤
    ((etaOrderIso.symm ⟨max b 1, le_max_right b 1⟩ : Ici (0 : ℝ)) : ℝ)
  exact etaOrderIso.symm.monotone (max_le_max hab le_rfl)

lemma xi_sub_two_log_antitone :
    AntitoneOn (fun s : ℝ => xi s - 2 * Real.log s) (Ici phaseThreshold) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici phaseThreshold)
  · apply xi_continuous.continuousOn.sub
    intro s hs
    exact (Real.continuousAt_log (ne_of_gt (lt_of_lt_of_le (by
      dsimp [phaseThreshold]
      exact Real.exp_pos 2) hs))).const_mul 2 |>.continuousWithinAt
  · intro s hs
    rw [interior_Ici] at hs
    have hspos : 0 < s := lt_trans (by
      dsimp [phaseThreshold]
      exact Real.exp_pos 2) hs
    exact ((xi_hasDerivAt (lt_trans (by
      dsimp [phaseThreshold]
      exact Real.one_lt_exp_iff.mpr (by norm_num)) hs)).differentiableAt.sub
        ((Real.hasDerivAt_log (ne_of_gt hspos)).const_mul 2).differentiableAt).differentiableWithinAt
  · intro s hs
    rw [interior_Ici] at hs
    have hs' : phaseThreshold ≤ s := hs.le
    have hspos : 0 < s := lt_of_lt_of_le (by
      dsimp [phaseThreshold]
      exact Real.exp_pos 2) hs'
    have hs0 : s ≠ 0 := ne_of_gt hspos
    have hderiv : deriv (fun u : ℝ => xi u - 2 * Real.log u) s =
        deriv xi s - 2 / s := by
      have hd := ((xi_hasDerivAt (lt_trans (by
        dsimp [phaseThreshold]
        exact Real.one_lt_exp_iff.mpr (by norm_num)) hs)).sub
          ((Real.hasDerivAt_log hs0).const_mul 2)).deriv
      have hfun : (xi - fun u : ℝ => 2 * Real.log u) =
          (fun u : ℝ => xi u - 2 * Real.log u) := by
        funext u
        rfl
      have hd' : deriv (fun u : ℝ => xi u - 2 * Real.log u) s =
          (xiSlope s)⁻¹ - 2 * s⁻¹ := by
        rw [← hfun]
        exact hd
      rw [hd', ← xi_deriv (lt_trans (by
        dsimp [phaseThreshold]
        exact Real.one_lt_exp_iff.mpr (by norm_num)) hs)]
      field_simp [hs0]
    rw [hderiv]
    exact sub_nonpos.mpr (xi_deriv_le_two_div hs')

lemma xi_le_two_log_add {s : ℝ} (hs : phaseThreshold ≤ s) :
    xi s ≤ xi phaseThreshold + 2 * Real.log s := by
  have h := xi_sub_two_log_antitone (show phaseThreshold ∈ Ici phaseThreshold by simp)
    (show s ∈ Ici phaseThreshold from hs) hs
  have hlogA : Real.log phaseThreshold = 2 := by
    dsimp [phaseThreshold]
    rw [Real.log_exp]
  simp only at h
  rw [hlogA] at h
  linarith

lemma phaseLogConstant_gt_one : 1 < phaseLogConstant := by
  have hA1 : 1 < phaseThreshold := by
    dsimp [phaseThreshold]
    exact Real.one_lt_exp_iff.mpr (by norm_num)
  have hx : 0 < xi phaseThreshold := xi_pos hA1
  dsimp [phaseLogConstant]
  linarith

/-- Pointwise coarse phase estimate obtained from the canonical equation, not assumed. -/
lemma xi_le_coarse_phase {s : ℝ} (hs : phaseThreshold ≤ s) :
    xi s ≤ Real.log s + Real.log (Real.log (3 * s)) +
      Real.log phaseLogConstant := by
  have hspos : 0 < s := lt_of_lt_of_le (by
    dsimp [phaseThreshold]
    exact Real.exp_pos 2) hs
  have hs1 : 1 < s := lt_of_lt_of_le (by
    dsimp [phaseThreshold]
    exact Real.one_lt_exp_iff.mpr (by norm_num)) hs
  have hlogs : 2 ≤ Real.log s := by
    rw [← Real.exp_log hspos] at hs
    dsimp [phaseThreshold] at hs
    exact Real.exp_le_exp.mp hs
  have h3spos : 0 < 3 * s := mul_pos (by norm_num) hspos
  have hlogmono : Real.log s ≤ Real.log (3 * s) :=
    Real.strictMonoOn_log.monotoneOn hspos h3spos (by nlinarith)
  have hlog3s : 1 < Real.log (3 * s) := lt_of_lt_of_le (by norm_num) hlogs |>.trans_le hlogmono
  have hxA0 : 0 ≤ xi phaseThreshold := (xi_pos (by
    dsimp [phaseThreshold]
    exact Real.one_lt_exp_iff.mpr (by norm_num))).le
  have hinv : 1 / s ≤ 1 := (div_le_one hspos).2 (by linarith)
  have hxi := xi_le_two_log_add hs
  have hprod : xi phaseThreshold + 2 * Real.log s + 1 ≤
      phaseLogConstant * Real.log (3 * s) := by
    dsimp [phaseLogConstant]
    nlinarith [mul_nonneg hxA0 (sub_nonneg.mpr hlog3s.le)]
  have harg : xi s + 1 / s ≤ phaseLogConstant * Real.log (3 * s) := by
    linarith
  have hargpos : 0 < xi s + 1 / s := add_pos (xi_pos hs1) (by positivity)
  have hLpos : 0 < phaseLogConstant := lt_trans (by norm_num) phaseLogConstant_gt_one
  have hlogpos : 0 < Real.log (3 * s) := lt_trans (by norm_num) hlog3s
  have hlogarg : Real.log (xi s + 1 / s) ≤
      Real.log (phaseLogConstant * Real.log (3 * s)) :=
    Real.strictMonoOn_log.monotoneOn hargpos (mul_pos hLpos hlogpos) harg
  have heq : Real.exp (xi s) = s * (xi s + 1 / s) := by
    calc
      Real.exp (xi s) = s * xi s + 1 := by linarith [xi_equation hs1]
      _ = s * (xi s + 1 / s) := by field_simp [ne_of_gt hspos]
  have hlogeq := congrArg Real.log heq
  rw [Real.log_exp, Real.log_mul (ne_of_gt hspos) (ne_of_gt hargpos)] at hlogeq
  rw [Real.log_mul (ne_of_gt hLpos) (ne_of_gt hlogpos)] at hlogarg
  linarith

lemma coarse_phase_uniform_on_Icc {s t : ℝ} (hs : phaseThreshold ≤ s)
    (ht : t ∈ Icc 1 s) :
    xi t ≤ Real.log s + Real.log (Real.log (3 * s)) + phaseConstant := by
  have hspos : 0 < s := lt_of_lt_of_le (by
    dsimp [phaseThreshold]
    exact Real.exp_pos 2) hs
  have h3spos : 0 < 3 * s := mul_pos (by norm_num) hspos
  have hlogs : 2 ≤ Real.log s := by
    rw [← Real.exp_log hspos] at hs
    dsimp [phaseThreshold] at hs
    exact Real.exp_le_exp.mp hs
  have hlog3s : 0 < Real.log (3 * s) := by
    have := Real.strictMonoOn_log.monotoneOn hspos h3spos (by nlinarith : s ≤ 3 * s)
    linarith
  by_cases htA : t < phaseThreshold
  · have hmono := xi_monotone htA.le
    dsimp [phaseConstant]
    have hLlog : 0 < Real.log phaseLogConstant := Real.log_pos phaseLogConstant_gt_one
    have hll : 0 < Real.log (Real.log (3 * s)) := Real.log_pos (by
      have hm : Real.log s ≤ Real.log (3 * s) :=
        Real.strictMonoOn_log.monotoneOn hspos h3spos (by nlinarith)
      linarith)
    linarith
  · have htA' : phaseThreshold ≤ t := le_of_not_gt htA
    have htpos : 0 < t := lt_of_lt_of_le (by
      dsimp [phaseThreshold]
      exact Real.exp_pos 2) htA'
    have h3tpos : 0 < 3 * t := mul_pos (by norm_num) htpos
    have hlogt : Real.log t ≤ Real.log s :=
      Real.strictMonoOn_log.monotoneOn htpos hspos ht.2
    have hlog3t : Real.log (3 * t) ≤ Real.log (3 * s) :=
      Real.strictMonoOn_log.monotoneOn h3tpos h3spos
        (mul_le_mul_of_nonneg_left ht.2 (by norm_num))
    have hinnerpos : 0 < Real.log (3 * t) := by
      have htl : 2 ≤ Real.log t := by
        rw [← Real.exp_log htpos] at htA'
        dsimp [phaseThreshold] at htA'
        exact Real.exp_le_exp.mp htA'
      have hm := Real.strictMonoOn_log.monotoneOn htpos h3tpos (by nlinarith : t ≤ 3 * t)
      linarith
    have hloglog : Real.log (Real.log (3 * t)) ≤ Real.log (Real.log (3 * s)) :=
      Real.strictMonoOn_log.monotoneOn hinnerpos hlog3s hlog3t
    have hpt := xi_le_coarse_phase htA'
    dsimp [phaseConstant]
    have hxA0 : 0 ≤ xi phaseThreshold := (xi_pos (by
      dsimp [phaseThreshold]
      exact Real.one_lt_exp_iff.mpr (by norm_num))).le
    linarith

/-- Proposition 10.23, coarse phase-integral upper bound for `κ=b=1`.
The bound is proved for the canonical `xi`; no phase estimate is a premise. -/
theorem proposition1023_coarse_phase :
    ∀ᶠ s : ℝ in atTop,
      (∫ t in (1 : ℝ)..s, xi t) ≤
        s * Real.log s + s * Real.log (Real.log (3 * s)) + phaseConstant * s := by
  filter_upwards [eventually_ge_atTop phaseThreshold] with s hs
  have hs1 : 1 ≤ s := le_trans (by
    dsimp [phaseThreshold]
    exact (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 2)).le) hs
  have hxiInt : IntervalIntegrable xi volume 1 s :=
    xi_continuous.intervalIntegrable 1 s
  let M : ℝ := Real.log s + Real.log (Real.log (3 * s)) + phaseConstant
  have hMInt : IntervalIntegrable (fun _ : ℝ => M) volume 1 s :=
    continuous_const.intervalIntegrable 1 s
  have hmono : (∫ t in (1 : ℝ)..s, xi t) ≤ ∫ _t in (1 : ℝ)..s, M := by
    apply intervalIntegral.integral_mono_on hs1 hxiInt hMInt
    intro t ht
    exact coarse_phase_uniform_on_Icc hs ht
  rw [intervalIntegral.integral_const] at hmono
  change (∫ t in (1 : ℝ)..s, xi t) ≤ (s - 1) * M at hmono
  have hspos : 0 < s := lt_of_lt_of_le (by
    dsimp [phaseThreshold]
    exact Real.exp_pos 2) hs
  have hlogs : 0 ≤ Real.log s := Real.log_nonneg (by linarith)
  have h3slog : 1 < Real.log (3 * s) := by
    have hlogs2 : 2 ≤ Real.log s := by
      rw [← Real.exp_log hspos] at hs
      dsimp [phaseThreshold] at hs
      exact Real.exp_le_exp.mp hs
    have h3spos : 0 < 3 * s := mul_pos (by norm_num) hspos
    have hm := Real.strictMonoOn_log.monotoneOn hspos h3spos (by nlinarith : s ≤ 3 * s)
    linarith
  have hloglog : 0 ≤ Real.log (Real.log (3 * s)) :=
    (Real.log_pos h3slog).le
  have hxA0 : 0 ≤ xi phaseThreshold := (xi_pos (by
    dsimp [phaseThreshold]
    exact Real.one_lt_exp_iff.mpr (by norm_num))).le
  have hlogL : 0 ≤ Real.log phaseLogConstant := (Real.log_pos phaseLogConstant_gt_one).le
  have hC : 0 ≤ phaseConstant := by
    dsimp [phaseConstant]
    positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  calc
    (∫ t in (1 : ℝ)..s, xi t) ≤ (s - 1) * M := hmono
    _ ≤ s * M := by nlinarith
    _ = s * Real.log s + s * Real.log (Real.log (3 * s)) + phaseConstant * s := by
      dsimp [M]
      ring

end Section10CanonicalXi
