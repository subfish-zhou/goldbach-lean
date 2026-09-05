import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLZeroFreeHalfPlaneLogDerivative

open Complex Metric Set

namespace Eq21FiniteLogDerivative
noncomputable section

/-- The entire anchor disk fits inside the finite enlarged rectangle. -/
theorem anchor_disk_subset_rectangle {δ T t : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) (ht : |t| ≤ T) {w : ℂ}
    (hw : w ∈ ball ((1 + δ / 2 : ℝ) + I * t) (3 * δ / 2)) :
    1 - δ ≤ w.re ∧ w.re ≤ 2 ∧ |w.im| ≤ T + 1 := by
  have hn : ‖w - ((1 + δ / 2 : ℝ) + I * t)‖ < 3 * δ / 2 := by
    simpa only [mem_ball, dist_eq_norm] using hw
  have hre := (abs_le.mp (Complex.abs_re_le_norm
    (w - ((1 + δ / 2 : ℝ) + I * t)))).2
  have him := Complex.abs_im_le_norm (w - ((1 + δ / 2 : ℝ) + I * t))
  simp only [sub_re, add_re, ofReal_re, mul_re, I_re, zero_mul,
    I_im, ofReal_im, mul_zero, sub_zero, add_zero] at hre
  simp only [sub_im, add_im, ofReal_im, mul_im, I_re, zero_mul,
    I_im, ofReal_re, one_mul, zero_add] at him
  refine ⟨(Eq21LocalLog.anchor_disk_re_lower hδ t hw).le, by linarith, ?_⟩
  have hab : |w.im| ≤ |w.im - t| + |t| := by
    simpa only [sub_add_cancel] using abs_add_le (w.im - t) t
  linarith

/-- Only finite-rectangle nonvanishing is assumed; growth, anchor and the
holomorphic logarithm are supplied by the genuine small-disk theorem. -/
theorem norm_logDeriv_LFunction_le_of_zeroFree_rectangle
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {δ T : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) (_hT : 0 ≤ T)
    (hzero : ∀ z : ℂ, 1 - δ ≤ z.re → z.re ≤ 2 → |z.im| ≤ T + 1 →
      χ.LFunction z ≠ 0)
    (t β : ℝ) (ht : |t| ≤ T) (hβlo : 1 - δ / 2 ≤ β) (hβhi : β ≤ 1 + δ) :
    ‖logDeriv χ.LFunction ((β : ℂ) + I * t)‖ ≤
      40 / δ * Real.log (32 * q * (1 + |t|) / δ) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
  have hbB : δ / 4 < 8 * q * (1 + |t|) := by
    have hprod : (1 : ℝ) ≤ q * (1 + |t|) := by
      nlinarith [abs_nonneg t]
    nlinarith
  have hz : dist ((β : ℂ) + I * t) ((1 + δ / 2 : ℝ) + I * t) ≤ δ := by
    rw [dist_add_right, dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have h := Eq21LocalLog.norm_logDeriv_le_small_disk χ.LFunction
    ((1 + δ / 2 : ℝ) + I * t) ((β : ℂ) + I * t) hδ
    (by positivity : 0 < δ / 4) hbB (χ.differentiable_LFunction hχ).differentiableOn
    (fun w hw ↦ by
      obtain ⟨hlo, hhi, him⟩ := anchor_disk_subset_rectangle hδ hδ1 ht hw
      exact hzero w hlo hhi him)
    (fun w hw ↦ Eq21LocalLog.norm_LFunction_le_on_anchor_disk χ hχ hδ hδ1 t hw)
    (Eq21LocalLog.delta_quarter_le_norm_LFunction_anchor χ hδ hδ1 t) hz
  have harg : (8 * (q : ℝ) * (1 + |t|)) / (δ / 4) =
      32 * q * (1 + |t|) / δ := by ring
  rw [harg] at h
  convert h using 1
  ring

end
end Eq21FiniteLogDerivative
