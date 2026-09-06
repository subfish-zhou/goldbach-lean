import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLCharacterHolomorphicLog
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLConditionalValueSeries
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLRightHalfPlaneBounds

open Complex Metric Set
open scoped Topology

namespace Eq21LocalLog
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.TatuzawaZeroContribution

noncomputable section

/-- The elementary conditional-series estimate, with no height restriction. -/
theorem norm_LFunction_le_growth {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (z : ℂ) (hz : 0 < z.re) :
    ‖χ.LFunction z‖ ≤ q * (1 + ‖z‖ / z.re) := by
  have hq1 : q ≠ 1 := by
    intro h
    subst q
    exact hχ (Subsingleton.elim _ _)
  let : Fact (1 < q) :=
    ⟨Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨NeZero.ne q, hq1⟩⟩
  have hzero : χ (0 : ZMod q) = 0 :=
    MulChar.map_nonunit χ not_isUnit_zero
  have h := DirichletLConditionalValueSeries.norm_orderedValueSeries_sub_sum_range_le
    χ hχ z hz (m := 1) le_rfl
  rw [DirichletLConditionalValueSeries.orderedValueSeries_eq_LFunction_of_re_pos
    χ hχ z hz] at h
  simpa [hzero] using h

/-- The absolute-convergence anchor, valid also for quadratic characters. -/
theorem delta_quarter_le_norm_LFunction_anchor {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4)
    (t : ℝ) : δ / 4 ≤ ‖χ.LFunction ((1 + δ / 2 : ℝ) + I * t)‖ := by
  let K : ℝ := 4 / δ
  have hK : 0 < K := by dsimp [K]; positivity
  have hbound : 1 + 1 / ((1 + δ / 2) - 1) ≤ K := by
    dsimp [K]
    rw [show (1 + δ / 2) - 1 = δ / 2 by ring]
    field_simp
    nlinarith
  have htriv : ‖DirichletCharacter.LFunctionTrivChar q (1 + (δ / 2 : ℂ))‖ ≤ K := by
    have h := norm_dirichletLFunction_le (1 : DirichletCharacter ℂ q)
      (1 + δ / 2) 0 (by linarith)
    simpa [DirichletCharacter.LFunctionTrivChar] using h.trans hbound
  have hsq : ‖(χ ^ 2).LFunction (1 + (δ / 2 : ℂ) + 2 * I * t)‖ ≤ K := by
    have h := norm_dirichletLFunction_le (χ ^ 2) (1 + δ / 2) (2 * t) (by linarith)
    convert h.trans hbound using 1 <;> push_cast <;> congr 2
    ring
  have hp := χ.norm_LFunction_product_ge_one (by positivity : 0 < δ / 2) t
  simp only [norm_mul, norm_pow] at hp
  have hmajor : 1 ≤ K ^ 3 * ‖χ.LFunction ((1 + δ / 2 : ℝ) + I * t)‖ ^ 4 * K := by
    refine hp.trans ?_
    push_cast
    gcongr
  by_contra hn
  have hn' : ‖χ.LFunction ((1 + δ / 2 : ℝ) + I * t)‖ < δ / 4 := lt_of_not_ge hn
  have hsmall : K ^ 3 * ‖χ.LFunction ((1 + δ / 2 : ℝ) + I * t)‖ ^ 4 * K <
      K ^ 3 * (δ / 4) ^ 4 * K := by
    gcongr
  have hid : K ^ 3 * (δ / 4) ^ 4 * K = 1 := by
    dsimp [K]
    field_simp
  exact (not_lt_of_ge hmajor) (hsmall.trans_eq hid)

/-- Interior derivative bound from a real-part oscillation at a nearby anchor. -/
theorem norm_deriv_le_small_disk
    (h : ℂ → ℂ) (a z : ℂ) {δ A : ℝ} (hδ : 0 < δ) (hA : 0 < A)
    (hh : DifferentiableOn ℂ h (ball a (3 * δ / 2)))
    (hosc : ∀ w ∈ ball a (3 * δ / 2), (h w).re - (h a).re ≤ A)
    (hz : dist z a ≤ δ) : ‖deriv h z‖ ≤ 40 * A / δ := by
  let H : ℂ → ℂ := fun w ↦ h (a + w) - h a
  have hR : 0 < 3 * δ / 2 := by positivity
  have hHd : DifferentiableOn ℂ H (ball 0 (3 * δ / 2)) := by
    intro w hw
    have haw : a + w ∈ ball a (3 * δ / 2) := by
      simpa [mem_ball, dist_comm] using hw
    have hhat := (hh (a + w) haw).differentiableAt (isOpen_ball.mem_nhds haw)
    exact ((hhat.comp w (by fun_prop)).sub
      (differentiableAt_const (h a))).differentiableWithinAt
  have hHre : MapsTo H (ball 0 (3 * δ / 2)) {w : ℂ | w.re ≤ A} := by
    intro w hw
    change (h (a + w) - h a).re ≤ A
    simpa only [sub_re] using hosc (a + w) (by simpa [mem_ball, dist_comm] using hw)
  have hH0 : H 0 = 0 := by simp [H]
  have hBC : ∀ w : ℂ, dist w a ≤ 5 * δ / 4 → ‖h w - h a‖ ≤ 10 * A := by
    intro w hw
    have hn : ‖w - a‖ ≤ 5 * δ / 4 := by simpa only [dist_eq_norm] using hw
    have hmem : w - a ∈ ball 0 (3 * δ / 2) := by
      simp only [mem_ball, dist_zero_right]
      linarith
    have hbc := borelCaratheodory_zero hA hHd hHre hR hmem hH0
    have hden : 0 < 3 * δ / 2 - ‖w - a‖ := by linarith
    have hrat : 2 * ‖w - a‖ / (3 * δ / 2 - ‖w - a‖) * A ≤ 10 * A := by
      apply mul_le_mul_of_nonneg_right _ hA.le
      apply (div_le_iff₀ hden).2
      linarith
    have heval : H (w - a) = h w - h a := by simp [H]
    rw [heval] at hbc
    apply hbc.trans
    calc
      _ = 2 * ‖w - a‖ / (3 * δ / 2 - ‖w - a‖) * A := by ring
      _ ≤ 10 * A := hrat
  have hquarter : 0 < δ / 4 := by positivity
  -- The Cauchy disk stays within the radius controlled by Borel–Carathéodory.
  have hdist : ∀ w ∈ closedBall z (δ / 4), dist w a ≤ 5 * δ / 4 := by
    intro w hw
    calc
      dist w a ≤ dist w z + dist z a := dist_triangle w z a
      _ ≤ δ / 4 + δ := add_le_add (mem_closedBall.mp hw) hz
      _ = 5 * δ / 4 := by ring
  have hsub : closedBall z (δ / 4) ⊆ ball a (3 * δ / 2) := by
    intro w hw
    exact mem_ball.mpr ((hdist w hw).trans_lt (by linarith))
  let F : ℂ → ℂ := fun w ↦ h w - h a
  have hFd : DifferentiableOn ℂ F (ball a (3 * δ / 2)) := hh.sub (differentiableOn_const _)
  have hcont : DiffContOnCl ℂ F (ball z (δ / 4)) := by
    refine ⟨hFd.mono (ball_subset_closedBall.trans hsub), ?_⟩
    rw [closure_ball z hquarter.ne']
    exact hFd.continuousOn.mono hsub
  have hcircle : ∀ w ∈ sphere z (δ / 4), ‖F w‖ ≤ 10 * A := by
    intro w hw
    exact hBC w (hdist w (mem_closedBall.mpr (mem_sphere.mp hw).le))
  have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hquarter hcont hcircle
  have hd : deriv F z = deriv h z := deriv_sub_const _
  rw [hd] at hc
  convert hc using 1
  field_simp
  ring

/-- The logarithm and its amplitude are constructed internally from nonvanishing,
a growth bound and a single lower anchor. No logarithm branch is assumed. -/
theorem norm_logDeriv_le_small_disk
    (g : ℂ → ℂ) (a z : ℂ) {δ B b : ℝ} (hδ : 0 < δ)
    (hb : 0 < b) (hbB : b < B)
    (hg : DifferentiableOn ℂ g (ball a (3 * δ / 2)))
    (hg0 : ∀ w ∈ ball a (3 * δ / 2), g w ≠ 0)
    (hbound : ∀ w ∈ ball a (3 * δ / 2), ‖g w‖ ≤ B)
    (hanchor : b ≤ ‖g a‖) (hz : dist z a ≤ δ) :
    ‖logDeriv g z‖ ≤ 40 * Real.log (B / b) / δ := by
  have hR : 0 < 3 * δ / 2 := by positivity
  have ha : a ∈ ball a (3 * δ / 2) := mem_ball_self hR
  have hzmem : z ∈ ball a (3 * δ / 2) := by rw [mem_ball]; linarith
  obtain ⟨h, hh, hexp⟩ := exists_holomorphicLog_on_ball g a hR hg hg0
  have hre : ∀ w ∈ ball a (3 * δ / 2), (h w).re = Real.log ‖g w‖ := by
    intro w hw
    rw [← hexp hw, Complex.norm_exp, Real.log_exp]
  have hB : 0 < B := hb.trans hbB
  have hosc : ∀ w ∈ ball a (3 * δ / 2), (h w).re - (h a).re ≤ Real.log (B / b) := by
    intro w hw
    rw [hre w hw, hre a ha, Real.log_div hB.ne' hb.ne']
    exact sub_le_sub (Real.log_le_log (norm_pos_iff.mpr (hg0 w hw)) (hbound w hw))
      (Real.log_le_log hb hanchor)
  have hA : 0 < Real.log (B / b) := Real.log_pos ((one_lt_div hb).2 hbB)
  have hd := norm_deriv_le_small_disk h a z hδ hA hh hosc hz
  have hhd := (hh z hzmem).differentiableAt (isOpen_ball.mem_nhds hzmem)
  have hevent : (fun w ↦ exp (h w)) =ᶠ[𝓝 z] g := by
    filter_upwards [isOpen_ball.mem_nhds hzmem] with w hw
    exact hexp hw
  have hderiv : deriv g z = g z * deriv h z := by
    rw [← hevent.deriv_eq]
    simpa [hexp hzmem] using hhd.hasDerivAt.cexp.deriv
  rw [logDeriv_apply, hderiv, mul_div_cancel_left₀ _ (hg0 z hzmem)]
  exact hd

/-- The small anchor disk lies in the asserted zero-free half-plane. -/
lemma anchor_disk_re_lower {δ : ℝ} (_hδ : 0 < δ) (t : ℝ) {w : ℂ}
    (hw : w ∈ ball ((1 + δ / 2 : ℝ) + I * t) (3 * δ / 2)) :
    1 - δ < w.re := by
  have hn : ‖w - ((1 + δ / 2 : ℝ) + I * t)‖ < 3 * δ / 2 := by
    simpa only [mem_ball, dist_eq_norm] using hw
  have hl := (abs_le.mp (Complex.abs_re_le_norm
    (w - ((1 + δ / 2 : ℝ) + I * t)))).1
  simp only [sub_re, add_re, ofReal_re, mul_re, I_re, zero_mul,
    I_im, ofReal_im, mul_zero, sub_zero, add_zero] at hl
  linarith

/-- Linear height growth on the small disk, paid for by the conditional series. -/
theorem norm_LFunction_le_on_anchor_disk {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) (t : ℝ) {w : ℂ}
    (hw : w ∈ ball ((1 + δ / 2 : ℝ) + I * t) (3 * δ / 2)) :
    ‖χ.LFunction w‖ ≤ 8 * q * (1 + |t|) := by
  have hre := anchor_disk_re_lower hδ t hw
  have hwpos : 0 < w.re := by linarith
  have hwhalf : (1 : ℝ) / 2 ≤ w.re := by linarith
  have hn : ‖w - ((1 + δ / 2 : ℝ) + I * t)‖ < 3 * δ / 2 := by
    simpa only [mem_ball, dist_eq_norm] using hw
  have ha : ‖((1 + δ / 2 : ℝ) : ℂ) + I * t‖ ≤ 1 + δ / 2 + |t| := by
    calc
      _ ≤ ‖((1 + δ / 2 : ℝ) : ℂ)‖ + ‖I * (t : ℂ)‖ := norm_add_le _ _
      _ = _ := by
        simp only [norm_real, Real.norm_eq_abs, norm_mul, norm_I, one_mul]
        rw [abs_of_pos (by linarith : 0 < 1 + δ / 2)]
  have hwnorm : ‖w‖ ≤ 2 + |t| := by
    have ht : ‖w‖ ≤ ‖w - ((1 + δ / 2 : ℝ) + I * t)‖ +
        ‖((1 + δ / 2 : ℝ) : ℂ) + I * t‖ := by
      simpa only [sub_add_cancel] using
        norm_add_le (w - ((1 + δ / 2 : ℝ) + I * t)) ((1 + δ / 2 : ℝ) + I * t)
    linarith only [ht, hn, ha, hδ1]
  have hdiv : ‖w‖ / w.re ≤ 2 * ‖w‖ := by
    apply (div_le_iff₀ hwpos).2
    nlinarith [norm_nonneg w]
  calc
    _ ≤ q * (1 + ‖w‖ / w.re) := norm_LFunction_le_growth χ hχ w hwpos
    _ ≤ q * (8 * (1 + |t|)) := by
      gcongr
      nlinarith [abs_nonneg t]
    _ = _ := by ring

/-- Quantitative logarithmic derivative in a zero-free half-plane.
The only conditional analytic input is the displayed nonvanishing hypothesis.
The explicit cost is one inverse width, uniformly in all real heights. -/
theorem norm_logDeriv_LFunction_le_of_zeroFree_halfPlane
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4)
    (hzero : ∀ z : ℂ, 1 - δ ≤ z.re → χ.LFunction z ≠ 0)
    (t β : ℝ) (hβlo : 1 - δ / 2 ≤ β) (hβhi : β ≤ 1 + δ) :
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
  have h := norm_logDeriv_le_small_disk χ.LFunction
    ((1 + δ / 2 : ℝ) + I * t) ((β : ℂ) + I * t) hδ
    (by positivity : 0 < δ / 4) hbB (χ.differentiable_LFunction hχ).differentiableOn
    (fun w hw ↦ hzero w (anchor_disk_re_lower hδ t hw).le)
    (fun w hw ↦ norm_LFunction_le_on_anchor_disk χ hχ hδ hδ1 t hw)
    (delta_quarter_le_norm_LFunction_anchor χ hδ hδ1 t) hz
  have harg : (8 * (q : ℝ) * (1 + |t|)) / (δ / 4) =
      32 * q * (1 + |t|) / δ := by ring
  rw [harg] at h
  convert h using 1
  ring

end
end Eq21LocalLog
