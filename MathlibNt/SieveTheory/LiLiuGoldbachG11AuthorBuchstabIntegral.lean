import MathlibNt.SieveTheory.LiLiuGoldbachG11AuthorIntegralScalar
import MathlibNt.SieveTheory.LiLiuBuchstabSharpClosure
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Set
open scoped Interval
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The literal author-weighted Buchstab integral; no counting interpretation is asserted. -/
def goldbachG11AuthorBuchstabIntegral : ℝ :=
  ∫ r in (4 / 53 : ℝ)..(4 / 33), ∫ q in r..(4 / 33),
    ∫ s in q..(4 / 33), ∫ t in s..(4 / 33),
      goldbachG11AuthorWeight r * LiLiuPrereqBuchstab.buchstab ((1-r-q-s-t)/q) /
        (r * q^2 * s * t)

theorem goldbachG11AuthorBuchstab_argument {r q s t : ℝ}
    (hr : (4/53 : ℝ) ≤ r) (hrq : r ≤ q) (hqs : q ≤ s) (hst : s ≤ t)
    (ht : t ≤ (4/33 : ℝ)) : (17/4 : ℝ) ≤ (1-r-q-s-t)/q := by
  have hq : 0 < q := by linarith
  apply (le_div_iff₀ hq).2
  linarith

private def posCoord (x : ℝ) : ℝ := max (4/53 : ℝ) x
private theorem continuous_posCoord : Continuous posCoord := continuous_const.max continuous_id
private theorem posCoord_pos (x : ℝ) : 0 < posCoord x :=
  lt_of_lt_of_le (by norm_num) (le_max_left _ _)
private theorem posCoord_eq {x : ℝ} (hx : (4/53 : ℝ) ≤ x) : posCoord x = x :=
  max_eq_right hx

private def extKernel (w : ℝ → ℝ) (p : ((ℝ × ℝ) × ℝ) × ℝ) : ℝ :=
  goldbachG11AuthorWeight p.1.1.1 * w ((1-p.1.1.1-p.1.1.2-p.1.2-p.2)/posCoord p.1.1.2) /
    (posCoord p.1.1.1 * posCoord p.1.1.2 ^ 2 * posCoord p.1.2 * posCoord p.2)

private theorem continuous_extKernel (w : ℝ → ℝ) (hw : Continuous w) :
    Continuous (extKernel w) := by
  unfold extKernel
  apply Continuous.div
  · apply Continuous.mul
    · exact continuous_goldbachG11AuthorWeight.comp (by fun_prop)
    · apply hw.comp
      apply Continuous.div
      · fun_prop
      · exact continuous_posCoord.comp (by fun_prop)
      · intro p; exact (posCoord_pos _).ne'
  · exact (((continuous_posCoord.comp (by fun_prop)).mul
      ((continuous_posCoord.comp (by fun_prop)).pow 2)).mul
      (continuous_posCoord.comp (by fun_prop))).mul (continuous_posCoord.comp (by fun_prop))
  · intro p
    exact ne_of_gt (mul_pos (mul_pos (mul_pos (posCoord_pos _) (pow_pos (posCoord_pos _) 2))
      (posCoord_pos _)) (posCoord_pos _))

private theorem continuous_tailIntegral {X : Type*} [TopologicalSpace X]
    (f : X × ℝ → ℝ) (hf : Continuous f) (a : X → ℝ) (ha : Continuous a) (b : ℝ) :
    Continuous (fun x => ∫ t in a x..b, f (x,t)) := by
  have h := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun x t => f (x,t)) (a₀ := b) hf ha (μ := volume)
  convert h.neg using 1
  funext x
  exact intervalIntegral.integral_symm _ _

private def int3 (F : ((ℝ × ℝ) × ℝ) × ℝ → ℝ) (p : (ℝ × ℝ) × ℝ) : ℝ :=
  ∫ t in p.2..(4/33 : ℝ), F (p,t)
private def int2 (F : ((ℝ × ℝ) × ℝ) × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ∫ s in p.2..(4/33 : ℝ), int3 F (p,s)
private def int1 (F : ((ℝ × ℝ) × ℝ) × ℝ → ℝ) (r : ℝ) : ℝ :=
  ∫ q in r..(4/33 : ℝ), int2 F (r,q)
private theorem continuous_int3 {F : ((ℝ × ℝ) × ℝ) × ℝ → ℝ} (hF : Continuous F) :
    Continuous (int3 F) := continuous_tailIntegral F hF Prod.snd continuous_snd _
private theorem continuous_int2 {F : ((ℝ × ℝ) × ℝ) × ℝ → ℝ} (hF : Continuous F) :
    Continuous (int2 F) := continuous_tailIntegral (int3 F) (continuous_int3 hF) Prod.snd continuous_snd _
private theorem continuous_int1 {F : ((ℝ × ℝ) × ℝ) × ℝ → ℝ} (hF : Continuous F) :
    Continuous (int1 F) := continuous_tailIntegral (int2 F) (continuous_int2 hF) id continuous_id _

private theorem fourIntegral_mono {F G : ((ℝ × ℝ) × ℝ) × ℝ → ℝ}
    (hF : Continuous F) (hG : Continuous G)
    (h : ∀ r q s t : ℝ, (4/53 : ℝ) ≤ r → r ≤ q → q ≤ s → s ≤ t →
      t ≤ (4/33 : ℝ) → F (((r,q),s),t) ≤ G (((r,q),s),t)) :
    (∫ r in (4/53 : ℝ)..(4/33), int1 F r) ≤ ∫ r in (4/53 : ℝ)..(4/33), int1 G r := by
  apply intervalIntegral.integral_mono_on (by norm_num)
    ((continuous_int1 hF).intervalIntegrable _ _) ((continuous_int1 hG).intervalIntegrable _ _)
  intro r hr
  apply intervalIntegral.integral_mono_on hr.2
    (((continuous_int2 hF).comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)
    (((continuous_int2 hG).comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)
  intro q hq
  apply intervalIntegral.integral_mono_on hq.2
    (((continuous_int3 hF).comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)
    (((continuous_int3 hG).comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)
  intro s hs
  apply intervalIntegral.integral_mono_on hs.2
    ((hF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)
    ((hG.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)
  intro t ht
  exact h r q s t hr.1 hq.1 hs.1 ht.1 ht.2

private theorem extKernel_eq (w : ℝ → ℝ) {r q s t : ℝ}
    (hr : (4/53 : ℝ) ≤ r) (hq : (4/53 : ℝ) ≤ q)
    (hs : (4/53 : ℝ) ≤ s) (ht : (4/53 : ℝ) ≤ t) :
    extKernel w (((r,q),s),t) = goldbachG11AuthorWeight r * w ((1-r-q-s-t)/q) /
      (r*q^2*s*t) := by
  simp only [extKernel, posCoord_eq hr, posCoord_eq hq, posCoord_eq hs, posCoord_eq ht]

private theorem int1_extKernel_eq (w : ℝ → ℝ) {r : ℝ}
    (hr : r ∈ Icc (4/53 : ℝ) (4/33)) :
    int1 (extKernel w) r = ∫ q in r..(4/33 : ℝ), ∫ s in q..(4/33 : ℝ),
      ∫ t in s..(4/33 : ℝ), goldbachG11AuthorWeight r * w ((1-r-q-s-t)/q) /
        (r*q^2*s*t) := by
  unfold int1 int2 int3
  apply intervalIntegral.integral_congr
  intro q hq
  rw [uIcc_of_le hr.2] at hq
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hq.2] at hs
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hs.2] at ht
  exact extKernel_eq w hr.1 (hr.1.trans hq.1) (hr.1.trans (hq.1.trans hs.1))
    (hr.1.trans (hq.1.trans (hs.1.trans ht.1)))

/-- Every literal inner slice is genuinely interval-integrable. -/
theorem goldbachG11AuthorBuchstab_t_intervalIntegrable {r q s : ℝ}
    (hr : r ∈ Icc (4/53 : ℝ) (4/33)) (hq : q ∈ Icc r (4/33 : ℝ))
    (hs : s ∈ Icc q (4/33 : ℝ)) :
    IntervalIntegrable (fun t : ℝ => goldbachG11AuthorWeight r *
      LiLiuPrereqBuchstab.buchstab ((1-r-q-s-t)/q) / (r*q^2*s*t)) volume s (4/33) := by
  apply ContinuousOn.intervalIntegrable_of_Icc hs.2
  apply ((continuous_extKernel _ LiLiuPrereqBuchstab.continuous_buchstab).comp
    (continuous_const.prodMk continuous_id)).continuousOn.congr
  intro t ht
  exact (extKernel_eq _ hr.1 (hr.1.trans hq.1) (hr.1.trans (hq.1.trans hs.1))
    (hr.1.trans (hq.1.trans (hs.1.trans ht.1)))).symm

/-- The actual once-integrated kernel is integrable in the next variable. -/
theorem goldbachG11AuthorBuchstab_s_intervalIntegrable {r q : ℝ}
    (hr : r ∈ Icc (4/53 : ℝ) (4/33)) (hq : q ∈ Icc r (4/33 : ℝ)) :
    IntervalIntegrable (fun s : ℝ => ∫ t in s..(4/33 : ℝ), goldbachG11AuthorWeight r *
      LiLiuPrereqBuchstab.buchstab ((1-r-q-s-t)/q) / (r*q^2*s*t)) volume q (4/33) := by
  apply ContinuousOn.intervalIntegrable_of_Icc hq.2
  apply ((continuous_int3 (continuous_extKernel _ LiLiuPrereqBuchstab.continuous_buchstab)).comp
    (continuous_const.prodMk continuous_id)).continuousOn.congr
  intro s hs
  unfold int3
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hs.2] at ht
  exact (extKernel_eq _ hr.1 (hr.1.trans hq.1) (hr.1.trans (hq.1.trans hs.1))
    (hr.1.trans (hq.1.trans (hs.1.trans ht.1)))).symm

/-- The actual twice-integrated kernel is integrable in q. -/
theorem goldbachG11AuthorBuchstab_q_intervalIntegrable {r : ℝ}
    (hr : r ∈ Icc (4/53 : ℝ) (4/33)) :
    IntervalIntegrable (fun q : ℝ => ∫ s in q..(4/33 : ℝ), ∫ t in s..(4/33 : ℝ),
      goldbachG11AuthorWeight r * LiLiuPrereqBuchstab.buchstab ((1-r-q-s-t)/q) /
        (r*q^2*s*t)) volume r (4/33) := by
  apply ContinuousOn.intervalIntegrable_of_Icc hr.2
  apply ((continuous_int2 (continuous_extKernel _ LiLiuPrereqBuchstab.continuous_buchstab)).comp
    (continuous_const.prodMk continuous_id)).continuousOn.congr
  intro q hq
  unfold int2 int3
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hq.2] at hs
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hs.2] at ht
  exact (extKernel_eq _ hr.1 (hr.1.trans hq.1) (hr.1.trans (hq.1.trans hs.1))
    (hr.1.trans (hq.1.trans (hs.1.trans ht.1)))).symm

/-- The outermost literal integrand is integrable, not a totalized undefined integral. -/
theorem goldbachG11AuthorBuchstab_r_intervalIntegrable :
    IntervalIntegrable (fun r : ℝ => ∫ q in r..(4/33 : ℝ), ∫ s in q..(4/33 : ℝ),
      ∫ t in s..(4/33 : ℝ), goldbachG11AuthorWeight r *
        LiLiuPrereqBuchstab.buchstab ((1-r-q-s-t)/q) / (r*q^2*s*t))
      volume (4/53) (4/33) := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
  apply (continuous_int1 (continuous_extKernel _ LiLiuPrereqBuchstab.continuous_buchstab)).continuousOn.congr
  intro r hr
  exact (int1_extKernel_eq _ hr).symm

theorem goldbachG11AuthorBuchstabIntegral_le_scalar :
    goldbachG11AuthorBuchstabIntegral ≤
      (561522/1000000 : ℝ) * goldbachG11PrimeIntegral goldbachG11AuthorWeight := by
  have h := fourIntegral_mono
    (continuous_extKernel _ LiLiuPrereqBuchstab.continuous_buchstab)
    (continuous_extKernel (fun _ => (561522/1000000 : ℝ)) continuous_const) (by
      intro r q s t hr hrq hqs hst ht
      rw [extKernel_eq _ hr (hr.trans hrq) (hr.trans (hrq.trans hqs))
        (hr.trans (hrq.trans (hqs.trans hst))),
        extKernel_eq _ hr (hr.trans hrq) (hr.trans (hrq.trans hqs))
        (hr.trans (hrq.trans (hqs.trans hst)))]
      apply div_le_div_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left
          (LiLiuBuchstabSharp.buchstab_sharp_tail_closed
            (goldbachG11AuthorBuchstab_argument hr hrq hqs hst ht))
          (goldbachG11AuthorWeight_nonneg r)
      · have hr0 : 0 ≤ r := by linarith
        exact mul_nonneg (mul_nonneg (mul_nonneg hr0 (sq_nonneg q))
          (hr0.trans (hrq.trans hqs))) (hr0.trans (hrq.trans (hqs.trans hst))))
  have he (w : ℝ → ℝ) : (∫ r in (4/53 : ℝ)..(4/33), int1 (extKernel w) r) =
      ∫ r in (4/53 : ℝ)..(4/33), ∫ q in r..(4/33 : ℝ), ∫ s in q..(4/33 : ℝ),
      ∫ t in s..(4/33 : ℝ), goldbachG11AuthorWeight r * w ((1-r-q-s-t)/q) /
        (r*q^2*s*t) := by
    apply intervalIntegral.integral_congr
    intro r hr
    exact int1_extKernel_eq w (by rwa [uIcc_of_le (by norm_num : (4/53 : ℝ) ≤ 4/33)] at hr)
  rw [he, he] at h
  convert h using 1
  · rfl
  unfold goldbachG11PrimeIntegral
  simp only [← intervalIntegral.integral_const_mul]
  congr 1; funext r
  congr 1; funext q
  congr 1; funext s
  congr 1; funext t
  ring

theorem goldbachG11AuthorBuchstabIntegral_le_10191 :
    goldbachG11AuthorBuchstabIntegral ≤ (10191/100000 : ℝ) :=
  goldbachG11AuthorBuchstabIntegral_le_scalar.trans goldbachG11PrimeIntegral_author_scalar_le_10191

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig