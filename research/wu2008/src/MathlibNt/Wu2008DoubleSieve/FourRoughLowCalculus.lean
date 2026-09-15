import MathlibNt.Wu2008DoubleSieve.FourRoughIntegral
import MathlibNt.Wu2008DoubleSieve.PrimeOrderedQuadratureBuchstab

namespace Wu2008DoubleSieve.FourRoughClosedMass
open Set Real MeasureTheory
noncomputable section

abbrev low : Set ℝ := Icc (1/15 : ℝ) (1/3)
def bounded (M : ℝ) (f : ℝ → ℝ) : Prop := ∀ t ∈ low, |f t| ≤ M
def lip (K : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ x ∈ low, ∀ y ∈ low, |f x-f y| ≤ K*|x-y|

theorem low_continuous {f : ℝ → ℝ} {K : ℝ} (h : lip K f) : ContinuousOn f low :=
  (LipschitzOnWith.of_dist_le' (by simpa only [Real.dist_eq, lip] using h)).continuousOn

theorem low_segment {a b : ℝ} (ha : a ∈ low) (hb : b ∈ low) : uIcc a b ⊆ low :=
  uIcc_subset_Icc ha hb

theorem low_integrable {f : ℝ → ℝ} (hf : ContinuousOn f low)
    {a b : ℝ} (ha : a ∈ low) (hb : b ∈ low) :
    IntervalIntegrable (fun t => f t/t) volume a b :=
  ((hf.mono (low_segment ha hb)).div continuousOn_id (fun t ht =>
    ne_of_gt (by have := (low_segment ha hb ht).1; change 0 < t; linarith))).intervalIntegrable

theorem low_integral_bound {f : ℝ → ℝ} {M a b : ℝ}
    (ha : a ∈ low) (hb : b ∈ low) (hf : bounded M f) :
    |∫ t in a..b, f t/t| ≤ 15*M*|b-a| := by
  rw [← Real.norm_eq_abs]
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro t ht
  have ht' := low_segment ha hb (uIoc_subset_uIcc ht)
  have ht0 : 0 < t := by linarith [ht'.1]
  rw [Real.norm_eq_abs, abs_div, abs_of_pos ht0]
  apply (div_le_div_of_nonneg_right (hf t ht') ht0.le).trans
  apply (div_le_iff₀ ht0).mpr
  have hM := (abs_nonneg _).trans (hf t ht')
  nlinarith [ht'.1]

theorem low_integral_bound_four {f : ℝ → ℝ} {M a b : ℝ}
    (ha : a ∈ low) (hb : b ∈ low) (hM : 0 ≤ M) (hf : bounded M f) :
    |∫ t in a..b, f t/t| ≤ 4*M := by
  have h := low_integral_bound ha hb hf
  have hd : |b-a| ≤ 4/15 := by
    rw [abs_le]; constructor <;> linarith [ha.1,ha.2,hb.1,hb.2]
  nlinarith [mul_le_mul_of_nonneg_left hd (show 0 ≤ 15*M by positivity)]

theorem low_integral_sub {f g : ℝ → ℝ} {e a b : ℝ}
    (hf : ContinuousOn f low) (hg : ContinuousOn g low)
    (ha : a ∈ low) (hb : b ∈ low) (he : 0 ≤ e)
    (hd : ∀ t ∈ low, |f t-g t| ≤ e) :
    |(∫ t in a..b, f t/t)-(∫ t in a..b, g t/t)| ≤ 4*e := by
  rw [← intervalIntegral.integral_sub (low_integrable hf ha hb) (low_integrable hg ha hb)]
  simpa only [sub_div] using low_integral_bound_four ha hb he hd

/-- Both moving endpoints remain in the entire legal low slab. -/
theorem low_moving_lip {H : ℝ → ℝ → ℝ} {l u : ℝ → ℝ} {M K L U : ℝ}
    (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hc : ∀ x ∈ low, ContinuousOn (H x) low)
    (hb : ∀ x ∈ low, bounded M (H x))
    (hl : ∀ x ∈ low, ∀ y ∈ low, ∀ t ∈ low, |H x t-H y t| ≤ K*|x-y|)
    (hlow : ∀ x ∈ low, l x ∈ low) (hupp : ∀ x ∈ low, u x ∈ low)
    (hll : lip L l) (hul : lip U u) :
    bounded (4*M) (fun x => ∫ t in l x..u x, H x t/t) ∧
    lip (4*K+15*M*(L+U)) (fun x => ∫ t in l x..u x, H x t/t) := by
  constructor
  · intro x hx
    exact low_integral_bound_four (hlow x hx) (hupp x hx) hM (hb x hx)
  · intro x hx y hy
    have h1 := low_integral_sub (hc x hx) (hc y hy) (hlow x hx) (hupp x hx)
      (mul_nonneg hK (abs_nonneg _)) (hl x hx y hy)
    have h2 := low_integral_bound (hlow x hx) (hlow y hy) (hb y hy)
    have h3 := low_integral_bound (hupp y hy) (hupp x hx) (hb y hy)
    have hadd1 := intervalIntegral.integral_add_adjacent_intervals
      (low_integrable (hc y hy) (hlow x hx) (hlow y hy))
      (low_integrable (hc y hy) (hlow y hy) (hupp y hy))
    have hadd2 := intervalIntegral.integral_add_adjacent_intervals
      (low_integrable (hc y hy) (hlow x hx) (hupp y hy))
      (low_integrable (hc y hy) (hupp y hy) (hupp x hx))
    have he : (∫ t in l x..u x, H y t/t)-(∫ t in l y..u y, H y t/t) =
        (∫ t in l x..l y, H y t/t)+(∫ t in u y..u x, H y t/t) := by
      linarith only [hadd1,hadd2]
    have htri := abs_sub_le (∫ t in l x..u x, H x t/t)
      (∫ t in l x..u x, H y t/t) (∫ t in l y..u y, H y t/t)
    rw [he] at htri
    have hsum := abs_add_le (∫ t in l x..l y, H y t/t) (∫ t in u y..u x, H y t/t)
    rw [abs_sub_comm (l y) (l x)] at h2
    have hlb := mul_le_mul_of_nonneg_left (hll x hx y hy) (show 0 ≤ 15*M by positivity)
    have hub := mul_le_mul_of_nonneg_left (hul x hx y hy) (show 0 ≤ 15*M by positivity)
    nlinarith only [h1,h2,h3,htri,hsum,hlb,hub]

def cap (x : ℝ) : ℝ := min beta (max alpha x)
theorem cap_mem (x : ℝ) : cap x ∈ Icc alpha beta := by
  exact ⟨le_min fixed_geometry.2.2.1 (le_max_left _ _), min_le_left _ _⟩
theorem cap_low (x : ℝ) : cap x ∈ low :=
  ⟨fixed_geometry.1.trans (cap_mem x).1, (cap_mem x).2.trans fixed_geometry.2.2.2.1⟩
theorem cap_eq {x : ℝ} (hx : x ∈ Icc alpha beta) : cap x = x := by
  simp only [cap, max_eq_right hx.1, min_eq_right hx.2]
theorem cap_lip : lip 1 cap := by
  intro x _ y _
  have hm : |min beta (max alpha x)-min beta (max alpha y)| ≤
      |max alpha x-max alpha y| := by
    simpa only [sub_self, abs_zero, max_eq_right (abs_nonneg (max alpha x-max alpha y))] using
      abs_min_sub_min_le_max beta (max alpha x) beta (max alpha y)
  have hM : |max alpha x-max alpha y| ≤ |x-y| := by
    simpa only [max_comm alpha] using abs_max_sub_max_le_abs x y alpha
  simpa only [cap, min_comm beta, one_mul] using hm.trans hM

theorem beta_low : beta ∈ low := ⟨fixed_geometry.1.trans fixed_geometry.2.2.1, fixed_geometry.2.2.2.1⟩
theorem alpha_low : alpha ∈ low := ⟨fixed_geometry.1, fixed_geometry.2.2.1.trans beta_low.2⟩
theorem top_low (x : ℝ) : lam-cap x ∈ low := by
  have hg := fixed_geometry
  have hx := cap_mem x
  constructor <;> linarith [hg.1,hg.2.2.1,hg.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2,hx.1,hx.2]
theorem top_lip : lip 1 (fun x => lam-cap x) := by
  intro x hx y hy
  convert cap_lip x hx y hy using 1
  rw [show lam-cap x-(lam-cap y) = -(cap x-cap y) by ring, abs_neg]

theorem quotient_low {x y b d T : ℝ} (hb : 1/15 ≤ b) (hd : 1/15 ≤ d)
    (hy : |y| ≤ T) : |x/b-y/d| ≤ 15*|x-y|+225*T*|b-d| := by
  have hb0 : 0 < b := by linarith
  have hd0 : 0 < d := by linarith
  have hT : 0 ≤ T := (abs_nonneg y).trans hy
  have he : x/b-y/d = (x-y)/b+y*(d-b)/(b*d) := by field_simp; ring
  rw [he]
  have h1 : |x-y|/b ≤ 15*|x-y| := by
    apply (div_le_iff₀ hb0).mpr
    nlinarith [mul_le_mul_of_nonneg_right hb (abs_nonneg (x-y))]
  have hprod : 1/225 ≤ b*d := by nlinarith
  have h2 : |y| * |d-b|/(b*d) ≤ 225*T*|b-d| := by
    rw [abs_sub_comm d b]
    apply (div_le_iff₀ (mul_pos hb0 hd0)).mpr
    have hyy := mul_le_mul_of_nonneg_right hy (abs_nonneg (b-d))
    have hh := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 225*T*|b-d| by positivity)
    nlinarith
  have hh := abs_add_le ((x-y)/b) (y*(d-b)/(b*d))
  rw [abs_div, abs_of_pos hb0, abs_div, abs_mul, abs_of_pos (mul_pos hb0 hd0)] at hh
  linarith only [h1,h2,hh]

end
end Wu2008DoubleSieve.FourRoughClosedMass
