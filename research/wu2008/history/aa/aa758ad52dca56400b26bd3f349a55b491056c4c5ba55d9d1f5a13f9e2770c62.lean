import MathlibNt.Wu2008DoubleSieve.PrimeOrderedQuadratureWeighted

/-! # Lipschitz stability of ordered integrals, without differentiability -/

namespace Wu2008DoubleSieve

open Finset Set Filter Real MeasureTheory LiLiuPrereqBuchstab
open scoped Classical Topology Interval

theorem primeOrdered_continuous_of_lipschitz {f : ℝ → ℝ} {K : ℝ}
    (h : ∀ x ∈ Icc (1 / 10 : ℝ) (1 / 2),
      ∀ y ∈ Icc (1 / 10 : ℝ) (1 / 2), |f x - f y| ≤ K * |x - y|) :
    ContinuousOn f (Icc (1 / 10 : ℝ) (1 / 2)) :=
  (LipschitzOnWith.of_dist_le' (by simpa only [Real.dist_eq] using h)).continuousOn

private theorem segment_subset {a b : ℝ}
    (ha : a ∈ Icc (1 / 10 : ℝ) (1 / 2))
    (hb : b ∈ Icc (1 / 10 : ℝ) (1 / 2)) :
    uIcc a b ⊆ Icc (1 / 10 : ℝ) (1 / 2) := by
  intro t ht
  rcases le_total a b with hab | hab
  · rw [uIcc_of_le hab] at ht
    exact ⟨ha.1.trans ht.1, ht.2.trans hb.2⟩
  · rw [uIcc_of_ge hab] at ht
    exact ⟨hb.1.trans ht.1, ht.2.trans ha.2⟩

theorem primeOrdered_integrable {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (1 / 10 : ℝ) (1 / 2)))
    {a b : ℝ} (ha : a ∈ Icc (1 / 10 : ℝ) (1 / 2))
    (hb : b ∈ Icc (1 / 10 : ℝ) (1 / 2)) :
    IntervalIntegrable (fun t => f t / t) volume a b :=
  ((hf.mono (segment_subset ha hb)).div continuousOn_id
    (fun t ht => ne_of_gt (by
      change 0 < t
      have := (segment_subset ha hb ht).1
      linarith))).intervalIntegrable

theorem primeOrdered_integral_norm_le {f : ℝ → ℝ} {M a b : ℝ}
    (ha : a ∈ Icc (1 / 10 : ℝ) (1 / 2))
    (hb : b ∈ Icc (1 / 10 : ℝ) (1 / 2))
    (hbound : ∀ t ∈ Icc (1 / 10 : ℝ) (1 / 2), |f t| ≤ M) :
    |∫ t in a..b, f t / t| ≤ 10 * M * |b - a| := by
  rw [← Real.norm_eq_abs]
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro t ht
  have ht' := segment_subset ha hb (uIoc_subset_uIcc ht)
  have ht0 : 0 < t := by linarith [ht'.1]
  rw [Real.norm_eq_abs, abs_div, abs_of_pos ht0]
  apply (div_le_div_of_nonneg_right (hbound t ht') ht0.le).trans
  apply (div_le_iff₀ ht0).2
  have hM := (abs_nonneg _).trans (hbound t ht')
  nlinarith [ht'.1]

theorem primeOrdered_integral_norm_le_four {f : ℝ → ℝ} {M a b : ℝ}
    (ha : a ∈ Icc (1 / 10 : ℝ) (1 / 2))
    (hb : b ∈ Icc (1 / 10 : ℝ) (1 / 2))
    (hM : 0 ≤ M)
    (hbound : ∀ t ∈ Icc (1 / 10 : ℝ) (1 / 2), |f t| ≤ M) :
    |∫ t in a..b, f t / t| ≤ 4 * M := by
  have h := primeOrdered_integral_norm_le ha hb hbound
  have hd : |b - a| ≤ 2 / 5 := by
    rw [abs_le]
    constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
  nlinarith [mul_le_mul_of_nonneg_left hd (show 0 ≤ 10 * M by positivity)]

theorem primeOrdered_integral_sub_bound {f g : ℝ → ℝ} {η a b : ℝ}
    (hf : ContinuousOn f (Icc (1 / 10 : ℝ) (1 / 2)))
    (hg : ContinuousOn g (Icc (1 / 10 : ℝ) (1 / 2)))
    (ha : a ∈ Icc (1 / 10 : ℝ) (1 / 2))
    (hb : b ∈ Icc (1 / 10 : ℝ) (1 / 2)) (hη : 0 ≤ η)
    (hd : ∀ t ∈ Icc (1 / 10 : ℝ) (1 / 2), |f t - g t| ≤ η) :
    |(∫ t in a..b, f t / t) - ∫ t in a..b, g t / t| ≤ 4 * η := by
  rw [← intervalIntegral.integral_sub (primeOrdered_integrable hf ha hb)
    (primeOrdered_integrable hg ha hb)]
  have h := primeOrdered_integral_norm_le_four ha hb hη hd
  simpa only [sub_div] using h

/-- The lower limit moves with the parameter, including in reversed intervals.
The bound is valid on the whole fixed compact interval, not only below `B`. -/
theorem primeOrdered_moving_integral_lipschitz
    {H : ℝ → ℝ → ℝ} {B M K : ℝ}
    (hB : B ∈ Icc (1 / 10 : ℝ) (1 / 2)) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hc : ∀ x ∈ Icc (1 / 10 : ℝ) (1 / 2),
      ContinuousOn (H x) (Icc (1 / 10 : ℝ) (1 / 2)))
    (hb : ∀ x ∈ Icc (1 / 10 : ℝ) (1 / 2),
      ∀ t ∈ Icc (1 / 10 : ℝ) (1 / 2), |H x t| ≤ M)
    (hl : ∀ x ∈ Icc (1 / 10 : ℝ) (1 / 2),
      ∀ y ∈ Icc (1 / 10 : ℝ) (1 / 2),
      ∀ t ∈ Icc (1 / 10 : ℝ) (1 / 2), |H x t - H y t| ≤ K * |x - y|) :
    (∀ x ∈ Icc (1 / 10 : ℝ) (1 / 2), |∫ t in x..B, H x t / t| ≤ 4 * M) ∧
    (∀ x ∈ Icc (1 / 10 : ℝ) (1 / 2),
      ∀ y ∈ Icc (1 / 10 : ℝ) (1 / 2),
      |(∫ t in x..B, H x t / t) - ∫ t in y..B, H y t / t| ≤
        (4 * K + 10 * M) * |x - y|) := by
  constructor
  · intro x hx
    exact primeOrdered_integral_norm_le_four hx hB hM (hb x hx)
  · intro x hx y hy
    have h₁ := primeOrdered_integral_sub_bound (hc x hx) (hc y hy) hx hB
      (mul_nonneg hK (abs_nonneg _)) (hl x hx y hy)
    have h₂ := primeOrdered_integral_norm_le hx hy (hb y hy)
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (primeOrdered_integrable (hc y hy) hx hy)
      (primeOrdered_integrable (hc y hy) hy hB)
    have he : (∫ t in x..B, H y t / t) - (∫ t in y..B, H y t / t) =
        ∫ t in x..y, H y t / t := by linarith only [hadd]
    have h₃ := abs_sub_le (∫ t in x..B, H x t / t)
      (∫ t in x..B, H y t / t) (∫ t in y..B, H y t / t)
    rw [he] at h₃
    rw [abs_sub_comm y x] at h₂
    nlinarith only [h₁, h₂, h₃]

end Wu2008DoubleSieve
