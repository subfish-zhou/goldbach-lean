import MathlibNt.Wu2008DoubleSieve.Gamma678FeedbackIntegrability
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Fixed-outer-coordinate affine substitution, followed by justified Fubini. -/
namespace Wu2008DoubleSieve.Gamma678Feedback
open Real Set MeasureTheory
open scoped Classical Topology Interval

noncomputable def scale : Kind → ℝ → ℝ
  | .six, _ => S
  | .seven, t => 1 / t
  | .eight, t => 1 / t

theorem scale_pos (j : Kind) {t : ℝ} (ht : 0 < t) : 0 < scale j t := by
  cases j
  · norm_num [scale, S]
  · exact one_div_pos.mpr ht
  · exact one_div_pos.mpr ht

theorem V_scale (j : Kind) (t u : ℝ) : V j t u = scale j t * ((1 - t) - u) := by
  cases j <;> dsimp [V, scale] <;> ring

theorem density_change (j : Kind) {t : ℝ} (ht : 0 < t) (u : ℝ) :
    D t u = scale j t * density j (V j t u) t := by
  rw [density, inv_V j ht]
  cases j <;> dsimp [D, scale, V, S] <;> field_simp

theorem source_change (j : Kind) (H : ℝ → ℝ) {t : ℝ} (ht : 0 < t) (u : ℝ) :
    source j H t u = scale j t * (H (V j t u) * masked j (V j t u) t) := by
  have he : slice j (V j t u) t ↔ region j t u := by
    unfold slice
    rw [inv_V j ht]
  unfold source masked
  simp only [he]
  split_ifs
  · rw [density_change j ht]
    ring
  · simp only [mul_zero]

/-- No division by an outer coordinate is performed outside its positive source interval. -/
theorem inner_substitution (j : Kind) (H : ℝ → ℝ) (t : ℝ) :
    (∫ u : ℝ, source j H t u) = ∫ v : ℝ, H v * masked j v t := by
  by_cases ht : t ∈ Icc a b
  · have ht0 := constants.1.trans_le ht.1
    simp_rw [source_change j H ht0, V_scale]
    rw [integral_const_mul]
    change scale j t * (∫ u : ℝ,
      (fun y => H (scale j t * y) * masked j (scale j t * y) t) ((1 - t) - u)) = _
    rw [integral_sub_left_eq_self
      (fun y : ℝ => H (scale j t * y) * masked j (scale j t * y) t) volume (1 - t)]
    rw [Measure.integral_comp_mul_left (fun v => H v * masked j v t)]
    rw [smul_eq_mul, abs_of_pos (inv_pos.mpr (scale_pos j ht0)),
      ← mul_assoc, mul_inv_cancel₀ (scale_pos j ht0).ne', one_mul]
  · have hs (u : ℝ) : source j H t u = 0 := if_neg (fun h => ht h.1)
    have hm (v : ℝ) : masked j v t = 0 := if_neg (fun h => ht h.1)
    simp only [hs, hm, mul_zero, integral_zero]

theorem source_inner (j : Kind) (H : ℝ → ℝ) {t : ℝ} (ht : t ∈ Icc a b) :
    (∫ u : ℝ, source j H t u) = ∫ u in lo j t..hi j, H (V j t u) * D t u := by
  have hs : Function.support (source j H t) ⊆ Icc (lo j t) (hi j) := by
    intro u hu
    by_contra hn
    exact hu (if_neg (fun h => hn h.2))
  rw [truncatedSixthMass_integral_eq_interval (lo_le_hi j ht) hs]
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le (lo_le_hi j ht)]
  intro u hu
  exact if_pos ⟨ht, hu⟩

theorem source_inner_integrable (j : Kind) {H : ℝ → ℝ} {M t : ℝ}
    (hm : Measurable H) (hM : 0 ≤ M) (hb : ∀ v, |H v| ≤ M) (ht : t ∈ Icc a b) :
    IntervalIntegrable (fun u => H (V j t u) * D t u) volume (lo j t) (hi j) := by
  apply (source_row_integrable j hm hM hb t).intervalIntegrable.congr
  intro u hu
  have hu' : u ∈ Icc (lo j t) (hi j) := by
    simpa only [uIcc_of_le (lo_le_hi j ht)] using uIoc_subset_uIcc hu
  exact if_pos ⟨ht, hu'⟩

theorem source_outer_integrable (j : Kind) {H : ℝ → ℝ} {M : ℝ}
    (hm : Measurable H) (hM : 0 ≤ M) (hb : ∀ v, |H v| ≤ M) :
    IntervalIntegrable (fun t => ∫ u in lo j t..hi j, H (V j t u) * D t u) volume a b := by
  apply (source_integrable j hm hM hb).integral_prod_left.intervalIntegrable.congr
  intro t ht
  exact source_inner j H (by simpa only [uIcc_of_le constants.2.1.le] using uIoc_subset_uIcc ht)

theorem source_product (j : Kind) {H : ℝ → ℝ} {M : ℝ}
    (hm : Measurable H) (hM : 0 ≤ M) (hb : ∀ v, |H v| ≤ M) :
    I j H = ∫ p : ℝ × ℝ, source j H p.1 p.2 := by
  have hs : Function.support (fun t => ∫ u, source j H t u) ⊆ Icc a b := by
    intro t ht
    by_contra hn
    apply ht
    have he (u : ℝ) : source j H t u = 0 := if_neg (fun h => hn h.1)
    simp only [he, integral_zero]
  rw [show (∫ p : ℝ × ℝ, source j H p.1 p.2) = ∫ t, ∫ u, source j H t u from
    integral_prod _ (source_integrable j hm hM hb),
    truncatedSixthMass_integral_eq_interval constants.2.1.le hs]
  symm
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le constants.2.1.le]
  exact fun t ht => source_inner j H ht

theorem transport (j : Kind) {H : ℝ → ℝ} {M : ℝ}
    (hm : Measurable H) (hM : 0 ≤ M) (hb : ∀ v, |H v| ≤ M) :
    I j H = ∫ v in (1 : ℝ)..3, H v * K j v := by
  rw [source_product j hm hM hb,
    show (∫ p : ℝ × ℝ, source j H p.1 p.2) = ∫ t, ∫ u, source j H t u from
      integral_prod _ (source_integrable j hm hM hb)]
  simp_rw [inner_substitution]
  rw [integral_integral_swap (f := fun t v => H v * masked j v t)
    (weighted_integrable j hm hM hb).swap]
  simp_rw [integral_const_mul, slice_integral]
  apply truncatedSixthMass_integral_eq_interval (by norm_num : (1 : ℝ) ≤ 3)
  intro v hv
  by_contra hn
  exact hv (by dsimp only; rw [kernel_outside j hn, mul_zero])

theorem weighted_kernel_integrable (j : Kind) {H : ℝ → ℝ} {M : ℝ}
    (hm : Measurable H) (hM : 0 ≤ M) (hb : ∀ v, |H v| ≤ M) :
    Integrable (fun v => H v * K j v) := by
  have hi := (weighted_integrable j hm hM hb).integral_prod_left
  simpa only [integral_const_mul, slice_integral] using hi

end Wu2008DoubleSieve.Gamma678Feedback
