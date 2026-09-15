import SecondFunctionalUnitPrimeFibreCap

open scoped BigOperators Classical Topology
namespace SecondFunctionalUnitFiniteKernel
open SecondFunctionalUnitPrimeFibre Wu2008DoubleSieve LiLiuPrereqBuchstab Real Finset Filter

/-- The ideal finite kernel has two strict gates. -/
noncomputable def F (v ell b : ℝ) : ℝ := if ell < v ∧ v < b then 1 / v else 0

theorem F_empty_lower {v ell b : ℝ} (h : v ≤ ell) : F v ell b = 0 := by
  simp [F, not_lt.mpr h]

theorem F_empty_cap {v ell b : ℝ} (h : b ≤ v) : F v ell b = 0 := by
  simp [F, not_lt.mpr h]

theorem F_empty_order {v ell b : ℝ} (h : b ≤ ell) : F v ell b = 0 := by
  apply if_neg
  rintro ⟨h1,h2⟩
  linarith

theorem F_range {v ell b : ℝ} (hel : 1/10 ≤ ell) :
    0 ≤ F v ell b ∧ F v ell b ≤ 10 := by
  unfold F
  split_ifs with h
  · have hv : (1/10 : ℝ) ≤ v := hel.trans h.1.le
    constructor
    · positivity
    · have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1/10) hv
      norm_num at hh
      simpa only [one_div] using hh
  · norm_num

/-- The original clipped, closed-cap fibre is empty when the cap is below the lower gate. -/
theorem weight_empty_order {R v ell b : ℝ} (hR : 1 < R) (h : b ≤ ell) :
    weight R v ell b = 0 := by
  unfold weight count
  rw [fibre_empty (rpow_nonneg (by linarith : 0 ≤ R) _)
    (rpow_le_rpow_of_exponent_le hR.le ((min_le_right _ _).trans h))]
  simp

/-- One PNT threshold controls all three moving scalar parameters and both discrete faces. -/
theorem pointwise_threshold (tau : ℝ) (ht : 0 < tau) (ht1 : tau ≤ 1) :
    ∃ T : ℝ, 1 < T ∧ ∀ R : ℝ, T ≤ R → ∀ v ell b eta : ℝ,
      1/10 ≤ ell → 0 < eta →
      |weight R v ell b - F v ell b| ≤
        (20*tau + 20*R^(-eta)) +
          (if |v-ell| ≤ eta then 30 else 0) + (if |v-b| ≤ eta then 30 else 0) := by
  obtain ⟨T,hT,h⟩ := scalar_threshold (1/10) tau (by norm_num) ht
  refine ⟨T,hT,?_⟩
  intro R hRT v ell b eta hel heta
  have hR := hT.trans_le hRT
  have hd : 0 ≤ R ^ (-eta) := rpow_nonneg (by linarith) _
  have hE : 0 ≤ 20*tau + 20*R^(-eta) := by positivity
  have hi : 0 ≤ (if |v-ell| ≤ eta then (30 : ℝ) else 0) := by split_ifs <;> norm_num
  have hj : 0 ≤ (if |v-b| ≤ eta then (30 : ℝ) else 0) := by split_ifs <;> norm_num
  by_cases heb : b ≤ ell
  · rw [weight_empty_order hR heb, F_empty_order heb, sub_self, abs_zero]
    positivity
  have hh := h R hRT v ell b hel (le_of_not_ge heb)
  have hg : |weight R v ell b - F v ell b| ≤ 30 := by
    have hf := F_range (v := v) (b := b) hel
    have hw := hh.1
    norm_num at hw
    apply abs_le.mpr
    constructor <;> linarith
  by_cases hl : |v-ell| ≤ eta
  · rw [if_pos hl]
    linarith
  by_cases hb : |v-b| ≤ eta
  · rw [if_pos hb]
    linarith
  rw [if_neg hl, if_neg hb, add_zero, add_zero]
  by_cases hv : v ≤ ell
  · rw [weight_empty hR hv, F_empty_lower hv, sub_self, abs_zero]
    exact hE
  have hvl : ell < v := lt_of_not_ge hv
  have hgap : ell + eta ≤ v := by
    rw [abs_of_pos (sub_pos.mpr hvl)] at hl
    linarith
  by_cases hvb : v < b
  · rw [F, if_pos ⟨hvl,hvb⟩]
    have hh' := hh.2.2.1 eta heta hgap hvb.le
    norm_num [div_eq_mul_inv] at hh' ⊢
    linarith
  · have hbgap : b + eta ≤ v := by
      rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_gt hvb))] at hb
      linarith
    rw [F_empty_cap (le_of_not_gt hvb), sub_zero, abs_of_nonneg hh.1.1]
    have hbpos : (0 : ℝ) < b := by linarith
    have hr := ratio_le (by norm_num : (0 : ℝ) < 1/10)
      (hel.trans (le_of_not_ge heb)) hd
    have he := hh.2.2.2 eta heta hbgap
    have hm := mul_le_mul_of_nonneg_left hr (by linarith : 0 ≤ 1+tau)
    rw [mul_div_assoc] at he
    have he' := he.trans hm
    norm_num [div_eq_mul_inv] at he'
    nlinarith
end SecondFunctionalUnitFiniteKernel
