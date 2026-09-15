import MathlibNt.Wu2008DoubleSieve.ReboxingParameterSource
import MathlibNt.Wu2008DoubleSieve.ReboxingBoundaryR2ReverseAtom

/-!
# The fixed-cutoff Omega2 parameter

Wu04 Lemma 5.1 (5.2) uses `(Q/d)^(1/t)`, not the selected prime as
cutoff. Its ratio is the transform `t*x/(x+1)` of the old Buchstab
ratio `x=log(Q/d)/log(p)-1`. The transform below is used explicitly;
the two ratios are never identified.
-/

namespace Wu2008DoubleSieve

open Real
open scoped Classical

noncomputable def omega2ParameterTransform (t x : ℝ) : ℝ :=
  t * (1 - 1 / (x + 1))

theorem omega2ParameterTransform_mono {t a b : ℝ}
    (ht : 0 ≤ t) (ha : 1 ≤ a) (hab : a ≤ b) :
    omega2ParameterTransform t a ≤ omega2ParameterTransform t b := by
  unfold omega2ParameterTransform
  exact mul_le_mul_of_nonneg_left
    (sub_le_sub_left (one_div_le_one_div_of_le (by linarith) (by linarith)) 1) ht

theorem omega2ParameterTransform_domain {t x : ℝ}
    (ht : 3 ≤ t) (ht5 : t ≤ 5) (hx : 1 ≤ x) :
    1 ≤ omega2ParameterTransform t x ∧ omega2ParameterTransform t x ≤ 10 := by
  have hden : 0 < x + 1 := by linarith
  have hr : 1 / (x + 1) ≤ (1 / 2 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hr0 : 0 ≤ 1 / (x + 1) := by positivity
  unfold omega2ParameterTransform
  constructor <;> nlinarith

theorem omega2ParameterTransform_width {t a b : ℝ}
    (ht : 0 ≤ t) (ht5 : t ≤ 5) (ha : 1 ≤ a) (hab : a ≤ b) :
    0 ≤ omega2ParameterTransform t b - omega2ParameterTransform t a ∧
      omega2ParameterTransform t b - omega2ParameterTransform t a ≤ 5 * (b - a) := by
  have ha0 : 0 < a + 1 := by linarith
  have hb0 : 0 < b + 1 := by linarith
  have hden : 1 ≤ (a + 1) * (b + 1) := by nlinarith
  have he : omega2ParameterTransform t b - omega2ParameterTransform t a =
      t * ((b - a) / ((a + 1) * (b + 1))) := by
    unfold omega2ParameterTransform
    field_simp
    ring
  refine ⟨sub_nonneg.mpr (omega2ParameterTransform_mono ht ha hab), ?_⟩
  rw [he]
  exact (mul_le_mul_of_nonneg_left (div_le_self (sub_nonneg.mpr hab) hden) ht).trans
    (mul_le_mul_of_nonneg_right ht5 (sub_nonneg.mpr hab))

theorem omega2_fixed_cutoff_ratio {D p t : ℝ}
    (hD : 1 < D) (hp : 0 < p) (ht : 0 < t) :
    log (D / p) / log (D ^ (1 / t)) = t * (1 - log p / log D) := by
  have hD0 : 0 < D := by linarith
  have hL : 0 < log D := log_pos hD
  rw [log_rpow hD0, log_div hD0.ne' hp.ne']
  field_simp

theorem omega2_fixed_cutoff_transform {D p t : ℝ}
    (_hD : 1 < D) (_hp : 1 < p) :
    omega2ParameterTransform t (log D / log p - 1) =
      t * (1 - log p / log D) := by
  simp only [omega2ParameterTransform, sub_add_cancel, one_div_div]

theorem omega2_fixed_cutoff_domain {D p s t : ℝ}
    (hD : 1 < D) (hs : 2 ≤ s) (ht : 3 ≤ t)
    (hcondition : 2 ≤ t - t / s)
    (hp : D ^ (1 / t) ≤ p) (hp' : p ≤ D ^ (1 / s)) :
    2 ≤ t * (1 - log p / log D) ∧ t * (1 - log p / log D) ≤ t - 1 := by
  have hD0 : 0 < D := by linarith
  have hL : 0 < log D := log_pos hD
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  have hp0 : 0 < p := (rpow_pos_of_pos hD0 _).trans_le hp
  have hlo := log_le_log (rpow_pos_of_pos hD0 (1 / t)) hp
  have hhi := log_le_log hp0 hp'
  rw [log_rpow hD0] at hlo hhi
  have hl : 1 / t ≤ log p / log D := (le_div_iff₀ hL).2 (by nlinarith)
  have hh : log p / log D ≤ 1 / s := (div_le_iff₀ hL).2 (by nlinarith)
  have htl : t * (1 / t) = 1 := by field_simp
  have hts : t * (1 / s) = t / s := by ring
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hl ht0.le,
    mul_le_mul_of_nonneg_left hh ht0.le]

theorem omega2_fixed_replacement_window_bounds {D p t a b : ℝ}
    (hD : 1 < D) (hp : 1 < p) (ht : 3 ≤ t) (ht5 : t ≤ 5)
    (ha : 1 ≤ a) (hau : a ≤ log D / log p - 1)
    (hub : log D / log p - 1 ≤ b) :
    let w := D ^ (1 / t)
    let v := omega2ParameterTransform t b
    (D / p) ^ (1 / v) ≤ w ∧ w ^ (1 / 10 : ℝ) ≤ (D / p) ^ (1 / v) ∧
      log (w / ((D / p) ^ (1 / v))) ≤ 5 * (b - a) * log w := by
  dsimp only
  let x := log D / log p - 1
  let u := omega2ParameterTransform t x
  let v := omega2ParameterTransform t b
  let w := D ^ (1 / t)
  have hD0 : 0 < D := by linarith
  have hp0 : 0 < p := by linarith
  have ht0 : 0 < t := by linarith
  have hw1 : 1 < w := one_lt_rpow hD (by positivity)
  have hw0 : 0 < w := by linarith
  have hLw : 0 < log w := log_pos hw1
  have hx : 1 ≤ x := ha.trans hau
  have hb : 1 ≤ b := hx.trans hub
  have hu := omega2ParameterTransform_domain ht ht5 hx
  have hv := omega2ParameterTransform_domain ht ht5 hb
  have huv : u ≤ v := omega2ParameterTransform_mono ht0.le hx hub
  have hv0 : 0 < v := by dsimp [v]; linarith [hv.1]
  have hz0 : 0 < (D / p) ^ (1 / v) := rpow_pos_of_pos (div_pos hD0 hp0) _
  have hr : log (D / p) / log w = u := by
    rw [omega2_fixed_cutoff_ratio hD hp0 ht0]
    exact (omega2_fixed_cutoff_transform hD hp).symm
  have he : log ((D / p) ^ (1 / v)) = (u / v) * log w := by
    rw [log_rpow (div_pos hD0 hp0)]
    have hh := (div_eq_iff hLw.ne').1 hr
    rw [hh]
    ring
  have hratio : u / v ≤ 1 := (div_le_one hv0).2 huv
  have hratiolo : (1 / 10 : ℝ) ≤ u / v := (le_div_iff₀ hv0).2 (by
    dsimp [u, v]
    linarith [hu.1, hv.2])
  have hle : (D / p) ^ (1 / v) ≤ w := by
    apply (log_le_log_iff hz0 hw0).1
    rw [he]
    nlinarith
  have hlo : w ^ (1 / 10 : ℝ) ≤ (D / p) ^ (1 / v) := by
    apply (log_le_log_iff (rpow_pos_of_pos hw0 _) hz0).1
    rw [log_rpow hw0, he]
    nlinarith
  refine ⟨hle, hlo, ?_⟩
  have hwidth := (omega2ParameterTransform_width ht0.le ht5 ha (hau.trans hub)).2
  have hua := omega2ParameterTransform_mono ht0.le ha hau
  have hquot : 1 - u / v ≤ 5 * (b - a) := by
    have hid : 1 - u / v = (v - u) / v := by field_simp
    rw [hid]
    have hh := div_le_self (sub_nonneg.mpr huv) hv.1
    dsimp [u, v] at hh ⊢
    linarith
  rw [log_div hw0.ne' hz0.ne', he]
  nlinarith

end Wu2008DoubleSieve
