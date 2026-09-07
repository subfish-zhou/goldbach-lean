import MathlibNt.SieveTheory.LiLiuBuchstabTailPropagation

set_option autoImplicit false

open Set MeasureTheory
open scoped BigOperators

namespace LiLiuBuchstabSharp

/-- The finite odd-power expansion used below is algebraic, not sampled data. -/
noncomputable def logLower (n : ℕ) (x : ℝ) : ℝ :=
  2 * ∑ i ∈ Finset.range n, ((x - 1) / (x + 1)) ^ (2 * i + 1) / (2 * i + 1)

/-- A uniform, explicitly bounded analytic remainder on the complete interval `[1,2]`. -/
theorem logLower_error {x : ℝ} (hx : 1 ≤ x) (hx₂ : x ≤ 2) (n : ℕ) :
    0 ≤ Real.log x - logLower n x ∧
      Real.log x - logLower n x ≤ (9 / 4 : ℝ) * (1 / 3 : ℝ) ^ (2 * n + 1) := by
  let z := (x - 1) / (x + 1)
  have hxp : 0 < x + 1 := by linarith
  have hz : 0 ≤ z := div_nonneg (by linarith) hxp.le
  have hz₃ : z ≤ 1 / 3 := by
    apply (div_le_iff₀ hxp).mpr
    linarith
  have hz₁ : z < 1 := by linarith
  have he : (1 + z) / (1 - z) = x := by
    dsimp [z]
    field_simp
    ring
  have hl := Real.sum_range_le_log_div hz hz₁ n
  have hu := Real.log_div_le_sum_range_add hz hz₁ n
  rw [he] at hl hu
  have hd : (8 / 9 : ℝ) ≤ 1 - z ^ 2 := by nlinarith
  have hpow : z ^ (2 * n + 1) ≤ (1 / 3 : ℝ) ^ (2 * n + 1) :=
    pow_le_pow_left₀ hz hz₃ _
  have herr : z ^ (2 * n + 1) / (1 - z ^ 2) ≤
      (9 / 8 : ℝ) * (1 / 3 : ℝ) ^ (2 * n + 1) := by
    calc
      _ ≤ (1 / 3 : ℝ) ^ (2 * n + 1) / (8 / 9 : ℝ) := by
        apply div_le_div₀ (by positivity) hpow (by norm_num) hd
      _ = _ := by ring
  constructor
  · dsimp [logLower, z] at *
    linarith
  · dsimp [logLower, z] at *
    linarith

/-- Twelve exact Taylor terms give a uniform error strictly below `10⁻¹¹`. -/
theorem logLower_twelve_error {x : ℝ} (hx : 1 ≤ x) (hx₂ : x ≤ 2) :
    0 ≤ Real.log x - logLower 12 x ∧
      Real.log x - logLower 12 x < (1 / 100000000000 : ℝ) := by
  have h := logLower_error hx hx₂ 12
  constructor
  · exact h.1
  · exact lt_of_le_of_lt h.2 (by norm_num)

/-- An unconditional improvement of the previous coarse bound. This is NOT
    the requested sharp decimal bound. -/
theorem buchstab_le_709_div_1250 {u : ℝ} (hu : 2 ≤ u) :
    LiLiuPrereqBuchstab.buchstab u ≤ (709 / 1250 : ℝ) := by
  apply LiLiuPrereqBuchstab.buchstab_upper_on_tail (a := 2) (by norm_num) _ u hu
  intro v hv
  rw [LiLiuPrereqBuchstab.buchstab_eq_log_div hv.1 (by norm_num at hv ⊢; linarith [hv.2])]
  have hvp : 0 < v := by linarith [hv.1]
  apply (div_le_iff₀ hvp).mpr
  have hc : Real.log (1250 / 709 : ℝ) ≤ (709 / 1250 : ℝ) := by
    have h := Real.log_div_le_sum_range_add
      (x := (541 / 1959 : ℝ)) (by norm_num) (by norm_num) 4
    norm_num [Finset.sum_range_succ] at h
    linarith
  have ht := Real.log_le_sub_one_of_pos
    (show 0 < (v - 1) / (1250 / 709 : ℝ) from
      div_pos (by linarith [hv.1]) (by norm_num))
  rw [Real.log_div (by linarith [hv.1]) (by norm_num)] at ht
  nlinarith

end LiLiuBuchstabSharp