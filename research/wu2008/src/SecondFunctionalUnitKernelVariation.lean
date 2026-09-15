import SecondFunctionalUnitKernelRegularity

open scoped BigOperators Classical
namespace SecondFunctionalUnitKernel
open Set Wu2008DoubleSieve

/-- The coefficient signs are retained inside the literal dot product. -/
theorem dot_variation {n : ℕ} (c x y : Fin n → ℝ) {d : ℝ}
    (hxy : ∀ i, |x i - y i| ≤ d) :
    |dot c x - dot c y| ≤ (∑ i, |c i|) * d := by
  unfold dot
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |c i * x i - c i * y i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |c i| * |x i - y i| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← mul_sub, abs_mul]
    _ ≤ ∑ i, |c i| * d := Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (hxy i) (abs_nonneg _))
    _ = _ := (Finset.sum_mul _ _ _).symm

theorem sum_variation {n : ℕ} (x y : Fin n → ℝ) {d : ℝ}
    (hxy : ∀ i, |x i - y i| ≤ d) : |(∑ i, x i) - ∑ i, y i| ≤ n*d := by
  simpa [dot] using dot_variation (fun _ => 1) x y hxy

/-- A changed strict or closed gate lies in the same closed band at the first point. -/
theorem row_change_band (s : Bool) {a z gamma w : ℝ} (hv : |a-z| ≤ w)
    (hc : ¬ (row s a gamma ↔ row s z gamma)) : |a-gamma| ≤ w := by
  have hv' := abs_le.mp hv
  cases s <;> simp only [row, Bool.false_eq_true, ↓reduceIte] at hc
  · by_cases ha : a ≤ gamma
    · have hz : ¬ z ≤ gamma := fun hz => hc (iff_of_true ha hz)
      apply abs_le.mpr
      constructor <;> linarith
    · have hz : z ≤ gamma := by
        by_contra hz
        exact hc (iff_of_false ha hz)
      apply abs_le.mpr
      constructor <;> linarith
  · by_cases ha : a < gamma
    · have hz : ¬ z < gamma := fun hz => hc (iff_of_true ha hz)
      apply abs_le.mpr
      constructor <;> linarith
    · have hz : z < gamma := by
        by_contra hz
        exact hc (iff_of_false ha hz)
      apply abs_le.mpr
      constructor <;> linarith

theorem affine_change_band {n : ℕ} (s : Bool) (c x y : Fin n → ℝ) (gamma : ℝ)
    {d : ℝ} (hxy : ∀ i, |x i-y i| ≤ d)
    (hc : ¬ (row s (dot c x) gamma ↔ row s (dot c y) gamma)) :
    x ∈ continuousBand c gamma ((∑ i, |c i|)*d) :=
  row_change_band s (dot_variation c x y hxy) hc

/-- Reciprocal control is only asserted on the common positive branch. -/
theorem reciprocal_variation {v w : ℝ} (hv : 1/10 ≤ v) (hw : 1/10 ≤ w) :
    |1/v - 1/w| ≤ 100 * |v-w| := by
  have hv0 : 0 < v := by linarith
  have hw0 : 0 < w := by linarith
  have hprod : (1/100 : ℝ) ≤ v*w := by nlinarith
  have he : 1/v - 1/w = (w-v)/(v*w) := by field_simp
  rw [he, abs_div, abs_of_pos (mul_pos hv0 hw0), abs_sub_comm]
  apply (div_le_iff₀ (mul_pos hv0 hw0)).mpr
  nlinarith [mul_nonneg (abs_nonneg (v-w)) (sub_nonneg.mpr hprod)]

theorem lower_variation {m : ℕ} (phi : ℝ) (x y : Fin (m+1) → ℝ) {d : ℝ}
    (hxy : ∀ i, |x i-y i| ≤ d) :
    |(phi - ∑ i, x i - x (Fin.last m)) -
      (phi - ∑ i, y i - y (Fin.last m))| ≤ (m+2 : ℝ)*d := by
  have hs := sum_variation x y hxy
  have hl := hxy (Fin.last m)
  calc
    _ = |((∑ i, y i) - ∑ i, x i) + (y (Fin.last m)-x (Fin.last m))| := by congr 1; ring
    _ ≤ |(∑ i, y i) - ∑ i, x i| + |y (Fin.last m)-x (Fin.last m)| := abs_add_le _ _
    _ = |(∑ i, x i) - ∑ i, y i| + |x (Fin.last m)-y (Fin.last m)| := by rw [abs_sub_comm (∑ i, y i), abs_sub_comm (y _)]
    _ ≤ _ := by push_cast at hs; linarith

theorem cap_variation {n : ℕ} (phi b : ℝ) (x y : Fin n → ℝ) {d : ℝ}
    (hxy : ∀ i, |x i-y i| ≤ d) :
    |(phi - ∑ i, x i - b) - (phi - ∑ i, y i - b)| ≤ (n : ℝ)*d := by
  convert sum_variation x y hxy using 1
  rw [show (phi - ∑ i, x i - b) - (phi - ∑ i, y i - b) = -((∑ i, x i) - ∑ i, y i) by ring, abs_neg]

end SecondFunctionalUnitKernel
