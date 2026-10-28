import MathlibNt.SieveTheory.Liu.Weights.LiuWeightPaperQ
import Mathlib.NumberTheory.Harmonic.Bounds

/-! Elementary harmonic bounds for the finite Liu source weight. -/

open Finset
namespace MathlibNt.SieveTheory.LiuWeight
noncomputable section

/-- The finite harmonic sum, with the empty sum giving its value at zero. -/
noncomputable def liuHarmonic (x : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 x, (m : ℝ)⁻¹

@[simp]
theorem liuHarmonic_zero : liuHarmonic 0 = 0 := by
  simp [liuHarmonic]

theorem liuHarmonic_eq_harmonic (m : ℕ) :
    liuHarmonic m = (harmonic m : ℝ) := by
  rw [liuHarmonic, harmonic_eq_sum_Icc, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Rat.cast_inv, Rat.cast_natCast]

theorem log_add_one_le_liuHarmonic (m : ℕ) :
    Real.log (m + 1) ≤ liuHarmonic m := by
  rw [liuHarmonic_eq_harmonic]
  simpa only [Nat.cast_add, Nat.cast_one] using log_add_one_le_harmonic m

theorem liuHarmonic_le_one_add_log (m : ℕ) :
    liuHarmonic m ≤ 1 + Real.log m := by
  rw [liuHarmonic_eq_harmonic]
  exact harmonic_le_one_add_log m

/-- The exact Liu source is an indicator, so replacing it by one is permitted
only through this explicit pointwise upper bound. -/
theorem liuWeight_le_one (N z y a : ℕ) : liuWeight N z y a ≤ 1 := by
  unfold liuWeight
  split <;> simp

/-- The reciprocal mass of the actual Liu source is bounded by the harmonic
sum; this is the source factor used for the long-quotient PNT range. -/
theorem sum_liuWeight_div_le_liuHarmonic (N : ℕ) :
    ∑ a ∈ Icc 1 N,
      liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a / a ≤
        liuHarmonic N := by
  rw [liuHarmonic]
  apply sum_le_sum
  intro a ha
  have ha0 : 0 < (a : ℝ) := by exact_mod_cast (mem_Icc.mp ha).1
  rw [div_eq_mul_inv]
  simpa using mul_le_mul_of_nonneg_right
    (liuWeight_le_one N (liuSourceZ10 N) (liuSourceY3 N) a)
    (inv_nonneg.mpr ha0.le)

/-- The reciprocal Liu-source mass costs at most one logarithm. -/
theorem sum_liuWeight_div_le_one_add_log (N : ℕ) :
    ∑ a ∈ Icc 1 N,
      liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a / a ≤
        1 + Real.log N :=
  (sum_liuWeight_div_le_liuHarmonic N).trans (liuHarmonic_le_one_add_log N)


end
end MathlibNt.SieveTheory.LiuWeight
