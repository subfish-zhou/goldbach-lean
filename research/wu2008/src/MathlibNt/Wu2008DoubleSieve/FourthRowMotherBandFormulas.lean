import MathlibNt.Wu2008DoubleSieve.FourthRowMotherColourCounts
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Real.Basic

/-! # All surviving prefix cardinalities and the unbounded scalar certificate -/

namespace Wu2008DoubleSieve

theorem fourthRowMother_band_formulas (x y z : ℕ) :
    fourthRowMotherBandCount x y z [0, 0] = x - 1 ∧
    fourthRowMotherBandCount x y z [0, 1] = (if 0 < x then y else 0) ∧
    fourthRowMotherBandCount x y z [1, 1, 2] = (if x = 0 ∧ 2 ≤ y then z else 0) ∧
    fourthRowMotherBandCount x y z [1, 2, 2] = (if x = 0 ∧ y = 1 then z - 1 else 0) ∧
    fourthRowMotherBandCount x y z [0, 1, 2] = (if x = 1 ∧ 1 ≤ y then z else 0) ∧
    fourthRowMotherBandCount x y z [0, 2, 2] = (if x = 1 ∧ y = 0 then z - 1 else 0) ∧
    fourthRowMotherBandCount x y z [2, 2, 2, 2] =
      (if x = 0 ∧ y = 0 then z - 3 else 0) ∧
    fourthRowMotherBandCount x y z [1, 1, 1] +
      fourthRowMotherBandCount x y z [1, 1, 2] +
      fourthRowMotherBandCount x y z [1, 2, 2] +
      fourthRowMotherBandCount x y z [2, 2, 2] =
      (if x = 0 then y + z - 2 else 0) := by
  have h00 : fourthRowMotherBandCount x y z [0, 0] = x - 1 := by
    norm_num [fourthRowMotherBandCount]
    omega
  have h01 : fourthRowMotherBandCount x y z [0, 1] = (if 0 < x then y else 0) := by
    norm_num [fourthRowMotherBandCount]
  have h112 : fourthRowMotherBandCount x y z [1, 1, 2] =
      (if x = 0 ∧ 2 ≤ y then z else 0) := by
    norm_num [fourthRowMotherBandCount]
    split_ifs <;> omega
  have h122 : fourthRowMotherBandCount x y z [1, 2, 2] =
      (if x = 0 ∧ y = 1 then z - 1 else 0) := by
    norm_num [fourthRowMotherBandCount]
    split_ifs <;> omega
  have h012 : fourthRowMotherBandCount x y z [0, 1, 2] =
      (if x = 1 ∧ 1 ≤ y then z else 0) := by
    norm_num [fourthRowMotherBandCount]
    split_ifs <;> omega
  have h022 : fourthRowMotherBandCount x y z [0, 2, 2] =
      (if x = 1 ∧ y = 0 then z - 1 else 0) := by
    norm_num [fourthRowMotherBandCount]
    split_ifs <;> omega
  have h2222 : fourthRowMotherBandCount x y z [2, 2, 2, 2] =
      (if x = 0 ∧ y = 0 then z - 3 else 0) := by
    norm_num [fourthRowMotherBandCount]
    split_ifs <;> omega
  refine ⟨h00, h01, h112, h122, h012, h022, h2222, ?_⟩
  rw [h112, h122]
  norm_num [fourthRowMotherBandCount]
  split_ifs <;> omega

noncomputable def fourthRowMotherScalar (x y z : ℕ) : ℝ :=
  4 + (if x = 0 then 1 else 0) - 2 * (x + y + z : ℕ) - (x + y : ℕ) +
    ((x + y).choose 2 : ℝ) + (x : ℝ) * z + (x - 1 : ℕ) +
    (if 0 < x then (y : ℝ) else 0) +
    (if x = 0 then (y + z - 2 : ℕ) else 0) +
    (if x = 0 ∧ 2 ≤ y then (z : ℝ) else 0) +
    (if x = 0 ∧ y = 1 then (z - 1 : ℕ) else 0) +
    (if x = 1 ∧ 1 ≤ y then (z : ℝ) else 0) +
    (if x = 1 ∧ y = 0 then (z - 1 : ℕ) else 0) +
    (if x = 0 ∧ y = 0 then (z - 3 : ℕ) else 0)

theorem fourthRowMother_scalar (x y z : ℕ) :
    (if x + y + z = 0 then (5 : ℝ) else 0) ≤ fourthRowMotherScalar x y z := by
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have hy0 : (0 : ℝ) ≤ y := Nat.cast_nonneg y
  have hz0 : (0 : ℝ) ≤ z := Nat.cast_nonneg z
  rcases (show x = 0 ∨ x = 1 ∨ 2 ≤ x by omega) with hx | hx | hx
  · subst x
    rcases (show y = 0 ∨ y = 1 ∨ 2 ≤ y by omega) with hy | hy | hy
    · subst y
      rcases (show z = 0 ∨ z = 1 ∨ z = 2 ∨ 3 ≤ z by omega) with hz | hz | hz | hz
      · norm_num [hz, fourthRowMotherScalar]
      · norm_num [hz, fourthRowMotherScalar]
      · norm_num [hz, fourthRowMotherScalar]
      · norm_num [fourthRowMotherScalar, show z ≠ 0 by omega]
        rw [Nat.cast_sub (by omega : 2 ≤ z), Nat.cast_sub hz]
        norm_num
        linarith
    · subst y
      by_cases hz : z = 0
      · norm_num [hz, fourthRowMotherScalar]
      · have hz1 : 1 ≤ z := by omega
        simp [fourthRowMotherScalar, Nat.cast_sub hz1,
          show 1 + z - 2 = z - 1 by omega]
        linarith
    · have hy2 : (2 : ℝ) ≤ y := by exact_mod_cast hy
      have hsum : 2 ≤ y + z := by omega
      have hne : y ≠ 0 := by omega
      have hne1 : y ≠ 1 := by omega
      simp [fourthRowMotherScalar, hne, hne1, hy,
        Nat.cast_choose_two]
      rw [Nat.cast_sub hsum]
      push_cast
      by_cases hy3 : y = 2
      · norm_num [hy3]
        linarith
      · have hy3' : (3 : ℝ) ≤ y := by exact_mod_cast (show 3 ≤ y by omega)
        nlinarith
  · subst x
    by_cases hy : y = 0
    · subst y
      by_cases hz : z = 0
      · norm_num [hz, fourthRowMotherScalar]
      · have hz1 : 1 ≤ z := by omega
        simp [fourthRowMotherScalar, Nat.cast_sub hz1]
        linarith
    · have hy1 : 1 ≤ y := by omega
      simp [fourthRowMotherScalar, hy, hy1, Nat.cast_choose_two]
      by_cases hy2 : y = 1
      · norm_num [hy2]
        linarith
      · have hy2' : (2 : ℝ) ≤ y := by exact_mod_cast (show 2 ≤ y by omega)
        nlinarith
  · have hx1 : 1 ≤ x := by omega
    have hxR : (2 : ℝ) ≤ x := by exact_mod_cast hx
    simp only [fourthRowMotherScalar, if_neg (by omega : x + y + z ≠ 0),
      if_neg (by omega : x ≠ 0), if_pos (show 0 < x by omega),
      if_neg (by omega : ¬(x = 0 ∧ 2 ≤ y)),
      if_neg (by omega : ¬(x = 0 ∧ y = 1)),
      if_neg (by omega : ¬(x = 1 ∧ 1 ≤ y)),
      if_neg (by omega : ¬(x = 1 ∧ y = 0)),
      if_neg (by omega : ¬(x = 0 ∧ y = 0)), add_zero,
      Nat.cast_choose_two, Nat.cast_sub hx1]
    push_cast
    have hprod : 0 ≤ ((x : ℝ) - 2) * z := mul_nonneg (by linarith) hz0
    by_cases hm : x + y = 2
    · have hmR : (x : ℝ) + y = 2 := by exact_mod_cast hm
      nlinarith
    · have hmR : (3 : ℝ) ≤ x + y := by exact_mod_cast (show 3 ≤ x + y by omega)
      nlinarith

end Wu2008DoubleSieve
