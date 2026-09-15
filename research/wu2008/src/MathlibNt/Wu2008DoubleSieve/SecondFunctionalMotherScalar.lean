import MathlibNt.Wu2008DoubleSieve.SecondFunctionalParameters

/-! # Unbounded four-band scalar certificate -/

namespace Wu2008DoubleSieve

noncomputable def secondFunctionalMotherScalar (x y z w : ℕ) : ℝ :=
  4 + (if x = 0 then 1 else 0) - 3*x - 3*y - 2*z - w +
    ((x+y).choose 2 : ℝ) + (x : ℝ)*z + (x-1 : ℕ) +
    (if 0 < x then (y : ℝ) else 0) +
    (if x = 0 then (y+z-2 : ℕ) else 0) +
    (if x = 0 ∧ 2 ≤ y then (z+w : ℕ) else 0) +
    (if x = 0 ∧ y = 1 then (z-1 : ℕ) else 0) +
    (if 2 ≤ x then (w : ℝ) else 0) +
    (if x = 1 ∧ 1 ≤ y then (z+w : ℕ) else 0) +
    (if x = 1 ∧ y = 0 then (z+w-1 : ℕ) else 0) +
    (if x = 0 ∧ y = 1 ∧ 1 ≤ z then (w : ℝ) else 0) +
    (if x = 0 ∧ y = 0 then (z-3 : ℕ) else 0) +
    (if x = 0 ∧ y = 0 ∧ 3 ≤ z then (w : ℝ) else 0) +
    (if x = 0 ∧ y = 0 ∧ z = 2 then (w-1 : ℕ) else 0) +
    (if x = 0 ∧ y = 1 ∧ z = 0 then (w-2 : ℕ) else 0) +
    (if x = 0 ∧ y = 0 ∧ z = 1 then (w-3 : ℕ) else 0) +
    (if x = 0 ∧ y = 0 ∧ z = 0 then (w-5 : ℕ) else 0)

theorem secondFunctionalMother_cast_sub_lower (n r : ℕ) :
    (n : ℝ) - r ≤ (n-r : ℕ) := by
  by_cases h : r ≤ n
  · rw [Nat.cast_sub h]
  · have hn : (n : ℝ) ≤ r := by exact_mod_cast (show n ≤ r by omega)
    exact le_trans (sub_nonpos.mpr hn) (Nat.cast_nonneg _)

theorem secondFunctionalMother_scalar (x y z w : ℕ) :
    (if x+y+z+w = 0 then (5 : ℝ) else 0) ≤ secondFunctionalMotherScalar x y z w := by
  have hw1 := secondFunctionalMother_cast_sub_lower w 1
  have hw2 := secondFunctionalMother_cast_sub_lower w 2
  have hw3 := secondFunctionalMother_cast_sub_lower w 3
  have hw5 := secondFunctionalMother_cast_sub_lower w 5
  norm_num at hw1 hw2 hw3 hw5
  have hz0 : (0 : ℝ) ≤ z := Nat.cast_nonneg z
  have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg w
  rcases (show x = 0 ∨ x = 1 ∨ 2 ≤ x by omega) with hx | hx | hx
  · subst x
    rcases (show y = 0 ∨ y = 1 ∨ 2 ≤ y by omega) with hy | hy | hy
    · subst y
      rcases (show z = 0 ∨ z = 1 ∨ z = 2 ∨ 3 ≤ z by omega) with hz | hz | hz | hz
      · subst z
        by_cases hw : w = 0
        · norm_num [hw, secondFunctionalMotherScalar]
        · simp [secondFunctionalMotherScalar, hw]
          linarith
      · subst z
        norm_num [secondFunctionalMotherScalar]
        linarith
      · subst z
        norm_num [secondFunctionalMotherScalar]
        linarith
      · have hz1 : z ≠ 1 := by omega
        have hz2 : z ≠ 2 := by omega
        have hzN : z ≠ 0 := by omega
        simp [secondFunctionalMotherScalar, hz, hz1, hz2, hzN,
          Nat.cast_sub hz,
          Nat.cast_sub (show 2 ≤ z by omega)]
        linarith
    · subst y
      by_cases hz : z = 0
      · norm_num [hz, secondFunctionalMotherScalar]
        linarith
      · have hz1 : 1 ≤ z := by omega
        simp [secondFunctionalMotherScalar, hz, hz1,
          show 1+z-2 = z-1 by omega, Nat.cast_sub hz1]
        linarith
    · have hyN : y ≠ 0 := by omega
      have hy1 : y ≠ 1 := by omega
      have hyR : (2 : ℝ) ≤ y := by exact_mod_cast hy
      simp [secondFunctionalMotherScalar, hy, hyN, hy1,
        Nat.cast_sub (show 2 ≤ y+z by omega),
        Nat.cast_choose_two]
      by_cases hy2 : y = 2
      · norm_num [hy2]
        linarith
      · have hyR3 : (3 : ℝ) ≤ y := by exact_mod_cast (show 3 ≤ y by omega)
        nlinarith
  · subst x
    by_cases hy : y = 0
    · subst y
      have hzw := secondFunctionalMother_cast_sub_lower (z+w) 1
      norm_num [secondFunctionalMotherScalar]
      push_cast at hzw
      linarith
    · have hy1 : 1 ≤ y := by omega
      simp [secondFunctionalMotherScalar, hy, hy1, Nat.cast_choose_two]
      by_cases hy2 : y = 1
      · norm_num [hy2]
        linarith
      · have hyR2 : (2 : ℝ) ≤ y := by exact_mod_cast (show 2 ≤ y by omega)
        nlinarith
  · have hxN : x ≠ 0 := by omega
    have hx1 : x ≠ 1 := by omega
    have hxR : (2 : ℝ) ≤ x := by exact_mod_cast hx
    have hy0 : (0 : ℝ) ≤ y := Nat.cast_nonneg y
    simp [secondFunctionalMotherScalar, hx, hxN, hx1,
      show 0 < x by omega,
      Nat.cast_sub (show 1 ≤ x by omega), Nat.cast_choose_two]
    have hprod : 0 ≤ ((x : ℝ)-2)*z := mul_nonneg (by linarith) hz0
    by_cases hm : x+y = 2
    · have hmR : (x : ℝ)+y = 2 := by exact_mod_cast hm
      nlinarith
    · have hmR : (3 : ℝ) ≤ x+y := by exact_mod_cast (show 3 ≤ x+y by omega)
      nlinarith

end Wu2008DoubleSieve
