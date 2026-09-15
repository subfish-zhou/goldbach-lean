import MathlibNt.Wu2008DoubleSieve.Omega3NonCoprime

/-!
# A reciprocal bound for the repeated-p1 fibre

Wu04, TeX2215--2219. A single repeated prime supplies a fixed-power
saving. The three remaining reciprocal factors cost only harmonic sums.
-/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical

theorem omega3_triple_reciprocal_le (N : ℕ) (S : Finset (ℕ × ℕ × ℕ))
    (hS : ∀ a ∈ S, a.1 ∈ Icc 1 N ∧ a.2.1 ∈ Icc 1 N ∧ a.2.2 ∈ Icc 1 N) :
    (∑ a ∈ S, (1 / (a.1 : ℝ)) * (1 / (a.2.1 : ℝ)) * (1 / (a.2.2 : ℝ))) ≤
      (1 + log N) ^ 3 := by
  let H : ℝ := ∑ n ∈ Icc 1 N, 1 / (n : ℝ)
  have hH0 : 0 ≤ H := sum_nonneg fun n _ => by positivity
  have hH : H ≤ 1 + log N := by
    simpa [H] using omega3_reciprocal_multiples_le N 1 (by decide)
  have hsub : S ⊆ (Icc 1 N).product ((Icc 1 N).product (Icc 1 N)) := by
    intro a ha
    exact mem_product.mpr ⟨(hS a ha).1, mem_product.mpr (hS a ha).2⟩
  calc
    _ ≤ ∑ a ∈ (Icc 1 N).product ((Icc 1 N).product (Icc 1 N)),
        (1 / (a.1 : ℝ)) * (1 / (a.2.1 : ℝ)) * (1 / (a.2.2 : ℝ)) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ => by positivity)
    _ = H ^ 3 := by
      simp only [product_eq_sprod, sum_product]
      dsimp [H]
      rw [pow_succ, pow_two]
      simp only [sum_mul, mul_sum]
      apply sum_congr rfl
      intro p1 _
      apply sum_congr rfl
      intro p2 _
      apply sum_congr rfl
      intro p3 _
      ring
    _ ≤ _ := pow_le_pow_left₀ hH0 hH 3

theorem omega3_triple_repeated_floor_le (N d : ℕ) (S : Finset (ℕ × ℕ × ℕ))
    {Y : ℝ} (hd : 0 < d) (hY : 0 < Y)
    (hS : ∀ a ∈ S, a.1 ∈ Icc 1 N ∧ a.2.1 ∈ Icc 1 N ∧ a.2.2 ∈ Icc 1 N)
    (hlow : ∀ a ∈ S, Y ≤ (a.1 : ℝ)) :
    (∑ a ∈ S, (⌊((N : ℝ) / ((d : ℝ) * a.1 * a.2.1 * a.2.2)) / a.1⌋₊ : ℝ)) ≤
      ((N : ℝ) / ((d : ℝ) * Y)) * (1 + log N) ^ 3 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  calc
    _ ≤ ∑ a ∈ S, ((N : ℝ) / ((d : ℝ) * Y)) *
        ((1 / (a.1 : ℝ)) * (1 / (a.2.1 : ℝ)) * (1 / (a.2.2 : ℝ))) := by
      apply sum_le_sum
      intro a ha
      have h1 : (0 : ℝ) < a.1 := by exact_mod_cast (mem_Icc.mp (hS a ha).1).1
      have h2 : (0 : ℝ) < a.2.1 := by exact_mod_cast (mem_Icc.mp (hS a ha).2.1).1
      have h3 : (0 : ℝ) < a.2.2 := by exact_mod_cast (mem_Icc.mp (hS a ha).2.2).1
      calc
        _ ≤ ((N : ℝ) / ((d : ℝ) * a.1 * a.2.1 * a.2.2)) / a.1 :=
          Nat.floor_le (by positivity)
        _ ≤ ((N : ℝ) / ((d : ℝ) * a.1 * a.2.1 * a.2.2)) / Y :=
          div_le_div_of_nonneg_left (by positivity) hY (hlow a ha)
        _ = _ := by ring
    _ = ((N : ℝ) / ((d : ℝ) * Y)) *
        ∑ a ∈ S, (1 / (a.1 : ℝ)) * (1 / (a.2.1 : ℝ)) * (1 / (a.2.2 : ℝ)) :=
      (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (omega3_triple_reciprocal_le N S hS) (by positivity)

end Wu2008DoubleSieve
