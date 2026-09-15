import U8TwoDimensionalConvolution

/-! A positive rectangular sub-sum of the actual lcm convolution. -/
noncomputable section
open Finset
open scoped BigOperators
namespace U8Literal.SmallProduct.TwoDimensional
open scoped Classical

def squarefreePrefix (T : ℕ) : Finset ℕ := (Icc 1 T).filter Squarefree

theorem mem_squarefreePrefix {d T : ℕ} :
    d ∈ squarefreePrefix T ↔ 1 ≤ d ∧ d ≤ T ∧ Squarefree d := by
  simp [squarefreePrefix, and_assoc]

theorem liuFactor_nonneg {N : ℕ} (hN : Even N) (d : ℕ) : 0 ≤ liuFactor N d := by
  by_cases hd : d = 0
  · simp [hd]
  rw [liuFactor, ArithmeticFunction.prodPrimeFactors_apply hd]
  apply prod_nonneg
  intro p hp
  split_ifs with h
  · exact le_rfl
  · have ht := roots_lt hN (Nat.prime_of_mem_primeFactors hp)
    rw [roots, if_neg h] at ht
    exact le_of_lt (one_div_pos.mpr (sub_pos.mpr ht))

theorem harmonicFactor_nonneg (d : ℕ) : 0 ≤ harmonicFactor d := by
  by_cases hd : d = 0
  · simp [hd]
  rw [harmonicFactor, ArithmeticFunction.prodPrimeFactors_apply hd]
  apply prod_nonneg
  intro p hp
  have ht : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  exact le_of_lt (one_div_pos.mpr (sub_pos.mpr ht))

theorem squarefree_lcm {d e : ℕ} (hd : Squarefree d) (he : Squarefree e) :
    Squarefree (Nat.lcm d e) := by
  apply Nat.squarefree_of_factorization_le_one (Nat.lcm_ne_zero hd.ne_zero he.ne_zero)
  intro p
  rw [Nat.factorization_lcm hd.ne_zero he.ne_zero]
  exact max_le (hd.natFactorization_le_one p) (he.natFactorization_le_one p)

theorem lcm_mem_prefix {d e T U : ℕ} (hd : d ∈ squarefreePrefix T)
    (he : e ∈ squarefreePrefix T) (hTU : T*T ≤ U) :
    Nat.lcm d e ∈ squarefreePrefix U := by
  obtain ⟨hd1, hdT, hds⟩ := mem_squarefreePrefix.mp hd
  obtain ⟨he1, heT, hes⟩ := mem_squarefreePrefix.mp he
  exact mem_squarefreePrefix.mpr
    ⟨Nat.one_le_iff_ne_zero.mpr (Nat.lcm_ne_zero hds.ne_zero hes.ne_zero),
    (Nat.lcm_le_mul hd1 he1).trans ((Nat.mul_le_mul hdT heT).trans hTU),
    squarefree_lcm hds hes⟩

theorem prefix_product_le {N T U : ℕ} (hN : Even N) (hTU : T*T ≤ U) :
    (∑ d ∈ squarefreePrefix T, liuFactor N d) *
      (∑ e ∈ squarefreePrefix T, harmonicFactor e) ≤
    ∑ n ∈ squarefreePrefix U, dimensionTwoFactor N n := by
  let S := (squarefreePrefix T) ×ˢ (squarefreePrefix T)
  have hmap : ∀ a ∈ S, Nat.lcm a.1 a.2 ∈ squarefreePrefix U := by
    intro a ha
    exact lcm_mem_prefix (mem_product.mp ha).1 (mem_product.mp ha).2 hTU
  rw [sum_mul_sum, ← sum_product _ _ (fun a : ℕ × ℕ => liuFactor N a.1 * harmonicFactor a.2)]
  rw [← sum_fiberwise_of_maps_to hmap (fun a => liuFactor N a.1 * harmonicFactor a.2)]
  apply sum_le_sum
  intro n hn
  rw [dimensionTwoFactor_eq_lcmConvolution hN (mem_squarefreePrefix.mp hn).2.2]
  unfold lcmConvolution
  rw [← sum_product _ _ (fun a : ℕ × ℕ =>
    if n = Nat.lcm a.1 a.2 then liuFactor N a.1 * harmonicFactor a.2 else 0)]
  calc
    _ = ∑ a ∈ S.filter (fun a => Nat.lcm a.1 a.2 = n),
        if n = Nat.lcm a.1 a.2 then liuFactor N a.1 * harmonicFactor a.2 else 0 := by
      apply sum_congr rfl
      intro a ha
      rw [if_pos (mem_filter.mp ha).2.symm]
    _ ≤ ∑ a ∈ n.divisors ×ˢ n.divisors,
        if n = Nat.lcm a.1 a.2 then liuFactor N a.1 * harmonicFactor a.2 else 0 := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro a ha
        have heq := (mem_filter.mp ha).2
        exact mem_product.mpr
          ⟨Nat.mem_divisors.mpr ⟨heq ▸ Nat.dvd_lcm_left _ _,
              (mem_squarefreePrefix.mp hn).2.2.ne_zero⟩,
           Nat.mem_divisors.mpr ⟨heq ▸ Nat.dvd_lcm_right _ _,
              (mem_squarefreePrefix.mp hn).2.2.ne_zero⟩⟩
      · intro a _ _
        split_ifs
        · exact mul_nonneg (liuFactor_nonneg hN _) (harmonicFactor_nonneg _)
        · exact le_rfl

theorem denominator_eq_prefix (N : ℕ) {Z R : ℝ} (hRZ : R < Z) :
    denominator N Z R = ∑ n ∈ squarefreePrefix ⌊R⌋₊, dimensionTwoFactor N n := by
  rw [denominator, carrier_eq_squarefree hRZ]
  apply sum_congr rfl
  intro n hn
  exact (ArithmeticFunction.prodPrimeFactors_apply (f := fun p => roots N p / ((p : ℝ)-roots N p))
    (mem_squarefreePrefix.mp hn).2.2.ne_zero).symm

/-- No coprimality is imposed on the two small factors. -/
theorem denominator_ge_prefix_product {N T : ℕ} (hN : Even N) {Z R : ℝ}
    (hRZ : R < Z) (hTR : (T : ℝ)^2 ≤ R) :
    (∑ d ∈ squarefreePrefix T, liuFactor N d) *
      (∑ e ∈ squarefreePrefix T, harmonicFactor e) ≤ denominator N Z R := by
  rw [denominator_eq_prefix N hRZ]
  apply prefix_product_le hN
  apply Nat.le_floor
  simpa only [Nat.cast_mul, pow_two] using hTR

end U8Literal.SmallProduct.TwoDimensional
