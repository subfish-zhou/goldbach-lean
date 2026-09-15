import U8Core
noncomputable section
open Finset
namespace U8Literal

theorem mem_halfOpenInterval {L U : ℝ} (hL : 1 ≤ L) (hU : 1 ≤ U) (n : ℕ) :
    n ∈ Ioc ⌊(⌈L⌉ : ℝ)-1⌋₊ ⌊(⌈U⌉ : ℝ)-1⌋₊ ↔ L ≤ (n : ℝ) ∧ (n : ℝ) < U := by
  have hlo : (0 : ℝ) ≤ (⌈L⌉ : ℝ)-1 := by have := Int.le_ceil L; linarith
  have hhi : (0 : ℝ) ≤ (⌈U⌉ : ℝ)-1 := by have := Int.le_ceil U; linarith
  rw [mem_Ioc, Nat.floor_lt hlo, Nat.le_floor_iff hhi]
  constructor
  · rintro ⟨hnL,hnU⟩
    have hzL : (⌈L⌉ : ℤ)-1 < (n : ℤ) := by exact_mod_cast hnL
    have hzU : (n : ℤ) ≤ (⌈U⌉ : ℤ)-1 := by exact_mod_cast hnU
    constructor
    · exact_mod_cast (Int.ceil_le.mp (show (⌈L⌉ : ℤ) ≤ (n : ℤ) by omega))
    · exact_mod_cast (Int.lt_ceil.mp (show (n : ℤ) < (⌈U⌉ : ℤ) by omega))
  · rintro ⟨hnL,hnU⟩
    have hzL : (⌈L⌉ : ℤ) ≤ (n : ℤ) := Int.ceil_le.mpr (by exact_mod_cast hnL)
    have hzU : (n : ℤ) < (⌈U⌉ : ℤ) := Int.lt_ceil.mpr (by exact_mod_cast hnU)
    constructor
    · exact_mod_cast (show (⌈L⌉ : ℤ)-1 < (n : ℤ) by omega)
    · exact_mod_cast (show (n : ℤ) ≤ (⌈U⌉ : ℤ)-1 by omega)

theorem mem_shortPrimeSupport {N : ℕ} (hN : 1 ≤ N) {ρ : ℝ} (hρ : 1 < ρ)
    (k : Key) (n : ℕ) : n ∈ shortPrimeSupport N ρ k ↔
      ρ^k.1 ≤ (n : ℝ) ∧ (N : ℝ)^originalAlpha ≤ n ∧
      (n : ℝ) < ρ^(k.1+1) ∧ (n : ℝ) < (N : ℝ)^(1/10 : ℝ) := by
  have hr : 1 ≤ ρ := hρ.le
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hU : (1 : ℝ) ≤ min (ρ^(k.1+1)) ((N : ℝ)^(1/10 : ℝ)) :=
    le_min (one_le_pow₀ hr) (Real.one_le_rpow hn (by norm_num))
  rw [shortPrimeSupport, mem_halfOpenInterval (le_max_of_le_left (one_le_pow₀ hr)) hU,
    max_le_iff, lt_min_iff]
  tauto

/-- The literal second Dirichlet divisor function, not an unordered quotient. -/
def tau2 (m : ℕ) : ℕ := (ArithmeticFunction.zeta ^ 2 : ArithmeticFunction ℕ) m

theorem tau2_eq_divisors (m : ℕ) : tau2 m = m.divisors.card := by
  unfold tau2
  rw [pow_two]
  calc
    _ = ∑ d ∈ m.divisors, (ArithmeticFunction.zeta : ArithmeticFunction ℕ) d :=
      ArithmeticFunction.coe_mul_zeta_apply (f := (ArithmeticFunction.zeta : ArithmeticFunction ℕ))
    _ = _ := ?_
  trans ∑ _d ∈ m.divisors, 1
  · apply sum_congr rfl
    intro d hd
    exact ArithmeticFunction.zeta_apply_ne (Nat.pos_of_mem_divisors hd).ne'
  · simp

theorem longAlpha_le_tau2 (N : ℕ) (ρ : ℝ) (k : Key) (m : ℕ) :
    longAlpha N ρ k m ≤ (tau2 m : ℝ) := by
  rw [tau2_eq_divisors]
  exact longAlpha_le_divisors N ρ k m

theorem longProducts_bounds {N : ℕ} {ρ : ℝ} (hρ : 1 < ρ)
    {k : Key} {m : ℕ} (hm : m ∈ longProducts N ρ k) :
    ρ^(k.2.1+k.2.2) ≤ (m : ℝ) ∧ (m : ℝ) < ρ^2*ρ^(k.2.1+k.2.2) := by
  obtain ⟨t,ht,rfl⟩ := mem_image.mp hm
  obtain ⟨_, _, hp, _, _, _, hlo, hhi, hlo', hhi'⟩ := mem_filter.mp ht
  have hr : 0 < ρ := lt_trans zero_lt_one hρ
  rw [Nat.cast_mul, pow_add]
  constructor
  · exact mul_le_mul hlo hlo' (pow_nonneg hr.le _) (Nat.cast_nonneg _)
  · have hh := mul_lt_mul hhi hhi'.le (by exact_mod_cast hp.pos)
      (pow_nonneg hr.le (k.2.1+1))
    rw [pow_succ,pow_succ] at hh
    nlinarith only [hh]

theorem longProducts_dyadic {N : ℕ} {ρ : ℝ} (hρ : 1 < ρ) (hρu : ρ ≤ 5/4)
    {k : Key} {m : ℕ} (hm : m ∈ longProducts N ρ k) :
    ρ^(k.2.1+k.2.2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2*ρ^(k.2.1+k.2.2) := by
  have hb := longProducts_bounds hρ hm
  have hr : 0 < ρ := lt_trans zero_lt_one hρ
  have hsq : ρ^2 ≤ 2 := by nlinarith
  exact ⟨hb.1, hb.2.le.trans (mul_le_mul_of_nonneg_right hsq (pow_nonneg hr.le _))⟩
end U8Literal
