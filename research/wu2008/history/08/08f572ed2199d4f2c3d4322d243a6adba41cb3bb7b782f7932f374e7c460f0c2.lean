import MathlibNt.Wu2008DoubleSieve.BoxMassPNT

/-!
# Finite real-endpoint transport and deletion of divisors

Wu (2004), (3.8)--(3.9). Counting primes and using `1/p ≥ 1/V` is
sufficient for the lower bound; no reciprocal partial summation is needed.
The ceiling transport pays one possible upper-endpoint prime and one unit
of interval length. Prime divisors of `N` are actually removed.
-/

namespace Wu2008DoubleSieve

open Finset Filter
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

/-- A lower bound for increments of the literal logarithmic integral. -/
theorem box_trueLi_sub_lower {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    (b - a) / Real.log b ≤ logarithmicIntegral b - logarithmicIntegral a := by
  have hia := MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegrand_intervalIntegrable ha
  have hib := MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegrand_intervalIntegrable
    (ha.trans hab)
  have hi := MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegrand_intervalIntegrable_of_two_le
    ha hab
  have heq : logarithmicIntegral b - logarithmicIntegral a =
      ∫ t in a..b, 1 / Real.log t := by
    simp only [logarithmicIntegral,
      MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral, zero_add]
    exact intervalIntegral.integral_interval_sub_left hib hia
  rw [heq]
  calc
    _ = ∫ _t in a..b, 1 / Real.log b := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul, div_eq_mul_inv, one_mul]
    _ ≤ _ := by
      apply intervalIntegral.integral_mono_on hab intervalIntegrable_const hi
      intro t ht
      exact one_div_le_one_div_of_le (Real.log_pos (by linarith [ht.1]))
        (Real.log_le_log (by linarith [ht.1]) ht.2)

/-- A finite covering, with the endpoint singleton and the deleted large
prime divisors both explicit. It remains valid for empty windows. -/
theorem boxPrimePrefix_subset_window_union {N : ℕ} (hN : N ≠ 0)
    {Y V z : ℝ} (hzY : z ≤ Y) :
    boxPrimePrefix ⌈V⌉₊ ⊆
      boxPrimePrefix ⌈Y⌉₊ ∪ primeWindow N Y V ∪
        largePrimeDivisors N z ∪ {⌈V⌉₊} := by
  intro p hp
  obtain ⟨hp, hpV⟩ := mem_boxPrimePrefix.mp hp
  by_cases hpY : p ≤ ⌈Y⌉₊
  · exact mem_union_left _ (mem_union_left _ (mem_union_left _
      (mem_boxPrimePrefix.mpr ⟨hp, hpY⟩)))
  by_cases he : p = ⌈V⌉₊
  · exact mem_union_right _ (mem_singleton.mpr he)
  have hYp : Y ≤ (p : ℝ) :=
    (Nat.le_ceil Y).trans (by exact_mod_cast (show ⌈Y⌉₊ ≤ p by omega))
  have hpV' : (p : ℝ) < V := Nat.lt_ceil.mp (by omega)
  by_cases hcop : p.Coprime N
  · exact mem_union_left _ (mem_union_left _ (mem_union_right _
      (mem_primeWindow.mpr ⟨hp, hcop, hYp, hpV'⟩)))
  · have hd : p ∣ N := Classical.not_not.mp ((hp.coprime_iff_not_dvd).not.mp hcop)
    exact mem_union_left _ (mem_union_right _
      (mem_largePrimeDivisors.mpr ⟨hp, hd, hN, hzY.trans hYp⟩))

theorem boxPrimePrefix_card_le_window {N : ℕ} (hN : N ≠ 0)
    {Y V z : ℝ} (hzY : z ≤ Y) :
    ((boxPrimePrefix ⌈V⌉₊).card : ℝ) ≤
      (boxPrimePrefix ⌈Y⌉₊).card + (primeWindow N Y V).card +
        (largePrimeDivisors N z).card + 1 := by
  have h := card_le_card (boxPrimePrefix_subset_window_union hN hzY (V := V))
  have hu := card_union_le
    (boxPrimePrefix ⌈Y⌉₊ ∪ primeWindow N Y V ∪ largePrimeDivisors N z) {⌈V⌉₊}
  have hu' := card_union_le
    (boxPrimePrefix ⌈Y⌉₊ ∪ primeWindow N Y V) (largePrimeDivisors N z)
  have hu'' := card_union_le (boxPrimePrefix ⌈Y⌉₊) (primeWindow N Y V)
  simp only [card_singleton] at hu
  have hn : (boxPrimePrefix ⌈V⌉₊).card ≤
      (boxPrimePrefix ⌈Y⌉₊).card + (primeWindow N Y V).card +
        (largePrimeDivisors N z).card + 1 := by omega
  exact_mod_cast hn

theorem box_card_le_mul_reciprocal_mass (N : ℕ) (Y V : ℝ) :
    ((primeWindow N Y V).card : ℝ) ≤
      V * ∑ p ∈ primeWindow N Y V, (1 : ℝ) / p := by
  rw [mul_sum]
  calc
    _ = ∑ _p ∈ primeWindow N Y V, (1 : ℝ) := by simp
    _ ≤ _ := ?_
  apply sum_le_sum
  intro p hp
  obtain ⟨hp, _, _, hpV⟩ := mem_primeWindow.mp hp
  rw [mul_one_div]
  exact (le_div_iff₀ (by exact_mod_cast hp.pos)).mpr (by simpa using hpV.le)

/-- Unconditional finite shrinking-window lower bound with the actual
PNT error and all endpoint/deletion payments visible. The constants precede
`N`, both real endpoints, and the lower-prime exponent. -/
theorem box_reciprocal_mass_trueLi_lower (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ N : ℕ, 1 < N →
      ∀ κ : ℝ, 0 < κ → ∀ Y V : ℝ,
        2 ≤ Y → Y ≤ V → (N : ℝ) ^ κ ≤ Y → X₀ ≤ ⌈V⌉₊ →
        (V - Y - 1) / Real.log (⌈V⌉₊ : ℝ) ≤
          V * (∑ p ∈ primeWindow N Y V, (1 : ℝ) / p) +
            1 / κ + 1 + 2 * (C * (⌈V⌉₊ : ℝ) / Real.log (⌈V⌉₊ : ℝ) ^ A) := by
  obtain ⟨C, hC, X₀, hPNT⟩ := boxPrimePrefix_trueLi A hA
  refine ⟨C, hC, X₀, ?_⟩
  intro N hN κ hκ Y V hY hYV hlow hX
  have hY0 : 0 ≤ Y := by linarith
  have hcY : (2 : ℝ) ≤ ⌈Y⌉₊ := hY.trans (Nat.le_ceil Y)
  have hcYV : (⌈Y⌉₊ : ℝ) ≤ ⌈V⌉₊ := by exact_mod_cast Nat.ceil_mono hYV
  have hcV : (2 : ℝ) ≤ ⌈V⌉₊ := hcY.trans hcYV
  have hP := hPNT ⌈V⌉₊ hX ⌈V⌉₊ (by exact_mod_cast hcV) le_rfl
  have hQ := hPNT ⌈V⌉₊ hX ⌈Y⌉₊ (by exact_mod_cast hcY) (Nat.ceil_mono hYV)
  have hcount := boxPrimePrefix_card_le_window (by omega : N ≠ 0) hlow (V := V)
  have hbad := largePrimeDivisors_card_le_inv hN (by omega : 0 < N) le_rfl hκ
  have hmass := box_card_le_mul_reciprocal_mass N Y V
  have hli := box_trueLi_sub_lower hcY hcYV
  have hlog : 0 < Real.log (⌈V⌉₊ : ℝ) := Real.log_pos (by linarith)
  have hend : V - Y - 1 ≤ (⌈V⌉₊ : ℝ) - ⌈Y⌉₊ := by
    have := Nat.ceil_lt_add_one hY0
    have := Nat.le_ceil V
    linarith
  have hlen := div_le_div_of_nonneg_right hend hlog.le
  have hP' := (abs_le.mp hP).1
  have hQ' := (abs_le.mp hQ).2
  linarith

end Wu2008DoubleSieve
