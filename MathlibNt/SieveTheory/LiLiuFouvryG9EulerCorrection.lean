import MathlibNt.SieveTheory.LiLiuFouvryG9ProgressionDensity

namespace MathlibNt.SieveTheory.LiLiuPrereqWF
open Finset
open scoped Classical

noncomputable def g9BaseEuler (P : Finset ℕ) : ℝ :=
  ∏ p ∈ P, (1 - 1 / ((p : ℝ) - 1))

/-- Uniform payment for deleting one large prime Euler factor. -/
theorem g9_euler_factor_payment {x L : ℝ} (hL : 4 ≤ L) (hx : L ≤ x) :
    1 ≤ (1 - 1 / (x - 1)) * (1 + 1 / (L - 2)) := by
  have hx1 : 0 < x - 1 := by linarith
  have hL2 : 0 < L - 2 := by linarith
  rw [show 1 - 1 / (x - 1) = (x - 2) / (x - 1) by field_simp; ring,
    show 1 + 1 / (L - 2) = (L - 1) / (L - 2) by field_simp; ring,
    div_mul_div_comm]
  apply (le_div_iff₀ (mul_pos hx1 hL2)).mpr
  nlinarith

theorem g9_baseEuler_nonneg (P : Finset ℕ) (hP : ∀ p ∈ P, 2 < p) :
    0 ≤ g9BaseEuler P := by
  apply prod_nonneg
  intro p hp
  have hpr : (2 : ℝ) < p := by exact_mod_cast hP p hp
  have : 1 / ((p : ℝ) - 1) ≤ 1 :=
    (div_le_one (by linarith)).mpr (by linarith)
  linarith

/-- Erasing a label costs at most one payment, even when it was already absent. -/
theorem g9_baseEuler_erase_le (P : Finset ℕ) (hP : ∀ p ∈ P, 2 < p)
    (q : ℕ) {L : ℝ} (hL : 4 ≤ L) (hq : L ≤ (q : ℝ)) :
    g9BaseEuler (P.erase q) ≤ g9BaseEuler P * (1 + 1 / (L - 2)) := by
  have hC : 1 ≤ 1 + 1 / (L - 2) := by
    have : 0 ≤ 1 / (L - 2) := div_nonneg zero_le_one (by linarith)
    linarith
  by_cases hqP : q ∈ P
  · have he : g9BaseEuler P = g9BaseEuler (P.erase q) *
        (1 - 1 / ((q : ℝ) - 1)) := (prod_erase_mul P _ hqP).symm
    rw [he, mul_assoc]
    exact le_mul_of_one_le_right
      (g9_baseEuler_nonneg _ (fun p hp => hP p (mem_of_mem_erase hp)))
      (g9_euler_factor_payment hL hq)
  · rw [erase_eq_of_notMem hqP]
    exact le_mul_of_one_le_right (g9_baseEuler_nonneg P hP) hC

/-- Exact deletion formula: repeated prime labels require no distinctness. -/
theorem g9_euler_three_primes_exact (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {n s t : ℕ}
    (hn : n.Prime) (hs : s.Prime) (ht : t.Prime) :
    (∏ p ∈ P, (1 - progressionDensity (n * (s * t)) p)) =
      g9BaseEuler (((P.erase n).erase s).erase t) := by
  have he : ((P.erase n).erase s).erase t =
      P.filter (fun p => p.Coprime (n * (s * t))) := by
    ext p
    simp only [mem_erase, mem_filter, Nat.coprime_mul_iff_right]
    by_cases hp : p ∈ P
    · simp only [hp, and_true, true_and, Nat.coprime_primes (hP p hp) hn,
        Nat.coprime_primes (hP p hp) hs, Nat.coprime_primes (hP p hp) ht]
      tauto
    · simp [hp]
  rw [g9BaseEuler, he, prod_filter]
  apply prod_congr rfl
  intro p hp
  rw [progressionDensity_prime _ (hP p hp)]
  split_ifs <;> simp

/-- The genuine Euler correction is bounded by three uniform payments.
No assumption that the three prime labels are distinct or belong to P. -/
theorem g9_euler_three_primes_le (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ 2 < p) {n s t : ℕ}
    (hn : n.Prime) (hs : s.Prime) (ht : t.Prime)
    {L : ℝ} (hL : 4 ≤ L) (hnL : L ≤ (n : ℝ))
    (hsL : L ≤ (s : ℝ)) (htL : L ≤ (t : ℝ)) :
    (∏ p ∈ P, (1 - progressionDensity (n * (s * t)) p)) ≤
      g9BaseEuler P * (1 + 1 / (L - 2)) ^ 3 := by
  rw [g9_euler_three_primes_exact P (fun p hp => (hP p hp).1) hn hs ht]
  have hP2 : ∀ p ∈ P, 2 < p := fun p hp => (hP p hp).2
  have hPn : ∀ p ∈ P.erase n, 2 < p := fun p hp => hP2 p (mem_of_mem_erase hp)
  have hPns : ∀ p ∈ (P.erase n).erase s, 2 < p :=
    fun p hp => hPn p (mem_of_mem_erase hp)
  have hC : 0 ≤ 1 + 1 / (L - 2) := by
    have : 0 ≤ 1 / (L - 2) := div_nonneg zero_le_one (by linarith)
    linarith
  calc
    _ ≤ g9BaseEuler ((P.erase n).erase s) * (1 + 1 / (L - 2)) :=
      g9_baseEuler_erase_le _ hPns t hL htL
    _ ≤ (g9BaseEuler (P.erase n) * (1 + 1 / (L - 2))) *
        (1 + 1 / (L - 2)) :=
      mul_le_mul_of_nonneg_right (g9_baseEuler_erase_le _ hPn s hL hsL) hC
    _ ≤ ((g9BaseEuler P * (1 + 1 / (L - 2))) * (1 + 1 / (L - 2))) *
        (1 + 1 / (L - 2)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (g9_baseEuler_erase_le P hP2 n hL hnL) hC) hC
    _ = _ := by ring

/-- Finite weighted transfer using only structural prime support.
Zero coefficient terms are removed before the prime-label bound is invoked. -/
theorem g9_weighted_euler_three_primes_le (P U V : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ 2 < p) (α β : ℕ → ℝ)
    (hα0 : ∀ m ∈ U, 0 ≤ α m) (hβ0 : ∀ n ∈ V, 0 ≤ β n)
    {L : ℝ} (hL : 4 ≤ L)
    (hα : ∀ m ∈ U, α m ≠ 0 → ∃ s t : ℕ,
      s.Prime ∧ t.Prime ∧ m = s * t ∧ L ≤ (s : ℝ) ∧ L ≤ (t : ℝ))
    (hβ : ∀ n ∈ V, β n ≠ 0 → n.Prime ∧ L ≤ (n : ℝ)) :
    (∑ m ∈ U, ∑ n ∈ V, α m * β n *
      (∏ p ∈ P, (1 - progressionDensity (m * n) p))) ≤
      g9BaseEuler P * (1 + 1 / (L - 2)) ^ 3 *
        (∑ m ∈ U, ∑ n ∈ V, α m * β n) := by
  rw [mul_sum]
  apply sum_le_sum
  intro m hm
  rw [mul_sum]
  apply sum_le_sum
  intro n hn
  by_cases ham : α m = 0
  · simp [ham]
  by_cases hbn : β n = 0
  · simp [hbn]
  obtain ⟨s, t, hs, ht, hme, hsL, htL⟩ := hα m hm ham
  obtain ⟨hnp, hnL⟩ := hβ n hn hbn
  have he := g9_euler_three_primes_le P hP hnp hs ht hL hnL hsL htL
  rw [← hme, Nat.mul_comm n m] at he
  simpa only [mul_comm (g9BaseEuler P * (1 + 1 / (L - 2)) ^ 3)] using
    mul_le_mul_of_nonneg_left he (mul_nonneg (hα0 m hm) (hβ0 n hn))

end MathlibNt.SieveTheory.LiLiuPrereqWF
