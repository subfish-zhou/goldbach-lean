import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLabelledPhysicalSieve
import MathlibNt.Wu2008DoubleSieve.Omega3NonCoprime

/-! Exact original-label splitting, without discarding exceptional prime outputs. -/
namespace Wu2008DoubleSieve.LabelledPhysical
open Finset
open scoped Classical

/-- Nat subtraction is retained; primality itself excludes the truncated-zero case. -/
theorem prime_output_dvd_of_not_coprime {N e q : ℕ}
    (hp : (N - e * q).Prime) (he : ¬ e.Coprime N) : N - e * q ∣ N := by
  obtain ⟨r, hr, hre, hrN⟩ := Nat.Prime.not_coprime_iff_dvd.mp he
  have hrd : r ∣ N - e * q := Nat.dvd_sub hrN (hre.trans (dvd_mul_right e q))
  have heq : r = N - e * q := (Nat.dvd_prime hp).mp hrd |>.resolve_left hr.ne_one
  exact heq ▸ hrN

namespace Family
variable {α : Type*} {N : ℕ} (L : Family α N)

/-- Filter only labels; every physical function is the original one. -/
noncomputable def coprimePart : Family α N where
  labels := L.labels.filter (fun c => (L.cofactor c).Coprime N)
  weight := L.weight
  cofactor := L.cofactor
  lower := L.lower
  upper := L.upper
  weight_nonneg := fun c hc => L.weight_nonneg c (mem_filter.mp hc).1
  geometry := fun c hc => L.geometry c (mem_filter.mp hc).1

/-- The complementary labels, with full original multiplicities and weights. -/
noncomputable def noncoprimePart : Family α N where
  labels := L.labels.filter (fun c => ¬ (L.cofactor c).Coprime N)
  weight := L.weight
  cofactor := L.cofactor
  lower := L.lower
  upper := L.upper
  weight_nonneg := fun c hc => L.weight_nonneg c (mem_filter.mp hc).1
  geometry := fun c hc => L.geometry c (mem_filter.mp hc).1

theorem coprimePart_coprime {c : α} (hc : c ∈ L.coprimePart.labels) :
    (L.coprimePart.cofactor c).Coprime N := (mem_filter.mp hc).2

theorem mass_coprime_split : L.mass = L.coprimePart.mass + L.noncoprimePart.mass := by
  unfold mass coprimePart noncoprimePart primes
  simp only [sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro c _
  by_cases h : (L.cofactor c).Coprime N <;> simp [h]

theorem primeMass_coprime_split :
    L.primeMass = L.coprimePart.primeMass + L.noncoprimePart.primeMass := by
  unfold primeMass coprimePart noncoprimePart primes
  simp only [sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro c _
  by_cases h : (L.cofactor c).Coprime N <;> simp [h]

theorem noncoprimePart_prime_output_mem (hN : 0 < N) {c : α}
    (hc : c ∈ L.noncoprimePart.labels) {q : ℕ}
    (hp : (N - L.noncoprimePart.cofactor c * q).Prime) :
    N - L.noncoprimePart.cofactor c * q ∈ N.primeFactors := by
  exact Nat.mem_primeFactors.mpr ⟨hp,
    prime_output_dvd_of_not_coprime hp (mem_filter.mp hc).2, hN.ne'⟩

theorem noncoprimePart_weightAt_le (b : ℕ) :
    L.noncoprimePart.weightAt b ≤ L.weightAt b := by
  unfold weightAt noncoprimePart primes
  apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
  intro c hc _
  exact mul_nonneg (L.weight_nonneg c hc) (Nat.cast_nonneg _)

/-- Genuine pushforward of the bad prime mass, not a multiplicity-free image count. -/
theorem noncoprimePart_primeMass_eq (hN : 0 < N) :
    L.noncoprimePart.primeMass = ∑ b ∈ N.primeFactors, L.noncoprimePart.weightAt b := by
  have ht := L.noncoprimePart.output_test
    (fun b => if b ∈ N.primeFactors then (1 : ℝ) else 0)
  have hs : (range (N + 1)).filter (fun b => b ∈ N.primeFactors) = N.primeFactors := by
    ext b
    simp only [mem_filter, mem_range, and_iff_right_iff_imp]
    intro hb
    exact Nat.lt_succ_of_le (Nat.le_of_dvd hN (Nat.mem_primeFactors.mp hb).2.1)
  simp only [mul_ite, mul_one, mul_zero, ← sum_filter, hs] at ht
  rw [ht]
  unfold primeMass
  apply sum_congr rfl
  intro c hc
  congr 1
  simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, sum_filter]
  apply sum_congr rfl
  intro q _
  have hi : (N - L.noncoprimePart.cofactor c * q).Prime ↔
      N - L.noncoprimePart.cofactor c * q ∈ N.primeFactors :=
    ⟨L.noncoprimePart_prime_output_mem hN hc, Nat.prime_of_mem_primeFactors⟩
  simp only [hi]

theorem noncoprimePart_primeMass_le_sum (hN : 0 < N) :
    L.noncoprimePart.primeMass ≤ ∑ b ∈ N.primeFactors, L.weightAt b := by
  rw [L.noncoprimePart_primeMass_eq hN]
  exact sum_le_sum fun b _ => L.noncoprimePart_weightAt_le b

/-- A local fixed-output bound is still an explicit input; no high-family payment is asserted. -/
theorem noncoprimePart_primeMass_le_log (hN : 0 < N) {F : ℝ} (hF : 0 ≤ F)
    (hlocal : ∀ b ∈ N.primeFactors, L.weightAt b ≤ F) :
    L.noncoprimePart.primeMass ≤ F * Real.log N / Real.log 2 := by
  have hcard : (N.primeFactors.card : ℝ) ≤ Real.log N / Real.log 2 := by
    exact (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
      (primeFactors_card_mul_log_two_le N hN)
  calc
    _ ≤ ∑ b ∈ N.primeFactors, L.weightAt b := L.noncoprimePart_primeMass_le_sum hN
    _ ≤ ∑ _b ∈ N.primeFactors, F := sum_le_sum hlocal
    _ = F * (N.primeFactors.card : ℝ) := by simp [mul_comm]
    _ ≤ F * (Real.log N / Real.log 2) := mul_le_mul_of_nonneg_left hcard hF
    _ = _ := by ring

theorem primeMass_le_coprimePart_add_log (hN : 0 < N) {F : ℝ} (hF : 0 ≤ F)
    (hlocal : ∀ b ∈ N.primeFactors, L.weightAt b ≤ F) :
    L.primeMass ≤ L.coprimePart.primeMass + F * Real.log N / Real.log 2 := by
  rw [L.primeMass_coprime_split]
  exact add_le_add le_rfl (L.noncoprimePart_primeMass_le_log hN hF hlocal)

end Family
end Wu2008DoubleSieve.LabelledPhysical
