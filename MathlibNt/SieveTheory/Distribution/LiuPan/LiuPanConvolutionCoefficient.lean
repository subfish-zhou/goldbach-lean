import MathlibNt.SieveTheory.Liu.Weights.LiuWeight
import Mathlib.NumberTheory.Divisors

open scoped BigOperators
open Finset
namespace MathlibNt.SieveTheory.LiuWeight

/-- The actual Liu weight convolved with the prime indicator. -/
noncomputable def liuBeta (N z y n : ℕ) : ℝ :=
  ∑ a ∈ n.divisors, liuWeight N z y a * if (n / a).Prime then 1 else 0

/-- Effective divisor terms, without multiplicities of pair representations. -/
def liuBetaSupport (N z y n : ℕ) : Finset ℕ :=
  n.divisors.filter fun a => LiuWeightSupport N z y a ∧ (n / a).Prime

theorem liuBeta_eq_card (N z y n : ℕ) :
    liuBeta N z y n = (liuBetaSupport N z y n).card := by
  classical
  simp only [liuBeta, liuBetaSupport, liuWeight, Finset.sum_filter,
    Nat.cast_sum, Finset.card_eq_sum_ones]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp_all

@[simp] theorem liuBeta_zero (N z y : ℕ) : liuBeta N z y 0 = 0 := by
  simp [liuBeta]

theorem liuBeta_nonneg (N z y n : ℕ) : 0 ≤ liuBeta N z y n := by
  rw [liuBeta_eq_card]
  positivity

/-- Distinct effective divisors have distinct complementary primes. -/
theorem liuBetaSupport_complement_injective (N z y n : ℕ) :
    Set.InjOn (fun a => n / a) (liuBetaSupport N z y n) := by
  intro a ha b hb hab
  change n / a = n / b at hab
  have ha' := Finset.mem_filter.mp ha
  have hb' := Finset.mem_filter.mp hb
  have ea := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors ha'.1)
  have eb := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hb'.1)
  apply Nat.mul_right_cancel ha'.2.2.pos
  calc
    a * (n / a) = n := ea
    _ = b * (n / a) := by rw [hab]; exact eb.symm

/-- Every effective complement belongs to the actual prime-factor carrier. -/
theorem liuBetaSupport_complement_mem_primeFactors {N z y n a : ℕ}
    (ha : a ∈ liuBetaSupport N z y n) : n / a ∈ n.primeFactors := by
  have ha' := Finset.mem_filter.mp ha
  exact Nat.mem_primeFactors.mpr ⟨ha'.2.2,
    Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors ha'.1),
    (Nat.mem_divisors.mp ha'.1).2⟩

/-- One effective term exhibits three prime factors; repetition only shrinks
this three-element finite set. -/
theorem liuBetaSupport_card_le_three (N z y n : ℕ) :
    (liuBetaSupport N z y n).card ≤ 3 := by
  classical
  by_cases h : (liuBetaSupport N z y n).Nonempty
  · obtain ⟨a₀, ha₀⟩ := h
    have ha₀' := Finset.mem_filter.mp ha₀
    obtain ⟨p₁, p₂, hp, heq⟩ := liuWeightSupport_iff.mp ha₀'.2.1
    let p₃ := n / a₀
    have hp₃ : p₃.Prime := ha₀'.2.2
    have hn : n = p₁ * p₂ * p₃ := by
      rw [← heq]
      exact (Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors ha₀'.1)).symm
    have hsub : n.primeFactors ⊆ {p₁, p₂, p₃} := by
      intro p hpMem
      obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hpMem
      rw [hn] at hpd
      rcases hpp.dvd_mul.mp hpd with hd | hd
      · rcases hpp.dvd_mul.mp hd with hd | hd
        · have := (Nat.prime_dvd_prime_iff_eq hpp hp.1).mp hd
          simp [this]
        · have := (Nat.prime_dvd_prime_iff_eq hpp hp.2.1).mp hd
          simp [this]
      · have := (Nat.prime_dvd_prime_iff_eq hpp hp₃).mp hd
        simp [this]
    calc
      (liuBetaSupport N z y n).card ≤ n.primeFactors.card :=
        Finset.card_le_card_of_injOn (fun a => n / a) (fun _ ha =>
          liuBetaSupport_complement_mem_primeFactors ha)
          (liuBetaSupport_complement_injective N z y n)
      _ ≤ ({p₁, p₂, p₃} : Finset ℕ).card := Finset.card_le_card hsub
      _ ≤ 3 := Finset.card_le_three
  · rw [Finset.not_nonempty_iff_eq_empty.mp h]
    simp

/-- Uniform, including n=0, and requiring no squarefreeness. -/
theorem liuBeta_le_three (N z y n : ℕ) : liuBeta N z y n ≤ 3 := by
  rw [liuBeta_eq_card]
  exact_mod_cast liuBetaSupport_card_le_three N z y n

end MathlibNt.SieveTheory.LiuWeight