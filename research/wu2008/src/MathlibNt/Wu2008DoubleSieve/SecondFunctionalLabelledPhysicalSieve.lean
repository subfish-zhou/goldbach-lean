import MathlibNt.Wu2008DoubleSieve.Omega3SieveUpper
import MathlibNt.Wu2008DoubleSieve.Omega3R1Distribution

/-! A physical prime-fibre sieve with arbitrary finite labels and original real weights. -/
namespace Wu2008DoubleSieve.LabelledPhysical
open Finset
open scoped Classical
open AnalyticNumberTheory.Sieve
open MathlibNt.SieveTheory.SwitchingPrinciple MathlibNt.SieveTheory.LinearSieve

variable {α : Type*}

/-- Only local geometry and nonnegativity; no analytic or sieve bound is assumed. -/
structure Family (α : Type*) (N : ℕ) where
  labels : Finset α
  weight : α → ℝ
  cofactor : α → ℕ
  lower : α → ℝ
  upper : α → ℝ
  weight_nonneg : ∀ c ∈ labels, 0 ≤ weight c
  geometry : ∀ c ∈ labels, 0 < cofactor c ∧ 2 ≤ lower c ∧
    lower c ≤ upper c ∧ (cofactor c : ℝ) * upper c ≤ N

namespace Family
variable {N : ℕ} (L : Family α N)
noncomputable def primes (c : α) : Finset ℕ :=
  omega3ProfilePrimes N (L.lower c) (L.upper c)
noncomputable def mass : ℝ := ∑ c ∈ L.labels, L.weight c * (L.primes c).card
noncomputable def sifted (Z : ℝ) : ℝ := ∑ c ∈ L.labels, L.weight c *
  (((L.primes c).filter (fun p => Sifted N (N - L.cofactor c * p) Z)).card : ℝ)
noncomputable def weightAt (b : ℕ) : ℝ := ∑ c ∈ L.labels, L.weight c *
  (((L.primes c).filter (fun p => N - L.cofactor c * p = b)).card : ℝ)
noncomputable def apCount (c : α) (q : ℕ) : ℕ :=
  ((L.primes c).filter (fun p => Nat.ModEq q (L.cofactor c * p) N)).card
noncomputable def reduced (q : ℕ) : ℝ :=
  ∑ c ∈ L.labels.filter (fun c => (L.cofactor c).Coprime q),
    L.weight c * omega3ProfileError N q (L.cofactor c) (L.lower c) (L.upper c)
noncomputable def missing (q : ℕ) : ℝ :=
  ∑ c ∈ L.labels.filter (fun c => ¬(L.cofactor c).Coprime q),
    L.weight c * (L.primes c).card
noncomputable def R1 (D : ℕ) (Z : ℝ) : ℝ :=
  ∑ q ∈ omega3SieveModuli N D Z, (3 : ℝ) ^ q.primeFactors.card * |L.reduced q|
noncomputable def R2 (D : ℕ) (Z : ℝ) : ℝ :=
  ∑ q ∈ omega3SieveModuli N D Z,
    ((3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ)) * L.missing q

noncomputable def sieve (he : Even N) (Z : ℝ) : BoundingSieve where
  support := range (N + 1)
  prodPrimes := ordinarySievePrimeProduct N Z
  prodPrimes_squarefree := ordinarySievePrimeProduct_squarefree _ _
  weights := L.weightAt
  weights_nonneg := fun _ => sum_nonneg fun c hc =>
    mul_nonneg (L.weight_nonneg c hc) (Nat.cast_nonneg _)
  totalMass := L.mass
  nu := goldbachNu
  nu_mult := goldbachNu_isMultiplicative
  nu_pos_of_prime := fun _ hp _ => goldbachNu_pos_of_prime hp
  nu_lt_one_of_prime := fun _ hp hd => goldbachNu_lt_one_of_prime hp
    (ordinarySievePrimeProduct_prime_gt_two he Z hp hd)

theorem output_test (f : ℕ → ℝ) :
    (∑ b ∈ range (N + 1), L.weightAt b * f b) =
      ∑ c ∈ L.labels, L.weight c * ∑ p ∈ L.primes c, f (N - L.cofactor c * p) := by
  unfold weightAt
  simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    mul_sum, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro c _
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  have hb : N - L.cofactor c * p ∈ range (N + 1) :=
    mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le _ _))
  rw [sum_eq_single (N - L.cofactor c * p)]
  · simp
  · intro b _ hn
    simp [Ne.symm hn]
  · exact fun hn => (hn hb).elim

theorem total_mass (he : Even N) (Z : ℝ) :
    (∑ b ∈ (L.sieve he Z).support, (L.sieve he Z).weights b) =
      (L.sieve he Z).totalMass := by
  simpa [sieve, mass] using L.output_test (fun _ => 1)

theorem output_le {c : α} (hc : c ∈ L.labels) {p : ℕ} (hp : p ∈ L.primes c) :
    L.cofactor c * p ≤ N := by
  have hupper := (mem_filter.mp hp).2.2.2
  exact_mod_cast (mul_le_mul_of_nonneg_left hupper
    (Nat.cast_nonneg (L.cofactor c))).trans (L.geometry c hc).2.2.2

theorem apCount_eq_divisible {c : α} (hc : c ∈ L.labels) (q : ℕ) :
    L.apCount c q = ((L.primes c).filter (fun p => q ∣ N - L.cofactor c * p)).card := by
  apply congrArg Finset.card
  exact filter_congr fun p hp => Nat.modEq_iff_dvd' (L.output_le hc hp)

theorem apCount_zero {c : α} (hc : c ∈ L.labels) {q : ℕ}
    (hq : q.Coprime N) (hbad : ¬(L.cofactor c).Coprime q) : L.apCount c q = 0 := by
  rw [L.apCount_eq_divisible hc]
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨hp, hdiv⟩ := mem_filter.mp hp
  have hgN : (L.cofactor c).gcd q ∣ N := by
    have hsub := (Nat.gcd_dvd_right (L.cofactor c) q).trans hdiv
    have hmul := (Nat.gcd_dvd_left (L.cofactor c) q).trans (dvd_mul_right (L.cofactor c) p)
    simpa only [Nat.sub_add_cancel (L.output_le hc hp)] using dvd_add hsub hmul
  have hg1 := Nat.dvd_gcd (Nat.gcd_dvd_right (L.cofactor c) q) hgN
  rw [hq.gcd_eq_one] at hg1
  exact hbad (Nat.coprime_iff_gcd_eq_one.mpr (Nat.dvd_one.mp hg1))

theorem sieve_sifted (he : Even N) (Z : ℝ) :
    (L.sieve he Z).siftedSum = L.sifted Z := by
  have h := L.output_test (fun b => if (ordinarySievePrimeProduct N Z).Coprime b then 1 else 0)
  simp only [BoundingSieve.siftedSum, sieve, sifted, sifted_iff_product_coprime,
    card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  convert h using 1
  apply sum_congr rfl
  intro b _
  by_cases hb : (ordinarySievePrimeProduct N Z).Coprime b
  · simp only [if_pos hb, mul_one]
    exact if_pos hb
  · simp only [if_neg hb, mul_zero]
    exact if_neg hb

theorem sieve_multSum (he : Even N) (Z : ℝ) (q : ℕ) :
    (L.sieve he Z).multSum q = ∑ c ∈ L.labels, L.weight c * (L.apCount c q : ℝ) := by
  have h := L.output_test (fun b => if q ∣ b then 1 else 0)
  simp only [BoundingSieve.multSum, sieve, mul_ite, mul_one, mul_zero] at h ⊢
  rw [h]
  apply sum_congr rfl
  intro c hc
  rw [L.apCount_eq_divisible hc]
  simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem sieve_remainder (he : Even N) (Z : ℝ) {q : ℕ}
    (hq : q ∣ ordinarySievePrimeProduct N Z) :
    (L.sieve he Z).rem q = L.reduced q - L.missing q / (Nat.totient q : ℝ) := by
  rw [BoundingSieve.rem, L.sieve_multSum]
  have hnu : (L.sieve he Z).nu q = 1 / (Nat.totient q : ℝ) :=
    goldbachNu_squarefree_eq_inv_totient
      ((ordinarySievePrimeProduct_squarefree N Z).squarefree_of_dvd hq)
  rw [hnu]
  change _ - (1 / (Nat.totient q : ℝ)) * L.mass = _
  rw [one_div_mul_eq_div]
  unfold mass reduced missing omega3ProfileError
  change _ - _ = (∑ c ∈ L.labels.filter (fun c => (L.cofactor c).Coprime q),
    L.weight c * ((L.apCount c q : ℝ) - (L.primes c).card / (Nat.totient q : ℝ))) - _
  simp only [sum_filter, sum_div, ← sum_sub_distrib]
  apply sum_congr rfl
  intro c hc
  by_cases hg : (L.cofactor c).Coprime q
  · simp only [if_pos hg, if_neg (not_not.mpr hg), zero_div, sub_zero]
    ring
  · rw [L.apCount_zero hc ((ordinarySievePrimeProduct_coprime N Z).of_dvd_left hq) hg]
    simp [hg]

theorem sieve_main (he : Even N) (D : ℕ) (Z : ℝ) :
    (L.sieve he Z).mainSum (upperRosserWeight (ordinarySievePrimeProduct N Z) D) =
      ordinaryRosserMainSum true N 1 D Z := by
  unfold BoundingSieve.mainSum ordinaryRosserMainSum
  simp only [sieve, one_mul]
  apply sum_congr rfl
  intro q hq
  rw [goldbachNu_squarefree_eq_inv_totient
    ((ordinarySievePrimeProduct_squarefree N Z).squarefree_of_dvd (Nat.mem_divisors.mp hq).1)]
  simp only [ordinaryRosserWeight, if_true, one_mul, div_eq_mul_inv]

theorem missing_nonneg (q : ℕ) : 0 ≤ L.missing q :=
  sum_nonneg fun c hc => mul_nonneg (L.weight_nonneg c (mem_filter.mp hc).1) (Nat.cast_nonneg _)

/-- The genuine finite Rosser certificate is constructed and consumed here. -/
theorem upper_finite (he : Even N) (D : ℕ) (Z : ℝ) (hD : 1 < D) (hZ : Z ≤ (D : ℝ)) :
    L.sifted Z ≤ L.mass * ordinaryRosserMainSum true N 1 D Z + L.R1 D Z + L.R2 D Z := by
  have herr : upperErrSum (L.sieve he Z) D
      (upperRosserWeight (ordinarySievePrimeProduct N Z) D) ≤ L.R1 D Z + L.R2 D Z := by
    unfold upperErrSum R1 R2
    change (∑ q ∈ omega3SieveModuli N D Z, _) ≤ _
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro q hq
    rw [L.sieve_remainder he Z (Nat.mem_divisors.mp (mem_filter.mp hq).1).1]
    have hn : 0 ≤ L.missing q / (Nat.totient q : ℝ) :=
      div_nonneg (L.missing_nonneg q) (Nat.cast_nonneg _)
    have ha : |L.reduced q - L.missing q / (Nat.totient q : ℝ)| ≤
        |L.reduced q| + L.missing q / (Nat.totient q : ℝ) := by
      simpa only [abs_of_nonneg hn] using abs_sub (L.reduced q) (L.missing q / (Nat.totient q : ℝ))
    have hw : |upperRosserWeight (ordinarySievePrimeProduct N Z) D q| ≤
        (3 : ℝ) ^ q.primeFactors.card :=
      (abs_upperRosserWeight_le_one _ _ _).trans (one_le_pow₀ (by norm_num))
    exact (mul_le_mul hw ha (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hprime : ∀ p ∈ (ordinarySievePrimeProduct N Z).primeFactors, p < D := by
    rw [ordinarySievePrimeProduct_primeFactors]
    intro p hp
    exact_mod_cast (mem_primeWindow.mp hp).2.2.2.trans_le hZ
  have hc := upperRosserWeight_certificate (ordinarySievePrimeProduct_squarefree N Z)
    (ordinarySievePrimeProduct_pos N Z).ne' hD hprime
  have hf := siftedSum_le_mainSum_add_upperErrSum_upperRosser (S := L.sieve he Z) D hc
  rw [L.sieve_sifted] at hf
  change L.sifted Z ≤ L.mass * (L.sieve he Z).mainSum
    (upperRosserWeight (ordinarySievePrimeProduct N Z) D) +
    upperErrSum (L.sieve he Z) D (upperRosserWeight (ordinarySievePrimeProduct N Z) D) at hf
  rw [L.sieve_main] at hf
  linarith

noncomputable def primeMass : ℝ := ∑ c ∈ L.labels, L.weight c *
  (((L.primes c).filter (fun p => (N - L.cofactor c * p).Prime)).card : ℝ)
noncomputable def small (Z : ℝ) : ℝ := ∑ c ∈ L.labels, L.weight c *
  (((L.primes c).filter (fun p => (N - L.cofactor c * p).Prime ∧
    ((N - L.cofactor c * p : ℕ) : ℝ) < Z)).card : ℝ)

/-- Prime outputs at or above the threshold survive every sieving prime. -/
theorem prime_sifted_or_small (n : ℕ) (Z : ℝ) (hn : n.Prime) :
    Sifted N n Z ∨ (n : ℝ) < Z := by
  by_cases hz : (n : ℝ) < Z
  · exact Or.inr hz
  · left
    intro p hp _ hpZ hdiv
    have hpn : p = n := (Nat.dvd_prime hn).mp hdiv |>.resolve_left hp.ne_one
    subst p
    exact hz hpZ

theorem prime_le_sifted_add_small (Z : ℝ) : L.primeMass ≤ L.sifted Z + L.small Z := by
  unfold primeMass sifted small
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro c hc
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (L.weight_nonneg c hc)
  simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro p _
  by_cases hn : (N - L.cofactor c * p).Prime
  · have h := prime_sifted_or_small (N := N) (N - L.cofactor c * p) Z hn
    by_cases hs : Sifted N (N - L.cofactor c * p) Z <;>
      by_cases hz : ((N - L.cofactor c * p : ℕ) : ℝ) < Z <;> simp_all
    positivity
  · simp [hn]
    positivity

/-- The actual original-weight prime output endpoint; Small is retained literally. -/
theorem prime_upper_finite (he : Even N) (D : ℕ) (Z : ℝ) (hD : 1 < D) (hZ : Z ≤ (D : ℝ)) :
    L.primeMass ≤ L.mass * ordinaryRosserMainSum true N 1 D Z + L.R1 D Z + L.R2 D Z + L.small Z := by
  have hprime := L.prime_le_sifted_add_small Z
  have hsieve := L.upper_finite he D Z hD hZ
  linarith

end Family
end Wu2008DoubleSieve.LabelledPhysical
