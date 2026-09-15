import MathlibNt.Wu2008DoubleSieve.NinthUpperSieveDefinitions

/-!
# Physical mass and exact ninth AP remainder identities

The noncoprime AP contribution is zero on moduli coprime to N.
Its missing main mass is retained with the negative sign in the remainder.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical
open AnalyticNumberTheory.Sieve
open MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.LinearSieve

theorem P9_AP_eq_divisible {N m : ℕ} (hm : m ∈ ninthProductSupport N) (q : ℕ) :
    (P9 N m).filter (fun c => Nat.ModEq q (m * c) N) =
      (P9 N m).filter (fun c => q ∣ N - m * c) := by
  apply filter_congr
  intro c hc
  exact Nat.modEq_iff_dvd' (P9_size hm hc).le

theorem P9_AP_empty_of_not_coprime {N m q : ℕ}
    (hm : m ∈ ninthProductSupport N) (hq : q.Coprime N) (hmq : ¬m.Coprime q) :
    (P9 N m).filter (fun c => Nat.ModEq q (m * c) N) = ∅ := by
  rw [P9_AP_eq_divisible hm q]
  apply eq_empty_iff_forall_notMem.mpr
  intro c hc
  obtain ⟨hc, hd⟩ := mem_filter.mp hc
  have hgN : Nat.gcd m q ∣ N := by
    have hsub := (Nat.gcd_dvd_right m q).trans hd
    have hmul := (Nat.gcd_dvd_left m q).trans (dvd_mul_right m c)
    simpa only [Nat.sub_add_cancel (P9_size hm hc).le] using dvd_add hsub hmul
  have hg1 := Nat.dvd_gcd (Nat.gcd_dvd_right m q) hgN
  rw [hq.gcd_eq_one] at hg1
  exact hmq (Nat.coprime_iff_gcd_eq_one.mpr (Nat.dvd_one.mp hg1))

theorem ninthSieve_remainder_identity {N q : ℕ} (hq : q.Coprime N) :
    ninthSieveDivisibleCount N q - X9 N / (Nat.totient q : ℝ) =
      ninthSieveAPResidual N q - ninthSieveMissingMass N q / (Nat.totient q : ℝ) := by
  unfold ninthSieveDivisibleCount X9 ninthSieveAPResidual ninthSieveMissingMass
  simp only [sum_filter, sum_div, ← sum_sub_distrib]
  apply sum_congr rfl
  intro m hm
  rw [← P9_AP_eq_divisible hm q]
  by_cases hmq : m.Coprime q
  · simp only [if_pos hmq, if_neg (not_not.mpr hmq), zero_div, sub_zero]
    rfl
  · rw [P9_AP_empty_of_not_coprime hm hq hmq]
    simp [hmq]

/-- Testing the physical output weights retains every product/prime label,
even when several labels produce the same output. -/
theorem B9_test (N : ℕ) (f : ℕ → ℝ) :
    (∑ b ∈ range (N + 1), B9 N b * f b) =
      ∑ m ∈ ninthProductSupport N, ∑ c ∈ P9 N m, f (N - m * c) := by
  unfold B9
  simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro m _
  rw [sum_comm]
  apply sum_congr rfl
  intro c _
  have hb : N - m * c ∈ range (N + 1) :=
    mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le _ _))
  rw [sum_eq_single (N - m * c)]
  · simp
  · intro b _ hne
    simp [Ne.symm hne]
  · exact fun hn => (hn hb).elim

theorem ninthBoundingSieve_mass (N : ℕ) (he : Even N) (Z : ℝ) :
    (∑ b ∈ (ninthBoundingSieve N he Z).support,
      (ninthBoundingSieve N he Z).weights b) = X9 N := by
  simpa only [ninthBoundingSieve, X9, mul_one, sum_const, nsmul_eq_mul] using
    B9_test N (fun _ => 1)

theorem ninthBoundingSieve_multSum (N : ℕ) (he : Even N) (Z : ℝ) (q : ℕ) :
    (ninthBoundingSieve N he Z).multSum q = ninthSieveDivisibleCount N q := by
  have h := B9_test N (fun b => if q ∣ b then 1 else 0)
  simpa only [BoundingSieve.multSum, ninthBoundingSieve, ninthSieveDivisibleCount,
    card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    mul_ite, mul_one, mul_zero] using h

theorem ninthBoundingSieve_siftedSum (N : ℕ) (he : Even N) (Z : ℝ) :
    (ninthBoundingSieve N he Z).siftedSum = ninthSiftedCount N Z := by
  have h := B9_test N (fun b => if (ordinarySievePrimeProduct N Z).Coprime b then 1 else 0)
  simp only [BoundingSieve.siftedSum, ninthBoundingSieve, ninthSiftedCount,
    sifted_iff_product_coprime, card_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]
  convert h using 1
  apply sum_congr rfl
  intro b _
  by_cases hb : (ordinarySievePrimeProduct N Z).Coprime b
  · simp only [if_pos hb, mul_one]
    exact if_pos hb
  · simp only [if_neg hb, mul_zero]
    exact if_neg hb

theorem ninthBoundingSieve_nu {N q : ℕ} (he : Even N) (Z : ℝ)
    (hq : q ∣ ordinarySievePrimeProduct N Z) :
    (ninthBoundingSieve N he Z).nu q = 1 / (Nat.totient q : ℝ) :=
  goldbachNu_squarefree_eq_inv_totient
    ((ordinarySievePrimeProduct_squarefree N Z).squarefree_of_dvd hq)

theorem ninthBoundingSieve_rem {N q : ℕ} (he : Even N) (Z : ℝ)
    (hq : q ∣ ordinarySievePrimeProduct N Z) :
    (ninthBoundingSieve N he Z).rem q =
      ninthSieveAPResidual N q - ninthSieveMissingMass N q / (Nat.totient q : ℝ) := by
  rw [BoundingSieve.rem, ninthBoundingSieve_multSum, ninthBoundingSieve_nu he Z hq]
  change ninthSieveDivisibleCount N q - (1 / (Nat.totient q : ℝ)) * X9 N = _
  rw [one_div_mul_eq_div]
  exact ninthSieve_remainder_identity ((ordinarySievePrimeProduct_coprime N Z).of_dvd_left hq)

theorem ninthBoundingSieve_mainSum (N D : ℕ) (he : Even N) (Z : ℝ) :
    (ninthBoundingSieve N he Z).mainSum
      (upperRosserWeight (ordinarySievePrimeProduct N Z) D) =
        ordinaryRosserMainSum true N 1 D Z := by
  unfold BoundingSieve.mainSum ordinaryRosserMainSum
  simp only [ninthBoundingSieve, one_mul]
  apply sum_congr rfl
  intro q hq
  rw [goldbachNu_squarefree_eq_inv_totient
    ((ordinarySievePrimeProduct_squarefree N Z).squarefree_of_dvd (Nat.mem_divisors.mp hq).1)]
  simp only [ordinaryRosserWeight, if_true, one_mul, div_eq_mul_inv]

end Wu2008DoubleSieve
