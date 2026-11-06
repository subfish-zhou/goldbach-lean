import MathlibNt.Wu2008DoubleSieve.Omega3SieveDefinitions

/-!
# Exact weighted count and AP remainder identities

Natural subtraction is only converted to a congruence using the literal
ep <= N fibre constraint. Output zero remains in the support.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical
open AnalyticNumberTheory.Sieve
open MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.LinearSieve

theorem omega3SieveAPCount_eq_divisible (N : ℕ) (δ s : ℝ)
    (c : Omega3CofactorIndex) (q : ℕ) :
    omega3SieveAPCount N δ s c q =
      ((omega3CofactorPrimeFibreLE N δ s c).filter
        (fun p => q ∣ N - omega3CofactorValue c * p)).card := by
  unfold omega3SieveAPCount
  congr 1
  apply filter_congr
  intro p hp
  exact Nat.modEq_iff_dvd' (mem_filter.mp hp).2.2.2.2

theorem omega3SieveAPCount_eq_zero_of_not_coprime {N q : ℕ} {δ s : ℝ}
    {c : Omega3CofactorIndex} (hq : q.Coprime N)
    (hc : ¬ (omega3CofactorValue c).Coprime q) :
    omega3SieveAPCount N δ s c q = 0 := by
  rw [omega3SieveAPCount_eq_divisible]
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨hp, hdiv⟩ := mem_filter.mp hp
  have hsize := (mem_filter.mp hp).2.2.2.2
  have hgN : Nat.gcd (omega3CofactorValue c) q ∣ N := by
    have hsub := (Nat.gcd_dvd_right (omega3CofactorValue c) q).trans hdiv
    have hmul := (Nat.gcd_dvd_left (omega3CofactorValue c) q).trans
      (dvd_mul_right (omega3CofactorValue c) p)
    simpa only [Nat.sub_add_cancel hsize] using dvd_add hsub hmul
  have hg1 := Nat.dvd_gcd (Nat.gcd_dvd_right (omega3CofactorValue c) q) hgN
  rw [hq.gcd_eq_one] at hg1
  exact hc (Nat.coprime_iff_gcd_eq_one.mpr (Nat.dvd_one.mp hg1))

/-- There is one absolute value only after this whole labelled residual
has been formed. The non-coprime main mass has the negative sign. -/
theorem omega3Sieve_density_remainder_identity {i N q : ℕ} (δ s t : ℝ)
    (W : Fin i → Finset ℕ) (hq : q.Coprime N) :
    omega3SieveDivisibleCount N δ s t W q -
        omega3SieveX N δ s t W / (Nat.totient q : ℝ) =
      omega3SieveAPResidual N δ s t W q -
        omega3SieveMissingMass N δ s t W q / (Nat.totient q : ℝ) := by
  unfold omega3SieveDivisibleCount omega3SieveX
    omega3SieveAPResidual omega3SieveMissingMass
  simp only [sum_filter, sum_div, ← sum_sub_distrib]
  apply sum_congr rfl
  intro c _
  rw [← omega3SieveAPCount_eq_divisible]
  by_cases hc : (omega3CofactorValue c).Coprime q
  · simp only [if_pos hc, if_neg (not_not.mpr hc), zero_div, sub_zero]
    ring
  · rw [omega3SieveAPCount_eq_zero_of_not_coprime hq hc]
    simp [hc]

theorem omega3SieveOutputWeight_test {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) (f : ℕ → ℝ) :
    (∑ b ∈ range (N + 1), omega3SieveOutputWeight N δ s t W b * f b) =
      ∑ c ∈ omega3CofactorLabels N δ s t W, (convolutionCoeff W c.1 : ℝ) *
        ∑ p ∈ omega3CofactorPrimeFibreLE N δ s c,
          f (N - omega3CofactorValue c * p) := by
  unfold omega3SieveOutputWeight
  simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    mul_sum, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro c _
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  have hb : N - omega3CofactorValue c * p ∈ range (N + 1) :=
    mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le _ _))
  rw [sum_eq_single (N - omega3CofactorValue c * p)]
  · simp
  · intro b _ hne
    simp [Ne.symm hne]
  · exact fun hn => (hn hb).elim


theorem omega3GoldbachBoundingSieve_multSum {i : ℕ} (N : ℕ) (he : Even N)
    (δ s t Z : ℝ) (W : Fin i → Finset ℕ) (q : ℕ) :
    (omega3GoldbachBoundingSieve N he δ s t Z W).multSum q =
      omega3SieveDivisibleCount N δ s t W q := by
  have h := omega3SieveOutputWeight_test N δ s t W
    (fun b => if q ∣ b then 1 else 0)
  simpa only [BoundingSieve.multSum, omega3GoldbachBoundingSieve,
    omega3SieveDivisibleCount, card_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero, mul_ite, mul_one, mul_zero] using h

theorem omega3GoldbachBoundingSieve_siftedSum {i : ℕ} (N : ℕ) (he : Even N)
    (δ s t Z : ℝ) (W : Fin i → Finset ℕ) :
    (omega3GoldbachBoundingSieve N he δ s t Z W).siftedSum =
      omega3SwitchedSiftedCountLE N δ s t Z W := by
  have h := omega3SieveOutputWeight_test N δ s t W
    (fun b => if (ordinarySievePrimeProduct N Z).Coprime b then 1 else 0)
  simp only [BoundingSieve.siftedSum, omega3GoldbachBoundingSieve,
    omega3SwitchedSiftedCountLE, sifted_iff_product_coprime,
    card_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]
  convert h using 1
  · apply sum_congr rfl
    intro b _
    by_cases hb : (ordinarySievePrimeProduct N Z).Coprime b
    · simp only [if_pos hb, mul_one]
      exact if_pos hb
    · simp only [if_neg hb, mul_zero]
      exact if_neg hb

theorem omega3GoldbachBoundingSieve_nu {i N q : ℕ} (he : Even N)
    (δ s t Z : ℝ) (W : Fin i → Finset ℕ)
    (hq : q ∣ ordinarySievePrimeProduct N Z) :
    (omega3GoldbachBoundingSieve N he δ s t Z W).nu q =
      1 / (Nat.totient q : ℝ) :=
  goldbachNu_squarefree_eq_inv_totient
    ((ordinarySievePrimeProduct_squarefree N Z).squarefree_of_dvd hq)


theorem omega3GoldbachBoundingSieve_rem {i N q : ℕ} (he : Even N)
    (δ s t Z : ℝ) (W : Fin i → Finset ℕ)
    (hq : q ∣ ordinarySievePrimeProduct N Z) :
    (omega3GoldbachBoundingSieve N he δ s t Z W).rem q =
      omega3SieveAPResidual N δ s t W q -
        omega3SieveMissingMass N δ s t W q / (Nat.totient q : ℝ) := by
  rw [BoundingSieve.rem, omega3GoldbachBoundingSieve_multSum,
    omega3GoldbachBoundingSieve_nu he δ s t Z W hq]
  change omega3SieveDivisibleCount N δ s t W q -
    (1 / (Nat.totient q : ℝ)) * omega3SieveX N δ s t W = _
  rw [one_div_mul_eq_div]
  exact omega3Sieve_density_remainder_identity δ s t W
    ((ordinarySievePrimeProduct_coprime N Z).of_dvd_left hq)

theorem omega3GoldbachBoundingSieve_mainSum {i : ℕ} (N D : ℕ) (he : Even N)
    (δ s t Z : ℝ) (W : Fin i → Finset ℕ) :
    (omega3GoldbachBoundingSieve N he δ s t Z W).mainSum
      (upperRosserWeight (ordinarySievePrimeProduct N Z) D) =
        ordinaryRosserMainSum true N 1 D Z := by
  unfold BoundingSieve.mainSum ordinaryRosserMainSum
  simp only [omega3GoldbachBoundingSieve, one_mul]
  apply sum_congr rfl
  intro q hq
  rw [goldbachNu_squarefree_eq_inv_totient
    ((ordinarySievePrimeProduct_squarefree N Z).squarefree_of_dvd
      (Nat.mem_divisors.mp hq).1)]
  simp only [ordinaryRosserWeight, if_true, one_mul, div_eq_mul_inv]





end Wu2008DoubleSieve
