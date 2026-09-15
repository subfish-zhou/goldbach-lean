import MathlibNt.Wu2008DoubleSieve.SignedSieveRemainder

/-!
# Finite canonical sieve inequalities on the actual Wu sequence

Frozen Rosser certificates are applied to the actual unscaled divisible
subsequence. The main sum, signed remainder, and ordinary AP error remain
separate. No analytic upper/lower sieve estimate is a hypothesis.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open MathlibNt.SieveTheory.LinearSieve

theorem ordinarySievePrimeProduct_squarefree (M : ℕ) (z : ℝ) :
    Squarefree (ordinarySievePrimeProduct M z) := by
  have hgen : ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) → Squarefree (∏ p ∈ s, p) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert p s hp ih =>
      intro hs
      rw [prod_insert hp, Nat.squarefree_mul_iff]
      have hpprime := hs p (mem_insert_self p s)
      refine ⟨Nat.coprime_prod_right_iff.mpr ?_, hpprime.prime.squarefree,
        ih (fun q hq => hs q (mem_insert_of_mem hq))⟩
      intro q hq
      exact (Nat.coprime_primes hpprime (hs q (mem_insert_of_mem hq))).mpr
        (by intro he; subst q; exact hp hq)
  exact hgen _ (fun _p hp => (mem_primeWindow.mp hp).1)

theorem sifted_iff_product_coprime (M n : ℕ) (z : ℝ) :
    Sifted M n z ↔ (ordinarySievePrimeProduct M z).Coprime n := by
  rw [ordinarySievePrimeProduct, Nat.coprime_prod_left_iff]
  constructor
  · intro hs q hq
    obtain ⟨hp, hc, _, hz⟩ := mem_primeWindow.mp hq
    exact hp.coprime_iff_not_dvd.mpr (hs q hp hc hz)
  · intro hs q hp hc hz
    exact hp.coprime_iff_not_dvd.mp
      (hs q (mem_primeWindow.mpr ⟨hp, hc, Nat.cast_nonneg _, hz⟩))

theorem sourceSieveCount_eq_gcd_indicator (N d M : ℕ) (z : ℝ) :
    (sourceSieveCount N d M z : ℝ) =
      ∑ p ∈ goldbachDivisible N d,
        if Nat.gcd (ordinarySievePrimeProduct M z) (N - p) = 1 then 1 else 0 := by
  rw [sum_boole]
  have hc :
      sourceSieveCarrier N d M z =
        (goldbachDivisible N d).filter
          (fun p => Nat.gcd (ordinarySievePrimeProduct M z) (N - p) = 1) := by
    ext p
    simp only [sourceSieveCarrier, goldbachDivisible, mem_filter,
      sifted_iff_product_coprime, Nat.coprime_iff_gcd_eq_one]
    tauto
  simp only [sourceSieveCount, hc, Int.cast_natCast]

theorem source_weighted_count_eq_gcd_sum (N d P : ℕ) (hP : P ≠ 0)
    (coeff : ℕ → ℝ) :
    (∑ q ∈ P.divisors, coeff q * (sourceSequenceCount N d q : ℝ)) =
      ∑ p ∈ goldbachDivisible N d, ∑ q ∈ (Nat.gcd P (N - p)).divisors, coeff q := by
  unfold sourceSequenceCount
  simp_rw [← sum_boole, mul_sum, mul_ite, mul_one, mul_zero]
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  rw [← sum_filter]
  have hf :
      P.divisors.filter (fun q => q ∣ N - p) = (Nat.gcd P (N - p)).divisors := by
    rw [← Nat.divisors_filter_dvd_of_dvd hP (Nat.gcd_dvd_left P (N - p))]
    ext q
    simp only [mem_filter, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨hq, hn⟩
      exact ⟨hq, (Nat.mem_divisors.mp hq).1, hn⟩
    · tauto
  rw [hf]

noncomputable def ordinaryRosserMainSum (upper : Bool) (N d D : ℕ) (z : ℝ) : ℝ :=
  ∑ q ∈ (ordinarySievePrimeProduct (d * N) z).divisors,
    ordinaryRosserWeight upper N d D z q / (Nat.totient q : ℝ)

/-- The true-li density and the signed error are an exact identity, including
the natural zero conventions. -/
theorem ordinaryRosser_density_identity (upper : Bool) (N d D : ℕ) (z : ℝ) :
    (∑ q ∈ (ordinarySievePrimeProduct (d * N) z).divisors,
      ordinaryRosserWeight upper N d D z q * (sourceSequenceCount N d q : ℝ)) =
      (logarithmicIntegral N / (Nat.totient d : ℝ)) *
        ordinaryRosserMainSum upper N d D z +
          ordinaryRosserRemainder upper N d D z := by
  unfold ordinaryRosserMainSum ordinaryRosserRemainder
  rw [mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro q hq
  have hc : d.Coprime q :=
    ((ordinarySievePrimeProduct_coprime (d * N) z).of_dvd_left
      (Nat.mem_divisors.mp hq).1 |>.of_dvd_right (dvd_mul_right d N)).symm
  unfold sourceSequenceRemainder
  rw [Nat.totient_mul hc, Nat.cast_mul, ← div_div]
  ring

theorem ordinaryRosser_upper_finite {N d D : ℕ} {z : ℝ}
    (hD : 1 < D) (hz : z ≤ (D : ℝ)) :
    (sourceSieveCount N d (d * N) z : ℝ) ≤
      (logarithmicIntegral N / (Nat.totient d : ℝ)) *
        ordinaryRosserMainSum true N d D z +
          ordinaryRosserRemainder true N d D z := by
  rw [← ordinaryRosser_density_identity, sourceSieveCount_eq_gcd_indicator,
    source_weighted_count_eq_gcd_sum N d _ (ordinarySievePrimeProduct_pos _ _).ne']
  have hprime : ∀ p ∈ (ordinarySievePrimeProduct (d * N) z).primeFactors, p < D := by
    intro p hp
    rw [ordinarySievePrimeProduct, Nat.primeFactors_prod
      (fun _q hq => (mem_primeWindow.mp hq).1)] at hp
    exact_mod_cast (mem_primeWindow.mp hp).2.2.2.trans_le hz
  have hcert := upperRosserWeight_certificate (ordinarySievePrimeProduct_squarefree _ _)
    (ordinarySievePrimeProduct_pos _ _).ne' hD hprime
  apply sum_le_sum
  intro p _
  exact upperRosserWeight_divisor_sum hcert (Nat.gcd_dvd_left _ _)

theorem ordinaryRosser_lower_finite {N d D : ℕ} {z : ℝ}
    (hz : z ≤ (D : ℝ)) :
    (logarithmicIntegral N / (Nat.totient d : ℝ)) *
        ordinaryRosserMainSum false N d D z +
          ordinaryRosserRemainder false N d D z ≤
      (sourceSieveCount N d (d * N) z : ℝ) := by
  rw [← ordinaryRosser_density_identity, sourceSieveCount_eq_gcd_indicator,
    source_weighted_count_eq_gcd_sum N d _ (ordinarySievePrimeProduct_pos _ _).ne']
  have hprime : ∀ p ∈ (ordinarySievePrimeProduct (d * N) z).primeFactors, p < D := by
    intro p hp
    rw [ordinarySievePrimeProduct, Nat.primeFactors_prod
      (fun _q hq => (mem_primeWindow.mp hq).1)] at hp
    exact_mod_cast (mem_primeWindow.mp hp).2.2.2.trans_le hz
  have hcert := lowerRosserWeight_certificate (ordinarySievePrimeProduct_squarefree _ _)
    (ordinarySievePrimeProduct_pos _ _).ne' hprime
  apply sum_le_sum
  intro p _
  exact lowerRosserWeight_divisor_sum hcert (Nat.gcd_dvd_left _ _)

noncomputable def convolutionSieveCount {i : ℕ} (N : ℕ)
    (W : Fin i → Finset ℕ) (z : ℕ → ℝ) : ℝ :=
  ∑ d ∈ (Fintype.piFinset W).image (fun t => ∏ j, t j),
    (convolutionCoeff W d : ℝ) * (sourceSieveCount N d (d * N) (z d) : ℝ)

noncomputable def convolutionRosserMain {i : ℕ} (N : ℕ)
    (W : Fin i → Finset ℕ) (upper : Bool) (D : ℕ → ℕ) (z : ℕ → ℝ) : ℝ :=
  ∑ d ∈ (Fintype.piFinset W).image (fun t => ∏ j, t j),
    (convolutionCoeff W d : ℝ) *
      ((logarithmicIntegral N / (Nat.totient d : ℝ)) *
        ordinaryRosserMainSum upper N d (D d) (z d))

theorem convolution_upper_sieve_with_AP_error {i N Q : ℕ}
    (W : Fin i → Finset ℕ) (D : ℕ → ℕ) (z : ℕ → ℝ)
    (hD : ∀ d ∈ (Fintype.piFinset W).image (fun t => ∏ j, t j),
      1 < D d ∧ z d ≤ (D d : ℝ) ∧ D d ≤ Q / d + 1) :
    convolutionSieveCount N W z ≤
      convolutionRosserMain N W true D z + convolutionAPError N Q W := by
  have h :
      convolutionSieveCount N W z ≤ convolutionRosserMain N W true D z +
        convolutionRosserRemainder N W true D z := by
    unfold convolutionSieveCount convolutionRosserMain convolutionRosserRemainder
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro d hd
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left
      (ordinaryRosser_upper_finite (N := N) (d := d) (hD d hd).1 (hD d hd).2.1)
      (Nat.cast_nonneg _)
  have he := convolutionRosserRemainder_le_AP (N := N) W true D z
    (fun d hd => (hD d hd).2.2)
  have hr := le_abs_self (convolutionRosserRemainder N W true D z)
  linarith

theorem convolution_lower_sieve_with_AP_error {i N Q : ℕ}
    (W : Fin i → Finset ℕ) (D : ℕ → ℕ) (z : ℕ → ℝ)
    (hD : ∀ d ∈ (Fintype.piFinset W).image (fun t => ∏ j, t j),
      z d ≤ (D d : ℝ) ∧ D d ≤ Q / d + 1) :
    convolutionRosserMain N W false D z - convolutionAPError N Q W ≤
      convolutionSieveCount N W z := by
  have h :
      convolutionRosserMain N W false D z + convolutionRosserRemainder N W false D z ≤
        convolutionSieveCount N W z := by
    unfold convolutionSieveCount convolutionRosserMain convolutionRosserRemainder
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro d hd
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left
      (ordinaryRosser_lower_finite (N := N) (d := d) (hD d hd).1) (Nat.cast_nonneg _)
  have he := convolutionRosserRemainder_le_AP (N := N) W false D z
    (fun d hd => (hD d hd).2)
  have hn := neg_abs_le (convolutionRosserRemainder N W false D z)
  linarith

end Wu2008DoubleSieve
