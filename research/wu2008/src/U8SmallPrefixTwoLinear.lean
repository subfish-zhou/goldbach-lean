import U8SmallPrefixFibres

/-! Finite two-linear-form Selberg bridge. The two primality conditions are
both used. This module does not claim a log-squared asymptotic bound. -/
noncomputable section
open Finset
open scoped BigOperators
namespace U8Literal.SmallProduct

/-- Both linear forms, with natural subtraction used only on the original interval. -/
def twoLinear (N : ℕ) (t : ℕ × ℕ) (r : ℕ) : ℕ := r*(N-t.1*t.2*r)

def sievePrimes (Z : ℝ) : Finset ℕ := by
  classical
  exact (range ⌈Z⌉₊).filter fun p => p.Prime

theorem mem_sievePrimes {Z : ℝ} {p : ℕ} :
    p ∈ sievePrimes Z ↔ p.Prime ∧ (p : ℝ) < Z := by
  classical
  simp only [sievePrimes, mem_filter, mem_range, Nat.lt_ceil]
  tauto

theorem sievePrimes_prod_ne_zero (Z : ℝ) : (sievePrimes Z).prod id ≠ 0 := by
  classical
  exact prod_ne_zero_iff.mpr fun p hp => (mem_sievePrimes.mp hp).1.ne_zero

/-- No boundary loss: sieve primes are strictly below Z; r=p2 is permitted. -/
theorem primePair_coprime {N : ℕ} {e Z : ℝ} {t : ℕ × ℕ} {r : ℕ}
    (ht : t ∈ pairs N e) (hr : r ∈ primePair N e t)
    (hZb : Z ≤ (t.2 : ℝ)) (hZo : Z ≤ (1-e)*(N : ℝ)) :
    (twoLinear N t r).Coprime ((sievePrimes Z).prod id) := by
  classical
  have hc := primePair_cutoff ht hr
  obtain ⟨_,hrp,hop⟩ := mem_filter.mp hr
  apply Nat.coprime_prod_right_iff.mpr
  intro p hp
  obtain ⟨hp,hpZ⟩ := mem_sievePrimes.mp hp
  have hbr : (t.2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hc.1
  have hpr : p < r := by exact_mod_cast hpZ.trans_le (hZb.trans hbr)
  have hpo : p < N-t.1*t.2*r := by exact_mod_cast hpZ.trans_le (hZo.trans hc.2.2)
  exact (Nat.coprime_of_lt_prime hp.ne_zero hpr hrp).mul_left
    (Nat.coprime_of_lt_prime hp.ne_zero hpo hop)

/-- A finite divisor sum with arbitrary real weights, normalized at 1. -/
def divisorSum (D : Finset ℕ) (w : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ d ∈ D, if d ∣ m then w d else 0

theorem divisorSum_eq_one {D : Finset ℕ} {Q m : ℕ} {w : ℕ → ℝ}
    (h1 : 1 ∈ D) (hD : ∀ d ∈ D, d ∣ Q) (hw : w 1 = 1)
    (hc : m.Coprime Q) : divisorSum D w m = 1 := by
  classical
  unfold divisorSum
  rw [sum_eq_single 1]
  · simpa using hw
  · intro d hd hd1
    have hn : ¬d ∣ m := fun hdm => hd1 (Nat.eq_one_of_dvd_coprimes hc hdm (hD d hd))
    simp only [if_neg hn]
  · exact fun hn => False.elim (hn h1)

/-- A genuine Selberg-square inequality on the actual two-prime fibre. -/
theorem primePair_card_le_square {N : ℕ} {e Z : ℝ} {t : ℕ × ℕ}
    (ht : t ∈ pairs N e) (hZb : Z ≤ (t.2 : ℝ)) (hZo : Z ≤ (1-e)*(N : ℝ))
    (D : Finset ℕ) (w : ℕ → ℝ) (h1 : 1 ∈ D)
    (hD : ∀ d ∈ D, d ∣ (sievePrimes Z).prod id) (hw : w 1 = 1) :
    ((primePair N e t).card : ℝ) ≤
      ∑ r ∈ interval N e t, (divisorSum D w (twoLinear N t r))^2 := by
  classical
  calc
    ((primePair N e t).card : ℝ) = ∑ r ∈ primePair N e t, (1 : ℝ) := by simp
    _ = ∑ r ∈ primePair N e t, (divisorSum D w (twoLinear N t r))^2 := by
      apply sum_congr rfl
      intro r hr
      rw [divisorSum_eq_one h1 hD hw (primePair_coprime ht hr hZb hZo), one_pow]
    _ ≤ ∑ r ∈ interval N e t, (divisorSum D w (twoLinear N t r))^2 := by
      apply sum_le_sum_of_subset_of_nonneg
      · exact filter_subset _ _
      · intro r _ _
        exact sq_nonneg _

/-- Exact intersection count for the two linear forms; no independent-density assertion. -/
def divisibilityCount (N : ℕ) (e : ℝ) (t : ℕ × ℕ) (d f : ℕ) : ℕ := by
  classical
  exact ((interval N e t).filter fun r => d ∣ twoLinear N t r ∧ f ∣ twoLinear N t r).card

/-- The finite quadratic form seen by a subsequent genuine dimension-two sieve estimate. -/
def quadratic (N : ℕ) (e : ℝ) (t : ℕ × ℕ) (D : Finset ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ d ∈ D, ∑ f ∈ D, w d * w f * (divisibilityCount N e t d f : ℝ)

theorem square_eq_quadratic (N : ℕ) (e : ℝ) (t : ℕ × ℕ)
    (D : Finset ℕ) (w : ℕ → ℝ) :
    (∑ r ∈ interval N e t, (divisorSum D w (twoLinear N t r))^2) =
      quadratic N e t D w := by
  classical
  unfold divisorSum quadratic
  simp_rw [pow_two, sum_mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro d _
  rw [sum_comm]
  apply sum_congr rfl
  intro f _
  have hpoint (r : ℕ) :
      (if d ∣ twoLinear N t r then w d else 0) *
        (if f ∣ twoLinear N t r then w f else 0) =
      if d ∣ twoLinear N t r ∧ f ∣ twoLinear N t r then w d*w f else 0 := by
    split_ifs <;> simp_all
  simp_rw [hpoint]
  rw [← sum_filter]
  simp only [sum_const, nsmul_eq_mul, divisibilityCount]
  ring

/-- Typed bound for the original actual smallPrefix, with both logarithm-producing
primality conditions retained in the finite sieve source. Not a normalized payment. -/
theorem smallPrefix_card_le_twoLinearQuadratic (N : ℕ) (e Z : ℝ)
    (hZb : Z ≤ (N : ℝ)^(1/3 : ℝ)) (hZo : Z ≤ (1-e)*(N : ℝ))
    (D : Finset ℕ) (w : ℕ → ℝ) (h1 : 1 ∈ D)
    (hD : ∀ d ∈ D, d ∣ (sievePrimes Z).prod id) (hw : w 1 = 1) :
    ((smallPrefix N e).card : ℝ) ≤ ∑ t ∈ pairs N e, quadratic N e t D w := by
  rw [smallPrefix_card_real_eq_sum]
  apply sum_le_sum
  intro t ht
  have htb := (pairs_data ht).2.2.2.2.2.1
  exact (primePair_card_le_square ht (hZb.trans htb) hZo D w h1 hD hw).trans_eq
    (square_eq_quadratic N e t D w)

/-- A concrete legal sieve cutoff for every fixed e≤1/2 and every N≥4.
Only order properties of powers and the square-root inequality are used. -/
theorem cubeRoot_le_output_floor {N : ℕ} {e : ℝ} (hN : 4 ≤ N) (he : e ≤ 1/2) :
    (N : ℝ)^(1/3 : ℝ) ≤ (1-e)*(N : ℝ) := by
  have hN4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  calc
    (N : ℝ)^(1/3 : ℝ) ≤ (N : ℝ)^(1/2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    _ = Real.sqrt (N : ℝ) := Real.sqrt_eq_rpow (N : ℝ) |>.symm
    _ ≤ (N : ℝ)/2 := (Real.sqrt_le_iff).mpr ⟨by positivity, by nlinarith⟩
    _ ≤ (1-e)*(N : ℝ) := by nlinarith

/-- Unconditional finite bound for the original prefix at a concrete legal cutoff.
The free normalized divisor weights are algebraic parameters, not a payment assumption. -/
theorem smallPrefix_card_le_cubeRootQuadratic (N : ℕ) (e : ℝ)
    (hN : 4 ≤ N) (he : e ≤ 1/2)
    (D : Finset ℕ) (w : ℕ → ℝ) (h1 : 1 ∈ D)
    (hD : ∀ d ∈ D, d ∣ (sievePrimes ((N : ℝ)^(1/3 : ℝ))).prod id)
    (hw : w 1 = 1) :
    ((smallPrefix N e).card : ℝ) ≤ ∑ t ∈ pairs N e, quadratic N e t D w :=
  smallPrefix_card_le_twoLinearQuadratic N e _ le_rfl
    (cubeRoot_le_output_floor hN he) D w h1 hD hw

end U8Literal.SmallProduct
