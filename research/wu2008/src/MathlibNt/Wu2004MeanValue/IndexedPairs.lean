import MathlibNt.Wu2004MeanValue.ClosedIntervals
import MathlibNt.Wu2004MeanValue.SieveSupport
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! Indexed prime-pair sequences, not image sets. A pair remains a separate
index even when another pair has the same value `N - m*p`. -/

namespace Wu2004MeanValue

open Classical Finset
open scoped BigOperators
noncomputable section

def intervalPrimeSet (closed : Bool) (lo hi : ℝ) (d b m : ℕ) : Finset ℕ :=
  if closed then closedScaledPrimeSet lo hi d b m else openScaledPrimeSet lo hi d b m

theorem mem_intervalPrimeSet {closed : Bool} {lo hi : ℝ} {d b m p : ℕ}
    (hhi : 0 ≤ hi) (hm : 0 < m) :
    p ∈ intervalPrimeSet closed lo hi d b m ↔
      p.Prime ∧ (if closed then lo ≤ (m : ℝ) * p ∧ (m : ℝ) * p ≤ hi
        else lo < (m : ℝ) * p ∧ (m : ℝ) * p < hi) ∧ m * p ≡ b [MOD d] := by
  cases closed
  · simp only [intervalPrimeSet, Bool.false_eq_true, if_false,
      openScaledPrimeSet, mem_filter, mem_scaledPrimeSet hhi hm]
    constructor
    · rintro ⟨⟨hp, _, hcong⟩, hinterval⟩
      exact ⟨hp, hinterval, hcong⟩
    · rintro ⟨hp, hinterval, hcong⟩
      exact ⟨⟨hp, hinterval.2.le, hcong⟩, hinterval⟩
  · simpa only [intervalPrimeSet, if_true, and_assoc] using
      (mem_closedScaledPrimeSet (lo := lo) (d := d) (b := b) (p := p) hhi hm)

def indexedPrimePairs (closed : Bool) (S : Finset ℕ) (lo hi : ℕ → ℝ) :
    Finset (Σ _ : ℕ, ℕ) :=
  S.sigma (fun m => intervalPrimeSet closed (lo m) (hi m) 1 0 m)

def pairValue (N : ℕ) (t : Σ _ : ℕ, ℕ) : ℕ := N - t.1 * t.2

def indexedDivisibleCount (N : ℕ) (T : Finset (Σ _ : ℕ, ℕ)) (d : ℕ) : ℕ :=
  (T.filter (fun t => d ∣ pairValue N t)).card

theorem mem_indexedPrimePairs {closed : Bool} {S : Finset ℕ} {lo hi : ℕ → ℝ}
    {m p : ℕ} (hhi : 0 ≤ hi m) (hm : 0 < m) :
    (⟨m, p⟩ : Σ _ : ℕ, ℕ) ∈ indexedPrimePairs closed S lo hi ↔
      m ∈ S ∧ p.Prime ∧
        (if closed then lo m ≤ (m : ℝ) * p ∧ (m : ℝ) * p ≤ hi m
         else lo m < (m : ℝ) * p ∧ (m : ℝ) * p < hi m) := by
  simp [indexedPrimePairs, mem_intervalPrimeSet hhi hm, Nat.ModEq, Nat.mod_one]

theorem pairValue_dvd_iff {N d : ℕ} {t : Σ _ : ℕ, ℕ}
    (ht : t.1 * t.2 ≤ N) :
    d ∣ pairValue N t ↔ t.1 * t.2 ≡ N [MOD d] :=
  (Nat.modEq_iff_dvd' ht).symm

theorem intervalPrimeSet_filter_divisible (closed : Bool) (lo hi : ℝ)
    (N d m : ℕ) (hm : 0 < m) (hhi : 0 ≤ hi) (hN : hi ≤ N) :
    (intervalPrimeSet closed lo hi 1 0 m).filter
        (fun p => d ∣ pairValue N ⟨m, p⟩) =
      intervalPrimeSet closed lo hi d N m := by
  ext p
  simp only [mem_filter, mem_intervalPrimeSet hhi hm]
  have hle (h : if closed then lo ≤ (m : ℝ) * p ∧ (m : ℝ) * p ≤ hi
      else lo < (m : ℝ) * p ∧ (m : ℝ) * p < hi) : m * p ≤ N := by
    have hprod : (m : ℝ) * p ≤ hi := by
      cases closed
      · exact h.2.le
      · exact h.2
    exact_mod_cast hprod.trans hN
  constructor
  · rintro ⟨⟨hp, hint, _⟩, hd⟩
    exact ⟨hp, hint, (pairValue_dvd_iff (hle hint)).mp hd⟩
  · rintro ⟨hp, hint, hd⟩
    exact ⟨⟨hp, hint, by simp [Nat.ModEq, Nat.mod_one]⟩,
      (pairValue_dvd_iff (hle hint)).mpr hd⟩

theorem indexedDivisibleCount_eq_sum (closed : Bool) (S : Finset ℕ)
    (lo hi : ℕ → ℝ) (N d : ℕ)
    (hS : ∀ m ∈ S, 0 < m ∧ 0 ≤ hi m ∧ hi m ≤ N) :
    indexedDivisibleCount N (indexedPrimePairs closed S lo hi) d =
      ∑ m ∈ S, (intervalPrimeSet closed (lo m) (hi m) d N m).card := by
  rw [indexedDivisibleCount, indexedPrimePairs, filter_sigma, card_sigma]
  apply sum_congr rfl
  intro m hm
  rw [intervalPrimeSet_filter_divisible closed (lo m) (hi m) N d m
    (hS m hm).1 (hS m hm).2.1 (hS m hm).2.2]

theorem source_coprime_of_scaled_congruence {m p N d : ℕ}
    (hN : N.Coprime d) (hcong : m * p ≡ N [MOD d]) : m.Coprime d := by
  have hprod : (m * p).Coprime d := by
    change Nat.gcd (m * p) d = 1
    rw [Nat.gcd_comm, Nat.gcd_rec, hcong, ← Nat.gcd_rec, Nat.gcd_comm]
    exact hN
  exact (Nat.coprime_mul_iff_left.mp hprod).1

theorem intervalPrimeSet_eq_empty_of_not_coprime (closed : Bool) (lo hi : ℝ)
    (N d m : ℕ) (hN : N.Coprime d) (hm : 0 < m) (hhi : 0 ≤ hi)
    (hmd : ¬m.Coprime d) :
    intervalPrimeSet closed lo hi d N m = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  exact hmd (source_coprime_of_scaled_congruence hN
    ((mem_intervalPrimeSet hhi hm).mp hp).2.2)

def intervalMass (S : Finset ℕ) (lo hi : ℕ → ℝ) : ℝ :=
  ∑ m ∈ S, (wuLi (hi m / m) - wuLi (lo m / m))

def intervalErrorSum (closed : Bool) (S : Finset ℕ) (lo hi : ℕ → ℝ) (d b : ℕ) : ℝ :=
  ∑ m ∈ S, if m.Coprime d then
    ((intervalPrimeSet closed (lo m) (hi m) d b m).card : ℝ) -
      (wuLi (hi m / m) - wuLi (lo m / m)) / d.totient else 0

theorem intervalErrorSum_closed (S : Finset ℕ) (lo hi : ℕ → ℝ) (d b : ℕ) :
    intervalErrorSum true S lo hi d b = actualClosedErrorSum S (fun _ => 1) lo hi d b := by
  simp [intervalErrorSum, intervalPrimeSet, actualClosedErrorSum]

theorem intervalErrorSum_open (S : Finset ℕ) (lo hi : ℕ → ℝ) (d b : ℕ) :
    intervalErrorSum false S lo hi d b = actualOpenErrorSum S (fun _ => 1) lo hi d b := by
  simp [intervalErrorSum, intervalPrimeSet, actualOpenErrorSum]

theorem indexedDivisibleCount_common_main (closed : Bool) (S : Finset ℕ)
    (lo hi : ℕ → ℝ) (N d : ℕ) (hN : N.Coprime d)
    (hS : ∀ m ∈ S, m.Prime ∧ 0 ≤ hi m ∧ hi m ≤ N) :
    (indexedDivisibleCount N (indexedPrimePairs closed S lo hi) d : ℝ) =
      intervalMass S lo hi / d.totient + intervalErrorSum closed S lo hi d N -
        (∑ m ∈ S with m ∣ d, (wuLi (hi m / m) - wuLi (lo m / m))) / d.totient := by
  rw [indexedDivisibleCount_eq_sum closed S lo hi N d
    (fun m hm => ⟨(hS m hm).1.pos, (hS m hm).2⟩), Nat.cast_sum]
  simp only [intervalMass, intervalErrorSum, sum_div, sum_filter, ← sum_add_distrib,
    ← sum_sub_distrib]
  apply sum_congr rfl
  intro m hm
  by_cases hmd : m.Coprime d
  · have hnot : ¬m ∣ d := (hS m hm).1.coprime_iff_not_dvd.mp hmd
    simp only [if_pos hmd, if_neg hnot, zero_div]
    ring
  · have hdvd : m ∣ d := by
      by_contra h
      exact hmd ((hS m hm).1.coprime_iff_not_dvd.mpr h)
    rw [intervalPrimeSet_eq_empty_of_not_coprime closed (lo m) (hi m) N d m
      hN (hS m hm).1.pos (hS m hm).2.1 hmd]
    simp [hmd, hdvd]

def indexedRemainder (closed : Bool) (S : Finset ℕ) (lo hi : ℕ → ℝ)
    (N d : ℕ) : ℝ :=
  (indexedDivisibleCount N (indexedPrimePairs closed S lo hi) d : ℝ) -
    intervalMass S lo hi / d.totient

theorem indexedRemainder_eq_error_on_sieve (closed : Bool) (S : Finset ℕ)
    (lo hi : ℕ → ℝ) {N Q d : ℕ} {z : ℝ} (hd : d ∈ sieveModuli N z Q)
    (hS : ∀ m ∈ S, m.Prime ∧ z ≤ (m : ℝ) ∧ 0 ≤ hi m ∧ hi m ≤ N) :
    indexedRemainder closed S lo hi N d = intervalErrorSum closed S lo hi d N := by
  rw [indexedRemainder, indexedDivisibleCount_common_main closed S lo hi N d
    (coprime_of_mem_sieveModuli hd) (fun m hm => ⟨(hS m hm).1, (hS m hm).2.2⟩),
    omitted_main_sum_eq_zero hd S _ (fun m hm => ⟨(hS m hm).1, (hS m hm).2.1⟩)]
  ring

end
end Wu2004MeanValue
