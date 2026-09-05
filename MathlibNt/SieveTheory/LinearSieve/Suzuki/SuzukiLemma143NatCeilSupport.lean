import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiNatCeilPowerCarrier
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma141Factorial
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma143UniformTailCore

/-!
# Suzuki Lemma 14.3 at the natural-ceiling cutoff

For `z = ⌈D^(1/s)⌉₊`, the strict condition `p < z` is transported exactly to
`p < D^(1/s)`.  This makes every source carrier through layer `⌊s-2⌋₊`
empty, without the generally false surrogate inequality `z^M ≤ D`.
-/

open scoped Classical BigOperators
open Finset Set

namespace MathlibNt.SieveTheory

open SwitchingPrinciple

private theorem nat_pow_lt_of_lt_rpow_one_div
    {p D m : ℕ} {s : ℝ} (hD : 1 < D) (hs : 0 < s)
    (hp : (p : ℝ) < (D : ℝ) ^ (1 / s)) (hp1 : 1 ≤ p)
    (hm : (m : ℝ) ≤ s) :
    p ^ m < D := by
  have hbase : (1 : ℝ) ≤ p := by exact_mod_cast hp1
  have hmono : (p : ℝ) ^ (m : ℝ) ≤ (p : ℝ) ^ s :=
    Real.rpow_le_rpow_of_exponent_le hbase hm
  have hstrict :
      (p : ℝ) ^ s < ((D : ℝ) ^ (1 / s)) ^ s :=
    Real.rpow_lt_rpow (by positivity) hp hs
  have hD0 : (0 : ℝ) ≤ D := by positivity
  rw [← Real.rpow_mul hD0] at hstrict
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hone : (1 / s) * s = (1 : ℝ) := by field_simp
  rw [hone, Real.rpow_one] at hstrict
  have hcast : ((p ^ m : ℕ) : ℝ) < (D : ℝ) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast]
    exact hmono.trans_lt hstrict
  exact_mod_cast hcast

/-- The lower-cutoff carrier is literally empty at the real power cutoff.
This is the strict-carrier replacement for a ceiling-power inequality. -/
theorem suzukiSourceLowerCarrier_rpow_eq_empty
    (S : BoundingSieve) {n D : ℕ} {s : ℝ}
    (hD : 1 < D) (hs : 0 < s) (hns : (n : ℝ) + 2 ≤ s) :
    (suzukiSupportedBelowPowerReal S ((D : ℝ) ^ (1 / s))).filter
        (fun p => D ≤ p ^ (n + 2)) = ∅ := by
  ext p
  constructor
  · intro hp
    simp only [Finset.mem_filter, suzukiSupportedBelowPowerReal] at hp
    rcases hp with ⟨⟨hpP, hplt⟩, hDpow⟩
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpP
    have hpowlt : p ^ (n + 2) < D :=
      nat_pow_lt_of_lt_rpow_one_div hD hs hplt hpPrime.one_le (by
        exact_mod_cast hns)
    omega
  · intro hp
    simp at hp

/-- Consequently the complete source outer carrier is empty.  The proof uses
its exact strict real-cutoff presentation, not finite-support exhaustion. -/
theorem suzukiSourceOuterCarrier_rpow_eq_empty
    (S : BoundingSieve) {n D : ℕ} {s : ℝ}
    (hD : 1 < D) (hs : 0 < s) (hns : (n : ℝ) + 2 ≤ s) :
    suzukiSourceOuterCarrierPowerReal n D ((D : ℝ) ^ (1 / s))
        S.prodPrimes.primeFactors = ∅ := by
  ext p
  constructor
  · intro hp
    simp only [suzukiSourceOuterCarrierPowerReal, Finset.mem_filter] at hp
    rcases hp with ⟨⟨hpP, hplt⟩, hDpow, _⟩
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpP
    have hpowlt : p ^ (n + 2) < D :=
      nat_pow_lt_of_lt_rpow_one_div hD hs hplt hpPrime.one_le (by
        exact_mod_cast hns)
    omega
  · intro hp
    simp at hp

/-- Actual source layers through `⌊s-2⌋₊` vanish for the natural-ceiling
choice `z = ⌈D^(1/s)⌉₊`. -/
theorem suzukiSourceV_eq_zero_below_natCeil_rpow
    (S : BoundingSieve) {n D z : ℕ} {s : ℝ}
    (hD : 1 < D) (hs : 2 ≤ s)
    (hz : z = ⌈(D : ℝ) ^ (1 / s)⌉₊)
    (hn : n ≤ ⌊s - 2⌋₊) :
    suzukiSourceV S n D z = 0 := by
  have hs0 : 0 < s := by linarith
  have hfloor : (⌊s - 2⌋₊ : ℝ) ≤ s - 2 :=
    Nat.floor_le (sub_nonneg.mpr hs)
  have hns : (n : ℝ) + 2 ≤ s := by
    have hcast : (n : ℝ) ≤ (⌊s - 2⌋₊ : ℕ) := by exact_mod_cast hn
    linarith
  cases n with
  | zero => rfl
  | succ k =>
      cases k with
      | zero =>
          rw [suzukiSourceV_one]
          rw [suzukiSourceBaseCarrier_natCeil_eq_powerReal S D
            (natCast_rpow_one_div_pos (by omega : 0 < D) s) hz]
          have hempty := suzukiSourceLowerCarrier_rpow_eq_empty
            (S := S) (n := 1) hD hs0 (by simpa using hns)
          rw [hempty]
          simp
      | succ k =>
          rw [suzukiSourceV_succ_natCeil_rpow_eq S
            (n := k + 1) (D := D) (z := z) (s := s)
            (by omega) (by omega) hz]
          have hempty := suzukiSourceOuterCarrier_rpow_eq_empty
            (S := S) (n := k + 2) hD hs0 (by
              norm_num at hns ⊢
              linarith)
          rw [hempty]
          simp

/-- Lemma 14.3 with both former abstract inputs discharged: support comes from
strict natural-ceiling carrier equality and the pointwise majorant is the
proved Lemma 14.1 factorial bound.  The right side is independent of `N`. -/
theorem suzukiLemma14_3_natCeil_uniform_exponentialTail
    (S : BoundingSieve) {N D z : ℕ} {s : ℝ}
    (hD : 1 < D) (hs : 2 ≤ s)
    (hz : z = ⌈(D : ℝ) ^ (1 / s)⌉₊) :
    suzukiActualT S N D z ≤
      suzukiExponentialTail
        (∑ p ∈ suzukiSupportedBelow S z, S.nu p) (⌊s - 2⌋₊ + 1) := by
  have hL : 0 ≤ ∑ p ∈ suzukiSupportedBelow S z, S.nu p := by
    apply Finset.sum_nonneg
    intro p hp
    have hpP := (Finset.mem_filter.mp hp).1
    exact (S.nu_pos_of_prime p (Nat.prime_of_mem_primeFactors hpP)
      (Nat.mem_primeFactors.mp hpP).2.1).le
  apply suzukiActualT_le_exponentialTail_of_support S hL
  · intro n hn
    apply suzukiSourceV_eq_zero_below_natCeil_rpow S hD hs hz
    omega
  · intro n
    exact suzukiSourceV_le_pow_div_factorial S n D z

/-- Explicit `tsum` form of the same `N`-uniform conclusion. -/
theorem suzukiLemma14_3_natCeil_uniform_tsum
    (S : BoundingSieve) {N D z : ℕ} {s : ℝ}
    (hD : 1 < D) (hs : 2 ≤ s)
    (hz : z = ⌈(D : ℝ) ^ (1 / s)⌉₊) :
    suzukiActualT S N D z ≤
      ∑' n : ℕ, if ⌊s - 2⌋₊ + 1 ≤ n then
        (∑ p ∈ suzukiSupportedBelow S z, S.nu p) ^ n /
          (n.factorial : ℝ) else 0 := by
  simpa [suzukiExponentialTail] using
    suzukiLemma14_3_natCeil_uniform_exponentialTail S hD hs hz


end MathlibNt.SieveTheory
