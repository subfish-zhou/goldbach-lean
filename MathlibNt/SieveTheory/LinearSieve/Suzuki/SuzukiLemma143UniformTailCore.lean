import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144ActualRecurrence
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma142InfiniteTail
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Suzuki Lemma 14.3: an `N`-uniform exponential-tail domination

This file proves the non-asymptotic core of Lemma 14.3 for the actual discrete
parity sum `suzukiActualT`.  It does not use eventual emptiness of the finite
prime support and it does not scan over depths.  The only analytic input is the
pointwise Lemma 14.1 majorant; the lower cutoff is obtained from the actual
support-vanishing theorem.

The production source objects specialize Suzuki's parameter to `β = 2`.  Thus
`⌊s - 2⌋₊ + 1` is the first possibly nonzero layer.  The hypothesis
`z ^ (⌊s - 2⌋₊ + 2) ≤ D` is the exact natural-number support condition needed
below (and is the form consumed from the real logarithmic coordinate bridge).
-/

open scoped Classical BigOperators
open Finset Set

namespace MathlibNt.SieveTheory

/-- The exponential series restricted to indices `n ≥ M`. -/
noncomputable def suzukiExponentialTail (L : ℝ) (M : ℕ) : ℝ :=
  ∑' n : ℕ, if M ≤ n then L ^ n / (n.factorial : ℝ) else 0

/-- The expected pointwise interface of Suzuki Lemma 14.1.  It is deliberately
pointwise, rather than an assumption of the desired tail estimate. -/
def SuzukiLemma141Majorant (S : BoundingSieve) (D z : ℕ) (L : ℝ) : Prop :=
  ∀ n : ℕ, suzukiSourceV S n D z ≤ L ^ n / (n.factorial : ℝ)


/-- Abstract finite-to-infinite step in Suzuki Lemma 14.3.  The finite carrier
may depend on `N`; the right side does not. -/
theorem suzukiActualT_le_exponentialTail_of_support
    (S : BoundingSieve) {N D z M : ℕ} {L : ℝ} (hL : 0 ≤ L)
    (hzero : ∀ n : ℕ, n < M → suzukiSourceV S n D z = 0)
    (h141 : SuzukiLemma141Majorant S D z L) :
    suzukiActualT S N D z ≤ suzukiExponentialTail L M := by
  rw [suzukiActualT_eq_parity_sum]
  let f : ℕ → ℝ := fun n =>
    if M ≤ n then L ^ n / (n.factorial : ℝ) else 0
  have hf : Summable f := by
    have hfull : Summable (fun n : ℕ => L ^ n / (n.factorial : ℝ)) :=
      Real.summable_pow_div_factorial L
    have hi := hfull.indicator (Set.Ici M)
    apply hi.congr
    intro n
    by_cases hMn : M ≤ n
    · have hnmem : n ∈ Set.Ici M := hMn
      simp [f, Set.indicator, hnmem, hMn]
    · have hnmem : n ∉ Set.Ici M := by simpa using hMn
      simp [f, Set.indicator, hnmem, hMn]
  calc
    (∑ n ∈ suzukiActualParityCarrier N, suzukiSourceV S n D z) =
        ∑ n ∈ suzukiActualParityCarrier N,
          (if M ≤ n then suzukiSourceV S n D z else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hMn : M ≤ n
      · simp [hMn]
      · rw [if_neg hMn, hzero n (Nat.lt_of_not_ge hMn)]
    _ ≤ ∑ n ∈ suzukiActualParityCarrier N, f n := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hMn : M ≤ n
      · simpa [f, hMn] using h141 n
      · simp [f, hMn]
    _ ≤ ∑' n : ℕ, f n := by
      apply hf.sum_le_tsum (suzukiActualParityCarrier N)
      intro n hn
      by_cases hMn : M ≤ n
      · simp only [f, if_pos hMn]
        exact div_nonneg (pow_nonneg hL n) (by positivity)
      · simp [f, hMn]
    _ = suzukiExponentialTail L M := by
      simp only [suzukiExponentialTail, f]


end MathlibNt.SieveTheory
