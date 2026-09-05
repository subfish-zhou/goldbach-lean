import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144ActualRecurrence
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma142InfiniteTail
import Mathlib.Analysis.SpecialFunctions.Pow.Real
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

/-- The support statement used in Suzuki's proof: layers at or below `s - β`
vanish.  This names the expected support interface without assuming any tail
estimate. -/
def SuzukiActualSupportVanishing
    (S : BoundingSieve) (D z : ℕ) (β s : ℝ) : Prop :=
  ∀ n : ℕ, (n : ℝ) ≤ s - β → suzukiSourceV S n D z = 0

/-- Actual source support vanishing below a natural cutoff.  This is a direct
consumer of the source-faithful support theorem, not finite-support emptiness. -/
theorem suzukiSourceV_eq_zero_below_cutoff
    (S : BoundingSieve) {M n D z : ℕ} (hz : 0 < z)
    (hpow : z ^ (M + 2) ≤ D) (hn : n ≤ M) :
    suzukiSourceV S n D z = 0 := by
  apply suzukiSourceV_eq_zero_of_pow_le_allDepth S n D z
  exact (Nat.pow_le_pow_right hz (by omega : n + 2 ≤ M + 2)).trans hpow

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

/-- Generic-`β` formulation of the exact tail stage.  It combines the actual
support cutoff and the Lemma 14.1 pointwise estimate, and removes both the
parity restriction and the upper endpoint `N`. -/
theorem suzukiActualT_le_uniform_tsum
    (S : BoundingSieve) {N D z : ℕ} {β s L : ℝ}
    (hβs : β ≤ s) (hL : 0 ≤ L)
    (hsupport : SuzukiActualSupportVanishing S D z β s)
    (h141 : SuzukiLemma141Majorant S D z L) :
    suzukiActualT S N D z ≤
      ∑' n : ℕ,
        if ⌊s - β⌋₊ + 1 ≤ n then L ^ n / (n.factorial : ℝ) else 0 := by
  have hfloor : (⌊s - β⌋₊ : ℝ) ≤ s - β :=
    Nat.floor_le (sub_nonneg.mpr hβs)
  apply suzukiActualT_le_exponentialTail_of_support S hL
  · intro n hn
    apply hsupport n
    have hnFloor : n ≤ ⌊s - β⌋₊ := by omega
    have hnFloorR : (n : ℝ) ≤ (⌊s - β⌋₊ : ℕ) := by exact_mod_cast hnFloor
    exact hnFloorR.trans hfloor
  · exact h141

/-- Suzuki Lemma 14.3 at the exact exponential-tail stage (`β = 2`).  This is
uniform in `N`: no term on the right depends on `N`. -/
theorem suzukiLemma14_3_uniform_exponentialTail
    (S : BoundingSieve) {N D z : ℕ} {s L : ℝ}
    (hz : 0 < z) (_hs : 2 ≤ s) (hL : 0 ≤ L)
    (hpow : z ^ (⌊s - 2⌋₊ + 2) ≤ D)
    (h141 : SuzukiLemma141Majorant S D z L) :
    suzukiActualT S N D z ≤ suzukiExponentialTail L (⌊s - 2⌋₊ + 1) := by
  apply suzukiActualT_le_exponentialTail_of_support S hL
  · intro n hn
    apply suzukiSourceV_eq_zero_below_cutoff S hz hpow
    omega
  · exact h141

/-- Spelling out the tail makes the floor endpoint and the absence of `N` on
its right-hand side explicit. -/
theorem suzukiLemma14_3_uniform_tsum
    (S : BoundingSieve) {N D z : ℕ} {s L : ℝ}
    (hz : 0 < z) (hs : 2 ≤ s) (hL : 0 ≤ L)
    (hpow : z ^ (⌊s - 2⌋₊ + 2) ≤ D)
    (h141 : SuzukiLemma141Majorant S D z L) :
    suzukiActualT S N D z ≤
      ∑' n : ℕ, if ⌊s - 2⌋₊ + 1 ≤ n then L ^ n / (n.factorial : ℝ) else 0 := by
  simpa [suzukiExponentialTail] using
    suzukiLemma14_3_uniform_exponentialTail S hz hs hL hpow h141


end MathlibNt.SieveTheory
