import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiFiniteContinuousLayersKappaOne

open scoped Classical BigOperators
open Finset Set

namespace MathlibNt.SieveTheory

open SuzukiFiniteContinuousLayers

set_option autoImplicit false

/-- Proposition 11.8, specialized to the compact source strip needed in
Suzuki (13.11). -/
def Proposition118InitialStripSourceBound : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ (N : ℕ) (x : ℝ),
    1 ≤ N →
    x ∈ KappaOneModel.parityDomain 2 N →
    x ≤ 4 →
    x * finiteSourceLayer 1 2 N x ≤ B

/-- A summable depth majorant is the precise convergence input from which the
uniform compact-strip consequence follows.  This lemma contains no finite scan:
the same sequence majorizes every legal compact-strip coordinate. -/
theorem proposition118_initialStrip_of_summable_layer_majorant
    (a : ℕ → ℝ) (ha0 : ∀ n, 0 ≤ a n) (ha : Summable a)
    (hmajor : ∀ (n : ℕ) (x : ℝ),
      x ∈ KappaOneModel.parityDomain 2 n → x ≤ 4 →
      x * suzukiLayer 1 2 n x ≤ a n) :
    Proposition118InitialStripSourceBound := by
  refine ⟨∑' n, a n, tsum_nonneg ha0, ?_⟩
  intro N x _hN hxdom hx4
  unfold finiteSourceLayer
  rw [Finset.mul_sum]
  calc
    (∑ n ∈ Finset.Icc 1 N,
        x * (if n % 2 = N % 2 then suzukiLayer 1 2 n x else 0)) ≤
        ∑ n ∈ Finset.Icc 1 N, a n := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hpar : n % 2 = N % 2
      · simp only [hpar, if_true]
        apply hmajor n x
        · simpa [KappaOneModel.parityDomain, hpar] using hxdom
        · exact hx4
      · simp only [hpar, if_false, mul_zero]
        exact ha0 n
    _ ≤ ∑' n, a n := by
      exact ha.sum_le_tsum (Finset.Icc 1 N) (fun n _ => ha0 n)


end MathlibNt.SieveTheory
