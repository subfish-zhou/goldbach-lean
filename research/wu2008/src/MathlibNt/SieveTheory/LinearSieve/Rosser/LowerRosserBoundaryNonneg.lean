import MathlibNt.SieveTheory.LinearSieve

namespace MathlibNt.SieveTheory.LinearSieve

open scoped Classical
/-- Every finite cubic-boundary mass is nonnegative when the local density is. -/
theorem lowerRosserBoundaryMass_nonneg
    (nu : ℕ → ℝ) (D q : ℕ) (P : Finset ℕ)
    (hnu : ∀ p ∈ P, 0 ≤ nu p) :
    0 ≤ lowerRosserBoundaryMass nu D q P := by
  unfold lowerRosserBoundaryMass
  apply Finset.sum_nonneg
  intro s hs
  apply Finset.prod_nonneg
  intro p hp
  exact hnu p (Finset.mem_powerset.mp (Finset.mem_filter.mp hs).1 hp)

/-- The fully iterated lower-Rosser boundary loss has a fixed nonnegative sign.
This is the useful replacement for taking the absolute value of an opaque
source-to-density discrepancy. -/
theorem lowerRosserBoundaryAccum_nonneg
    (nu : ℕ → ℝ) (D : ℕ) (P : Finset ℕ) (qs : List ℕ)
    (hnu : ∀ p ∈ qs.foldr insert P, 0 ≤ nu p)
    (hnuOne : ∀ p ∈ qs.foldr insert P, nu p ≤ 1) :
    0 ≤ lowerRosserBoundaryAccum nu D P qs := by
  induction qs with
  | nil => simp [lowerRosserBoundaryAccum]
  | cons q qs ih =>
      rw [lowerRosserBoundaryAccum]
      have hq : q ∈ (q :: qs).foldr insert P := by simp
      have htail : ∀ p ∈ qs.foldr insert P, 0 ≤ nu p := by
        intro p hp
        exact hnu p (by simp [hp])
      have htailOne : ∀ p ∈ qs.foldr insert P, nu p ≤ 1 := by
        intro p hp
        exact hnuOne p (by simp [hp])
      exact add_nonneg
        (mul_nonneg (sub_nonneg.mpr (hnuOne q hq)) (ih htail htailOne))
        (mul_nonneg (hnu q hq)
          (lowerRosserBoundaryMass_nonneg nu D q (qs.foldr insert P) htail))

end MathlibNt.SieveTheory.LinearSieve
