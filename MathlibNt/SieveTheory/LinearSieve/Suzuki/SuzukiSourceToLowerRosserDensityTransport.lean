import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144ActualRecurrenceStrictCeil

open scoped Classical BigOperators
open Finset

namespace MathlibNt.SieveTheory

open LinearSieve
open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144Equation1410


/-- Iterating the one-prime recurrence expands the lower density as the full
Euler product minus an explicit recursively weighted sum of odd cubic boundary
layers.  The list is increasing, so its head is the least prime inserted last. -/
theorem lowerRosserSetDensitySum_eq_euler_sub_boundaryAccum
    (S : BoundingSieve) {D z : ℕ} (qs : List ℕ)
    (hcarrier : qs.toFinset = suzukiSupportedBelow S z)
    (hprime : ∀ q ∈ qs, q.Prime) (hD : ∀ q ∈ qs, q < D)
    (hordered : qs.Pairwise (· < ·)) (hD1 : 1 < D) :
    lowerRosserSetDensitySum S.nu D (suzukiSupportedBelow S z) =
      sourceDiscreteEuler S z -
        lowerRosserBoundaryAccum S.nu D (∅ : Finset ℕ) qs := by
  have hfoldAll : ∀ ls : List ℕ, ls.foldr insert ∅ = ls.toFinset := by
    intro ls
    induction ls with
    | nil => simp
    | cons q ls ih => simp [ih]
  have hfold := hfoldAll qs
  have hiter := lowerRosserSetDensitySum_foldr_insert
    S.nu D (∅ : Finset ℕ) qs hprime hD hordered (by simp) (by simp)
  rw [hfold, hcarrier] at hiter
  have hbase : lowerRosserSetDensitySum S.nu D ∅ = 1 := by
    have hrel := lowerRosserSetRelativeDensity_empty S.nu hD1
    simpa [lowerRosserSetRelativeDensity] using hrel
  have hprod : (qs.map (fun q => 1 - S.nu q)).prod =
      sourceDiscreteEuler S z := by
    rw [← List.prod_toFinset (fun q => 1 - S.nu q) hordered.nodup,
      hcarrier]
    rfl
  rw [hbase, hprod, mul_one] at hiter
  exact hiter


end MathlibNt.SieveTheory
