import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finset.Card

namespace MathlibNt.SieveTheory

/-- A finite real half-open window is the difference of its closed prefixes.
The arbitrary predicate retains all arithmetic gates, including a product residue. -/
theorem filter_range_real_window_eq_sdiff (N : ℕ) (L U : ℝ)
    (P : ℕ → Prop) [DecidablePred P] (hL : 0 ≤ L) (hLU : L ≤ U) (hUN : U ≤ N) :
    ((Finset.range (N + 1)).filter (fun r => P r ∧ L < (r : ℝ) ∧ (r : ℝ) ≤ U)) =
      ((Finset.range (⌊U⌋₊ + 1)).filter P) \
        ((Finset.range (⌊L⌋₊ + 1)).filter P) := by
  ext r
  simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff,
    Finset.mem_sdiff, Nat.le_floor_iff (hL.trans hLU), Nat.le_floor_iff hL]
  constructor
  · rintro ⟨_, hp, hl, hu⟩
    exact ⟨⟨hu, hp⟩, fun h => (not_le_of_gt hl) h.1⟩
  · rintro ⟨⟨hu, hp⟩, hl⟩
    exact ⟨Nat.cast_le.mp (hu.trans hUN), hp,
      lt_of_not_ge (fun h => hl ⟨h, hp⟩), hu⟩

end MathlibNt.SieveTheory
