import MathlibNt.SieveTheory.LiLiuGoldbachG11ExceptionBudget

open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

#check GoldbachG11Label
#print axioms GoldbachG11Label
#check goldbachG11Labels
#print goldbachG11Labels
#print axioms goldbachG11Labels
#check mem_goldbachG11Labels_iff
#print axioms mem_goldbachG11Labels_iff
#check goldbachG11LabelProd
#print goldbachG11LabelProd
#print axioms goldbachG11LabelProd
#check goldbachG11RSquareException
#print goldbachG11RSquareException
#print axioms goldbachG11RSquareException
#check goldbachG11NException
#print goldbachG11NException
#print axioms goldbachG11NException
#check goldbachG11RSquareCount
#print goldbachG11RSquareCount
#print axioms goldbachG11RSquareCount
#check goldbachG11NCount
#print goldbachG11NCount
#print axioms goldbachG11NCount
#check goldbachG11_difference_data
#print axioms goldbachG11_difference_data
#check largePrimeDivisors_card_le_twenty
#print axioms largePrimeDivisors_card_le_twenty
#check goldbachS5SquareSet
#print goldbachS5SquareSet
#print axioms goldbachS5SquareSet
#check mem_goldbachS5SquareSet_iff
#print axioms mem_goldbachS5SquareSet_iff
#check goldbachS5SquareCount
#print goldbachS5SquareCount
#print axioms goldbachS5SquareCount
#check goldbachBadCount
#print goldbachBadCount
#print axioms goldbachBadCount
#check goldbachS5SquareCount_normalized
#print axioms goldbachS5SquareCount_normalized
#check goldbachS4_finiteLoss_normalized
#print axioms goldbachS4_finiteLoss_normalized

#check goldbachG11LabelCoordinates
#print axioms goldbachG11LabelCoordinates
#check goldbachG11LabelCoordinates_injective
#print axioms goldbachG11LabelCoordinates_injective
#check goldbachG11DivisorFiber
#print axioms goldbachG11DivisorFiber
#check goldbachG11LabelCoordinates_mem_largePrimeDivisors
#print axioms goldbachG11LabelCoordinates_mem_largePrimeDivisors
#check goldbachG11DivisorFiber_card_le
#print axioms goldbachG11DivisorFiber_card_le
#check goldbachG11_difference_strict_bounds
#print axioms goldbachG11_difference_strict_bounds
#check goldbachG11RSquareCount_sum_le
#print axioms goldbachG11RSquareCount_sum_le
#check goldbachG11NCount_sum_le
#print axioms goldbachG11NCount_sum_le
#check goldbachG11_exceptions_normalized
#print axioms goldbachG11_exceptions_normalized

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

theorem goldbachG11_canonical_fiber_audit {N n : ℕ}
    (hn1 : 1 ≤ n) (hnN : n < N) :
    ((goldbachG11Labels N ((N : ℝ) ^ ((4 : ℝ) / 53))
      ((N : ℝ) ^ ((4 : ℝ) / 33))).filter fun v => goldbachG11LabelProd v ∣ n).card ≤
        160000 :=
  goldbachG11DivisorFiber_card_le hn1 hnN

theorem goldbachG11_exceptions_eps_zero_audit (delta : ℝ) (hdelta : 0 < delta) :
    ∃ N0 : ℕ, 4 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
      (((∑ v ∈ goldbachG11Labels N ((N : ℝ) ^ ((4 : ℝ) / 53))
          ((N : ℝ) ^ ((4 : ℝ) / 33)),
          goldbachG11RSquareCount (goldbachDifferenceCarrier N 0) v) +
        (∑ v ∈ goldbachG11Labels N ((N : ℝ) ^ ((4 : ℝ) / 53))
          ((N : ℝ) ^ ((4 : ℝ) / 33)),
          goldbachG11NCount (goldbachDifferenceCarrier N 0) N v) : ℤ) : ℝ) ≤
        delta * (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2) := by
  obtain ⟨N0, hN0, h⟩ := goldbachG11_exceptions_normalized delta hdelta
  exact ⟨N0, hN0, fun N hN => h N hN 0 le_rfl⟩

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

#check goldbachG11_canonical_fiber_audit
#print axioms goldbachG11_canonical_fiber_audit
#check goldbachG11_exceptions_eps_zero_audit
#print axioms goldbachG11_exceptions_eps_zero_audit