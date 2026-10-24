import WR2GammaHighTailMultiplicity

noncomputable section
namespace WuPaper.R2GammaHigh.Tail
open Wu2008DoubleSieve HighNonunit HighBoxRecovery Finset
open scoped Classical

/-- Restricting to physical labels preserves the full cofactor multiplicity bound. -/
theorem fixed_cofactor_bound {N : ℕ} {δ : ℝ} (j : Fin 3) (k : Bool)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1/100) (E : ℕ) :
    (∑ x ∈ (sourceFamily j N δ k).layerFibre E,
      (sourceFamily j N δ k).weight x) ≤ (max 1 (1/highEta))^6 := by
  have hfull := actual_fixed_cofactor j hN hd hh k (fun _ q hq => by
    have hg := prime_geometry j hN hd hh hq
    exact ⟨hg.1,hg.2.2.1⟩) E
  apply le_trans _ (hfull.trans (pow_le_pow_right₀ (le_max_left _ _) (by cases k <;> norm_num [arity])))
  apply sum_le_sum_of_subset_of_nonneg
  · intro x hx
    exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hx).1).1,(mem_filter.mp hx).2⟩
  · intro x _ _
    exact Nat.cast_nonneg _

end WuPaper.R2GammaHigh.Tail
#print axioms WuPaper.R2GammaHigh.Tail.fixed_cofactor_bound
