import MathlibNt.SieveTheory.LiLiuGoldbachB10ProductCount

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Only the enlarged right-hand mother family loses its epsilon lower endpoint. -/
theorem goldbachB10ProductQFiber_subset_zeroPrefix (N : ℕ) (ε : ℝ) (m : ℕ) :
    goldbachB10ProductQFiber N ε m ⊆ goldbachB10ProductQFiber N 0 m := by
  intro q hq
  obtain ⟨hqr, hp, _hlo, hhi⟩ := mem_goldbachB10ProductQFiber_iff.mp hq
  apply mem_goldbachB10ProductQFiber_iff.mpr
  refine ⟨hqr, hp, ?_, hhi⟩
  simpa only [zero_mul, zero_div] using (show (0 : ℝ) < q by exact_mod_cast hp.pos)

/-- Literal fibre multiplicities and the output sieve remain unchanged. -/
theorem goldbachB10SiftedCount_le_zeroPrefix (N : ℕ) (ε b c Z : ℝ) :
    goldbachB10SiftedCount N ε b c Z ≤ goldbachB10SiftedCount N 0 b c Z := by
  classical
  rw [goldbachB10SiftedCount_eq_sum_productSupport,
    goldbachB10SiftedCount_eq_sum_productSupport]
  apply Finset.sum_le_sum
  intro m hm
  apply mul_le_mul_of_nonneg_left
  · apply Int.ofNat_le.mpr
    apply Finset.card_le_card
    intro q hq
    obtain ⟨hmem, hsift⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr
      ⟨goldbachB10ProductQFiber_subset_zeroPrefix N ε m hmem, hsift⟩
  · exact Int.natCast_nonneg _

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig