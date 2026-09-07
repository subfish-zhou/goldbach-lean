import MathlibNt.SieveTheory.LiLiuGoldbachG12SharpGeometry

open scoped BigOperators
open Classical Finset LiLiuPrereqBuchstab
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The original weighted rough mother reaches the sharp step kernel.
Only the vanishing rough-count error uses the continuous author kernel. -/
theorem g12Sharp_authorRough_le_kernel (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀,
      Real.log (N : ℝ)/N * goldbachG12WeightedRough N (goldbachG12AuthorPrimeWeight N) ≤
        goldbachG12PrimeKernel G12SharpWeight.weight N +
          η * goldbachG12PrimeKernel goldbachG11AuthorWeight N := by
  obtain ⟨K,hK,hb⟩ := goldbachG12_rough_upper_buchstab η hη
  refine ⟨K,hK,?_⟩
  intro N hN
  have hN4 : 4 ≤ N := hK.trans hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ N by omega))
  unfold goldbachG12WeightedRough goldbachG12PrimeKernel
  rw [mul_sum,mul_sum,← sum_add_distrib]
  apply sum_le_sum
  intro v hv
  have hg := goldbachG12PrimeKernel_logGeometry hN4 hv
  have hbv := hb N hN v hv
  have hw := g12Sharp_buchstab_le_factor hN4 hv
  have hmass : (roughCount ((N : ℝ)/goldbachG11LabelProd v) v.2.2.2 : ℝ) ≤
      (G12SharpWeight.factor (Real.log (v.2.2.1 : ℝ)/Real.log (N : ℝ))+η) *
        ((N : ℝ)/goldbachG11LabelProd v) / Real.log (v.2.2.2 : ℝ) := by
    apply hbv.trans
    unfold goldbachG11BuchstabMass
    calc
      _ ≤ ((N : ℝ)/goldbachG11LabelProd v) *
          G12SharpWeight.factor (Real.log (v.2.2.1 : ℝ)/Real.log (N : ℝ)) /
            Real.log (v.2.2.2 : ℝ) + η*((N : ℝ)/goldbachG11LabelProd v) /
              Real.log (v.2.2.2 : ℝ) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ Real.log (N : ℝ)/N * (goldbachG12AuthorPrimeWeight N v.2.2.1 *
        ((G12SharpWeight.factor (Real.log (v.2.2.1 : ℝ)/Real.log (N : ℝ))+η)*
          ((N : ℝ)/goldbachG11LabelProd v)/Real.log (v.2.2.2 : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hmass (goldbachG11AuthorWeight_nonneg _))
        (div_nonneg hlog hNp.le)
    _ = (G12SharpWeight.weight (Real.log (v.2.2.1 : ℝ)/Real.log (N : ℝ)) *
          Real.log (N : ℝ)/((goldbachG11LabelProd v : ℝ)*Real.log (v.2.2.2 : ℝ)) +
        η * (goldbachG11AuthorWeight (Real.log (v.2.2.1 : ℝ)/Real.log (N : ℝ)) *
          Real.log (N : ℝ)/((goldbachG11LabelProd v : ℝ)*Real.log (v.2.2.2 : ℝ)))) *
            ((N : ℝ)/N) := by
      unfold G12SharpWeight.weight goldbachG12AuthorPrimeWeight
      ring
    _ = _ := by rw [div_self hNp.ne',mul_one]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
