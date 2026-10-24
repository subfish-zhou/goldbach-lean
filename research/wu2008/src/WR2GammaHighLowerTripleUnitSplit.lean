import WR2GammaHighLowerTriplePaidRough

noncomputable section
namespace WuPaper.R2GammaHigh.LowerTriple
open Wu2008DoubleSieve LowerTripleGroupedFinite LiLiuPrereqBuchstab Finset
open scoped Classical

noncomputable def unitMass (j : Fin 3) (N : ℕ) (δ : ℝ) (k : Fin 6) : ℝ :=
  ∑ d ∈ boxConvolutionSupport (windows j N),
    (convolutionCoeff (windows j N) d : ℝ) *
    ∑ t ∈ actualPrimeTriples N δ (Wu04RemainingCore.row j) k d, if tupleProduct d t ≤ N then 1 else 0

noncomputable def nonunitMass (j : Fin 3) (N : ℕ) (δ : ℝ) (k : Fin 6) : ℝ :=
  ∑ d ∈ boxConvolutionSupport (windows j N),
    (convolutionCoeff (windows j N) d : ℝ) *
    ∑ t ∈ actualPrimeTriples N δ (Wu04RemainingCore.row j) k d,
      (((roughNumbers ((N : ℝ)/tupleProduct d t) t.2.1).erase 1).card : ℝ)

/-- No unit term is discarded or declared paid. -/
theorem rough_mass_unit_nonunit (j : Fin 3) (N : ℕ) (δ : ℝ) (k : Fin 6) :
    (roughFamily j N δ k).mass =
      unitMass j N δ k + nonunitMass j N δ k := by
  rw [rough_mass_triple_dictionary]
  unfold unitMass nonunitMass
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro d hd
  rw [← mul_add,← sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro t ht
  exact residual_card_unit_nonunit N _ _ (tupleProduct_pos
    (boxConvolutionSupport_pos (fun _ _ h => (mem_primeWindow.mp h).1.pos) hd) ht)

/-- Six original overlapping bands are summed separately with their full sigma weights. -/
theorem six_rough_mass_unit_nonunit (j : Fin 3) (N : ℕ) (δ : ℝ) :
    (∑ k : Fin 6, (roughFamily j N δ k).mass) =
      (∑ k : Fin 6, unitMass j N δ k) + ∑ k : Fin 6, nonunitMass j N δ k := by
  simp_rw [rough_mass_unit_nonunit]
  exact sum_add_distrib


end WuPaper.R2GammaHigh.LowerTriple
#print axioms WuPaper.R2GammaHigh.LowerTriple.six_rough_mass_unit_nonunit
