import WR2GammaHighLowerTripleUnitSplit
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleUnitPrimeFinite

noncomputable section
namespace WuPaper.R2GammaHigh.LowerTriple
open Wu2008DoubleSieve LowerTripleGroupedUnit Finset
open scoped Classical

theorem unitMass_pair_fibre (j : Fin 3) (N : ℕ) (δ : ℝ) (k : Fin 6) :
    unitMass j N δ k =
      ∑ d ∈ boxConvolutionSupport (windows j N),
        (convolutionCoeff (windows j N) d : ℝ) *
        ∑ x ∈ actualPairs N δ (Wu04RemainingCore.row j) k d,
          ((fibre N d (LowerTripleGrouped.actualBands N δ (Wu04RemainingCore.row j) k d).2.2.2.2.1
            (LowerTripleGrouped.actualBands N δ (Wu04RemainingCore.row j) k d).2.2.2.2.2 x).card : ℝ) := by
  unfold unitMass
  apply sum_congr rfl
  intro d hd
  have hdp := boxConvolutionSupport_pos
    (fun _ _ h => (mem_primeWindow.mp h).1.pos) hd
  congr 1
  exact triple_pair_dictionary _ _ _ _ _ _ _ hdp

/-- The unchanged original unitMass, exactly, with both closed endpoints. -/
theorem unitMass_pair_prefix (j : Fin 3) (N : ℕ) (δ : ℝ) (k : Fin 6) :
    unitMass j N δ k =
      ∑ d ∈ boxConvolutionSupport (windows j N),
        (convolutionCoeff (windows j N) d : ℝ) *
        ∑ x ∈ actualPairs N δ (Wu04RemainingCore.row j) k d,
          prefixDifference (actualLower N δ (Wu04RemainingCore.row j) k d x) (actualUpper N δ (Wu04RemainingCore.row j) k d x) := by
  rw [unitMass_pair_fibre]
  apply sum_congr rfl
  intro d hd
  have hdp := boxConvolutionSupport_pos
    (fun _ _ h => (mem_primeWindow.mp h).1.pos) hd
  congr 1
  exact sum_congr rfl (fun x hx => fibre_prefix_dictionary _ _ _ _ _ (denominator_pos hdp hx))


end WuPaper.R2GammaHigh.LowerTriple
#print axioms WuPaper.R2GammaHigh.LowerTriple.unitMass_pair_prefix
