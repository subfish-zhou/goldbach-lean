import WR2GammaHighTailPaidRough
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitRoughMassScalar

noncomputable section
namespace WuPaper.R2GammaHigh.Tail
open Wu2008DoubleSieve HighNonunit Finset LiLiuPrereqBuchstab
open scoped Classical

theorem rough_mass_dictionary (j : Fin 3) (N : ℕ) (δ : ℝ) (k : Bool) :
    (roughFamily j N δ k).mass =
      ∑ x ∈ (actualProfiles N δ (Wu04RemainingCore.row j) (windows j N) k).filter profileRough,
        (convolutionCoeff (windows j N) x.1 : ℝ) *
          (actualRawFibre N δ (Wu04RemainingCore.row j) x).card := by
  simpa only [LabelledPhysical.Family.mass, roughFamily,
    LabelledPhysical.Family.restrictLabels, sourceFamily, actualFamily, physicalFamily,
    sum_const, nsmul_eq_mul, mul_comm] using
    rough_test_dictionary j N δ k (fun x _ => (convolutionCoeff (windows j N) x.1 : ℝ))

/-- Full original four-prime tuples and erased unit residual, without product deduplication. -/
theorem rough_mass_tuple_dictionary (j : Fin 3) (N : ℕ) (δ : ℝ) (k : Bool) :
    (roughFamily j N δ k).mass =
      ∑ d ∈ boxConvolutionSupport (windows j N), (convolutionCoeff (windows j N) d : ℝ) *
        ∑ t ∈ actualPrimeTuples N δ (Wu04RemainingCore.row j) k d,
          (((roughNumbers ((N:ℝ)/tupleProduct d t) t.2.1).erase 1).card : ℝ) := by
  let W := windows j N
  have hd : ∀ d ∈ boxConvolutionSupport W, 0 < d :=
    fun _ h => boxConvolutionSupport_pos
      (fun _ _ hq => (mem_primeWindow.mp hq).1.pos) h
  rw [rough_mass_dictionary]
  have hh := rough_profiles_dictionary N W
    (fun d => wuLocalCutoff N δ d (Wu04RemainingCore.row j).S) (fun d => wuLocalCutoff N δ d (Wu04RemainingCore.row j).kappa1)
    (fun d => wuLocalCutoff N δ d (Wu04RemainingCore.row j).kappa2) (fun d => wuLocalCutoff N δ d (Wu04RemainingCore.row j).kappa3)
    (fun d => wuLocalCutoff N δ d (Wu04RemainingCore.row j).s) (word k) hd
  simpa only [actualProfiles, actualRawFibre, actualPrimeTuples, sum_filter,
    sum_ite_irrel, sum_const_zero, sum_const, nsmul_eq_mul, mul_comm, W] using hh

end WuPaper.R2GammaHigh.Tail
#print axioms WuPaper.R2GammaHigh.Tail.rough_mass_tuple_dictionary
