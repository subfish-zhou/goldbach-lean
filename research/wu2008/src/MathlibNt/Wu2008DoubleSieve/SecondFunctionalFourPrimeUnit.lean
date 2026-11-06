import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeUnitRegression

/-! Unit-only four-prime end-to-end entry point. -/
namespace Wu2008DoubleSieve.FourPrimeUnit
open Finset Real
open scoped Classical

/-- Exact same-weight partition of each actual restored Gamma16--19 source. -/
theorem actual_gamma_partition {i : ℕ} (N : ℕ) (δ : ℝ) (p : SecondFunctionalParameters)
    (W : Fin i → Finset ℕ) (j : Fin 4) :
    actualSource N δ p W j +
      (∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
        prefixTerm false N d (wuLocalCutoff N δ d p.S)
          (wuLocalCutoff N δ d p.kappa1) (wuLocalCutoff N δ d p.kappa2)
          (wuLocalCutoff N δ d p.kappa3) (wuLocalCutoff N δ d p.s) (word j)) =
      ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
        secondFunctionalMotherGamma N d N (wuLocalCutoff N δ d p.S)
          (wuLocalCutoff N δ d p.kappa1) (wuLocalCutoff N δ d p.kappa2)
          (wuLocalCutoff N δ d p.kappa3) (wuLocalCutoff N δ d p.s) (16+j.val) := by
  unfold actualSource source
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro d _
  rw [← mul_add, gamma_partition]



end Wu2008DoubleSieve.FourPrimeUnit
