import WR2GammaHighCoupledCount
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalCoupledKernel

noncomputable section
namespace WuPaper.R2GammaHigh.Coupled
open Wu2008DoubleSieve Real Finset
open scoped Classical

theorem integralMass_kernel (row : Fin 3) (N : ℕ) (δ : ℝ) :
    integralMass row N δ =
      ∑ d ∈ boxConvolutionSupport (windows row N),
        (convolutionCoeff (windows row N) d : ℝ)*((N:ℝ)/(d*log ((N:ℝ)^(1/2-δ)/d)))*
          SecondFunctionalCoupled.kernel (Wu04RemainingCore.row row) (omega3XPhi N d δ) := by
  have swap {ι : Type} [Fintype ι] (f : ι → ℕ → ℝ) :
      (∑ k : ι, ∑ d ∈ boxConvolutionSupport (windows row N), f k d) =
      ∑ d ∈ boxConvolutionSupport (windows row N), ∑ k : ι, f k d := sum_comm
  unfold integralMass LowerTriple.integralKMain Four.integralKMain Tail.integralKMain
    TailUnit.integralJMain HighUnit.boxedIntegral20 HighUnit.boxedIntegral21
  simp only [swap, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro d _
  simp only [SecondFunctionalCoupled.kernel, FourPrimeNonunit.sourceLegalK,
    HighNonunit.sourceLegalK, Fintype.sum_bool, Bool.false_eq_true, if_false, if_true,
    ← mul_sum, div_div]
  ring

theorem integralMass_le_jointSup {N : ℕ} {δ : ℝ} (row : Fin 3)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1/100) :
    integralMass row N δ ≤
      (∑ d ∈ boxConvolutionSupport (windows row N),
        (convolutionCoeff (windows row N) d : ℝ)*((N:ℝ)/(d*log ((N:ℝ)^(1/2-δ)/d))))*
        SecondFunctionalCoupled.jointSup (Wu04RemainingCore.row row) := by
  rw [integralMass_kernel, sum_mul]
  apply sum_le_sum
  intro d hm
  have hg := LowerTriple.phi_bounds row hN hd hh hm
  have hphi : 2 ≤ omega3XPhi N d δ := by
    have hgap : 0 ≤ 2*δ/(1/2-δ) := div_nonneg (by positivity) (by linarith)
    linarith [hg.2.2.1]
  apply mul_le_mul_of_nonneg_left
    (SecondFunctionalCoupled.kernel_le_jointSup _ (row_analytic row).mother
      (row_analytic row).two_lt_s.le hphi)
  exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg (Nat.cast_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) (log_pos hg.2.1).le))

end WuPaper.R2GammaHigh.Coupled
#print axioms WuPaper.R2GammaHigh.Coupled.integralMass_kernel
#print axioms WuPaper.R2GammaHigh.Coupled.integralMass_le_jointSup
