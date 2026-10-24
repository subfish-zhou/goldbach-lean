import WR2XiPositive
import WR2XiSecondPaid

/-! Finite coefficients for the literal original Xi2 kernel. -/
noncomputable section
namespace WuPaper.R2Xi
open Real Set MeasureTheory NodeExtension Wu2008DoubleSieve MotherPair ActualNineFeedback
open WuPaper.RMapMMatrix
open Wu2004MeanValue.GammaFiveLossBudget
open scoped Interval BigOperators

/-- Exact cell coefficients; numerical lower bounds must still be certified. -/
def Xi2Coefficient (p : SecondFunctionalParameters) (k : Fin 9) : ℝ :=
  ∫ t in (1:ℝ)..3, nineProfile (nodeBasis k) t * Xi2 p t

theorem Xi2Coefficient_nonneg {p : SecondFunctionalParameters}
    (hp : PropositionFourGeometry p) (k : Fin 9) : 0 ≤ Xi2Coefficient p k :=
  Xi2_integral_nonneg (nineProfile_integrable _) (fun t _ =>
    nineProfile_nonneg (nodeBasis_nonneg k) t) hp

theorem Xi2_profile_expansion {p : SecondFunctionalParameters}
    (hp : PropositionFourGeometry p) (z : Fin 9 → ℝ) :
    (∫ t in (1:ℝ)..3, nineProfile z t * Xi2 p t) =
      ∑ k : Fin 9, Xi2Coefficient p k * z k := by
  have he (t : ℝ) : nineProfile z t * Xi2 p t =
      ∑ k : Fin 9, z k * (nineProfile (nodeBasis k) t * Xi2 p t) := by
    rw [nineProfile_expansion, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_finsetSum]
  · simp only [intervalIntegral.integral_const_mul, Xi2Coefficient, mul_comm]
  · intro k _
    exact (Xi2_integrable (nineProfile_integrable _) hp).const_mul _

theorem Xi2_matrix_le_actual {p : SecondFunctionalParameters}
    (hp : PropositionFourGeometry p) {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/10) :
    (∑ k : Fin 9, Xi2Coefficient p k * actualNine δ k) ≤
      ∫ t in (1:ℝ)..3, wuImprovementLimit true δ t * Xi2 p t := by
  rw [← Xi2_profile_expansion hp]
  exact Xi2_integral_mono (nineProfile_integrable _)
    (wuImprovementLimit_intervalIntegrable true hd (by linarith : δ < 1/2)
      (a := 1) (b := 3) (by norm_num) (by norm_num) (by norm_num))
    (fun _ ht => nineProfile_le_actual hd hh ht) hp

/-- The four original matrix rows with the proved Gamma5 and positive-delta losses. -/
theorem Xi2_four_rows_matrix_paid (r : Fin 4) {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/10) :
    coupledBase (gamma5OriginalRow r) - deltaLoss δ * coupledLoss (gamma5OriginalRow r) -
        rowDebit r/2 + (∑ k : Fin 9, Xi2Coefficient (gamma5OriginalRow r) k * actualNine δ k) ≤
      wuImprovementLimit true δ (gamma5OriginalRow r).s := by
  have h := Xi2_four_rows_paid_base r hd hh
  have hm := Xi2_matrix_le_actual (original_four_rows_qualified r) hd hh
  change (∑ k : Fin 9, Xi2Coefficient (gamma5OriginalRow r) k * actualNine δ k) ≤
    (∫ t in (1:ℝ)..3, wuImprovementLimit true δ t * Xi2 (gamma5OriginalRow r) t) at hm
  linarith only [h, hm]

end WuPaper.R2Xi
