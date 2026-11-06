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


end WuPaper.R2Xi
