import W17JointSymbolicActual
import NineOriginalTargets

noncomputable section
namespace WuSource.SrcNine
open Wu2008DoubleSieve ActualNineFeedback NodeExtension
open scoped BigOperators

def d : ℝ := WuTarget.W09.commonRadius

theorem d_pos : 0 < d := WuTarget.W09.commonRadius_pos

theorem d_cap : d ≤ 1 / 10 := WuTarget.W09.commonRadius_cap

theorem actual_coordinates (δ : ℝ) (i : Fin 9) :
    actualNine δ i = wuImprovementLimit true δ ((22 + (i.val : ℝ)) / 10) := by
  rfl

theorem coupled_qualified (i : Fin 4) : CoupledGeometry (coupledRow i) :=
  coupledRow_geometry i

theorem first_qualified (i : Fin 5) :
    2 ≤ firstNode i ∧ firstNode i ≤ 3 ∧ 3 ≤ firstS i ∧ firstS i ≤ 5 ∧
      2 ≤ firstS i - firstS i / firstNode i :=
  first_geometry i

theorem coupled_source_cost (p : SecondFunctionalParameters) {δ : ℝ}
    (hδ : δ ≤ 1 / 10) :
    SecondFunctionalCoupledFeedback.cost p δ / 5 =
      (4 * wuUpperCoefficient p.S + wuUpperCoefficient p.kappa1 +
        SecondFunctionalCoupledFeedback.classical p + 2 * coupledCostMass p) / 5 +
      deltaLoss δ * coupledLoss p :=
  exact_cost_loss p hδ

theorem coupled_source_actual {p : SecondFunctionalParameters}
    (hp : CoupledGeometry p) {δ : ℝ} (hδ : 0 < δ) (hr : δ ≤ d) :
    Wu08OriginalPsiRecovery.classicalNumerator p / 5 -
      2 * coupledCostMass p / (5 * (1 - 2 * δ)) +
      coupledFeedback p (actualNine δ) ≤ wuImprovementLimit true δ p.s :=
  Wu08OriginalPsiRecovery.original_logs_actual_lower hp hδ (hr.trans d_cap)

theorem lower_matrix_bounds (i k : Fin 9) :
    0 ≤ WuTarget.W17Joint.jointMatrix i k ∧
      WuTarget.W17Joint.jointMatrix i k ≤ feedbackMatrix i k :=
  ⟨WuTarget.W17Joint.jointMatrix_nonneg i k,
    WuTarget.W17Joint.jointMatrix_le_feedbackMatrix i k⟩

theorem actual_paid_system {δ : ℝ} (hδ : 0 < δ) (hr : δ ≤ d) :
    (∀ i, 0 ≤ actualNine δ i) ∧
    (∀ i, WuTarget.W09.seed i + matrixApply feedbackMatrix (actualNine δ) i ≤
      actualNine δ i) :=
  ⟨(actual_nine_system hδ (hr.trans d_cap)).2.2.1,
    WuTarget.W09.seed_feedback_actual hδ hr⟩

theorem seed_positive {i : Fin 9} (hi : i ≠ 8) : 0 < WuTarget.W09.seed i := by
  rw [WuTarget.W09.seed_eq_publication_add_increment]
  have hn : 0 ≤ WuTarget.W09.increment i := by
    fin_cases i <;> norm_num [WuTarget.W09.increment]
  exact add_pos_of_pos_of_nonneg (NineFeedbackStrength.publication_pos hi) hn

theorem certified_lower_subsolution {z : Fin 9 → ℝ}
    (hz : ∀ i, 0 ≤ z i)
    (hrow : ∀ i, z i ≤ WuTarget.W09.seed i +
      matrixApply WuTarget.W17Joint.jointMatrix z i)
    {δ : ℝ} (hδ : 0 < δ) (hr : δ ≤ d) :
    ∀ i, z i ≤ actualNine δ i := by
  apply NineFeedbackStrength.subsolution_le_supersolution
    WuTarget.W09.seed_nonneg (fun _ hi => seed_positive hi)
    (actual_paid_system hδ hr).1
  · intro i
    exact (hrow i).trans (add_le_add le_rfl
      (WuTarget.W17Joint.symbolic_apply_le_feedback hz i))
  · exact (actual_paid_system hδ hr).2

end WuSource.SrcNine

#print axioms WuSource.SrcNine.certified_lower_subsolution
#print axioms WuSource.SrcNine.coupled_source_actual
#print Wu2008DoubleSieve.SecondFunctionalParameters
#print Wu2008DoubleSieve.SecondFunctionalParameters.MotherAdmissible
#print Wu2008DoubleSieve.MotherPair.AnalyticParameters
#print Wu2008DoubleSieve.wuImprovementLimit
#print Wu2008DoubleSieve.wuAdmissibleImprovements
#print Wu2008DoubleSieve.sourceSieveCarrier
