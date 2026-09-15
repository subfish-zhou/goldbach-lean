import GammaFullUpper

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve
open FullAdmissibleSeed
open SharpLogRecurrence JointLogTotalComparison
namespace GammaFullActual

/-- The latest old-package upper and both original corrections, each once. -/
def upperCoefficient : ℝ := MiddleInitialActual.upperRational+
  (GammaFullUpper.gammaUpper-47/481250)/4+U8ActualThreshold.gainUpper

theorem actual_upper : U8CanonicalMother.improvedCoefficient < upperCoefficient := by
  have ho := MiddleInitialActual.actual_upper
  have hg := GammaFullUpper.gamma_upper
  have hs := CorrectedCoefficientUpper.small_correction_interval.2
  rw [U8ActualThreshold.actual_identity]
  unfold upperCoefficient
  linarith only [ho,hg,hs]

theorem exact_descent : MiddleInitialActual.upperCoefficient-upperCoefficient =
    65179308691530313902851808311/9839809192196786654880000000000 := by
  unfold MiddleInitialActual.upperCoefficient upperCoefficient
  rw [GammaFullUpper.gamma_upper_exact,CorrectedCoefficientUpper.gamma_upper_exact]
  ring

def rationalCap : ℝ := 892230/1000000+
  (GammaFullUpper.gammaUpper-47/481250)/4+4979/1000000

theorem cap_exact : rationalCap =
    3892727172118963119943285672163/4329516044566586128147200000000 := by
  unfold rationalCap
  rw [GammaFullUpper.gamma_upper_exact]
  norm_num

theorem upper_below_cap : upperCoefficient < rationalCap := by
  have ho := MiddleInitialActual.old_upper_bounds.2
  have hs := CorrectedCoefficientUpper.small_upper_bounds.2
  unfold upperCoefficient rationalCap
  linarith only [ho,hs]

theorem complete_rational_upper : U8CanonicalMother.improvedCoefficient <
    3892727172118963119943285672163/4329516044566586128147200000000 := by
  rw [← cap_exact]
  exact actual_upper.trans upper_below_cap

theorem upper_bounds : (899110/1000000:ℝ) < upperCoefficient ∧
    upperCoefficient < 899114/1000000 := by
  have ho := MiddleInitialActual.old_upper_bounds.1
  have hs := CorrectedCoefficientUpper.small_upper_bounds.1
  have he : (899110/1000000:ℝ) < 892228/1000000+
      (GammaFullUpper.gammaUpper-47/481250)/4+4978/1000000 := by
    rw [GammaFullUpper.gamma_upper_exact]
    norm_num
  have hu := upper_below_cap
  rw [cap_exact] at hu
  constructor
  · unfold upperCoefficient
    linarith only [ho,hs,he]
  · linarith only [hu]

theorem actual_corridor : (834331/1000000:ℝ) < U8CanonicalMother.improvedCoefficient ∧
    U8CanonicalMother.improvedCoefficient < 899114/1000000 :=
  ⟨JJointPayment.rational_corridor.1,actual_upper.trans upper_bounds.2⟩

/-- Exact unpaid upper slack, with the full Gamma integral still literal. -/
def upperSlack : ℝ :=
  (MiddleInitialActual.upperRational-JointHMotherPayment.unroundedCoefficient)+
  (GammaFullUpper.gammaUpper-Gamma6)/4+
  (U8ActualThreshold.gainUpper-2*(U8CanonicalMother.L-U8CanonicalMother.I))

theorem actual_remaining_identity :
    upperCoefficient-U8CanonicalMother.improvedCoefficient = upperSlack := by
  rw [U8ActualThreshold.actual_identity]
  unfold upperCoefficient upperSlack
  ring

theorem slack_components :
    0 < MiddleInitialActual.upperRational-JointHMotherPayment.unroundedCoefficient ∧
    0 ≤ (GammaFullUpper.gammaUpper-Gamma6)/4 ∧
    0 ≤ U8ActualThreshold.gainUpper-2*(U8CanonicalMother.L-U8CanonicalMother.I) := by
  refine ⟨sub_pos.mpr MiddleInitialActual.actual_upper,?_,?_⟩
  · linarith only [GammaFullUpper.gamma_upper]
  · linarith only [CorrectedCoefficientUpper.small_correction_interval.2]

/-- The improved upper certificate, not the actual coefficient, exceeds target. -/
theorem certificate_above_target : 8*log (5000/4469) < upperCoefficient := by
  have ht := log_le_V (by norm_num : (1:ℝ) ≤ 5000/4469)
  have hp : 8*V (5000/4469) < (899110/1000000:ℝ) := by
    norm_num [V,lowerLog,upperLog]
  linarith only [ht,hp,upper_bounds.1]

theorem target_inside_corridor : JJointPayment.coefficient < 8*log (5000/4469) ∧
    8*log (5000/4469) < upperCoefficient :=
  ⟨JJointPayment.certificate_below_target,certificate_above_target⟩

def budget : ℝ := 4*(8*lowerLog (5000/4469)-892230/1000000-4979/1000000)+47/481250

theorem budget_exact : budget = 65346038131997983/16343425342648250000 := by
  norm_num [budget,lowerLog]

/-- Exact shortfall of this sufficient certificate; not an estimate of Gamma6. -/
theorem budget_shortfall : GammaFullUpper.gammaUpper-budget =
    3416781944956460156750770692661002167567/918949639534698102715284382388491200000000 := by
  rw [GammaFullUpper.gamma_upper_exact,budget_exact]
  norm_num

theorem cap_remaining_exact : rationalCap-8*lowerLog (5000/4469) =
    3416781944956460156750770692661002167567/3675798558138792410861137529553964800000000 := by
  rw [cap_exact]
  norm_num [lowerLog]

/-- Both signs remain unresolved: this records exactly what is still unpaid. -/
theorem actual_target_iff : U8CanonicalMother.improvedCoefficient < 8*log (5000/4469) ↔
    upperCoefficient-8*log (5000/4469) < upperSlack := by
  rw [← actual_remaining_identity]
  constructor <;> intro h <;> linarith only [h]

end GammaFullActual
