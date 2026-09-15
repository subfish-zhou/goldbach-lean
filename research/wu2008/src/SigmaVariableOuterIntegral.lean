import SigmaVariableOuterRational

noncomputable section
namespace SigmaVariableOuterPayment
open Real Set MeasureTheory SigmaVariableFull TerminalE
open Wu2008DoubleSieve SharpLogRecurrence JointLogTotalComparison F1FullRecoveryPayment
open Wu04FactorEnvelopes NodeExtension FirstFeedbackIntegrals OriginalProfileSigmaPayment
open Wu04WholeCollection OriginalSigmaStrength ActualNineFeedback
open scoped Interval BigOperators

theorem basicLower_continuousAt {x : ℝ} (hx : 0<x) :
    ContinuousAt RemainingHf.basicLower x := by
  unfold RemainingHf.basicLower lowerGapPayment lowerLog upperLog
    F1LowerResidual.payment F1LowerResidual.denom
  fun_prop (disch := positivity)

theorem basicUpper_continuousAt {x : ℝ} (hx : 0<x) :
    ContinuousAt RemainingHf.basicUpper x := by
  unfold RemainingHf.basicUpper V lowerLog upperLog upperGapPayment
  fun_prop (disch := positivity)

theorem splitLower_continuousAt {x : ℝ} (hx : 0<x) :
    ContinuousAt RemainingHf.splitLower x := by
  have hl : 0<leftFactor x := by unfold leftFactor; positivity
  have hr : 0<rightFactor x := by unfold rightFactor; positivity
  have hleft : ContinuousAt leftFactor x := by unfold leftFactor; fun_prop
  have hright : ContinuousAt rightFactor x := by
    unfold rightFactor
    fun_prop (disch := positivity)
  exact ((basicLower_continuousAt hl).comp hleft).add ((basicLower_continuousAt hr).comp hright)

theorem splitUpper_continuousAt {x : ℝ} (hx : 0<x) :
    ContinuousAt RemainingHf.splitUpper x := by
  have hl : 0<leftFactor x := by unfold leftFactor; positivity
  have hr : 0<rightFactor x := by unfold rightFactor; positivity
  have hleft : ContinuousAt leftFactor x := by unfold leftFactor; fun_prop
  have hright : ContinuousAt rightFactor x := by
    unfold rightFactor
    fun_prop (disch := positivity)
  exact ((basicUpper_continuousAt hl).comp hleft).add ((basicUpper_continuousAt hr).comp hright)

theorem paidWeight_continuousAt {t : ℝ} (ht : t ∈ Icc 1 3) :
    ContinuousAt paidWeight t := by
  have ht0 : 0<t := by linarith [ht.1]
  have ht1 : t+1 ≠ 0 := by linarith [ht.1]
  have hp : -(t+1) ≠ 0 := neg_ne_zero.mpr ht1
  have hp1 : -(t+1)+1 ≠ 0 := by linarith [ht.1]
  have hq : q (-(t+1)) ≠ 0 := (SigmaVariableFull.pole_quadratic ht).ne
  have hr : radical ≠ 0 := radical_pos.ne'
  have h5m : 0<5-radical := by linarith [radical_lt_four]
  have h9p : 0<t+9+2*radical := by linarith [radical_pos]
  have c0 : ContinuousAt zeroRatio t := by unfold zeroRatio; fun_prop
  have c1 : ContinuousAt negRatio t := by unfold negRatio; fun_prop (disch := positivity)
  have cq : ContinuousAt quadRatio t := by unfold quadRatio; fun_prop (disch := positivity)
  have cr : ContinuousAt radRatio t := by
    unfold radRatio
    fun_prop (disch := first | positivity | exact h5m.ne' | exact h9p.ne')
  have l0 := (splitUpper_continuousAt (lt_of_lt_of_le zero_lt_one (zeroRatio_ge ht.1))).comp c0
  have l1 := (splitLower_continuousAt (lt_of_lt_of_le zero_lt_one (negRatio_ge ht.1))).comp c1
  have lq := (splitLower_continuousAt (lt_of_lt_of_le zero_lt_one (quadRatio_ge ht.1))).comp cq
  have lr := (splitLower_continuousAt (lt_of_lt_of_le zero_lt_one (radRatio_ge ht.1))).comp cr
  unfold paidWeight paidMass logZeroCoeff logNegCoeff logQuadCoeff logRadCoeff jointRational
    zeroOne zeroTwo negOne negTwo negThree negFour quadOne quadZero TerminalE.residue
  unfold q at hq ⊢
  fun_prop (disch := first | assumption | positivity | linarith [radical_pos])

theorem paidWeight_continuous : ContinuousOn paidWeight (uIcc (1:ℝ) 3) := by
  rw [uIcc_of_le (by norm_num : (1:ℝ) ≤ 3)]
  intro t ht
  exact (paidWeight_continuousAt ht).continuousWithinAt

/-- The remaining outer rational integral; this is not a finite scalar payment. -/
def rationalCellMass (a b : ℝ) : ℝ := ∫ t in a..b,paidWeight t

def rationalNumerator (z : Fin 9 → ℝ) : ℝ :=
  ∑ k : Fin 9,z k*rationalCellMass (upperLeft k) (upperNode k)

theorem rationalNumerator_integral (z : Fin 9 → ℝ) :
    rationalNumerator z=∫ t in (1:ℝ)..3,nineProfile z t*paidWeight t := by
  rw [profile_integral_cells z le_rfl (by norm_num [upperNode]) paidWeight_continuous]
  apply Finset.sum_congr rfl
  intro k _
  have he : cellLeft 1 k=upperLeft k := by
    unfold cellLeft upperLeft
    split_ifs <;> rfl
  rw [he]
  rfl

/-- The lower numerator uses the identical original nine-cell profile. -/
theorem rationalNumerator_le {z : Fin 9 → ℝ} (hz : ∀ k,0 ≤ z k) :
    rationalNumerator z ≤ SigmaVariableFull.numerator z := by
  rw [rationalNumerator_integral,SigmaVariableFull.numerator_integral]
  apply intervalIntegral.integral_mono_on (by norm_num)
    ((nineProfile_integrable z).mul_continuousOn paidWeight_continuous)
    ((nineProfile_integrable z).mul_continuousOn SigmaVariableFull.weight_continuous)
  intro t ht
  exact mul_le_mul_of_nonneg_left (paidWeight_le ht) (nineProfile_nonneg hz t)

end SigmaVariableOuterPayment
