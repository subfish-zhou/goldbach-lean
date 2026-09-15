import ActualTailVariation
noncomputable section
namespace ActualTailConsumption
open Real Set MeasureTheory FirstIntegralRecovery FirstCRationalPayment F1BFullFTC
open FreshRemainingFactors F1SecondLogRecovery
open scoped Interval

def splitFloor (x : ℝ) : ℝ := ActualTailVariation.floor ((1+x)/2)+
  ActualTailVariation.floor (2*x/(1+x))
def retained (x : ℝ) : ℝ := splitL x+kept x

theorem retained_eq (x : ℝ) : retained x=F1JointSplit.splitLow x := by
  unfold retained kept splitGap splitFresh splitL F1JointSplit.splitLow F1JointFTC.low
  ring

theorem splitFloor_le {x : ℝ} (hx : 1 ≤ x) : splitFloor x ≤ logTail x := by
  have ha := ActualTailVariation.floor_le (split_arguments hx).1
  have hb := ActualTailVariation.floor_le (split_arguments hx).2
  unfold splitFloor logTail kept splitL splitGap splitFresh
  rw [split_log_identity hx]
  linarith only [ha,hb]

theorem splitFloor_le_endpoint {x : ℝ} (hx : 1 ≤ x) :
    splitFloor x ≤ log x-F1JointSplit.splitLow x := by
  rw [← retained_eq]
  have he : logTail x=log x-retained x := by unfold logTail retained; ring
  rw [← he]
  exact splitFloor_le hx

theorem splitFloor_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ splitFloor x :=
  add_nonneg (ActualTailVariation.floor_nonneg (split_arguments hx).1)
    (ActualTailVariation.floor_nonneg (split_arguments hx).2)

theorem retained_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ retained x :=
  add_nonneg (splitL_nonneg hx) (add_nonneg (gap_nonneg hx) (fresh_nonneg hx))

theorem retained_le_log {x : ℝ} (hx : 1 ≤ x) : retained x ≤ log x := by
  rw [retained_eq]
  exact F1JointSplit.splitLow_le hx

def density (u : ℝ) : ℝ := splitFloor (u-1)/u*retained (ratio u)+
  retained (u-1)/u*splitFloor (ratio u)

theorem density_bounds {u : ℝ} (hu : u ∈ Icc 2 (927/200)) :
    0 ≤ density u ∧ density u ≤ F1FactorCross.tails u := by
  have hx : 1 ≤ u-1 := by linarith [hu.1]
  have hr : 1 ≤ ratio u := ratio_ge_one
    (show u ∈ Icc 2 ((1327:ℝ)/200-2) by constructor <;> linarith [hu.1,hu.2])
  have hu0 : 0 ≤ u := by linarith [hu.1]
  constructor
  · exact add_nonneg (mul_nonneg (div_nonneg (splitFloor_nonneg hx) hu0) (retained_nonneg hr))
      (mul_nonneg (div_nonneg (retained_nonneg hx) hu0) (splitFloor_nonneg hr))
  · apply add_le_add
    · exact mul_le_mul (div_le_div_of_nonneg_right (splitFloor_le hx) hu0)
        (retained_le_log hr) (retained_nonneg hr)
        (div_nonneg (FreshRemainingFactors.tails_nonneg hx) hu0)
    · exact mul_le_mul_of_nonneg_left (splitFloor_le hr)
        (div_nonneg (retained_nonneg hx) hu0)

theorem floor_continuousAt {x : ℝ} (hx : 1 ≤ x) : ContinuousAt splitFloor x := by
  have hx0 : 0<x := by linarith
  unfold splitFloor ActualTailVariation.floor ActualTailVariation.denominator
  fun_prop (disch := positivity)

theorem retained_continuousAt {x : ℝ} (hx : 1 ≤ x) : ContinuousAt retained x := by
  have hx0 : 0<x := by linarith
  unfold retained kept splitL splitGap splitFresh F1FullRecoveryPayment.lowerGapPayment
    Wu2008DoubleSieve.SharpLogRecurrence.lowerLog Wu2008DoubleSieve.SharpLogRecurrence.upperLog
    F1LowerResidual.payment F1LowerResidual.denom
  fun_prop (disch := positivity)

theorem density_continuous : ContinuousOn density (Icc 2 (927/200)) := by
  intro u hu
  have hx : 1 ≤ u-1 := by linarith [hu.1]
  have hr : 1 ≤ ratio u := ratio_ge_one
    (show u ∈ Icc 2 ((1327:ℝ)/200-2) by constructor <;> linarith [hu.1,hu.2])
  have hu0 : u ≠ 0 := by linarith [hu.1]
  have hu1 : u+1 ≠ 0 := by linarith [hu.1]
  have hc : ContinuousAt ratio u := by unfold ratio; fun_prop (disch := assumption)
  have fa : ContinuousAt (fun v : ℝ => splitFloor (v-1)) u :=
    (floor_continuousAt hx).comp (f := fun v : ℝ => v-1) (continuousAt_id.sub_const 1)
  have ra : ContinuousAt (fun v : ℝ => retained (v-1)) u :=
    (retained_continuousAt hx).comp (f := fun v : ℝ => v-1) (continuousAt_id.sub_const 1)
  exact (((fa.div continuousAt_id hu0).mul ((retained_continuousAt hr).comp hc)).add
    ((ra.div continuousAt_id hu0).mul ((floor_continuousAt hr).comp hc))).continuousWithinAt

def mass : ℝ := ∫ u in (2:ℝ)..(927/200),density u

theorem mass_bounds : 0 ≤ mass ∧ mass ≤ F1CrossMass.tailMass := by
  constructor
  · exact intervalIntegral.integral_nonneg (by norm_num) (fun u hu => (density_bounds hu).1)
  · exact intervalIntegral.integral_mono_on (by norm_num)
      (density_continuous.intervalIntegrable_of_Icc (by norm_num))
      (F1CrossMass.tails_continuousOn.intervalIntegrable_of_Icc (by norm_num))
      (fun u hu => (density_bounds hu).2)

theorem original_firstMain_lower : 8*(WholeCommonLog.collected+mass) ≤
    Wu08TerminalAlignment.firstMain := by
  rw [WholeCommonLog.firstMain_exact]
  linarith only [mass_bounds.2,FreshCommonLog.eLoss_nonneg]
end ActualTailConsumption
