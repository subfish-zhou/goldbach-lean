import FreshSignedPayment

noncomputable section
open Real Set MeasureTheory FirstIntegralRecovery FirstCRationalPayment
open F1BFullFTC F1SecondLogRecovery
open scoped Interval
namespace FreshRemainingFactors

def ratio (u : ℝ) : ℝ := ((1327:ℝ)/200-1)/(u+1)
def kept (x : ℝ) : ℝ := splitGap x+splitFresh x
def logTail (x : ℝ) : ℝ := log x-splitL x-kept x
/-- These factor differences were not paid by any of the eight kernels. -/
def factorA (u : ℝ) : ℝ := splitL (u-1)-linearA u
def factorB (u : ℝ) : ℝ := log (ratio u)-linearB u

def remainingA (u : ℝ) : ℝ :=
  logTail (u-1)/u*log (ratio u)+kept (u-1)/u*factorB u
def remainingB (u : ℝ) : ℝ :=
  factorA u/u*kept (ratio u)+splitL (u-1)/u*logTail (ratio u)

theorem remainingA_exact {u : ℝ} (hu : 2 ≤ u) :
    unpaidA u-freshA u = remainingA u := by
  have h := a_paid_identity hu
  unfold unpaidA freshA remainingA logTail kept factorB ratio
  linear_combination h

theorem remainingB_exact {u : ℝ} (hu : u ∈ Icc 2 (927/200)) :
    unpaidB u-freshB u = remainingB u := by
  have h := b_paid_identity hu
  unfold unpaidB freshB secondExact remainingB logTail kept factorA ratio
  linear_combination h

theorem tails_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ logTail x :=
  sub_nonneg.mpr (split_retained hx)

theorem factors_nonneg {u : ℝ} (hu : u ∈ Icc 2 (927/200)) :
    0 ≤ factorA u ∧ 0 ≤ factorB u := by
  have ha := splitL_linear hu.1
  have hb := F1RemainingRecovery.ratio_log_payment
    (show u ∈ Icc 2 ((1327:ℝ)/200-2) by constructor <;> linarith [hu.1,hu.2])
  constructor
  · exact sub_nonneg.mpr ha
  · exact sub_nonneg.mpr hb

theorem summands_nonneg {u : ℝ} (hu : u ∈ Icc 2 (927/200)) :
    0 ≤ logTail (u-1)/u*log (ratio u) ∧
    0 ≤ kept (u-1)/u*factorB u ∧
    0 ≤ factorA u/u*kept (ratio u) ∧
    0 ≤ splitL (u-1)/u*logTail (ratio u) := by
  have hx : 1 ≤ u-1 := by linarith [hu.1]
  have hr : 1 ≤ ratio u := ratio_ge_one
    (show u ∈ Icc 2 ((1327:ℝ)/200-2) by constructor <;> linarith [hu.1,hu.2])
  have hu0 : 0 ≤ u := by linarith [hu.1]
  have ha : 0 ≤ kept (u-1) := add_nonneg (gap_nonneg hx) (fresh_nonneg hx)
  have hb : 0 ≤ kept (ratio u) := add_nonneg (gap_nonneg hr) (fresh_nonneg hr)
  obtain ⟨hfa,hfb⟩ := factors_nonneg hu
  exact ⟨mul_nonneg (div_nonneg (tails_nonneg hx) hu0) (log_nonneg hr),
    mul_nonneg (div_nonneg ha hu0) hfb,mul_nonneg (div_nonneg hfa hu0) hb,
    mul_nonneg (div_nonneg (splitL_nonneg hx) hu0) (tails_nonneg hr)⟩

def mass : ℝ := (∫ u in (2:ℝ)..(927/200), remainingA u)+
  (∫ u in (2:ℝ)..(927/200), remainingB u)

theorem mass_exact : mass = FreshFTCJoint.remaining := by
  have ha := intervalIntegral.integral_congr (μ := volume) (a := (2:ℝ)) (b := (927/200))
    (fun u hu => remainingA_exact (u := u) (by
      rw [uIcc_of_le (by norm_num : (2:ℝ)≤927/200)] at hu
      exact hu.1))
  have hb := intervalIntegral.integral_congr (μ := volume) (a := (2:ℝ)) (b := (927/200))
    (fun u hu => remainingB_exact (u := u) (by
      rwa [uIcc_of_le (by norm_num : (2:ℝ)≤927/200)] at hu))
  rw [intervalIntegral.integral_sub
    (unpaid_continuousOn.1.intervalIntegrable_of_Icc (by norm_num))
    (F1FreshMass.fresh_continuousOn.1.intervalIntegrable_of_Icc (by norm_num))] at ha
  rw [intervalIntegral.integral_sub
    (unpaid_continuousOn.2.intervalIntegrable_of_Icc (by norm_num))
    (F1FreshMass.fresh_continuousOn.2.intervalIntegrable_of_Icc (by norm_num))] at hb
  unfold mass FreshFTCJoint.remaining unpaidMassA unpaidMassB F1FreshMass.massA F1FreshMass.massB
  rw [ha,hb]

theorem mass_nonneg : 0 ≤ mass := by
  rw [mass_exact]
  exact FreshFTCJoint.remaining_nonneg
end FreshRemainingFactors
