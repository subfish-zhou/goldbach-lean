import F1BFullJoint

noncomputable section
open Real Set MeasureTheory FirstIntegralRecovery FirstCRationalPayment
open Wu2008DoubleSieve SharpLogRecurrence F1RemainingRecovery F1UnpaidRecovery
open F1SecondLogRecovery
open scoped Interval
namespace F1BFullFTC

def unpaidA (u : ℝ) : ℝ :=
  (log (u-1)-splitL (u-1))/u*log (((1327:ℝ)/200-1)/(u+1))-
    F1JointFTC.kernel u-F1ActualSecondFTC.kernel u

def unpaidB (u : ℝ) : ℝ := secondExact u-kernelOne u-kernelTwo u

theorem unpaid_identity (u : ℝ) :
    cExactKernel (1327/200) u-cLowerKernel (1327/200) u =
      F1JointFTC.kernel u+F1ActualSecondFTC.kernel u+kernelOne u+kernelTwo u+
        unpaidA u+unpaidB u := by
  unfold unpaidA unpaidB cExactKernel cLowerKernel secondExact
  ring

theorem unpaid_nonneg {u : ℝ} (hu : u ∈ Icc 2 (927/200)) :
    0 ≤ unpaidA u ∧ 0 ≤ unpaidB u := by
  have ha := F1ActualSecondFTC.retained hu
  have hb := second_rational_lower hu
  constructor
  · unfold unpaidA
    unfold cExactKernel cLowerKernel secondExact at ha
    simp only [sub_div,mul_sub,sub_mul] at *
    linarith only [ha]
  · change 0 ≤ secondExact u-kernelOne u-kernelTwo u
    change kernelOne u+kernelTwo u ≤ secondExact u at hb
    linarith only [hb]

theorem unpaid_continuousOn : ContinuousOn unpaidA (Icc 2 (927/200)) ∧
    ContinuousOn unpaidB (Icc 2 (927/200)) := by
  have hn : ∀ u ∈ Icc (2:ℝ) (927/200), u ≠ 0 := fun u hu => by linarith [hu.1]
  have hn1 : ∀ u ∈ Icc (2:ℝ) (927/200), u+1 ≠ 0 := fun u hu => by linarith [hu.1]
  have hratio : ∀ u ∈ Icc (2:ℝ) (927/200), 1 ≤ ((1327:ℝ)/200-1)/(u+1) := by
    intro u hu
    apply ratio_ge_one
    constructor <;> linarith [hu.1,hu.2]
  have hL : ContinuousOn (fun u : ℝ => splitL (u-1)) (Icc 2 (927/200)) :=
    splitL_continuousOn.comp (continuousOn_id.sub continuousOn_const)
      (fun u hu => show 1 ≤ u-1 by linarith [hu.1])
  have hR : ContinuousOn (fun u : ℝ => ((1327:ℝ)/200-1)/(u+1)) (Icc 2 (927/200)) :=
    continuousOn_const.div (continuousOn_id.add continuousOn_const) hn1
  have hlogR := hR.log (fun u hu => ne_of_gt (lt_of_lt_of_le zero_lt_one (hratio u hu)))
  have hsplitR := splitL_continuousOn.comp hR (fun u hu => hratio u hu)
  have hlogL : ContinuousOn (fun u : ℝ => log (u-1)) (Icc 2 (927/200)) :=
    (continuousOn_id.sub continuousOn_const).log (fun u hu => show u-1 ≠ 0 by linarith [hu.1])
  exact ⟨((((hlogL.sub hL).div continuousOn_id hn).mul hlogR).sub
    F1JointFTC.kernel_continuousOn).sub F1ActualSecondFTC.kernel_continuousOn,
    ((((hL.div continuousOn_id hn).mul (hlogR.sub hsplitR))).sub kernelOne_continuousOn).sub
      kernelTwo_continuousOn⟩

def unpaidMassA : ℝ := ∫ u in (2:ℝ)..(927/200), unpaidA u
def unpaidMassB : ℝ := ∫ u in (2:ℝ)..(927/200), unpaidB u

theorem unpaidMass_nonneg : 0 ≤ unpaidMassA ∧ 0 ≤ unpaidMassB := by
  constructor
  · exact intervalIntegral.integral_nonneg (by norm_num) (fun _ hu => (unpaid_nonneg hu).1)
  · exact intervalIntegral.integral_nonneg (by norm_num) (fun _ hu => (unpaid_nonneg hu).2)

theorem residual_integral_exact : FirstActualRecovery.kernelRecovery =
    cPayment+unpaidMassA+unpaidMassB := by
  have h1 := ContinuousOn.intervalIntegrable_of_Icc (μ := volume)
    (by norm_num : (2:ℝ) ≤ (1327:ℝ)/200-2) (cExactKernel_continuousOn (1327/200))
  have h2 := ContinuousOn.intervalIntegrable_of_Icc (μ := volume)
    (by norm_num : (2:ℝ) ≤ (1327:ℝ)/200-2) (cLowerKernel_continuousOn (1327/200))
  norm_num at h1 h2
  have ha1 := F1JointFTC.kernel_continuousOn.intervalIntegrable_of_Icc (μ := volume)
    (by norm_num : (2:ℝ) ≤ 927/200)
  have ha2 := F1ActualSecondFTC.kernel_continuousOn.intervalIntegrable_of_Icc (μ := volume)
    (by norm_num : (2:ℝ) ≤ 927/200)
  have hb1 := kernelOne_continuousOn.intervalIntegrable_of_Icc (μ := volume)
    (by norm_num : (2:ℝ) ≤ 927/200)
  have hb2 := kernelTwo_continuousOn.intervalIntegrable_of_Icc (μ := volume)
    (by norm_num : (2:ℝ) ≤ 927/200)
  have hra := unpaid_continuousOn.1.intervalIntegrable_of_Icc (μ := volume)
    (by norm_num : (2:ℝ) ≤ 927/200)
  have hrb := unpaid_continuousOn.2.intervalIntegrable_of_Icc (μ := volume)
    (by norm_num : (2:ℝ) ≤ 927/200)
  have hi := intervalIntegral.integral_congr (μ := volume) (fun u _ => unpaid_identity u)
    (a := (2:ℝ)) (b := (927/200))
  rw [intervalIntegral.integral_sub h1 h2,
    intervalIntegral.integral_add ((((ha1.add ha2).add hb1).add hb2).add hra) hrb,
    intervalIntegral.integral_add (((ha1.add ha2).add hb1).add hb2) hra,
    intervalIntegral.integral_add ((ha1.add ha2).add hb1) hb2,
    intervalIntegral.integral_add (ha1.add ha2) hb1,intervalIntegral.integral_add ha1 ha2,
    F1JointFTC.kernel_integral,F1ActualSecondFTC.kernel_integral,integral_one,integral_two] at hi
  unfold FirstActualRecovery.kernelRecovery
  rw [← cLowerMass_eq_endpointMass,C_flat (by norm_num : (4:ℝ) ≤ 1327/200)]
  norm_num only [show (1327:ℝ)/200-2=927/200 by norm_num,cLowerMass] at *
  change _ = F1JointFTC.exactMass+F1ActualSecondFTC.exactMass+(massOne+massTwo)+unpaidMassA+unpaidMassB
  unfold unpaidMassA unpaidMassB
  convert hi using 1
  · unfold cExactKernel
    norm_num
  · ring

end F1BFullFTC
