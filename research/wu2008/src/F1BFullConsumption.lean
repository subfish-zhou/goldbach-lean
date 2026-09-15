import F1BFullIntegral

noncomputable section
open Real Set MeasureTheory FirstIntegralRecovery FirstCRationalPayment
open Wu2008DoubleSieve SharpLogRecurrence F1RemainingRecovery F1UnpaidRecovery
open F1SecondLogRecovery
open scoped Interval
namespace F1BFullFTC

theorem polynomial_lower {u : ℝ} (hu : u ∈ Icc 2 (927/200)) :
    polynomialOne u+polynomialTwo u ≤ kernelOne u+kernelTwo u := by
  have hw : 0 ≤ weight u := by
    unfold weight
    exact mul_nonneg (sub_nonneg.mpr hu.1) (pow_nonneg (sub_nonneg.mpr hu.2) _)
  obtain ⟨_,_,hd1,hd2⟩ := denominators_pos hu.1
  have h1 := mul_le_mul_of_nonneg_left (weighted_square_payment hw hd1 aOne)
    (by norm_num : (0:ℝ) ≤ 4)
  have h2 := mul_le_mul_of_nonneg_left (weighted_square_payment hw hd2 aTwo)
    (by norm_num : (0:ℝ) ≤ 4)
  unfold polynomialOne polynomialTwo kernelOne kernelTwo
  simp only [mul_div_assoc] at h1 h2 ⊢
  linarith only [h1,h2]

theorem exactMass_ge_old : secondPayment ≤ exactMass := by
  have hk1 := kernelOne_continuousOn.intervalIntegrable_of_Icc (μ := volume)
    (by norm_num : (2:ℝ) ≤ 927/200)
  have hk2 := kernelTwo_continuousOn.intervalIntegrable_of_Icc (μ := volume)
    (by norm_num : (2:ℝ) ≤ 927/200)
  have hp1 := polynomialOne_continuous.intervalIntegrable (μ := volume) 2 (927/200)
  have hp2 := polynomialTwo_continuous.intervalIntegrable (μ := volume) 2 (927/200)
  have h := intervalIntegral.integral_mono_on (by norm_num : (2:ℝ) ≤ 927/200)
    (hp1.add hp2) (hk1.add hk2) (fun _ hu => polynomial_lower hu)
  rw [intervalIntegral.integral_add hp1 hp2,intervalIntegral.integral_add hk1 hk2,
    polynomialOne_integral,polynomialTwo_integral,integral_one,integral_two] at h
  exact h

def cPayment : ℝ := F1JointFTC.exactMass+F1ActualSecondFTC.exactMass+exactMass

theorem cPayment_ge_previous : F1ActualSecondFTC.cPayment ≤ cPayment := by
  unfold cPayment F1ActualSecondFTC.cPayment
  linarith only [exactMass_ge_old]

theorem retained {u : ℝ} (hu : u ∈ Icc 2 (927/200)) :
    F1JointFTC.kernel u+F1ActualSecondFTC.kernel u+kernelOne u+kernelTwo u ≤
      cExactKernel (1327/200) u-cLowerKernel (1327/200) u := by
  have hb := second_rational_lower hu
  change kernelOne u+kernelTwo u ≤ secondExact u at hb
  linarith only [F1ActualSecondFTC.retained hu,hb]

theorem cPayment_le_actual : cPayment ≤ FirstActualRecovery.kernelRecovery := by
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
  have h := intervalIntegral.integral_mono_on (by norm_num : (2:ℝ) ≤ 927/200)
    (((ha1.add ha2).add hb1).add hb2) (h1.sub h2) (fun _ hu => retained hu)
  rw [intervalIntegral.integral_add ((ha1.add ha2).add hb1) hb2,
    intervalIntegral.integral_add (ha1.add ha2) hb1,intervalIntegral.integral_add ha1 ha2,
    F1JointFTC.kernel_integral,F1ActualSecondFTC.kernel_integral,integral_one,integral_two,
    intervalIntegral.integral_sub h1 h2] at h
  have he : FirstActualRecovery.kernelRecovery =
      (∫ u in (2:ℝ)..(927/200), cExactKernel (1327/200) u)-
        (∫ u in (2:ℝ)..(927/200), cLowerKernel (1327/200) u) := by
    unfold FirstActualRecovery.kernelRecovery
    rw [← cLowerMass_eq_endpointMass,C_flat (by norm_num : (4:ℝ) ≤ 1327/200)]
    norm_num [cLowerMass,cExactKernel]
  rw [← he] at h
  unfold cPayment exactMass
  linarith only [h]

/-- New B replaces, rather than duplicates, the old W-squared payment. -/
def jointMass : ℝ := F1TwoFactor.jointMass-secondPayment+exactMass

theorem jointMass_exact : jointMass = signedMainLogs+cPayment+EJoint.payment := by
  unfold jointMass cPayment
  rw [F1TwoFactor.jointMass_exact]
  unfold F1ActualSecondFTC.cPayment
  ring

theorem jointMass_le_actual : 8*jointMass ≤ Wu08TerminalAlignment.firstMain := by
  have hc := cPayment_le_actual
  have he := EJoint.payment_le
  rw [jointMass_exact,FirstActualRecovery.actual_first_recoveries,← finiteMainPayment_exact]
  unfold logRecovery
  linarith only [hc,he]

theorem previous_mass_le : F1TwoFactor.jointMass ≤ jointMass := by
  unfold jointMass
  linarith only [exactMass_ge_old]

end F1BFullFTC
