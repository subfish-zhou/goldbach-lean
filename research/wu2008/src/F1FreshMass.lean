import F1BFullFresh
namespace F1FreshMass
open Real Set MeasureTheory FirstCRationalPayment F1BFullFTC
open Wu2008DoubleSieve SharpLogRecurrence
open scoped Interval
noncomputable section

theorem fresh_continuousOn : ContinuousOn freshA (Icc 2 (927/200)) ∧
    ContinuousOn freshB (Icc 2 (927/200)) := by
  constructor <;> intro u hu
  · have hu0 : 0<u := by linarith [hu.1]
    have hum : 0<u-1 := by linarith [hu.1]
    unfold freshA splitFresh F1LowerResidual.payment F1LowerResidual.denom linearB
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  · have hu0 : 0<u := by linarith [hu.1]
    have hut : 0<3*u-2 := by linarith [hu.1]
    have hk : 0<(1327:ℝ)/200-1 := by norm_num
    have hr : 0<((1327:ℝ)/200-1)/(u+1) := by positivity
    unfold freshB splitFresh F1LowerResidual.payment F1LowerResidual.denom linearA
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)

def massA : ℝ := ∫ u in (2:ℝ)..(927/200), freshA u
def massB : ℝ := ∫ u in (2:ℝ)..(927/200), freshB u

theorem mass_bounds : 0 ≤ massA ∧ massA ≤ unpaidMassA ∧ 0 ≤ massB ∧ massB ≤ unpaidMassB := by
  refine ⟨?_,?_,?_,?_⟩
  · exact intervalIntegral.integral_nonneg (by norm_num) (fun _ hu => (fresh_covers hu).1)
  · exact intervalIntegral.integral_mono_on (by norm_num)
      (fresh_continuousOn.1.intervalIntegrable_of_Icc (by norm_num))
      (unpaid_continuousOn.1.intervalIntegrable_of_Icc (by norm_num))
      (fun _ hu => (fresh_covers hu).2.1)
  · exact intervalIntegral.integral_nonneg (by norm_num) (fun _ hu => (fresh_covers hu).2.2.1)
  · exact intervalIntegral.integral_mono_on (by norm_num)
      (fresh_continuousOn.2.intervalIntegrable_of_Icc (by norm_num))
      (unpaid_continuousOn.2.intervalIntegrable_of_Icc (by norm_num))
      (fun _ hu => (fresh_covers hu).2.2.2)

theorem charged_once : cPayment+massA+massB ≤ FirstActualRecovery.kernelRecovery := by
  linarith only [mass_bounds.2.1,mass_bounds.2.2.2,residual_integral_exact]

theorem joint_le_actual : 8*(jointMass+massA+massB) ≤ Wu08TerminalAlignment.firstMain := by
  have hc := charged_once
  have he := EJoint.payment_le
  rw [jointMass_exact,FirstActualRecovery.actual_first_recoveries,← finiteMainPayment_exact]
  unfold logRecovery
  linarith only [hc,he]

def lower : ℝ := jointLower+massA+massB

theorem lower_le_actual : 8*lower ≤ Wu08TerminalAlignment.firstMain := by
  unfold lower
  linarith only [jointLower_le_mass,joint_le_actual]

theorem actual_count {ε : ℝ} (hε : 0<ε) :
    ∃ T : ℕ, 4≤T ∧ ∀ N : ℕ, T≤N → Even N →
      (8*lower-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        (sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ) := by
  have he : 0<Wu08TerminalAlignment.firstMain-8*lower+ε := by
    linarith only [lower_le_actual,hε]
  obtain ⟨T,hT,h⟩ := Wu08TerminalAlignment.first_actual_count he
  refine ⟨T,hT,?_⟩
  intro N hN hEven
  have hid : Wu08TerminalAlignment.firstMain-(Wu08TerminalAlignment.firstMain-8*lower+ε)=
      8*lower-ε := by ring
  simpa only [hid] using h N hN hEven
end
end F1FreshMass
