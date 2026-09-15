import F1FreshConsumption
namespace FreshFTCJoint
open Real Wu2008DoubleSieve SharpLogRecurrence
noncomputable section

def exactMass : ℝ := F1FreshFTC.AOne.mass+F1FreshFTC.ATwo.mass+
  F1FreshFTC.BOne.mass+F1FreshFTC.BTwo.mass

theorem exactMass_eq : exactMass=F1FreshMass.massA+F1FreshMass.massB := by
  rw [F1FreshFTC.massA_exact,F1FreshFTC.massB_exact]
  unfold exactMass
  ring

theorem exactMass_nonneg : 0 ≤ exactMass := by
  rw [exactMass_eq]
  exact add_nonneg F1FreshMass.mass_bounds.1 F1FreshMass.mass_bounds.2.2.1

def remaining : ℝ := (F1BFullFTC.unpaidMassA-F1FreshMass.massA)+
  (F1BFullFTC.unpaidMassB-F1FreshMass.massB)

theorem remaining_nonneg : 0 ≤ remaining :=
  add_nonneg (sub_nonneg.mpr F1FreshMass.mass_bounds.2.1)
    (sub_nonneg.mpr F1FreshMass.mass_bounds.2.2.2)

theorem recovery_exact : FirstActualRecovery.kernelRecovery=
    F1BFullFTC.cPayment+exactMass+remaining := by
  rw [F1BFullFTC.residual_integral_exact,exactMass_eq]
  unfold remaining
  ring

/-- Complete old joint expression plus the four newly integrated genuine residual kernels. -/
def joint : ℝ := F1BFullFTC.collectedJoint+exactMass

theorem joint_le_actual : 8*joint ≤ Wu08TerminalAlignment.firstMain := by
  have h := F1FreshMass.joint_le_actual
  rw [F1BFullFTC.collectedJoint_exact] at h
  unfold joint
  rw [exactMass_eq]
  linarith only [h]

theorem actual_count {ε : ℝ} (hε : 0<ε) :
    ∃ T : ℕ, 4≤T ∧ ∀ N : ℕ, T≤N → Even N →
      (8*joint-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        (sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ) := by
  have he : 0<Wu08TerminalAlignment.firstMain-8*joint+ε := by
    linarith only [joint_le_actual,hε]
  obtain ⟨T,hT,h⟩ := Wu08TerminalAlignment.first_actual_count he
  refine ⟨T,hT,?_⟩
  intro N hN hEven
  have hid : Wu08TerminalAlignment.firstMain-(Wu08TerminalAlignment.firstMain-8*joint+ε)=
      8*joint-ε := by ring
  simpa only [hid] using h N hN hEven
end
end FreshFTCJoint
