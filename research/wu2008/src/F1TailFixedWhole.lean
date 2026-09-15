import F1TailFixedAB11
import F1TailFixedAB12
import F1TailFixedAB21
import F1TailFixedAB22
import F1TailFixedBA11
import F1TailFixedBA12
import F1TailFixedBA21
import F1TailFixedBA22

noncomputable section
open Real Set MeasureTheory Polynomial Wu2008DoubleSieve
namespace F1TailFixedWhole

theorem AB11_monic : F1TailFixedAB11.D.Monic := by
  unfold F1TailFixedAB11.D
  monicity <;> norm_num

theorem AB12_monic : F1TailFixedAB12.D.Monic := by
  unfold F1TailFixedAB12.D
  monicity <;> norm_num

theorem AB21_monic : F1TailFixedAB21.D.Monic := by
  unfold F1TailFixedAB21.D
  monicity <;> norm_num

theorem AB22_monic : F1TailFixedAB22.D.Monic := by
  unfold F1TailFixedAB22.D
  monicity <;> norm_num

theorem BA11_monic : F1TailFixedBA11.D.Monic := by
  unfold F1TailFixedBA11.D
  monicity <;> norm_num

theorem BA12_monic : F1TailFixedBA12.D.Monic := by
  unfold F1TailFixedBA12.D
  monicity <;> norm_num

theorem BA21_monic : F1TailFixedBA21.D.Monic := by
  unfold F1TailFixedBA21.D
  monicity <;> norm_num

theorem BA22_monic : F1TailFixedBA22.D.Monic := by
  unfold F1TailFixedBA22.D
  monicity <;> norm_num

def payment : ℝ := F1TailFixedAB11.payment+F1TailFixedAB12.payment+F1TailFixedAB21.payment+F1TailFixedAB22.payment+F1TailFixedBA11.payment+F1TailFixedBA12.payment+F1TailFixedBA21.payment+F1TailFixedBA22.payment

theorem payment_le_mass : payment ≤ ActualTailFinite.mass := by
  unfold payment ActualTailFinite.mass
  exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (F1TailFixedAB11.payment_le_mass) F1TailFixedAB12.payment_le_mass) F1TailFixedAB21.payment_le_mass) F1TailFixedAB22.payment_le_mass) F1TailFixedBA11.payment_le_mass) F1TailFixedBA12.payment_le_mass) F1TailFixedBA21.payment_le_mass) F1TailFixedBA22.payment_le_mass

def unpaidMass : ℝ := ActualTailFinite.mass-payment

theorem unpaidMass_nonneg : 0 ≤ unpaidMass := sub_nonneg.mpr payment_le_mass

def paid : ℝ := WholeCommonLog.lower+TailEndpointPayment.recovery+payment

theorem paid_le_collected : paid ≤ TailWholeCommonLog.collected := by
  rw [← TailWholeCommonLog.collected_exact]
  unfold paid
  linarith only [TailEndpointPayment.recovery_le_loss,payment_le_mass]

/-- This branch accounts for the original endpoint, unpaid mass, tail and E once each. -/
theorem paid_firstMain_exact : Wu08TerminalAlignment.firstMain =
    8*(paid+TailEndpointPayment.endpointRemainder+unpaidMass+
      TailEndpointPayment.tailRemainder+FreshCommonLog.eLoss) := by
  rw [TailEndpointPayment.firstMain_exact]
  unfold paid TailEndpointPayment.paid unpaidMass
  rw [ActualTailFinite.mass_exact]
  ring

/-- Frozen before any scalar evaluation: retain the complete preceding max baseline. -/
def finite : ℝ := max TailWholeCommonLog.finite paid

theorem finite_le_collected : finite ≤ TailWholeCommonLog.collected :=
  max_le TailWholeCommonLog.finite_le_collected paid_le_collected

def branchLoss : ℝ := TailWholeCommonLog.collected-finite

theorem branchLoss_nonneg : 0 ≤ branchLoss := sub_nonneg.mpr finite_le_collected

/-- The max branch is paid by its own actual gap; no branch cost is discarded. -/
theorem finite_firstMain_exact : Wu08TerminalAlignment.firstMain =
    8*(finite+branchLoss+TailEndpointPayment.tailRemainder+FreshCommonLog.eLoss) := by
  rw [TailWholeCommonLog.firstMain_exact]
  unfold branchLoss
  ring

theorem finite_le_actual : 8*finite ≤ Wu08TerminalAlignment.firstMain := by
  rw [finite_firstMain_exact]
  linarith only [branchLoss_nonneg,TailEndpointPayment.tailRemainder_nonneg,
    FreshCommonLog.eLoss_nonneg]

def targetGap : ℝ := 8*finite-14900897/1000000

theorem original_target_of_gap (h : 0 ≤ targetGap) :
    (14900897:ℝ)/1000000 ≤ Wu08TerminalAlignment.firstMain := by
  unfold targetGap at h
  linarith only [h,finite_le_actual]

theorem actual_count {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (8*finite-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        (sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ) := by
  have he : 0 < Wu08TerminalAlignment.firstMain-8*finite+ε := by
    linarith only [finite_le_actual,hε]
  obtain ⟨T,hT,hcount⟩ := Wu08TerminalAlignment.first_actual_count he
  refine ⟨T,hT,?_⟩
  intro N hN hEven
  convert hcount N hN hEven using 1
  ring

theorem original_target_count_of_gap (h : 0 ≤ targetGap) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (14900897/1000000-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        (sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ) := by
  have he : 0 < Wu08TerminalAlignment.firstMain-14900897/1000000+ε := by
    linarith only [original_target_of_gap h,hε]
  obtain ⟨T,hT,hcount⟩ := Wu08TerminalAlignment.first_actual_count he
  refine ⟨T,hT,?_⟩
  intro N hN hEven
  convert hcount N hN hEven using 1
  ring

end F1TailFixedWhole
