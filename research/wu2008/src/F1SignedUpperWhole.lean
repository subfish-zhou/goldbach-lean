import F1SignedUpperLedger

noncomputable section
open Real Wu2008DoubleSieve
namespace F1SignedUpperWhole
open F1SignedUpperLedger

/-- Unused old upper errors are subtracted only from the original endpoint balance. -/
def oldEndpointBalance : ℝ := TailEndpointPayment.endpointRemainder-oldPayment

theorem oldEndpointBalance_nonneg : 0 ≤ oldEndpointBalance :=
  sub_nonneg.mpr oldPayment_le_endpointRemainder

/-- The original fixed tail payment and its unpaid mass remain unchanged. -/
theorem old_firstMain_exact : Wu08TerminalAlignment.firstMain =
    8*(F1TailFixedWhole.paid+oldPayment+oldEndpointBalance+
      F1TailFixedWhole.unpaidMass+TailEndpointPayment.tailRemainder+FreshCommonLog.eLoss) := by
  rw [F1TailFixedWhole.paid_firstMain_exact]
  unfold oldEndpointBalance
  ring

def oldBase : ℝ := WholeCommonLog.lower+TailEndpointPayment.recovery

def newBase : ℝ := TailWholeCommonLog.lower+TailWholeCommonLog.recovery

/-- Exactly the old nested max, with the separately paid upper errors in each branch. -/
def finite : ℝ := max (max (oldBase+oldPayment) (newBase+newPayment))
  (F1TailFixedWhole.paid+oldPayment)

theorem oldBase_upper_le : oldBase+oldPayment ≤ TailWholeCommonLog.collected := by
  have hm : 0 ≤ ActualTailFinite.mass := by
    rw [← ActualTailFinite.mass_exact]
    exact ActualTailConsumption.mass_bounds.1
  rw [← TailWholeCommonLog.collected_exact]
  unfold oldBase
  linarith only [oldPayment_le_balance,hm]

theorem newBase_upper_le : newBase+newPayment ≤ TailWholeCommonLog.collected := by
  unfold newBase
  linarith only [newPayment_le_balance]

theorem oldPaid_upper_le : F1TailFixedWhole.paid+oldPayment ≤
    TailWholeCommonLog.collected := by
  rw [← TailWholeCommonLog.collected_exact]
  unfold F1TailFixedWhole.paid
  linarith only [oldPayment_le_balance,F1TailFixedWhole.payment_le_mass]

theorem finite_le_collected : finite ≤ TailWholeCommonLog.collected :=
  max_le (max_le oldBase_upper_le newBase_upper_le) oldPaid_upper_le

/-- A common positive lower bound for every original max branch, not a scalar test. -/
def guaranteed : ℝ := min oldPayment newPayment

theorem guaranteed_pos : 0 < guaranteed := lt_min oldPayment_pos newPayment_pos

theorem original_plus_guaranteed_le : F1TailFixedWhole.finite+guaranteed ≤ finite := by
  have ho : oldBase+oldPayment ≤ finite :=
    (le_max_left _ _).trans (le_max_left _ _)
  have hn : newBase+newPayment ≤ finite :=
    (le_max_right _ _).trans (le_max_left _ _)
  have hp : F1TailFixedWhole.paid+oldPayment ≤ finite := le_max_right _ _
  have hgo : guaranteed ≤ oldPayment := min_le_left _ _
  have hgn : guaranteed ≤ newPayment := min_le_right _ _
  apply (le_sub_iff_add_le).mp
  unfold F1TailFixedWhole.finite TailWholeCommonLog.finite
  refine max_le (max_le ?_ ?_) ?_
  · change oldBase ≤ finite-guaranteed
    linarith only [ho,hgo]
  · change newBase ≤ finite-guaranteed
    linarith only [hn,hgn]
  · linarith only [hp,hgo]

/-- Actual improvement of the full original max expression, including branch costs. -/
def payment : ℝ := finite-F1TailFixedWhole.finite

theorem guaranteed_le_payment : guaranteed ≤ payment := by
  unfold payment
  linarith only [original_plus_guaranteed_le]

theorem payment_pos : 0 < payment := guaranteed_pos.trans_le guaranteed_le_payment

theorem payment_le_original_branchLoss : payment ≤ F1TailFixedWhole.branchLoss := by
  unfold payment F1TailFixedWhole.branchLoss
  linarith only [finite_le_collected]

theorem strict_improvement : F1TailFixedWhole.finite < finite := by
  have h := payment_pos
  unfold payment at h
  linarith only [h]

/-- The exact original branch loss after the new payment, not a replacement baseline. -/
def endpointBalance : ℝ := F1TailFixedWhole.branchLoss-payment

theorem endpointBalance_nonneg : 0 ≤ endpointBalance :=
  sub_nonneg.mpr payment_le_original_branchLoss

theorem endpointBalance_exact : endpointBalance = TailWholeCommonLog.collected-finite := by
  unfold endpointBalance F1TailFixedWhole.branchLoss payment
  ring

/-- Original mother expression: all old tail and E balances occur exactly once. -/
theorem original_firstMain_exact : Wu08TerminalAlignment.firstMain =
    8*(F1TailFixedWhole.finite+payment+endpointBalance+
      TailEndpointPayment.tailRemainder+FreshCommonLog.eLoss) := by
  rw [F1TailFixedWhole.finite_firstMain_exact]
  unfold endpointBalance
  ring

theorem finite_firstMain_exact : Wu08TerminalAlignment.firstMain =
    8*(finite+endpointBalance+TailEndpointPayment.tailRemainder+FreshCommonLog.eLoss) := by
  rw [original_firstMain_exact]
  unfold payment
  ring

theorem finite_le_actual : 8*finite ≤ Wu08TerminalAlignment.firstMain := by
  rw [finite_firstMain_exact]
  linarith only [endpointBalance_nonneg,TailEndpointPayment.tailRemainder_nonneg,
    FreshCommonLog.eLoss_nonneg]

/-- An actual count at the proved expression; no unproved target-gap hypothesis. -/
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

end F1SignedUpperWhole
