import CliF1AffinePaymentParent

noncomputable section
open Real Wu2008DoubleSieve
open F1JointFTC F1ActualSecondFTC F1BFullFTC F1JointSplit
namespace F1NextLedger

/-- The explicit analytic increment already proved in the affine payment. -/
def gain (x : ℝ) : ℝ := (x-1)^9/(210*x^4*(x+1)^5)

def splitGain (x : ℝ) : ℝ := gain ((1+x)/2) + gain (2*x/(1+x))

theorem splitPayment_exact (x : ℝ) :
    CliF1AffinePaymentParent.splitPayment x =
      F1SignedUpperFTC.splitPayment x + splitGain x := by
  unfold CliF1AffinePaymentParent.splitPayment CliF1AffinePaymentParent.payment
    F1SignedUpperFTC.splitPayment splitGain gain
  ring

theorem splitGain_pos {x : ℝ} (hx : 1 < x) : 0 < splitGain x := by
  have h := CliF1AffinePaymentParent.old_splitPayment_lt hx
  rw [splitPayment_exact] at h
  linarith only [h]

theorem weighted_mono {c x : ℝ} (hc : c ≤ 0) (hx : 1 ≤ x) :
    (-c)*F1SignedUpperFTC.splitPayment x ≤
      (-c)*CliF1AffinePaymentParent.splitPayment x :=
  mul_le_mul_of_nonneg_left (CliF1AffinePaymentParent.old_splitPayment_le hx)
    (neg_nonneg.mpr hc)

theorem weighted_exact (c x : ℝ) :
    (-c)*CliF1AffinePaymentParent.splitPayment x =
      (-c)*F1SignedUpperFTC.splitPayment x + (-c)*splitGain x := by
  rw [splitPayment_exact]
  ring

/-- A concrete common positive increment, not an assumed unpaid deficit. -/
def guaranteed : ℝ := min
  ((-WholeCommonLog.coeffThreeHalf)*splitGain (3/2))
  ((-TailWholeCommonLog.coeffThreeHalf)*splitGain (3/2))

theorem guaranteed_pos : 0 < guaranteed := by
  have ho : WholeCommonLog.coeffThreeHalf < 0 := by
    rw [WholeCommonLog.coeffThreeHalf_exact]
    norm_num
  have hn : TailWholeCommonLog.coeffThreeHalf < 0 := by
    rw [TailWholeCommonLog.coeffThreeHalf_exact]
    norm_num
  have hg := splitGain_pos (by norm_num : (1:ℝ) < 3/2)
  exact lt_min (mul_pos (neg_pos.mpr ho) hg) (mul_pos (neg_pos.mpr hn) hg)

theorem old_ledger_gain :
    F1SignedUpperLedger.oldPayment +
      (-WholeCommonLog.coeffThreeHalf)*splitGain (3/2) ≤
        CliF1AffinePaymentParent.oldPayment := by
  obtain ⟨_, hxp, hym, _⟩ := cross_arguments
  obtain ⟨hbxm, _, _, _⟩ := b_cross_arguments
  have h0 := weighted_exact WholeCommonLog.coeffThreeHalf (3/2)
  have h1 := weighted_mono WholeCommonLog.coeffD_sign (by norm_num : (1:ℝ) ≤ 4508/3981)
  have h2 := weighted_mono WholeCommonLog.poleZero_sign (by norm_num : (1:ℝ) ≤ 927/800)
  have h3 := weighted_mono WholeCommonLog.coeffAP_sign hxp
  have h4 := weighted_mono WholeCommonLog.coeffTM_sign hym
  have h5 := weighted_mono WholeCommonLog.coeffBM_sign hbxm
  unfold F1SignedUpperLedger.oldPayment CliF1AffinePaymentParent.oldPayment
  linarith only [h0, h1, h2, h3, h4, h5]

theorem new_ledger_gain :
    F1SignedUpperLedger.newPayment +
      (-TailWholeCommonLog.coeffThreeHalf)*splitGain (3/2) ≤
        CliF1AffinePaymentParent.newPayment := by
  obtain ⟨hxm, _, _, _⟩ := cross_arguments
  obtain ⟨_, hbxp, _, hbyp⟩ := b_cross_arguments
  have h0 := weighted_exact TailWholeCommonLog.coeffThreeHalf (3/2)
  have h1 := weighted_mono TailWholeCommonLog.coeffA_sign (by norm_num : (1:ℝ) ≤ 3884129/3606400)
  have h2 := weighted_mono TailWholeCommonLog.coeffAC_sign (by norm_num : (1:ℝ) ≤ 4508/2927)
  have h3 := weighted_mono (neg_nonpos.mpr TailWholeCommonLog.coeffB_sign)
    (by norm_num : (1:ℝ) ≤ 2400/2381)
  have h4 := weighted_mono TailWholeCommonLog.coeffS_sign (by norm_num : (1:ℝ) ≤ 2254/1727)
  have h5 := weighted_mono TailWholeCommonLog.poleOne_sign (by norm_num : (1:ℝ) ≤ 727/600)
  have h6 := weighted_mono TailWholeCommonLog.coeffAM_sign hxm
  have h7 := weighted_mono TailWholeCommonLog.coeffBP_sign hbxp
  have h8 := weighted_mono TailWholeCommonLog.coeffDP_sign hbyp
  unfold F1SignedUpperLedger.newPayment CliF1AffinePaymentParent.newPayment
  linarith only [h0, h1, h2, h3, h4, h5, h6, h7, h8]

theorem old_ledger_plus_guaranteed :
    F1SignedUpperLedger.oldPayment + guaranteed ≤ CliF1AffinePaymentParent.oldPayment := by
  have hg : guaranteed ≤ (-WholeCommonLog.coeffThreeHalf)*splitGain (3/2) := min_le_left _ _
  linarith only [old_ledger_gain, hg]

theorem new_ledger_plus_guaranteed :
    F1SignedUpperLedger.newPayment + guaranteed ≤ CliF1AffinePaymentParent.newPayment := by
  have hg : guaranteed ≤ (-TailWholeCommonLog.coeffThreeHalf)*splitGain (3/2) := min_le_right _ _
  linarith only [new_ledger_gain, hg]

/-- All three original max branches improve by the same proved explicit amount. -/
theorem original_finite_plus_guaranteed :
    F1SignedUpperWhole.finite + guaranteed ≤ CliF1AffinePaymentParent.finite := by
  have ho : WholeCommonLog.lower + TailEndpointPayment.recovery +
      CliF1AffinePaymentParent.oldPayment ≤ CliF1AffinePaymentParent.finite :=
    (le_max_left _ _).trans (le_max_left _ _)
  have hn : TailWholeCommonLog.lower + TailWholeCommonLog.recovery +
      CliF1AffinePaymentParent.newPayment ≤ CliF1AffinePaymentParent.finite :=
    (le_max_right _ _).trans (le_max_left _ _)
  have hp : F1TailFixedWhole.paid + CliF1AffinePaymentParent.oldPayment ≤
      CliF1AffinePaymentParent.finite := le_max_right _ _
  apply (le_sub_iff_add_le).mp
  unfold F1SignedUpperWhole.finite F1SignedUpperWhole.oldBase F1SignedUpperWhole.newBase
  refine max_le (max_le ?_ ?_) ?_
  · linarith only [ho, old_ledger_plus_guaranteed]
  · linarith only [hn, new_ledger_plus_guaranteed]
  · linarith only [hp, old_ledger_plus_guaranteed]

theorem original_finite_strict_improvement :
    F1SignedUpperWhole.finite < CliF1AffinePaymentParent.finite := by
  linarith only [original_finite_plus_guaranteed, guaranteed_pos]

theorem original_finite_gain_le_actual :
    8*(F1SignedUpperWhole.finite + guaranteed) ≤ Wu08TerminalAlignment.firstMain := by
  linarith only [original_finite_plus_guaranteed, CliF1AffinePaymentParent.finite_le_actual]

/-- The concrete gain is now exposed at the original counting conclusion. -/
theorem actual_count {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (8*(F1SignedUpperWhole.finite+guaranteed)-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        (sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ) := by
  have he : 0 < Wu08TerminalAlignment.firstMain -
      8*(F1SignedUpperWhole.finite+guaranteed) + ε := by
    linarith only [original_finite_gain_le_actual, hε]
  obtain ⟨T, hT, hcount⟩ := Wu08TerminalAlignment.first_actual_count he
  refine ⟨T, hT, ?_⟩
  intro N hN hEven
  convert hcount N hN hEven using 1
  ring

end F1NextLedger
