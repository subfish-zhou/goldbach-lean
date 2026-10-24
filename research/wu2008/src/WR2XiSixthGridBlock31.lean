import WR2XiSixthPayments
import WR2XiSixthPanels31
noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
set_option maxHeartbeats 2000000 in
theorem grid_block_31 (j : Fin 32) : payment (32*31+j.val) ≤ panelBound (32*31+j.val) := by
  fin_cases j
  · convert panel_paid_992 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock31,panelBound,grid]
  · convert panel_paid_993 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock31,panelBound,grid]
  · convert panel_paid_994 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock31,panelBound,grid]
  · convert panel_paid_995 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock31,panelBound,grid]
  · convert panel_paid_996 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock31,panelBound,grid]
  · convert panel_paid_997 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock31,panelBound,grid]
  · convert panel_paid_998 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock31,panelBound,grid]
  · convert panel_paid_999 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock31,panelBound,grid]
  · convert panel_paid_1000 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock31,panelBound,grid]
  · convert panel_paid_1001 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock31,panelBound,grid]
  · convert panel_paid_1002 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock31,panelBound,grid]
  · convert panel_paid_1003 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock31,panelBound,grid]
  · convert panel_paid_1004 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock31,panelBound,grid]
  · convert panel_paid_1005 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock31,panelBound,grid]
  · convert panel_paid_1006 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock31,panelBound,grid]
  · convert panel_paid_1007 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock31,panelBound,grid]
  · convert panel_paid_1008 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock31,panelBound,grid]
  · convert panel_paid_1009 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock31,panelBound,grid]
  · convert panel_paid_1010 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock31,panelBound,grid]
  · convert panel_paid_1011 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock31,panelBound,grid]
  · convert panel_paid_1012 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock31,panelBound,grid]
  · convert panel_paid_1013 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock31,panelBound,grid]
  · convert panel_paid_1014 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock31,panelBound,grid]
  · convert panel_paid_1015 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock31,panelBound,grid]
  · convert panel_paid_1016 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock31,panelBound,grid]
  · convert panel_paid_1017 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock31,panelBound,grid]
  · convert panel_paid_1018 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock31,panelBound,grid]
  · convert panel_paid_1019 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock31,panelBound,grid]
  · convert panel_paid_1020 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock31,panelBound,grid]
  · convert panel_paid_1021 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock31,panelBound,grid]
  · convert panel_paid_1022 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock31,panelBound,grid]
  · convert panel_paid_1023 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock31,panelBound,grid]
end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.grid_block_31
