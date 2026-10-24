import WR2XiSixthPayments
import WR2XiSixthPanels00
noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
set_option maxHeartbeats 2000000 in
theorem grid_block_00 (j : Fin 32) : payment (32*0+j.val) ≤ panelBound (32*0+j.val) := by
  fin_cases j
  · convert panel_paid_0 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock00,panelBound,grid]
  · convert panel_paid_1 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock00,panelBound,grid]
  · convert panel_paid_2 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock00,panelBound,grid]
  · convert panel_paid_3 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock00,panelBound,grid]
  · convert panel_paid_4 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock00,panelBound,grid]
  · convert panel_paid_5 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock00,panelBound,grid]
  · convert panel_paid_6 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock00,panelBound,grid]
  · convert panel_paid_7 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock00,panelBound,grid]
  · convert panel_paid_8 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock00,panelBound,grid]
  · convert panel_paid_9 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock00,panelBound,grid]
  · convert panel_paid_10 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock00,panelBound,grid]
  · convert panel_paid_11 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock00,panelBound,grid]
  · convert panel_paid_12 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock00,panelBound,grid]
  · convert panel_paid_13 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock00,panelBound,grid]
  · convert panel_paid_14 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock00,panelBound,grid]
  · convert panel_paid_15 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock00,panelBound,grid]
  · convert panel_paid_16 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock00,panelBound,grid]
  · convert panel_paid_17 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock00,panelBound,grid]
  · convert panel_paid_18 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock00,panelBound,grid]
  · convert panel_paid_19 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock00,panelBound,grid]
  · convert panel_paid_20 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock00,panelBound,grid]
  · convert panel_paid_21 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock00,panelBound,grid]
  · convert panel_paid_22 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock00,panelBound,grid]
  · convert panel_paid_23 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock00,panelBound,grid]
  · convert panel_paid_24 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock00,panelBound,grid]
  · convert panel_paid_25 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock00,panelBound,grid]
  · convert panel_paid_26 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock00,panelBound,grid]
  · convert panel_paid_27 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock00,panelBound,grid]
  · convert panel_paid_28 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock00,panelBound,grid]
  · convert panel_paid_29 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock00,panelBound,grid]
  · convert panel_paid_30 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock00,panelBound,grid]
  · convert panel_paid_31 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock00,panelBound,grid]
end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.grid_block_00
