import WR2XiSixthPayments
import WR2XiSixthPanels01
noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
set_option maxHeartbeats 2000000 in
theorem grid_block_01 (j : Fin 32) : payment (32*1+j.val) ≤ panelBound (32*1+j.val) := by
  fin_cases j
  · convert panel_paid_32 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock01,panelBound,grid]
  · convert panel_paid_33 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock01,panelBound,grid]
  · convert panel_paid_34 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock01,panelBound,grid]
  · convert panel_paid_35 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock01,panelBound,grid]
  · convert panel_paid_36 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock01,panelBound,grid]
  · convert panel_paid_37 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock01,panelBound,grid]
  · convert panel_paid_38 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock01,panelBound,grid]
  · convert panel_paid_39 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock01,panelBound,grid]
  · convert panel_paid_40 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock01,panelBound,grid]
  · convert panel_paid_41 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock01,panelBound,grid]
  · convert panel_paid_42 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock01,panelBound,grid]
  · convert panel_paid_43 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock01,panelBound,grid]
  · convert panel_paid_44 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock01,panelBound,grid]
  · convert panel_paid_45 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock01,panelBound,grid]
  · convert panel_paid_46 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock01,panelBound,grid]
  · convert panel_paid_47 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock01,panelBound,grid]
  · convert panel_paid_48 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock01,panelBound,grid]
  · convert panel_paid_49 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock01,panelBound,grid]
  · convert panel_paid_50 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock01,panelBound,grid]
  · convert panel_paid_51 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock01,panelBound,grid]
  · convert panel_paid_52 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock01,panelBound,grid]
  · convert panel_paid_53 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock01,panelBound,grid]
  · convert panel_paid_54 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock01,panelBound,grid]
  · convert panel_paid_55 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock01,panelBound,grid]
  · convert panel_paid_56 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock01,panelBound,grid]
  · convert panel_paid_57 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock01,panelBound,grid]
  · convert panel_paid_58 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock01,panelBound,grid]
  · convert panel_paid_59 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock01,panelBound,grid]
  · convert panel_paid_60 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock01,panelBound,grid]
  · convert panel_paid_61 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock01,panelBound,grid]
  · convert panel_paid_62 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock01,panelBound,grid]
  · convert panel_paid_63 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock01,panelBound,grid]
end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.grid_block_01
