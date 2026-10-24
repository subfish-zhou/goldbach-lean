import WR2XiSixthPayments
import WR2XiSixthPanels02
noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
set_option maxHeartbeats 2000000 in
theorem grid_block_02 (j : Fin 32) : payment (32*2+j.val) ≤ panelBound (32*2+j.val) := by
  fin_cases j
  · convert panel_paid_64 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock02,panelBound,grid]
  · convert panel_paid_65 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock02,panelBound,grid]
  · convert panel_paid_66 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock02,panelBound,grid]
  · convert panel_paid_67 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock02,panelBound,grid]
  · convert panel_paid_68 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock02,panelBound,grid]
  · convert panel_paid_69 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock02,panelBound,grid]
  · convert panel_paid_70 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock02,panelBound,grid]
  · convert panel_paid_71 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock02,panelBound,grid]
  · convert panel_paid_72 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock02,panelBound,grid]
  · convert panel_paid_73 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock02,panelBound,grid]
  · convert panel_paid_74 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock02,panelBound,grid]
  · convert panel_paid_75 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock02,panelBound,grid]
  · convert panel_paid_76 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock02,panelBound,grid]
  · convert panel_paid_77 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock02,panelBound,grid]
  · convert panel_paid_78 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock02,panelBound,grid]
  · convert panel_paid_79 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock02,panelBound,grid]
  · convert panel_paid_80 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock02,panelBound,grid]
  · convert panel_paid_81 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock02,panelBound,grid]
  · convert panel_paid_82 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock02,panelBound,grid]
  · convert panel_paid_83 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock02,panelBound,grid]
  · convert panel_paid_84 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock02,panelBound,grid]
  · convert panel_paid_85 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock02,panelBound,grid]
  · convert panel_paid_86 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock02,panelBound,grid]
  · convert panel_paid_87 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock02,panelBound,grid]
  · convert panel_paid_88 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock02,panelBound,grid]
  · convert panel_paid_89 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock02,panelBound,grid]
  · convert panel_paid_90 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock02,panelBound,grid]
  · convert panel_paid_91 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock02,panelBound,grid]
  · convert panel_paid_92 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock02,panelBound,grid]
  · convert panel_paid_93 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock02,panelBound,grid]
  · convert panel_paid_94 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock02,panelBound,grid]
  · convert panel_paid_95 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock02,panelBound,grid]
end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.grid_block_02
