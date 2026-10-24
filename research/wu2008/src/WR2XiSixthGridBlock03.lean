import WR2XiSixthPayments
import WR2XiSixthPanels03
noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
set_option maxHeartbeats 2000000 in
theorem grid_block_03 (j : Fin 32) : payment (32*3+j.val) ≤ panelBound (32*3+j.val) := by
  fin_cases j
  · convert panel_paid_96 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock03,panelBound,grid]
  · convert panel_paid_97 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock03,panelBound,grid]
  · convert panel_paid_98 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock03,panelBound,grid]
  · convert panel_paid_99 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock03,panelBound,grid]
  · convert panel_paid_100 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock03,panelBound,grid]
  · convert panel_paid_101 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock03,panelBound,grid]
  · convert panel_paid_102 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock03,panelBound,grid]
  · convert panel_paid_103 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock03,panelBound,grid]
  · convert panel_paid_104 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock03,panelBound,grid]
  · convert panel_paid_105 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock03,panelBound,grid]
  · convert panel_paid_106 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock03,panelBound,grid]
  · convert panel_paid_107 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock03,panelBound,grid]
  · convert panel_paid_108 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock03,panelBound,grid]
  · convert panel_paid_109 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock03,panelBound,grid]
  · convert panel_paid_110 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock03,panelBound,grid]
  · convert panel_paid_111 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock03,panelBound,grid]
  · convert panel_paid_112 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock03,panelBound,grid]
  · convert panel_paid_113 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock03,panelBound,grid]
  · convert panel_paid_114 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock03,panelBound,grid]
  · convert panel_paid_115 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock03,panelBound,grid]
  · convert panel_paid_116 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock03,panelBound,grid]
  · convert panel_paid_117 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock03,panelBound,grid]
  · convert panel_paid_118 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock03,panelBound,grid]
  · convert panel_paid_119 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock03,panelBound,grid]
  · convert panel_paid_120 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock03,panelBound,grid]
  · convert panel_paid_121 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock03,panelBound,grid]
  · convert panel_paid_122 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock03,panelBound,grid]
  · convert panel_paid_123 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock03,panelBound,grid]
  · convert panel_paid_124 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock03,panelBound,grid]
  · convert panel_paid_125 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock03,panelBound,grid]
  · convert panel_paid_126 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock03,panelBound,grid]
  · convert panel_paid_127 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock03,panelBound,grid]
end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.grid_block_03
