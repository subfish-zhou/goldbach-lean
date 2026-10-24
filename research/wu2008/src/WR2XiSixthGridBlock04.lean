import WR2XiSixthPayments
import WR2XiSixthPanels04
noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
set_option maxHeartbeats 2000000 in
theorem grid_block_04 (j : Fin 32) : payment (32*4+j.val) ≤ panelBound (32*4+j.val) := by
  fin_cases j
  · convert panel_paid_128 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock04,panelBound,grid]
  · convert panel_paid_129 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock04,panelBound,grid]
  · convert panel_paid_130 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock04,panelBound,grid]
  · convert panel_paid_131 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock04,panelBound,grid]
  · convert panel_paid_132 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock04,panelBound,grid]
  · convert panel_paid_133 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock04,panelBound,grid]
  · convert panel_paid_134 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock04,panelBound,grid]
  · convert panel_paid_135 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock04,panelBound,grid]
  · convert panel_paid_136 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock04,panelBound,grid]
  · convert panel_paid_137 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock04,panelBound,grid]
  · convert panel_paid_138 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock04,panelBound,grid]
  · convert panel_paid_139 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock04,panelBound,grid]
  · convert panel_paid_140 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock04,panelBound,grid]
  · convert panel_paid_141 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock04,panelBound,grid]
  · convert panel_paid_142 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock04,panelBound,grid]
  · convert panel_paid_143 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock04,panelBound,grid]
  · convert panel_paid_144 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock04,panelBound,grid]
  · convert panel_paid_145 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock04,panelBound,grid]
  · convert panel_paid_146 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock04,panelBound,grid]
  · convert panel_paid_147 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock04,panelBound,grid]
  · convert panel_paid_148 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock04,panelBound,grid]
  · convert panel_paid_149 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock04,panelBound,grid]
  · convert panel_paid_150 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock04,panelBound,grid]
  · convert panel_paid_151 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock04,panelBound,grid]
  · convert panel_paid_152 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock04,panelBound,grid]
  · convert panel_paid_153 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock04,panelBound,grid]
  · convert panel_paid_154 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock04,panelBound,grid]
  · convert panel_paid_155 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock04,panelBound,grid]
  · convert panel_paid_156 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock04,panelBound,grid]
  · convert panel_paid_157 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock04,panelBound,grid]
  · convert panel_paid_158 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock04,panelBound,grid]
  · convert panel_paid_159 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock04,panelBound,grid]
end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.grid_block_04
