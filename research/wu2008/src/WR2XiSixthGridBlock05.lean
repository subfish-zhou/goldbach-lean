import WR2XiSixthPayments
import WR2XiSixthPanels05
noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
set_option maxHeartbeats 2000000 in
theorem grid_block_05 (j : Fin 32) : payment (32*5+j.val) ≤ panelBound (32*5+j.val) := by
  fin_cases j
  · convert panel_paid_160 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock05,panelBound,grid]
  · convert panel_paid_161 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock05,panelBound,grid]
  · convert panel_paid_162 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock05,panelBound,grid]
  · convert panel_paid_163 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock05,panelBound,grid]
  · convert panel_paid_164 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock05,panelBound,grid]
  · convert panel_paid_165 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock05,panelBound,grid]
  · convert panel_paid_166 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock05,panelBound,grid]
  · convert panel_paid_167 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock05,panelBound,grid]
  · convert panel_paid_168 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock05,panelBound,grid]
  · convert panel_paid_169 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock05,panelBound,grid]
  · convert panel_paid_170 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock05,panelBound,grid]
  · convert panel_paid_171 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock05,panelBound,grid]
  · convert panel_paid_172 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock05,panelBound,grid]
  · convert panel_paid_173 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock05,panelBound,grid]
  · convert panel_paid_174 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock05,panelBound,grid]
  · convert panel_paid_175 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock05,panelBound,grid]
  · convert panel_paid_176 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock05,panelBound,grid]
  · convert panel_paid_177 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock05,panelBound,grid]
  · convert panel_paid_178 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock05,panelBound,grid]
  · convert panel_paid_179 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock05,panelBound,grid]
  · convert panel_paid_180 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock05,panelBound,grid]
  · convert panel_paid_181 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock05,panelBound,grid]
  · convert panel_paid_182 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock05,panelBound,grid]
  · convert panel_paid_183 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock05,panelBound,grid]
  · convert panel_paid_184 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock05,panelBound,grid]
  · convert panel_paid_185 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock05,panelBound,grid]
  · convert panel_paid_186 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock05,panelBound,grid]
  · convert panel_paid_187 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock05,panelBound,grid]
  · convert panel_paid_188 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock05,panelBound,grid]
  · convert panel_paid_189 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock05,panelBound,grid]
  · convert panel_paid_190 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock05,panelBound,grid]
  · convert panel_paid_191 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock05,panelBound,grid]
end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.grid_block_05
