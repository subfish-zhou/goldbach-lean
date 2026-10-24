import WR2XiSixthPayments
import WR2XiSixthPanels06
noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
set_option maxHeartbeats 2000000 in
theorem grid_block_06 (j : Fin 32) : payment (32*6+j.val) ≤ panelBound (32*6+j.val) := by
  fin_cases j
  · convert panel_paid_192 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock06,panelBound,grid]
  · convert panel_paid_193 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock06,panelBound,grid]
  · convert panel_paid_194 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock06,panelBound,grid]
  · convert panel_paid_195 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock06,panelBound,grid]
  · convert panel_paid_196 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock06,panelBound,grid]
  · convert panel_paid_197 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock06,panelBound,grid]
  · convert panel_paid_198 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock06,panelBound,grid]
  · convert panel_paid_199 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock06,panelBound,grid]
  · convert panel_paid_200 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock06,panelBound,grid]
  · convert panel_paid_201 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock06,panelBound,grid]
  · convert panel_paid_202 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock06,panelBound,grid]
  · convert panel_paid_203 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock06,panelBound,grid]
  · convert panel_paid_204 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock06,panelBound,grid]
  · convert panel_paid_205 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock06,panelBound,grid]
  · convert panel_paid_206 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock06,panelBound,grid]
  · convert panel_paid_207 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock06,panelBound,grid]
  · convert panel_paid_208 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock06,panelBound,grid]
  · convert panel_paid_209 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock06,panelBound,grid]
  · convert panel_paid_210 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock06,panelBound,grid]
  · convert panel_paid_211 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock06,panelBound,grid]
  · convert panel_paid_212 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock06,panelBound,grid]
  · convert panel_paid_213 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock06,panelBound,grid]
  · convert panel_paid_214 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock06,panelBound,grid]
  · convert panel_paid_215 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock06,panelBound,grid]
  · convert panel_paid_216 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock06,panelBound,grid]
  · convert panel_paid_217 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock06,panelBound,grid]
  · convert panel_paid_218 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock06,panelBound,grid]
  · convert panel_paid_219 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock06,panelBound,grid]
  · convert panel_paid_220 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock06,panelBound,grid]
  · convert panel_paid_221 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock06,panelBound,grid]
  · convert panel_paid_222 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock06,panelBound,grid]
  · convert panel_paid_223 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock06,panelBound,grid]
end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.grid_block_06
