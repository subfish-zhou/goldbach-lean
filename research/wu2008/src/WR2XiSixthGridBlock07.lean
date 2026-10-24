import WR2XiSixthPayments
import WR2XiSixthPanels07
noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
set_option maxHeartbeats 2000000 in
theorem grid_block_07 (j : Fin 32) : payment (32*7+j.val) ≤ panelBound (32*7+j.val) := by
  fin_cases j
  · convert panel_paid_224 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock07,panelBound,grid]
  · convert panel_paid_225 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock07,panelBound,grid]
  · convert panel_paid_226 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock07,panelBound,grid]
  · convert panel_paid_227 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock07,panelBound,grid]
  · convert panel_paid_228 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock07,panelBound,grid]
  · convert panel_paid_229 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock07,panelBound,grid]
  · convert panel_paid_230 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock07,panelBound,grid]
  · convert panel_paid_231 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock07,panelBound,grid]
  · convert panel_paid_232 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock07,panelBound,grid]
  · convert panel_paid_233 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock07,panelBound,grid]
  · convert panel_paid_234 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock07,panelBound,grid]
  · convert panel_paid_235 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock07,panelBound,grid]
  · convert panel_paid_236 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock07,panelBound,grid]
  · convert panel_paid_237 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock07,panelBound,grid]
  · convert panel_paid_238 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock07,panelBound,grid]
  · convert panel_paid_239 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock07,panelBound,grid]
  · convert panel_paid_240 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock07,panelBound,grid]
  · convert panel_paid_241 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock07,panelBound,grid]
  · convert panel_paid_242 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock07,panelBound,grid]
  · convert panel_paid_243 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock07,panelBound,grid]
  · convert panel_paid_244 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock07,panelBound,grid]
  · convert panel_paid_245 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock07,panelBound,grid]
  · convert panel_paid_246 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock07,panelBound,grid]
  · convert panel_paid_247 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock07,panelBound,grid]
  · convert panel_paid_248 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock07,panelBound,grid]
  · convert panel_paid_249 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock07,panelBound,grid]
  · convert panel_paid_250 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock07,panelBound,grid]
  · convert panel_paid_251 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock07,panelBound,grid]
  · convert panel_paid_252 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock07,panelBound,grid]
  · convert panel_paid_253 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock07,panelBound,grid]
  · convert panel_paid_254 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock07,panelBound,grid]
  · convert panel_paid_255 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock07,panelBound,grid]
end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.grid_block_07
