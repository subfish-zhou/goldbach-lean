import WR2XiSixthPayments
import WR2XiSixthPanels08
noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
set_option maxHeartbeats 2000000 in
theorem grid_block_08 (j : Fin 32) : payment (32*8+j.val) ≤ panelBound (32*8+j.val) := by
  fin_cases j
  · convert panel_paid_256 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock08,panelBound,grid]
  · convert panel_paid_257 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock08,panelBound,grid]
  · convert panel_paid_258 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock08,panelBound,grid]
  · convert panel_paid_259 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock08,panelBound,grid]
  · convert panel_paid_260 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock08,panelBound,grid]
  · convert panel_paid_261 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock08,panelBound,grid]
  · convert panel_paid_262 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock08,panelBound,grid]
  · convert panel_paid_263 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock08,panelBound,grid]
  · convert panel_paid_264 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock08,panelBound,grid]
  · convert panel_paid_265 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock08,panelBound,grid]
  · convert panel_paid_266 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock08,panelBound,grid]
  · convert panel_paid_267 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock08,panelBound,grid]
  · convert panel_paid_268 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock08,panelBound,grid]
  · convert panel_paid_269 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock08,panelBound,grid]
  · convert panel_paid_270 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock08,panelBound,grid]
  · convert panel_paid_271 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock08,panelBound,grid]
  · convert panel_paid_272 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock08,panelBound,grid]
  · convert panel_paid_273 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock08,panelBound,grid]
  · convert panel_paid_274 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock08,panelBound,grid]
  · convert panel_paid_275 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock08,panelBound,grid]
  · convert panel_paid_276 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock08,panelBound,grid]
  · convert panel_paid_277 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock08,panelBound,grid]
  · convert panel_paid_278 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock08,panelBound,grid]
  · convert panel_paid_279 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock08,panelBound,grid]
  · convert panel_paid_280 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock08,panelBound,grid]
  · convert panel_paid_281 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock08,panelBound,grid]
  · convert panel_paid_282 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock08,panelBound,grid]
  · convert panel_paid_283 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock08,panelBound,grid]
  · convert panel_paid_284 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock08,panelBound,grid]
  · convert panel_paid_285 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock08,panelBound,grid]
  · convert panel_paid_286 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock08,panelBound,grid]
  · convert panel_paid_287 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock08,panelBound,grid]
end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.grid_block_08
