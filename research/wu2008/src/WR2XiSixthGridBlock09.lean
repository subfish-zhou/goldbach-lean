import WR2XiSixthPayments
import WR2XiSixthPanels09
noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
set_option maxHeartbeats 2000000 in
theorem grid_block_09 (j : Fin 32) : payment (32*9+j.val) ≤ panelBound (32*9+j.val) := by
  fin_cases j
  · convert panel_paid_288 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock09,panelBound,grid]
  · convert panel_paid_289 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock09,panelBound,grid]
  · convert panel_paid_290 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock09,panelBound,grid]
  · convert panel_paid_291 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock09,panelBound,grid]
  · convert panel_paid_292 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock09,panelBound,grid]
  · convert panel_paid_293 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock09,panelBound,grid]
  · convert panel_paid_294 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock09,panelBound,grid]
  · convert panel_paid_295 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock09,panelBound,grid]
  · convert panel_paid_296 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock09,panelBound,grid]
  · convert panel_paid_297 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock09,panelBound,grid]
  · convert panel_paid_298 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock09,panelBound,grid]
  · convert panel_paid_299 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock09,panelBound,grid]
  · convert panel_paid_300 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock09,panelBound,grid]
  · convert panel_paid_301 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock09,panelBound,grid]
  · convert panel_paid_302 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock09,panelBound,grid]
  · convert panel_paid_303 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock09,panelBound,grid]
  · convert panel_paid_304 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock09,panelBound,grid]
  · convert panel_paid_305 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock09,panelBound,grid]
  · convert panel_paid_306 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock09,panelBound,grid]
  · convert panel_paid_307 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock09,panelBound,grid]
  · convert panel_paid_308 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock09,panelBound,grid]
  · convert panel_paid_309 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock09,panelBound,grid]
  · convert panel_paid_310 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock09,panelBound,grid]
  · convert panel_paid_311 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock09,panelBound,grid]
  · convert panel_paid_312 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock09,panelBound,grid]
  · convert panel_paid_313 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock09,panelBound,grid]
  · convert panel_paid_314 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock09,panelBound,grid]
  · convert panel_paid_315 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock09,panelBound,grid]
  · convert panel_paid_316 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock09,panelBound,grid]
  · convert panel_paid_317 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock09,panelBound,grid]
  · convert panel_paid_318 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock09,panelBound,grid]
  · convert panel_paid_319 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock09,panelBound,grid]
end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.grid_block_09
