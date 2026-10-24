import WR2XiSixthPayments
import WR2XiSixthPanels10
noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
set_option maxHeartbeats 2000000 in
theorem grid_block_10 (j : Fin 32) : payment (32*10+j.val) ≤ panelBound (32*10+j.val) := by
  fin_cases j
  · convert panel_paid_320 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock10,panelBound,grid]
  · convert panel_paid_321 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock10,panelBound,grid]
  · convert panel_paid_322 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock10,panelBound,grid]
  · convert panel_paid_323 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock10,panelBound,grid]
  · convert panel_paid_324 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock10,panelBound,grid]
  · convert panel_paid_325 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock10,panelBound,grid]
  · convert panel_paid_326 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock10,panelBound,grid]
  · convert panel_paid_327 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock10,panelBound,grid]
  · convert panel_paid_328 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock10,panelBound,grid]
  · convert panel_paid_329 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock10,panelBound,grid]
  · convert panel_paid_330 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock10,panelBound,grid]
  · convert panel_paid_331 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock10,panelBound,grid]
  · convert panel_paid_332 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock10,panelBound,grid]
  · convert panel_paid_333 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock10,panelBound,grid]
  · convert panel_paid_334 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock10,panelBound,grid]
  · convert panel_paid_335 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock10,panelBound,grid]
  · convert panel_paid_336 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock10,panelBound,grid]
  · convert panel_paid_337 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock10,panelBound,grid]
  · convert panel_paid_338 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock10,panelBound,grid]
  · convert panel_paid_339 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock10,panelBound,grid]
  · convert panel_paid_340 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock10,panelBound,grid]
  · convert panel_paid_341 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock10,panelBound,grid]
  · convert panel_paid_342 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock10,panelBound,grid]
  · convert panel_paid_343 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock10,panelBound,grid]
  · convert panel_paid_344 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock10,panelBound,grid]
  · convert panel_paid_345 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock10,panelBound,grid]
  · convert panel_paid_346 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock10,panelBound,grid]
  · convert panel_paid_347 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock10,panelBound,grid]
  · convert panel_paid_348 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock10,panelBound,grid]
  · convert panel_paid_349 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock10,panelBound,grid]
  · convert panel_paid_350 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock10,panelBound,grid]
  · convert panel_paid_351 using 1 <;> norm_num [payment,paymentNumerator,paymentBlock10,panelBound,grid]
end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.grid_block_10
