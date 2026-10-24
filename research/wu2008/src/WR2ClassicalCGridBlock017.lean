import WR2ClassicalCPayments
import WR2ClassicalCPoints017
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_017 (j : Fin 16) : cPayment (16*17+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*17+j.val)+point (1327/200) 4096 (16*17+j.val+1))/2) := by
  fin_cases j
  · change cPayment 272 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 272+point (1327/200) 4096 273)/2)
    have hp : cPayment 272 = (42591770048:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 272+point (1327/200) 4096 273)/2 = (712803:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_272
  · change cPayment 273 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 273+point (1327/200) 4096 274)/2)
    have hp : cPayment 273 = (42708337007:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 273+point (1327/200) 4096 274)/2 = (3565069:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_273
  · change cPayment 274 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 274+point (1327/200) 4096 275)/2)
    have hp : cPayment 274 = (42824657456:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 274+point (1327/200) 4096 275)/2 = (3566123:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_274
  · change cPayment 275 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 275+point (1327/200) 4096 276)/2)
    have hp : cPayment 275 = (42940731813:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 275+point (1327/200) 4096 276)/2 = (3567177:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_275
  · change cPayment 276 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 276+point (1327/200) 4096 277)/2)
    have hp : cPayment 276 = (43056560496:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 276+point (1327/200) 4096 277)/2 = (3568231:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_276
  · change cPayment 277 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 277+point (1327/200) 4096 278)/2)
    have hp : cPayment 277 = (43172143921:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 277+point (1327/200) 4096 278)/2 = (713857:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_277
  · change cPayment 278 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 278+point (1327/200) 4096 279)/2)
    have hp : cPayment 278 = (43287482502:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 278+point (1327/200) 4096 279)/2 = (3570339:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_278
  · change cPayment 279 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 279+point (1327/200) 4096 280)/2)
    have hp : cPayment 279 = (43402576656:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 279+point (1327/200) 4096 280)/2 = (3571393:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_279
  · change cPayment 280 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 280+point (1327/200) 4096 281)/2)
    have hp : cPayment 280 = (43517426795:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 280+point (1327/200) 4096 281)/2 = (3572447:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_280
  · change cPayment 281 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 281+point (1327/200) 4096 282)/2)
    have hp : cPayment 281 = (43632033332:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 281+point (1327/200) 4096 282)/2 = (3573501:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_281
  · change cPayment 282 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 282+point (1327/200) 4096 283)/2)
    have hp : cPayment 282 = (43746396680:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 282+point (1327/200) 4096 283)/2 = (714911:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_282
  · change cPayment 283 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 283+point (1327/200) 4096 284)/2)
    have hp : cPayment 283 = (43860517250:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 283+point (1327/200) 4096 284)/2 = (3575609:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_283
  · change cPayment 284 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 284+point (1327/200) 4096 285)/2)
    have hp : cPayment 284 = (43974395452:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 284+point (1327/200) 4096 285)/2 = (3576663:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_284
  · change cPayment 285 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 285+point (1327/200) 4096 286)/2)
    have hp : cPayment 285 = (44088031698:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 285+point (1327/200) 4096 286)/2 = (3577717:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_285
  · change cPayment 286 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 286+point (1327/200) 4096 287)/2)
    have hp : cPayment 286 = (44201426394:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 286+point (1327/200) 4096 287)/2 = (3578771:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_286
  · change cPayment 287 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 287+point (1327/200) 4096 288)/2)
    have hp : cPayment 287 = (44314579951:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 287+point (1327/200) 4096 288)/2 = (143193:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_287
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_017
