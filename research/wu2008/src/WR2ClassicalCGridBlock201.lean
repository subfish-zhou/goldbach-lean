import WR2ClassicalCPayments
import WR2ClassicalCPoints201
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_201 (j : Fin 16) : cPayment (16*201+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*201+j.val)+point (1327/200) 4096 (16*201+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3216 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3216+point (1327/200) 4096 3217)/2)
    have hp : cPayment 3216 = (29160511567:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3216+point (1327/200) 4096 3217)/2 = (6666991:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3216
  · change cPayment 3217 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3217+point (1327/200) 4096 3218)/2)
    have hp : cPayment 3217 = (29126378860:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3217+point (1327/200) 4096 3218)/2 = (1333609:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3217
  · change cPayment 3218 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3218+point (1327/200) 4096 3219)/2)
    have hp : cPayment 3218 = (29092247173:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3218+point (1327/200) 4096 3219)/2 = (6669099:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3218
  · change cPayment 3219 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3219+point (1327/200) 4096 3220)/2)
    have hp : cPayment 3219 = (29058116512:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3219+point (1327/200) 4096 3220)/2 = (6670153:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3219
  · change cPayment 3220 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3220+point (1327/200) 4096 3221)/2)
    have hp : cPayment 3220 = (29023986882:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3220+point (1327/200) 4096 3221)/2 = (6671207:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3220
  · change cPayment 3221 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3221+point (1327/200) 4096 3222)/2)
    have hp : cPayment 3221 = (28989858288:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3221+point (1327/200) 4096 3222)/2 = (6672261:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3221
  · change cPayment 3222 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3222+point (1327/200) 4096 3223)/2)
    have hp : cPayment 3222 = (28955730737:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3222+point (1327/200) 4096 3223)/2 = (1334663:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3222
  · change cPayment 3223 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3223+point (1327/200) 4096 3224)/2)
    have hp : cPayment 3223 = (28921604233:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3223+point (1327/200) 4096 3224)/2 = (6674369:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3223
  · change cPayment 3224 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3224+point (1327/200) 4096 3225)/2)
    have hp : cPayment 3224 = (28887478781:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3224+point (1327/200) 4096 3225)/2 = (6675423:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3224
  · change cPayment 3225 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3225+point (1327/200) 4096 3226)/2)
    have hp : cPayment 3225 = (28853354389:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3225+point (1327/200) 4096 3226)/2 = (6676477:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3225
  · change cPayment 3226 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3226+point (1327/200) 4096 3227)/2)
    have hp : cPayment 3226 = (28819231059:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3226+point (1327/200) 4096 3227)/2 = (6677531:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3226
  · change cPayment 3227 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3227+point (1327/200) 4096 3228)/2)
    have hp : cPayment 3227 = (28785108799:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3227+point (1327/200) 4096 3228)/2 = (1335717:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3227
  · change cPayment 3228 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3228+point (1327/200) 4096 3229)/2)
    have hp : cPayment 3228 = (28750987613:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3228+point (1327/200) 4096 3229)/2 = (6679639:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3228
  · change cPayment 3229 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3229+point (1327/200) 4096 3230)/2)
    have hp : cPayment 3229 = (28716867507:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3229+point (1327/200) 4096 3230)/2 = (6680693:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3229
  · change cPayment 3230 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3230+point (1327/200) 4096 3231)/2)
    have hp : cPayment 3230 = (28682748487:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3230+point (1327/200) 4096 3231)/2 = (6681747:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3230
  · change cPayment 3231 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3231+point (1327/200) 4096 3232)/2)
    have hp : cPayment 3231 = (28648630556:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3231+point (1327/200) 4096 3232)/2 = (6682801:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3231
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_201
