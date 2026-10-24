import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints206
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_206 (j : Fin 16) : lowerPayment (16*206+j.val) ≤
    lowerValue ((point 2 split 4096 (16*206+j.val)+point 2 split 4096 (16*206+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3296 ≤ lowerValue ((point 2 split 4096 3296+point 2 split 4096 3297)/2)
    have hp : lowerPayment 3296 = (347751500629:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3296+point 2 split 4096 3297)/2 = (529571083:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((529571083:ℝ)/168755200)/ClassicalSixthBranch.v ((529571083:ℝ)/168755200) = (559150650363:ℝ)/262320456856 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3296
  · change lowerPayment 3297 ≤ lowerValue ((point 2 split 4096 3297+point 2 split 4096 3298)/2)
    have hp : lowerPayment 3297 = (347842030206:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3297+point 2 split 4096 3298)/2 = (105925869:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((105925869:ℝ)/33751040)/ClassicalSixthBranch.v ((105925869:ℝ)/33751040) = (559073336689:ℝ)/262272448968 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3297
  · change lowerPayment 3298 ≤ lowerValue ((point 2 split 4096 3298+point 2 split 4096 3299)/2)
    have hp : lowerPayment 3298 = (347932568718:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3298+point 2 split 4096 3299)/2 = (529687607:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((529687607:ℝ)/168755200)/ClassicalSixthBranch.v ((529687607:ℝ)/168755200) = (111799204603:ℝ)/52444888216 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3298
  · change lowerPayment 3299 ≤ lowerValue ((point 2 split 4096 3299+point 2 split 4096 3300)/2)
    have hp : lowerPayment 3299 = (348023116180:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3299+point 2 split 4096 3300)/2 = (529745869:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((529745869:ℝ)/168755200)/ClassicalSixthBranch.v ((529745869:ℝ)/168755200) = (558918709341:ℝ)/262176433192 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3299
  · change lowerPayment 3300 ≤ lowerValue ((point 2 split 4096 3300+point 2 split 4096 3301)/2)
    have hp : lowerPayment 3300 = (348113672607:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3300+point 2 split 4096 3301)/2 = (529804131:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((529804131:ℝ)/168755200)/ClassicalSixthBranch.v ((529804131:ℝ)/168755200) = (558841395667:ℝ)/262128425304 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3300
  · change lowerPayment 3301 ≤ lowerValue ((point 2 split 4096 3301+point 2 split 4096 3302)/2)
    have hp : lowerPayment 3301 = (348204238013:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3301+point 2 split 4096 3302)/2 = (529862393:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((529862393:ℝ)/168755200)/ClassicalSixthBranch.v ((529862393:ℝ)/168755200) = (558764081993:ℝ)/262080417416 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3301
  · change lowerPayment 3302 ≤ lowerValue ((point 2 split 4096 3302+point 2 split 4096 3303)/2)
    have hp : lowerPayment 3302 = (348294812414:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3302+point 2 split 4096 3303)/2 = (105984131:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((105984131:ℝ)/33751040)/ClassicalSixthBranch.v ((105984131:ℝ)/33751040) = (558686768319:ℝ)/262032409528 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3302
  · change lowerPayment 3303 ≤ lowerValue ((point 2 split 4096 3303+point 2 split 4096 3304)/2)
    have hp : lowerPayment 3303 = (348385395824:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3303+point 2 split 4096 3304)/2 = (529978917:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((529978917:ℝ)/168755200)/ClassicalSixthBranch.v ((529978917:ℝ)/168755200) = (111721890929:ℝ)/52396880328 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3303
  · change lowerPayment 3304 ≤ lowerValue ((point 2 split 4096 3304+point 2 split 4096 3305)/2)
    have hp : lowerPayment 3304 = (348475988257:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3304+point 2 split 4096 3305)/2 = (530037179:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((530037179:ℝ)/168755200)/ClassicalSixthBranch.v ((530037179:ℝ)/168755200) = (558532140971:ℝ)/261936393752 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3304
  · change lowerPayment 3305 ≤ lowerValue ((point 2 split 4096 3305+point 2 split 4096 3306)/2)
    have hp : lowerPayment 3305 = (348566589730:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3305+point 2 split 4096 3306)/2 = (530095441:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((530095441:ℝ)/168755200)/ClassicalSixthBranch.v ((530095441:ℝ)/168755200) = (558454827297:ℝ)/261888385864 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3305
  · change lowerPayment 3306 ≤ lowerValue ((point 2 split 4096 3306+point 2 split 4096 3307)/2)
    have hp : lowerPayment 3306 = (348657200255:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3306+point 2 split 4096 3307)/2 = (530153703:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((530153703:ℝ)/168755200)/ClassicalSixthBranch.v ((530153703:ℝ)/168755200) = (558377513623:ℝ)/261840377976 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3306
  · change lowerPayment 3307 ≤ lowerValue ((point 2 split 4096 3307+point 2 split 4096 3308)/2)
    have hp : lowerPayment 3307 = (348747819849:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3307+point 2 split 4096 3308)/2 = (106042393:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((106042393:ℝ)/33751040)/ClassicalSixthBranch.v ((106042393:ℝ)/33751040) = (558300199949:ℝ)/261792370088 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3307
  · change lowerPayment 3308 ≤ lowerValue ((point 2 split 4096 3308+point 2 split 4096 3309)/2)
    have hp : lowerPayment 3308 = (348838448526:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3308+point 2 split 4096 3309)/2 = (530270227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((530270227:ℝ)/168755200)/ClassicalSixthBranch.v ((530270227:ℝ)/168755200) = (22328915451:ℝ)/10469774488 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3308
  · change lowerPayment 3309 ≤ lowerValue ((point 2 split 4096 3309+point 2 split 4096 3310)/2)
    have hp : lowerPayment 3309 = (348929086301:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3309+point 2 split 4096 3310)/2 = (530328489:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((530328489:ℝ)/168755200)/ClassicalSixthBranch.v ((530328489:ℝ)/168755200) = (558145572601:ℝ)/261696354312 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3309
  · change lowerPayment 3310 ≤ lowerValue ((point 2 split 4096 3310+point 2 split 4096 3311)/2)
    have hp : lowerPayment 3310 = (349019733188:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3310+point 2 split 4096 3311)/2 = (530386751:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((530386751:ℝ)/168755200)/ClassicalSixthBranch.v ((530386751:ℝ)/168755200) = (558068258927:ℝ)/261648346424 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3310
  · change lowerPayment 3311 ≤ lowerValue ((point 2 split 4096 3311+point 2 split 4096 3312)/2)
    have hp : lowerPayment 3311 = (349110389202:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3311+point 2 split 4096 3312)/2 = (530445013:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((530445013:ℝ)/168755200)/ClassicalSixthBranch.v ((530445013:ℝ)/168755200) = (557990945253:ℝ)/261600338536 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3311
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_206
