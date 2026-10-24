import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints137
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_137 (j : Fin 16) : lowerPayment (16*137+j.val) ≤
    lowerValue ((point 2 split 4096 (16*137+j.val)+point 2 split 4096 (16*137+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2192 ≤ lowerValue ((point 2 split 4096 2192+point 2 split 4096 2193)/2)
    have hp : lowerPayment 2192 = (250030996421:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2192+point 2 split 4096 2193)/2 = (93049967:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((93049967:ℝ)/33751040)/ClassicalSixthBranch.v ((93049967:ℝ)/33751040) = (644504946459:ℝ)/315321165208 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2192
  · change lowerPayment 2193 ≤ lowerValue ((point 2 split 4096 2193+point 2 split 4096 2194)/2)
    have hp : lowerPayment 2193 = (250120413536:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2193+point 2 split 4096 2194)/2 = (465308097:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((465308097:ℝ)/168755200)/ClassicalSixthBranch.v ((465308097:ℝ)/168755200) = (128885526557:ℝ)/63054631464 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2193
  · change lowerPayment 2194 ≤ lowerValue ((point 2 split 4096 2194+point 2 split 4096 2195)/2)
    have hp : lowerPayment 2194 = (250209823586:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2194+point 2 split 4096 2195)/2 = (465366359:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((465366359:ℝ)/168755200)/ClassicalSixthBranch.v ((465366359:ℝ)/168755200) = (644350319111:ℝ)/315225149432 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2194
  · change lowerPayment 2195 ≤ lowerValue ((point 2 split 4096 2195+point 2 split 4096 2196)/2)
    have hp : lowerPayment 2195 = (250299226588:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2195+point 2 split 4096 2196)/2 = (465424621:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((465424621:ℝ)/168755200)/ClassicalSixthBranch.v ((465424621:ℝ)/168755200) = (644273005437:ℝ)/315177141544 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2195
  · change lowerPayment 2196 ≤ lowerValue ((point 2 split 4096 2196+point 2 split 4096 2197)/2)
    have hp : lowerPayment 2196 = (250388622557:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2196+point 2 split 4096 2197)/2 = (465482883:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((465482883:ℝ)/168755200)/ClassicalSixthBranch.v ((465482883:ℝ)/168755200) = (644195691763:ℝ)/315129133656 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2196
  · change lowerPayment 2197 ≤ lowerValue ((point 2 split 4096 2197+point 2 split 4096 2198)/2)
    have hp : lowerPayment 2197 = (250478011509:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2197+point 2 split 4096 2198)/2 = (93108229:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((93108229:ℝ)/33751040)/ClassicalSixthBranch.v ((93108229:ℝ)/33751040) = (644118378089:ℝ)/315081125768 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2197
  · change lowerPayment 2198 ≤ lowerValue ((point 2 split 4096 2198+point 2 split 4096 2199)/2)
    have hp : lowerPayment 2198 = (250567393459:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2198+point 2 split 4096 2199)/2 = (465599407:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((465599407:ℝ)/168755200)/ClassicalSixthBranch.v ((465599407:ℝ)/168755200) = (128808212883:ℝ)/63006623576 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2198
  · change lowerPayment 2199 ≤ lowerValue ((point 2 split 4096 2199+point 2 split 4096 2200)/2)
    have hp : lowerPayment 2199 = (250656768423:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2199+point 2 split 4096 2200)/2 = (465657669:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((465657669:ℝ)/168755200)/ClassicalSixthBranch.v ((465657669:ℝ)/168755200) = (643963750741:ℝ)/314985109992 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2199
  · change lowerPayment 2200 ≤ lowerValue ((point 2 split 4096 2200+point 2 split 4096 2201)/2)
    have hp : lowerPayment 2200 = (250746136416:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2200+point 2 split 4096 2201)/2 = (465715931:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((465715931:ℝ)/168755200)/ClassicalSixthBranch.v ((465715931:ℝ)/168755200) = (643886437067:ℝ)/314937102104 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2200
  · change lowerPayment 2201 ≤ lowerValue ((point 2 split 4096 2201+point 2 split 4096 2202)/2)
    have hp : lowerPayment 2201 = (250835497454:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2201+point 2 split 4096 2202)/2 = (465774193:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((465774193:ℝ)/168755200)/ClassicalSixthBranch.v ((465774193:ℝ)/168755200) = (643809123393:ℝ)/314889094216 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2201
  · change lowerPayment 2202 ≤ lowerValue ((point 2 split 4096 2202+point 2 split 4096 2203)/2)
    have hp : lowerPayment 2202 = (250924851553:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2202+point 2 split 4096 2203)/2 = (93166491:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((93166491:ℝ)/33751040)/ClassicalSixthBranch.v ((93166491:ℝ)/33751040) = (643731809719:ℝ)/314841086328 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2202
  · change lowerPayment 2203 ≤ lowerValue ((point 2 split 4096 2203+point 2 split 4096 2204)/2)
    have hp : lowerPayment 2203 = (251014198728:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2203+point 2 split 4096 2204)/2 = (465890717:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((465890717:ℝ)/168755200)/ClassicalSixthBranch.v ((465890717:ℝ)/168755200) = (128730899209:ℝ)/62958615688 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2203
  · change lowerPayment 2204 ≤ lowerValue ((point 2 split 4096 2204+point 2 split 4096 2205)/2)
    have hp : lowerPayment 2204 = (251103538995:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2204+point 2 split 4096 2205)/2 = (465948979:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((465948979:ℝ)/168755200)/ClassicalSixthBranch.v ((465948979:ℝ)/168755200) = (643577182371:ℝ)/314745070552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2204
  · change lowerPayment 2205 ≤ lowerValue ((point 2 split 4096 2205+point 2 split 4096 2206)/2)
    have hp : lowerPayment 2205 = (251192872370:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2205+point 2 split 4096 2206)/2 = (466007241:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((466007241:ℝ)/168755200)/ClassicalSixthBranch.v ((466007241:ℝ)/168755200) = (643499868697:ℝ)/314697062664 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2205
  · change lowerPayment 2206 ≤ lowerValue ((point 2 split 4096 2206+point 2 split 4096 2207)/2)
    have hp : lowerPayment 2206 = (251282198867:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2206+point 2 split 4096 2207)/2 = (466065503:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((466065503:ℝ)/168755200)/ClassicalSixthBranch.v ((466065503:ℝ)/168755200) = (643422555023:ℝ)/314649054776 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2206
  · change lowerPayment 2207 ≤ lowerValue ((point 2 split 4096 2207+point 2 split 4096 2208)/2)
    have hp : lowerPayment 2207 = (251371518503:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2207+point 2 split 4096 2208)/2 = (93224753:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((93224753:ℝ)/33751040)/ClassicalSixthBranch.v ((93224753:ℝ)/33751040) = (643345241349:ℝ)/314601046888 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2207
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_137
