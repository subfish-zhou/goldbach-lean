import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints075
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_075 (j : Fin 16) : lowerPayment (16*75+j.val) ≤
    lowerValue ((point 2 split 4096 (16*75+j.val)+point 2 split 4096 (16*75+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1200 ≤ lowerValue ((point 2 split 4096 1200+point 2 split 4096 1201)/2)
    have hp : lowerPayment 1200 = (155030726428:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1200+point 2 split 4096 1201)/2 = (407453931:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((407453931:ℝ)/168755200)/ClassicalSixthBranch.v ((407453931:ℝ)/168755200) = (721200111067:ℝ)/362944990104 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1200
  · change lowerPayment 1201 ≤ lowerValue ((point 2 split 4096 1201+point 2 split 4096 1202)/2)
    have hp : lowerPayment 1201 = (155136014646:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1201+point 2 split 4096 1202)/2 = (407512193:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((407512193:ℝ)/168755200)/ClassicalSixthBranch.v ((407512193:ℝ)/168755200) = (721122797393:ℝ)/362896982216 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1201
  · change lowerPayment 1202 ≤ lowerValue ((point 2 split 4096 1202+point 2 split 4096 1203)/2)
    have hp : lowerPayment 1202 = (155241276318:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1202+point 2 split 4096 1203)/2 = (81514091:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((81514091:ℝ)/33751040)/ClassicalSixthBranch.v ((81514091:ℝ)/33751040) = (721045483719:ℝ)/362848974328 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1202
  · change lowerPayment 1203 ≤ lowerValue ((point 2 split 4096 1203+point 2 split 4096 1204)/2)
    have hp : lowerPayment 1203 = (155346511471:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1203+point 2 split 4096 1204)/2 = (407628717:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((407628717:ℝ)/168755200)/ClassicalSixthBranch.v ((407628717:ℝ)/168755200) = (144193634009:ℝ)/72560193288 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1203
  · change lowerPayment 1204 ≤ lowerValue ((point 2 split 4096 1204+point 2 split 4096 1205)/2)
    have hp : lowerPayment 1204 = (155451720129:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1204+point 2 split 4096 1205)/2 = (407686979:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((407686979:ℝ)/168755200)/ClassicalSixthBranch.v ((407686979:ℝ)/168755200) = (720890856371:ℝ)/362752958552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1204
  · change lowerPayment 1205 ≤ lowerValue ((point 2 split 4096 1205+point 2 split 4096 1206)/2)
    have hp : lowerPayment 1205 = (155556902319:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1205+point 2 split 4096 1206)/2 = (407745241:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((407745241:ℝ)/168755200)/ClassicalSixthBranch.v ((407745241:ℝ)/168755200) = (720813542697:ℝ)/362704950664 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1205
  · change lowerPayment 1206 ≤ lowerValue ((point 2 split 4096 1206+point 2 split 4096 1207)/2)
    have hp : lowerPayment 1206 = (155662058066:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1206+point 2 split 4096 1207)/2 = (407803503:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((407803503:ℝ)/168755200)/ClassicalSixthBranch.v ((407803503:ℝ)/168755200) = (720736229023:ℝ)/362656942776 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1206
  · change lowerPayment 1207 ≤ lowerValue ((point 2 split 4096 1207+point 2 split 4096 1208)/2)
    have hp : lowerPayment 1207 = (155767187396:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1207+point 2 split 4096 1208)/2 = (81572353:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((81572353:ℝ)/33751040)/ClassicalSixthBranch.v ((81572353:ℝ)/33751040) = (720658915349:ℝ)/362608934888 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1207
  · change lowerPayment 1208 ≤ lowerValue ((point 2 split 4096 1208+point 2 split 4096 1209)/2)
    have hp : lowerPayment 1208 = (155872290333:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1208+point 2 split 4096 1209)/2 = (407920027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((407920027:ℝ)/168755200)/ClassicalSixthBranch.v ((407920027:ℝ)/168755200) = (28823264067:ℝ)/14502437080 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1208
  · change lowerPayment 1209 ≤ lowerValue ((point 2 split 4096 1209+point 2 split 4096 1210)/2)
    have hp : lowerPayment 1209 = (155977366905:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1209+point 2 split 4096 1210)/2 = (407978289:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((407978289:ℝ)/168755200)/ClassicalSixthBranch.v ((407978289:ℝ)/168755200) = (720504288001:ℝ)/362512919112 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1209
  · change lowerPayment 1210 ≤ lowerValue ((point 2 split 4096 1210+point 2 split 4096 1211)/2)
    have hp : lowerPayment 1210 = (156082417136:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1210+point 2 split 4096 1211)/2 = (408036551:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((408036551:ℝ)/168755200)/ClassicalSixthBranch.v ((408036551:ℝ)/168755200) = (720426974327:ℝ)/362464911224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1210
  · change lowerPayment 1211 ≤ lowerValue ((point 2 split 4096 1211+point 2 split 4096 1212)/2)
    have hp : lowerPayment 1211 = (156187441052:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1211+point 2 split 4096 1212)/2 = (408094813:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((408094813:ℝ)/168755200)/ClassicalSixthBranch.v ((408094813:ℝ)/168755200) = (720349660653:ℝ)/362416903336 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1211
  · change lowerPayment 1212 ≤ lowerValue ((point 2 split 4096 1212+point 2 split 4096 1213)/2)
    have hp : lowerPayment 1212 = (156292438678:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1212+point 2 split 4096 1213)/2 = (16326123:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((16326123:ℝ)/6750208)/ClassicalSixthBranch.v ((16326123:ℝ)/6750208) = (720272346979:ℝ)/362368895448 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1212
  · change lowerPayment 1213 ≤ lowerValue ((point 2 split 4096 1213+point 2 split 4096 1214)/2)
    have hp : lowerPayment 1213 = (156397410040:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1213+point 2 split 4096 1214)/2 = (408211337:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((408211337:ℝ)/168755200)/ClassicalSixthBranch.v ((408211337:ℝ)/168755200) = (144039006661:ℝ)/72464177512 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1213
  · change lowerPayment 1214 ≤ lowerValue ((point 2 split 4096 1214+point 2 split 4096 1215)/2)
    have hp : lowerPayment 1214 = (156502355164:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1214+point 2 split 4096 1215)/2 = (408269599:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((408269599:ℝ)/168755200)/ClassicalSixthBranch.v ((408269599:ℝ)/168755200) = (720117719631:ℝ)/362272879672 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1214
  · change lowerPayment 1215 ≤ lowerValue ((point 2 split 4096 1215+point 2 split 4096 1216)/2)
    have hp : lowerPayment 1215 = (156607274075:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1215+point 2 split 4096 1216)/2 = (408327861:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((408327861:ℝ)/168755200)/ClassicalSixthBranch.v ((408327861:ℝ)/168755200) = (720040405957:ℝ)/362224871784 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1215
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_075
