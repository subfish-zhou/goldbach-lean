import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints079
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_079 (j : Fin 16) : lowerPayment (16*79+j.val) ≤
    lowerValue ((point 2 split 4096 (16*79+j.val)+point 2 split 4096 (16*79+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1264 ≤ lowerValue ((point 2 split 4096 1264+point 2 split 4096 1265)/2)
    have hp : lowerPayment 1264 = (161716715484:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1264+point 2 split 4096 1265)/2 = (411182699:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((411182699:ℝ)/168755200)/ClassicalSixthBranch.v ((411182699:ℝ)/168755200) = (716252035931:ℝ)/359872485272 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1264
  · change lowerPayment 1265 ≤ lowerValue ((point 2 split 4096 1265+point 2 split 4096 1266)/2)
    have hp : lowerPayment 1265 = (161820355841:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1265+point 2 split 4096 1266)/2 = (411240961:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((411240961:ℝ)/168755200)/ClassicalSixthBranch.v ((411240961:ℝ)/168755200) = (716174722257:ℝ)/359824477384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1265
  · change lowerPayment 1266 ≤ lowerValue ((point 2 split 4096 1266+point 2 split 4096 1267)/2)
    have hp : lowerPayment 1266 = (161923971261:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1266+point 2 split 4096 1267)/2 = (411299223:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((411299223:ℝ)/168755200)/ClassicalSixthBranch.v ((411299223:ℝ)/168755200) = (716097408583:ℝ)/359776469496 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1266
  · change lowerPayment 1267 ≤ lowerValue ((point 2 split 4096 1267+point 2 split 4096 1268)/2)
    have hp : lowerPayment 1267 = (162027561770:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1267+point 2 split 4096 1268)/2 = (82271497:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((82271497:ℝ)/33751040)/ClassicalSixthBranch.v ((82271497:ℝ)/33751040) = (716020094909:ℝ)/359728461608 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1267
  · change lowerPayment 1268 ≤ lowerValue ((point 2 split 4096 1268+point 2 split 4096 1269)/2)
    have hp : lowerPayment 1268 = (162131127392:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1268+point 2 split 4096 1269)/2 = (411415747:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((411415747:ℝ)/168755200)/ClassicalSixthBranch.v ((411415747:ℝ)/168755200) = (143188556247:ℝ)/71936090744 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1268
  · change lowerPayment 1269 ≤ lowerValue ((point 2 split 4096 1269+point 2 split 4096 1270)/2)
    have hp : lowerPayment 1269 = (162234668151:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1269+point 2 split 4096 1270)/2 = (411474009:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((411474009:ℝ)/168755200)/ClassicalSixthBranch.v ((411474009:ℝ)/168755200) = (715865467561:ℝ)/359632445832 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1269
  · change lowerPayment 1270 ≤ lowerValue ((point 2 split 4096 1270+point 2 split 4096 1271)/2)
    have hp : lowerPayment 1270 = (162338184072:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1270+point 2 split 4096 1271)/2 = (411532271:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((411532271:ℝ)/168755200)/ClassicalSixthBranch.v ((411532271:ℝ)/168755200) = (715788153887:ℝ)/359584437944 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1270
  · change lowerPayment 1271 ≤ lowerValue ((point 2 split 4096 1271+point 2 split 4096 1272)/2)
    have hp : lowerPayment 1271 = (162441675180:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1271+point 2 split 4096 1272)/2 = (411590533:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((411590533:ℝ)/168755200)/ClassicalSixthBranch.v ((411590533:ℝ)/168755200) = (715710840213:ℝ)/359536430056 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1271
  · change lowerPayment 1272 ≤ lowerValue ((point 2 split 4096 1272+point 2 split 4096 1273)/2)
    have hp : lowerPayment 1272 = (162545141498:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1272+point 2 split 4096 1273)/2 = (82329759:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((82329759:ℝ)/33751040)/ClassicalSixthBranch.v ((82329759:ℝ)/33751040) = (715633526539:ℝ)/359488422168 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1272
  · change lowerPayment 1273 ≤ lowerValue ((point 2 split 4096 1273+point 2 split 4096 1274)/2)
    have hp : lowerPayment 1273 = (162648583052:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1273+point 2 split 4096 1274)/2 = (411707057:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((411707057:ℝ)/168755200)/ClassicalSixthBranch.v ((411707057:ℝ)/168755200) = (143111242573:ℝ)/71888082856 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1273
  · change lowerPayment 1274 ≤ lowerValue ((point 2 split 4096 1274+point 2 split 4096 1275)/2)
    have hp : lowerPayment 1274 = (162751999866:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1274+point 2 split 4096 1275)/2 = (411765319:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((411765319:ℝ)/168755200)/ClassicalSixthBranch.v ((411765319:ℝ)/168755200) = (715478899191:ℝ)/359392406392 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1274
  · change lowerPayment 1275 ≤ lowerValue ((point 2 split 4096 1275+point 2 split 4096 1276)/2)
    have hp : lowerPayment 1275 = (162855391964:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1275+point 2 split 4096 1276)/2 = (411823581:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((411823581:ℝ)/168755200)/ClassicalSixthBranch.v ((411823581:ℝ)/168755200) = (715401585517:ℝ)/359344398504 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1275
  · change lowerPayment 1276 ≤ lowerValue ((point 2 split 4096 1276+point 2 split 4096 1277)/2)
    have hp : lowerPayment 1276 = (162958759372:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1276+point 2 split 4096 1277)/2 = (411881843:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((411881843:ℝ)/168755200)/ClassicalSixthBranch.v ((411881843:ℝ)/168755200) = (715324271843:ℝ)/359296390616 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1276
  · change lowerPayment 1277 ≤ lowerValue ((point 2 split 4096 1277+point 2 split 4096 1278)/2)
    have hp : lowerPayment 1277 = (163062102112:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1277+point 2 split 4096 1278)/2 = (82388021:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((82388021:ℝ)/33751040)/ClassicalSixthBranch.v ((82388021:ℝ)/33751040) = (715246958169:ℝ)/359248382728 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1277
  · change lowerPayment 1278 ≤ lowerValue ((point 2 split 4096 1278+point 2 split 4096 1279)/2)
    have hp : lowerPayment 1278 = (163165420211:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1278+point 2 split 4096 1279)/2 = (411998367:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((411998367:ℝ)/168755200)/ClassicalSixthBranch.v ((411998367:ℝ)/168755200) = (143033928899:ℝ)/71840074968 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1278
  · change lowerPayment 1279 ≤ lowerValue ((point 2 split 4096 1279+point 2 split 4096 1280)/2)
    have hp : lowerPayment 1279 = (163268713691:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1279+point 2 split 4096 1280)/2 = (412056629:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((412056629:ℝ)/168755200)/ClassicalSixthBranch.v ((412056629:ℝ)/168755200) = (715092330821:ℝ)/359152366952 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1279
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_079
