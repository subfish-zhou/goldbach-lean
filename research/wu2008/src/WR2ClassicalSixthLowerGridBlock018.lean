import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints018
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_018 (j : Fin 16) : lowerPayment (16*18+j.val) ≤
    lowerValue ((point 2 split 4096 (16*18+j.val)+point 2 split 4096 (16*18+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 288 ≤ lowerValue ((point 2 split 4096 288+point 2 split 4096 289)/2)
    have hp : lowerPayment 288 = (44064443904:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 288+point 2 split 4096 289)/2 = (354318987:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((354318987:ℝ)/168755200)/ClassicalSixthBranch.v ((354318987:ℝ)/168755200) = (158342036351:ℝ)/81345636792 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_288
  · change lowerPayment 289 ≤ lowerValue ((point 2 split 4096 289+point 2 split 4096 290)/2)
    have hp : lowerPayment 289 = (44207579882:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 289+point 2 split 4096 290)/2 = (354377249:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((354377249:ℝ)/168755200)/ClassicalSixthBranch.v ((354377249:ℝ)/168755200) = (791632868081:ℝ)/406680176072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_289
  · change lowerPayment 290 ≤ lowerValue ((point 2 split 4096 290+point 2 split 4096 291)/2)
    have hp : lowerPayment 290 = (44350655191:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 290+point 2 split 4096 291)/2 = (354435511:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((354435511:ℝ)/168755200)/ClassicalSixthBranch.v ((354435511:ℝ)/168755200) = (791555554407:ℝ)/406632168184 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_290
  · change lowerPayment 291 ≤ lowerValue ((point 2 split 4096 291+point 2 split 4096 292)/2)
    have hp : lowerPayment 291 = (44493669884:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 291+point 2 split 4096 292)/2 = (354493773:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((354493773:ℝ)/168755200)/ClassicalSixthBranch.v ((354493773:ℝ)/168755200) = (791478240733:ℝ)/406584160296 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_291
  · change lowerPayment 292 ≤ lowerValue ((point 2 split 4096 292+point 2 split 4096 293)/2)
    have hp : lowerPayment 292 = (44636624015:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 292+point 2 split 4096 293)/2 = (70910407:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((70910407:ℝ)/33751040)/ClassicalSixthBranch.v ((70910407:ℝ)/33751040) = (791400927059:ℝ)/406536152408 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_292
  · change lowerPayment 293 ≤ lowerValue ((point 2 split 4096 293+point 2 split 4096 294)/2)
    have hp : lowerPayment 293 = (44779517640:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 293+point 2 split 4096 294)/2 = (354610297:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((354610297:ℝ)/168755200)/ClassicalSixthBranch.v ((354610297:ℝ)/168755200) = (158264722677:ℝ)/81297628904 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_293
  · change lowerPayment 294 ≤ lowerValue ((point 2 split 4096 294+point 2 split 4096 295)/2)
    have hp : lowerPayment 294 = (44922350811:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 294+point 2 split 4096 295)/2 = (354668559:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((354668559:ℝ)/168755200)/ClassicalSixthBranch.v ((354668559:ℝ)/168755200) = (791246299711:ℝ)/406440136632 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_294
  · change lowerPayment 295 ≤ lowerValue ((point 2 split 4096 295+point 2 split 4096 296)/2)
    have hp : lowerPayment 295 = (45065123583:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 295+point 2 split 4096 296)/2 = (354726821:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((354726821:ℝ)/168755200)/ClassicalSixthBranch.v ((354726821:ℝ)/168755200) = (791168986037:ℝ)/406392128744 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_295
  · change lowerPayment 296 ≤ lowerValue ((point 2 split 4096 296+point 2 split 4096 297)/2)
    have hp : lowerPayment 296 = (45207836010:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 296+point 2 split 4096 297)/2 = (354785083:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((354785083:ℝ)/168755200)/ClassicalSixthBranch.v ((354785083:ℝ)/168755200) = (791091672363:ℝ)/406344120856 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_296
  · change lowerPayment 297 ≤ lowerValue ((point 2 split 4096 297+point 2 split 4096 298)/2)
    have hp : lowerPayment 297 = (45350488146:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 297+point 2 split 4096 298)/2 = (70968669:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((70968669:ℝ)/33751040)/ClassicalSixthBranch.v ((70968669:ℝ)/33751040) = (791014358689:ℝ)/406296112968 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_297
  · change lowerPayment 298 ≤ lowerValue ((point 2 split 4096 298+point 2 split 4096 299)/2)
    have hp : lowerPayment 298 = (45493080044:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 298+point 2 split 4096 299)/2 = (354901607:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((354901607:ℝ)/168755200)/ClassicalSixthBranch.v ((354901607:ℝ)/168755200) = (158187409003:ℝ)/81249621016 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_298
  · change lowerPayment 299 ≤ lowerValue ((point 2 split 4096 299+point 2 split 4096 300)/2)
    have hp : lowerPayment 299 = (45635611760:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 299+point 2 split 4096 300)/2 = (354959869:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((354959869:ℝ)/168755200)/ClassicalSixthBranch.v ((354959869:ℝ)/168755200) = (790859731341:ℝ)/406200097192 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_299
  · change lowerPayment 300 ≤ lowerValue ((point 2 split 4096 300+point 2 split 4096 301)/2)
    have hp : lowerPayment 300 = (45778083346:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 300+point 2 split 4096 301)/2 = (355018131:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((355018131:ℝ)/168755200)/ClassicalSixthBranch.v ((355018131:ℝ)/168755200) = (790782417667:ℝ)/406152089304 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_300
  · change lowerPayment 301 ≤ lowerValue ((point 2 split 4096 301+point 2 split 4096 302)/2)
    have hp : lowerPayment 301 = (45920494856:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 301+point 2 split 4096 302)/2 = (355076393:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((355076393:ℝ)/168755200)/ClassicalSixthBranch.v ((355076393:ℝ)/168755200) = (790705103993:ℝ)/406104081416 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_301
  · change lowerPayment 302 ≤ lowerValue ((point 2 split 4096 302+point 2 split 4096 303)/2)
    have hp : lowerPayment 302 = (46062846344:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 302+point 2 split 4096 303)/2 = (71026931:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((71026931:ℝ)/33751040)/ClassicalSixthBranch.v ((71026931:ℝ)/33751040) = (790627790319:ℝ)/406056073528 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_302
  · change lowerPayment 303 ≤ lowerValue ((point 2 split 4096 303+point 2 split 4096 304)/2)
    have hp : lowerPayment 303 = (46205137863:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 303+point 2 split 4096 304)/2 = (355192917:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((355192917:ℝ)/168755200)/ClassicalSixthBranch.v ((355192917:ℝ)/168755200) = (158110095329:ℝ)/81201613128 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_303
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_018
