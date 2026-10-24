import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints080
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_080 (j : Fin 16) : lowerPayment (16*80+j.val) ≤
    lowerValue ((point 2 split 4096 (16*80+j.val)+point 2 split 4096 (16*80+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1280 ≤ lowerValue ((point 2 split 4096 1280+point 2 split 4096 1281)/2)
    have hp : lowerPayment 1280 = (163371982579:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1280+point 2 split 4096 1281)/2 = (412114891:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((412114891:ℝ)/168755200)/ClassicalSixthBranch.v ((412114891:ℝ)/168755200) = (715015017147:ℝ)/359104359064 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1280
  · change lowerPayment 1281 ≤ lowerValue ((point 2 split 4096 1281+point 2 split 4096 1282)/2)
    have hp : lowerPayment 1281 = (163475226897:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1281+point 2 split 4096 1282)/2 = (412173153:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((412173153:ℝ)/168755200)/ClassicalSixthBranch.v ((412173153:ℝ)/168755200) = (714937703473:ℝ)/359056351176 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1281
  · change lowerPayment 1282 ≤ lowerValue ((point 2 split 4096 1282+point 2 split 4096 1283)/2)
    have hp : lowerPayment 1282 = (163578446670:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1282+point 2 split 4096 1283)/2 = (82446283:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((82446283:ℝ)/33751040)/ClassicalSixthBranch.v ((82446283:ℝ)/33751040) = (714860389799:ℝ)/359008343288 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1282
  · change lowerPayment 1283 ≤ lowerValue ((point 2 split 4096 1283+point 2 split 4096 1284)/2)
    have hp : lowerPayment 1283 = (163681641924:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1283+point 2 split 4096 1284)/2 = (412289677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((412289677:ℝ)/168755200)/ClassicalSixthBranch.v ((412289677:ℝ)/168755200) = (28591323045:ℝ)/14358413416 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1283
  · change lowerPayment 1284 ≤ lowerValue ((point 2 split 4096 1284+point 2 split 4096 1285)/2)
    have hp : lowerPayment 1284 = (163784812681:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1284+point 2 split 4096 1285)/2 = (412347939:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((412347939:ℝ)/168755200)/ClassicalSixthBranch.v ((412347939:ℝ)/168755200) = (714705762451:ℝ)/358912327512 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1284
  · change lowerPayment 1285 ≤ lowerValue ((point 2 split 4096 1285+point 2 split 4096 1286)/2)
    have hp : lowerPayment 1285 = (163887958967:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1285+point 2 split 4096 1286)/2 = (412406201:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((412406201:ℝ)/168755200)/ClassicalSixthBranch.v ((412406201:ℝ)/168755200) = (714628448777:ℝ)/358864319624 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1285
  · change lowerPayment 1286 ≤ lowerValue ((point 2 split 4096 1286+point 2 split 4096 1287)/2)
    have hp : lowerPayment 1286 = (163991080805:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1286+point 2 split 4096 1287)/2 = (412464463:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((412464463:ℝ)/168755200)/ClassicalSixthBranch.v ((412464463:ℝ)/168755200) = (714551135103:ℝ)/358816311736 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1286
  · change lowerPayment 1287 ≤ lowerValue ((point 2 split 4096 1287+point 2 split 4096 1288)/2)
    have hp : lowerPayment 1287 = (164094178220:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1287+point 2 split 4096 1288)/2 = (160203:ℝ)/65536 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((160203:ℝ)/65536)/ClassicalSixthBranch.v ((160203:ℝ)/65536) = (6936639043:ℝ)/3483187416 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1287
  · change lowerPayment 1288 ≤ lowerValue ((point 2 split 4096 1288+point 2 split 4096 1289)/2)
    have hp : lowerPayment 1288 = (164197251237:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1288+point 2 split 4096 1289)/2 = (412580987:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((412580987:ℝ)/168755200)/ClassicalSixthBranch.v ((412580987:ℝ)/168755200) = (142879301551:ℝ)/71744059192 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1288
  · change lowerPayment 1289 ≤ lowerValue ((point 2 split 4096 1289+point 2 split 4096 1290)/2)
    have hp : lowerPayment 1289 = (164300299879:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1289+point 2 split 4096 1290)/2 = (412639249:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((412639249:ℝ)/168755200)/ClassicalSixthBranch.v ((412639249:ℝ)/168755200) = (714319194081:ℝ)/358672288072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1289
  · change lowerPayment 1290 ≤ lowerValue ((point 2 split 4096 1290+point 2 split 4096 1291)/2)
    have hp : lowerPayment 1290 = (164403324170:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1290+point 2 split 4096 1291)/2 = (412697511:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((412697511:ℝ)/168755200)/ClassicalSixthBranch.v ((412697511:ℝ)/168755200) = (714241880407:ℝ)/358624280184 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1290
  · change lowerPayment 1291 ≤ lowerValue ((point 2 split 4096 1291+point 2 split 4096 1292)/2)
    have hp : lowerPayment 1291 = (164506324136:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1291+point 2 split 4096 1292)/2 = (412755773:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((412755773:ℝ)/168755200)/ClassicalSixthBranch.v ((412755773:ℝ)/168755200) = (714164566733:ℝ)/358576272296 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1291
  · change lowerPayment 1292 ≤ lowerValue ((point 2 split 4096 1292+point 2 split 4096 1293)/2)
    have hp : lowerPayment 1292 = (164609299800:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1292+point 2 split 4096 1293)/2 = (82562807:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((82562807:ℝ)/33751040)/ClassicalSixthBranch.v ((82562807:ℝ)/33751040) = (714087253059:ℝ)/358528264408 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1292
  · change lowerPayment 1293 ≤ lowerValue ((point 2 split 4096 1293+point 2 split 4096 1294)/2)
    have hp : lowerPayment 1293 = (164712251185:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1293+point 2 split 4096 1294)/2 = (412872297:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((412872297:ℝ)/168755200)/ClassicalSixthBranch.v ((412872297:ℝ)/168755200) = (142801987877:ℝ)/71696051304 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1293
  · change lowerPayment 1294 ≤ lowerValue ((point 2 split 4096 1294+point 2 split 4096 1295)/2)
    have hp : lowerPayment 1294 = (164815178318:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1294+point 2 split 4096 1295)/2 = (412930559:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((412930559:ℝ)/168755200)/ClassicalSixthBranch.v ((412930559:ℝ)/168755200) = (713932625711:ℝ)/358432248632 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1294
  · change lowerPayment 1295 ≤ lowerValue ((point 2 split 4096 1295+point 2 split 4096 1296)/2)
    have hp : lowerPayment 1295 = (164918081221:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1295+point 2 split 4096 1296)/2 = (412988821:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((412988821:ℝ)/168755200)/ClassicalSixthBranch.v ((412988821:ℝ)/168755200) = (713855312037:ℝ)/358384240744 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1295
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_080
