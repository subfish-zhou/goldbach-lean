import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints016
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_016 (j : Fin 16) : lowerPayment (16*16+j.val) ≤
    lowerValue ((point 2 split 4096 (16*16+j.val)+point 2 split 4096 (16*16+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 256 ≤ lowerValue ((point 2 split 4096 256+point 2 split 4096 257)/2)
    have hp : lowerPayment 256 = (39451731381:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 256+point 2 split 4096 257)/2 = (352454603:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((352454603:ℝ)/168755200)/ClassicalSixthBranch.v ((352454603:ℝ)/168755200) = (794184219323:ℝ)/408264436376 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_256
  · change lowerPayment 257 ≤ lowerValue ((point 2 split 4096 257+point 2 split 4096 258)/2)
    have hp : lowerPayment 257 = (39596837767:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 257+point 2 split 4096 258)/2 = (684491:ℝ)/327680 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((684491:ℝ)/327680)/ClassicalSixthBranch.v ((684491:ℝ)/327680) = (7709775783:ℝ)/3963266296 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_257
  · change lowerPayment 258 ≤ lowerValue ((point 2 split 4096 258+point 2 split 4096 259)/2)
    have hp : lowerPayment 258 = (39741881718:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 258+point 2 split 4096 259)/2 = (352571127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((352571127:ℝ)/168755200)/ClassicalSixthBranch.v ((352571127:ℝ)/168755200) = (31761183679:ℝ)/16326736824 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_258
  · change lowerPayment 259 ≤ lowerValue ((point 2 split 4096 259+point 2 split 4096 260)/2)
    have hp : lowerPayment 259 = (39886863290:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 259+point 2 split 4096 260)/2 = (352629389:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((352629389:ℝ)/168755200)/ClassicalSixthBranch.v ((352629389:ℝ)/168755200) = (793952278301:ℝ)/408120412712 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_259
  · change lowerPayment 260 ≤ lowerValue ((point 2 split 4096 260+point 2 split 4096 261)/2)
    have hp : lowerPayment 260 = (40031782540:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 260+point 2 split 4096 261)/2 = (352687651:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((352687651:ℝ)/168755200)/ClassicalSixthBranch.v ((352687651:ℝ)/168755200) = (793874964627:ℝ)/408072404824 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_260
  · change lowerPayment 261 ≤ lowerValue ((point 2 split 4096 261+point 2 split 4096 262)/2)
    have hp : lowerPayment 261 = (40176639523:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 261+point 2 split 4096 262)/2 = (352745913:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((352745913:ℝ)/168755200)/ClassicalSixthBranch.v ((352745913:ℝ)/168755200) = (793797650953:ℝ)/408024396936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_261
  · change lowerPayment 262 ≤ lowerValue ((point 2 split 4096 262+point 2 split 4096 263)/2)
    have hp : lowerPayment 262 = (40321434295:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 262+point 2 split 4096 263)/2 = (14112167:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((14112167:ℝ)/6750208)/ClassicalSixthBranch.v ((14112167:ℝ)/6750208) = (793720337279:ℝ)/407976389048 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_262
  · change lowerPayment 263 ≤ lowerValue ((point 2 split 4096 263+point 2 split 4096 264)/2)
    have hp : lowerPayment 263 = (40466166912:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 263+point 2 split 4096 264)/2 = (352862437:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((352862437:ℝ)/168755200)/ClassicalSixthBranch.v ((352862437:ℝ)/168755200) = (158728604721:ℝ)/81585676232 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_263
  · change lowerPayment 264 ≤ lowerValue ((point 2 split 4096 264+point 2 split 4096 265)/2)
    have hp : lowerPayment 264 = (40610837429:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 264+point 2 split 4096 265)/2 = (352920699:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((352920699:ℝ)/168755200)/ClassicalSixthBranch.v ((352920699:ℝ)/168755200) = (793565709931:ℝ)/407880373272 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_264
  · change lowerPayment 265 ≤ lowerValue ((point 2 split 4096 265+point 2 split 4096 266)/2)
    have hp : lowerPayment 265 = (40755445903:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 265+point 2 split 4096 266)/2 = (352978961:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((352978961:ℝ)/168755200)/ClassicalSixthBranch.v ((352978961:ℝ)/168755200) = (793488396257:ℝ)/407832365384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_265
  · change lowerPayment 266 ≤ lowerValue ((point 2 split 4096 266+point 2 split 4096 267)/2)
    have hp : lowerPayment 266 = (40899992389:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 266+point 2 split 4096 267)/2 = (353037223:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((353037223:ℝ)/168755200)/ClassicalSixthBranch.v ((353037223:ℝ)/168755200) = (793411082583:ℝ)/407784357496 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_266
  · change lowerPayment 267 ≤ lowerValue ((point 2 split 4096 267+point 2 split 4096 268)/2)
    have hp : lowerPayment 267 = (41044476941:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 267+point 2 split 4096 268)/2 = (70619097:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((70619097:ℝ)/33751040)/ClassicalSixthBranch.v ((70619097:ℝ)/33751040) = (793333768909:ℝ)/407736349608 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_267
  · change lowerPayment 268 ≤ lowerValue ((point 2 split 4096 268+point 2 split 4096 269)/2)
    have hp : lowerPayment 268 = (41188899617:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 268+point 2 split 4096 269)/2 = (353153747:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((353153747:ℝ)/168755200)/ClassicalSixthBranch.v ((353153747:ℝ)/168755200) = (158651291047:ℝ)/81537668344 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_268
  · change lowerPayment 269 ≤ lowerValue ((point 2 split 4096 269+point 2 split 4096 270)/2)
    have hp : lowerPayment 269 = (41333260471:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 269+point 2 split 4096 270)/2 = (353212009:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((353212009:ℝ)/168755200)/ClassicalSixthBranch.v ((353212009:ℝ)/168755200) = (793179141561:ℝ)/407640333832 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_269
  · change lowerPayment 270 ≤ lowerValue ((point 2 split 4096 270+point 2 split 4096 271)/2)
    have hp : lowerPayment 270 = (41477559559:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 270+point 2 split 4096 271)/2 = (353270271:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((353270271:ℝ)/168755200)/ClassicalSixthBranch.v ((353270271:ℝ)/168755200) = (793101827887:ℝ)/407592325944 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_270
  · change lowerPayment 271 ≤ lowerValue ((point 2 split 4096 271+point 2 split 4096 272)/2)
    have hp : lowerPayment 271 = (41621796935:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 271+point 2 split 4096 272)/2 = (353328533:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((353328533:ℝ)/168755200)/ClassicalSixthBranch.v ((353328533:ℝ)/168755200) = (793024514213:ℝ)/407544318056 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_271
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_016
