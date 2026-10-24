import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints025
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_025 (j : Fin 16) : lowerPayment (16*25+j.val) ≤
    lowerValue ((point 2 split 4096 (16*25+j.val)+point 2 split 4096 (16*25+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 400 ≤ lowerValue ((point 2 split 4096 400+point 2 split 4096 401)/2)
    have hp : lowerPayment 400 = (59730602804:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 400+point 2 split 4096 401)/2 = (360844331:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((360844331:ℝ)/168755200)/ClassicalSixthBranch.v ((360844331:ℝ)/168755200) = (783051050267:ℝ)/401351300504 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_400
  · change lowerPayment 401 ≤ lowerValue ((point 2 split 4096 401+point 2 split 4096 402)/2)
    have hp : lowerPayment 401 = (59867269591:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 401+point 2 split 4096 402)/2 = (360902593:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((360902593:ℝ)/168755200)/ClassicalSixthBranch.v ((360902593:ℝ)/168755200) = (782973736593:ℝ)/401303292616 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_401
  · change lowerPayment 402 ≤ lowerValue ((point 2 split 4096 402+point 2 split 4096 403)/2)
    have hp : lowerPayment 402 = (60003881476:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 402+point 2 split 4096 403)/2 = (72192171:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((72192171:ℝ)/33751040)/ClassicalSixthBranch.v ((72192171:ℝ)/33751040) = (782896422919:ℝ)/401255284728 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_402
  · change lowerPayment 403 ≤ lowerValue ((point 2 split 4096 403+point 2 split 4096 404)/2)
    have hp : lowerPayment 403 = (60140438509:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 403+point 2 split 4096 404)/2 = (361019117:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((361019117:ℝ)/168755200)/ClassicalSixthBranch.v ((361019117:ℝ)/168755200) = (156563821849:ℝ)/80241455368 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_403
  · change lowerPayment 404 ≤ lowerValue ((point 2 split 4096 404+point 2 split 4096 405)/2)
    have hp : lowerPayment 404 = (60276940737:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 404+point 2 split 4096 405)/2 = (361077379:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((361077379:ℝ)/168755200)/ClassicalSixthBranch.v ((361077379:ℝ)/168755200) = (782741795571:ℝ)/401159268952 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_404
  · change lowerPayment 405 ≤ lowerValue ((point 2 split 4096 405+point 2 split 4096 406)/2)
    have hp : lowerPayment 405 = (60413388210:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 405+point 2 split 4096 406)/2 = (361135641:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((361135641:ℝ)/168755200)/ClassicalSixthBranch.v ((361135641:ℝ)/168755200) = (782664481897:ℝ)/401111261064 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_405
  · change lowerPayment 406 ≤ lowerValue ((point 2 split 4096 406+point 2 split 4096 407)/2)
    have hp : lowerPayment 406 = (60549780976:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 406+point 2 split 4096 407)/2 = (361193903:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((361193903:ℝ)/168755200)/ClassicalSixthBranch.v ((361193903:ℝ)/168755200) = (782587168223:ℝ)/401063253176 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_406
  · change lowerPayment 407 ≤ lowerValue ((point 2 split 4096 407+point 2 split 4096 408)/2)
    have hp : lowerPayment 407 = (60686119085:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 407+point 2 split 4096 408)/2 = (72250433:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((72250433:ℝ)/33751040)/ClassicalSixthBranch.v ((72250433:ℝ)/33751040) = (782509854549:ℝ)/401015245288 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_407
  · change lowerPayment 408 ≤ lowerValue ((point 2 split 4096 408+point 2 split 4096 409)/2)
    have hp : lowerPayment 408 = (60822402583:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 408+point 2 split 4096 409)/2 = (361310427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((361310427:ℝ)/168755200)/ClassicalSixthBranch.v ((361310427:ℝ)/168755200) = (31297301635:ℝ)/16038689496 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_408
  · change lowerPayment 409 ≤ lowerValue ((point 2 split 4096 409+point 2 split 4096 410)/2)
    have hp : lowerPayment 409 = (60958631521:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 409+point 2 split 4096 410)/2 = (361368689:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((361368689:ℝ)/168755200)/ClassicalSixthBranch.v ((361368689:ℝ)/168755200) = (782355227201:ℝ)/400919229512 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_409
  · change lowerPayment 410 ≤ lowerValue ((point 2 split 4096 410+point 2 split 4096 411)/2)
    have hp : lowerPayment 410 = (61094805947:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 410+point 2 split 4096 411)/2 = (361426951:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((361426951:ℝ)/168755200)/ClassicalSixthBranch.v ((361426951:ℝ)/168755200) = (782277913527:ℝ)/400871221624 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_410
  · change lowerPayment 411 ≤ lowerValue ((point 2 split 4096 411+point 2 split 4096 412)/2)
    have hp : lowerPayment 411 = (61230925908:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 411+point 2 split 4096 412)/2 = (361485213:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((361485213:ℝ)/168755200)/ClassicalSixthBranch.v ((361485213:ℝ)/168755200) = (782200599853:ℝ)/400823213736 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_411
  · change lowerPayment 412 ≤ lowerValue ((point 2 split 4096 412+point 2 split 4096 413)/2)
    have hp : lowerPayment 412 = (61366991455:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 412+point 2 split 4096 413)/2 = (14461739:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((14461739:ℝ)/6750208)/ClassicalSixthBranch.v ((14461739:ℝ)/6750208) = (782123286179:ℝ)/400775205848 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_412
  · change lowerPayment 413 ≤ lowerValue ((point 2 split 4096 413+point 2 split 4096 414)/2)
    have hp : lowerPayment 413 = (61503002633:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 413+point 2 split 4096 414)/2 = (361601737:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((361601737:ℝ)/168755200)/ClassicalSixthBranch.v ((361601737:ℝ)/168755200) = (156409194501:ℝ)/80145439592 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_413
  · change lowerPayment 414 ≤ lowerValue ((point 2 split 4096 414+point 2 split 4096 415)/2)
    have hp : lowerPayment 414 = (61638959493:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 414+point 2 split 4096 415)/2 = (361659999:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((361659999:ℝ)/168755200)/ClassicalSixthBranch.v ((361659999:ℝ)/168755200) = (781968658831:ℝ)/400679190072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_414
  · change lowerPayment 415 ≤ lowerValue ((point 2 split 4096 415+point 2 split 4096 416)/2)
    have hp : lowerPayment 415 = (61774862083:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 415+point 2 split 4096 416)/2 = (361718261:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((361718261:ℝ)/168755200)/ClassicalSixthBranch.v ((361718261:ℝ)/168755200) = (781891345157:ℝ)/400631182184 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_415
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_025
