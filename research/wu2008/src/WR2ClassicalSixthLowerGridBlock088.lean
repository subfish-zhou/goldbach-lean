import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints088
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_088 (j : Fin 16) : lowerPayment (16*88+j.val) ≤
    lowerValue ((point 2 split 4096 (16*88+j.val)+point 2 split 4096 (16*88+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1408 ≤ lowerValue ((point 2 split 4096 1408+point 2 split 4096 1409)/2)
    have hp : lowerPayment 1408 = (176395904096:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1408+point 2 split 4096 1409)/2 = (419572427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((419572427:ℝ)/168755200)/ClassicalSixthBranch.v ((419572427:ℝ)/168755200) = (28204754675:ℝ)/14118373976 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1408
  · change lowerPayment 1409 ≤ lowerValue ((point 2 split 4096 1409+point 2 split 4096 1410)/2)
    have hp : lowerPayment 1409 = (176496199385:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1409+point 2 split 4096 1410)/2 = (419630689:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((419630689:ℝ)/168755200)/ClassicalSixthBranch.v ((419630689:ℝ)/168755200) = (705041553201:ℝ)/352911341512 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1409
  · change lowerPayment 1410 ≤ lowerValue ((point 2 split 4096 1410+point 2 split 4096 1411)/2)
    have hp : lowerPayment 1410 = (176596473123:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1410+point 2 split 4096 1411)/2 = (419688951:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((419688951:ℝ)/168755200)/ClassicalSixthBranch.v ((419688951:ℝ)/168755200) = (704964239527:ℝ)/352863333624 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1410
  · change lowerPayment 1411 ≤ lowerValue ((point 2 split 4096 1411+point 2 split 4096 1412)/2)
    have hp : lowerPayment 1411 = (176696725332:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1411+point 2 split 4096 1412)/2 = (419747213:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((419747213:ℝ)/168755200)/ClassicalSixthBranch.v ((419747213:ℝ)/168755200) = (704886925853:ℝ)/352815325736 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1411
  · change lowerPayment 1412 ≤ lowerValue ((point 2 split 4096 1412+point 2 split 4096 1413)/2)
    have hp : lowerPayment 1412 = (176796956036:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1412+point 2 split 4096 1413)/2 = (16792219:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((16792219:ℝ)/6750208)/ClassicalSixthBranch.v ((16792219:ℝ)/6750208) = (704809612179:ℝ)/352767317848 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1412
  · change lowerPayment 1413 ≤ lowerValue ((point 2 split 4096 1413+point 2 split 4096 1414)/2)
    have hp : lowerPayment 1413 = (176897165256:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1413+point 2 split 4096 1414)/2 = (419863737:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((419863737:ℝ)/168755200)/ClassicalSixthBranch.v ((419863737:ℝ)/168755200) = (140946459701:ℝ)/70543861992 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1413
  · change lowerPayment 1414 ≤ lowerValue ((point 2 split 4096 1414+point 2 split 4096 1415)/2)
    have hp : lowerPayment 1414 = (176997353016:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1414+point 2 split 4096 1415)/2 = (419921999:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((419921999:ℝ)/168755200)/ClassicalSixthBranch.v ((419921999:ℝ)/168755200) = (704654984831:ℝ)/352671302072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1414
  · change lowerPayment 1415 ≤ lowerValue ((point 2 split 4096 1415+point 2 split 4096 1416)/2)
    have hp : lowerPayment 1415 = (177097519336:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1415+point 2 split 4096 1416)/2 = (419980261:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((419980261:ℝ)/168755200)/ClassicalSixthBranch.v ((419980261:ℝ)/168755200) = (704577671157:ℝ)/352623294184 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1415
  · change lowerPayment 1416 ≤ lowerValue ((point 2 split 4096 1416+point 2 split 4096 1417)/2)
    have hp : lowerPayment 1416 = (177197664241:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1416+point 2 split 4096 1417)/2 = (420038523:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((420038523:ℝ)/168755200)/ClassicalSixthBranch.v ((420038523:ℝ)/168755200) = (704500357483:ℝ)/352575286296 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1416
  · change lowerPayment 1417 ≤ lowerValue ((point 2 split 4096 1417+point 2 split 4096 1418)/2)
    have hp : lowerPayment 1417 = (177297787752:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1417+point 2 split 4096 1418)/2 = (84019357:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((84019357:ℝ)/33751040)/ClassicalSixthBranch.v ((84019357:ℝ)/33751040) = (704423043809:ℝ)/352527278408 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1417
  · change lowerPayment 1418 ≤ lowerValue ((point 2 split 4096 1418+point 2 split 4096 1419)/2)
    have hp : lowerPayment 1418 = (177397889891:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1418+point 2 split 4096 1419)/2 = (420155047:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((420155047:ℝ)/168755200)/ClassicalSixthBranch.v ((420155047:ℝ)/168755200) = (140869146027:ℝ)/70495854104 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1418
  · change lowerPayment 1419 ≤ lowerValue ((point 2 split 4096 1419+point 2 split 4096 1420)/2)
    have hp : lowerPayment 1419 = (177497970681:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1419+point 2 split 4096 1420)/2 = (420213309:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((420213309:ℝ)/168755200)/ClassicalSixthBranch.v ((420213309:ℝ)/168755200) = (704268416461:ℝ)/352431262632 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1419
  · change lowerPayment 1420 ≤ lowerValue ((point 2 split 4096 1420+point 2 split 4096 1421)/2)
    have hp : lowerPayment 1420 = (177598030144:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1420+point 2 split 4096 1421)/2 = (420271571:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((420271571:ℝ)/168755200)/ClassicalSixthBranch.v ((420271571:ℝ)/168755200) = (704191102787:ℝ)/352383254744 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1420
  · change lowerPayment 1421 ≤ lowerValue ((point 2 split 4096 1421+point 2 split 4096 1422)/2)
    have hp : lowerPayment 1421 = (177698068303:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1421+point 2 split 4096 1422)/2 = (420329833:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((420329833:ℝ)/168755200)/ClassicalSixthBranch.v ((420329833:ℝ)/168755200) = (704113789113:ℝ)/352335246856 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1421
  · change lowerPayment 1422 ≤ lowerValue ((point 2 split 4096 1422+point 2 split 4096 1423)/2)
    have hp : lowerPayment 1422 = (177798085180:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1422+point 2 split 4096 1423)/2 = (84077619:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((84077619:ℝ)/33751040)/ClassicalSixthBranch.v ((84077619:ℝ)/33751040) = (704036475439:ℝ)/352287238968 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1422
  · change lowerPayment 1423 ≤ lowerValue ((point 2 split 4096 1423+point 2 split 4096 1424)/2)
    have hp : lowerPayment 1423 = (177898080797:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1423+point 2 split 4096 1424)/2 = (420446357:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((420446357:ℝ)/168755200)/ClassicalSixthBranch.v ((420446357:ℝ)/168755200) = (140791832353:ℝ)/70447846216 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1423
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_088
