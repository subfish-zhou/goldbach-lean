import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints087
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_087 (j : Fin 16) : lowerPayment (16*87+j.val) ≤
    lowerValue ((point 2 split 4096 (16*87+j.val)+point 2 split 4096 (16*87+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1392 ≤ lowerValue ((point 2 split 4096 1392+point 2 split 4096 1393)/2)
    have hp : lowerPayment 1392 = (174788230187:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1392+point 2 split 4096 1393)/2 = (83728047:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((83728047:ℝ)/33751040)/ClassicalSixthBranch.v ((83728047:ℝ)/33751040) = (706355885659:ℝ)/353727475608 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1392
  · change lowerPayment 1393 ≤ lowerValue ((point 2 split 4096 1393+point 2 split 4096 1394)/2)
    have hp : lowerPayment 1393 = (174888873354:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1393+point 2 split 4096 1394)/2 = (418698497:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((418698497:ℝ)/168755200)/ClassicalSixthBranch.v ((418698497:ℝ)/168755200) = (141255714397:ℝ)/70735893544 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1393
  · change lowerPayment 1394 ≤ lowerValue ((point 2 split 4096 1394+point 2 split 4096 1395)/2)
    have hp : lowerPayment 1394 = (174989494610:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1394+point 2 split 4096 1395)/2 = (418756759:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((418756759:ℝ)/168755200)/ClassicalSixthBranch.v ((418756759:ℝ)/168755200) = (706201258311:ℝ)/353631459832 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1394
  · change lowerPayment 1395 ≤ lowerValue ((point 2 split 4096 1395+point 2 split 4096 1396)/2)
    have hp : lowerPayment 1395 = (175090093976:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1395+point 2 split 4096 1396)/2 = (418815021:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((418815021:ℝ)/168755200)/ClassicalSixthBranch.v ((418815021:ℝ)/168755200) = (706123944637:ℝ)/353583451944 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1395
  · change lowerPayment 1396 ≤ lowerValue ((point 2 split 4096 1396+point 2 split 4096 1397)/2)
    have hp : lowerPayment 1396 = (175190671475:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1396+point 2 split 4096 1397)/2 = (418873283:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((418873283:ℝ)/168755200)/ClassicalSixthBranch.v ((418873283:ℝ)/168755200) = (706046630963:ℝ)/353535444056 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1396
  · change lowerPayment 1397 ≤ lowerValue ((point 2 split 4096 1397+point 2 split 4096 1398)/2)
    have hp : lowerPayment 1397 = (175291227130:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1397+point 2 split 4096 1398)/2 = (83786309:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((83786309:ℝ)/33751040)/ClassicalSixthBranch.v ((83786309:ℝ)/33751040) = (705969317289:ℝ)/353487436168 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1397
  · change lowerPayment 1398 ≤ lowerValue ((point 2 split 4096 1398+point 2 split 4096 1399)/2)
    have hp : lowerPayment 1398 = (175391760964:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1398+point 2 split 4096 1399)/2 = (418989807:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((418989807:ℝ)/168755200)/ClassicalSixthBranch.v ((418989807:ℝ)/168755200) = (141178400723:ℝ)/70687885656 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1398
  · change lowerPayment 1399 ≤ lowerValue ((point 2 split 4096 1399+point 2 split 4096 1400)/2)
    have hp : lowerPayment 1399 = (175492272999:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1399+point 2 split 4096 1400)/2 = (419048069:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((419048069:ℝ)/168755200)/ClassicalSixthBranch.v ((419048069:ℝ)/168755200) = (705814689941:ℝ)/353391420392 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1399
  · change lowerPayment 1400 ≤ lowerValue ((point 2 split 4096 1400+point 2 split 4096 1401)/2)
    have hp : lowerPayment 1400 = (175592763258:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1400+point 2 split 4096 1401)/2 = (419106331:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((419106331:ℝ)/168755200)/ClassicalSixthBranch.v ((419106331:ℝ)/168755200) = (705737376267:ℝ)/353343412504 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1400
  · change lowerPayment 1401 ≤ lowerValue ((point 2 split 4096 1401+point 2 split 4096 1402)/2)
    have hp : lowerPayment 1401 = (175693231763:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1401+point 2 split 4096 1402)/2 = (419164593:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((419164593:ℝ)/168755200)/ClassicalSixthBranch.v ((419164593:ℝ)/168755200) = (705660062593:ℝ)/353295404616 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1401
  · change lowerPayment 1402 ≤ lowerValue ((point 2 split 4096 1402+point 2 split 4096 1403)/2)
    have hp : lowerPayment 1402 = (175793678538:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1402+point 2 split 4096 1403)/2 = (83844571:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((83844571:ℝ)/33751040)/ClassicalSixthBranch.v ((83844571:ℝ)/33751040) = (705582748919:ℝ)/353247396728 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1402
  · change lowerPayment 1403 ≤ lowerValue ((point 2 split 4096 1403+point 2 split 4096 1404)/2)
    have hp : lowerPayment 1403 = (175894103603:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1403+point 2 split 4096 1404)/2 = (419281117:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((419281117:ℝ)/168755200)/ClassicalSixthBranch.v ((419281117:ℝ)/168755200) = (141101087049:ℝ)/70639877768 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1403
  · change lowerPayment 1404 ≤ lowerValue ((point 2 split 4096 1404+point 2 split 4096 1405)/2)
    have hp : lowerPayment 1404 = (175994506984:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1404+point 2 split 4096 1405)/2 = (419339379:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((419339379:ℝ)/168755200)/ClassicalSixthBranch.v ((419339379:ℝ)/168755200) = (705428121571:ℝ)/353151380952 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1404
  · change lowerPayment 1405 ≤ lowerValue ((point 2 split 4096 1405+point 2 split 4096 1406)/2)
    have hp : lowerPayment 1405 = (176094888700:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1405+point 2 split 4096 1406)/2 = (419397641:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((419397641:ℝ)/168755200)/ClassicalSixthBranch.v ((419397641:ℝ)/168755200) = (705350807897:ℝ)/353103373064 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1405
  · change lowerPayment 1406 ≤ lowerValue ((point 2 split 4096 1406+point 2 split 4096 1407)/2)
    have hp : lowerPayment 1406 = (176195248776:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1406+point 2 split 4096 1407)/2 = (419455903:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((419455903:ℝ)/168755200)/ClassicalSixthBranch.v ((419455903:ℝ)/168755200) = (705273494223:ℝ)/353055365176 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1406
  · change lowerPayment 1407 ≤ lowerValue ((point 2 split 4096 1407+point 2 split 4096 1408)/2)
    have hp : lowerPayment 1407 = (176295587234:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1407+point 2 split 4096 1408)/2 = (83902833:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((83902833:ℝ)/33751040)/ClassicalSixthBranch.v ((83902833:ℝ)/33751040) = (705196180549:ℝ)/353007357288 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1407
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_087
