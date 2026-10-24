import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints084
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_084 (j : Fin 16) : lowerPayment (16*84+j.val) ≤
    lowerValue ((point 2 split 4096 (16*84+j.val)+point 2 split 4096 (16*84+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1344 ≤ lowerValue ((point 2 split 4096 1344+point 2 split 4096 1345)/2)
    have hp : lowerPayment 1344 = (169931141458:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1344+point 2 split 4096 1345)/2 = (415843659:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((415843659:ℝ)/168755200)/ClassicalSixthBranch.v ((415843659:ℝ)/168755200) = (710066942011:ℝ)/356031854232 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1344
  · change lowerPayment 1345 ≤ lowerValue ((point 2 split 4096 1345+point 2 split 4096 1346)/2)
    have hp : lowerPayment 1345 = (170032863357:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1345+point 2 split 4096 1346)/2 = (415901921:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((415901921:ℝ)/168755200)/ClassicalSixthBranch.v ((415901921:ℝ)/168755200) = (709989628337:ℝ)/355983846344 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1345
  · change lowerPayment 1346 ≤ lowerValue ((point 2 split 4096 1346+point 2 split 4096 1347)/2)
    have hp : lowerPayment 1346 = (170134562238:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1346+point 2 split 4096 1347)/2 = (415960183:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((415960183:ℝ)/168755200)/ClassicalSixthBranch.v ((415960183:ℝ)/168755200) = (709912314663:ℝ)/355935838456 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1346
  · change lowerPayment 1347 ≤ lowerValue ((point 2 split 4096 1347+point 2 split 4096 1348)/2)
    have hp : lowerPayment 1347 = (170236238124:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1347+point 2 split 4096 1348)/2 = (83203689:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((83203689:ℝ)/33751040)/ClassicalSixthBranch.v ((83203689:ℝ)/33751040) = (709835000989:ℝ)/355887830568 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1347
  · change lowerPayment 1348 ≤ lowerValue ((point 2 split 4096 1348+point 2 split 4096 1349)/2)
    have hp : lowerPayment 1348 = (170337891040:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1348+point 2 split 4096 1349)/2 = (416076707:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((416076707:ℝ)/168755200)/ClassicalSixthBranch.v ((416076707:ℝ)/168755200) = (141951537463:ℝ)/71167964536 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1348
  · change lowerPayment 1349 ≤ lowerValue ((point 2 split 4096 1349+point 2 split 4096 1350)/2)
    have hp : lowerPayment 1349 = (170439521009:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1349+point 2 split 4096 1350)/2 = (416134969:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((416134969:ℝ)/168755200)/ClassicalSixthBranch.v ((416134969:ℝ)/168755200) = (709680373641:ℝ)/355791814792 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1349
  · change lowerPayment 1350 ≤ lowerValue ((point 2 split 4096 1350+point 2 split 4096 1351)/2)
    have hp : lowerPayment 1350 = (170541128053:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1350+point 2 split 4096 1351)/2 = (416193231:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((416193231:ℝ)/168755200)/ClassicalSixthBranch.v ((416193231:ℝ)/168755200) = (709603059967:ℝ)/355743806904 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1350
  · change lowerPayment 1351 ≤ lowerValue ((point 2 split 4096 1351+point 2 split 4096 1352)/2)
    have hp : lowerPayment 1351 = (170642712197:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1351+point 2 split 4096 1352)/2 = (416251493:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((416251493:ℝ)/168755200)/ClassicalSixthBranch.v ((416251493:ℝ)/168755200) = (709525746293:ℝ)/355695799016 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1351
  · change lowerPayment 1352 ≤ lowerValue ((point 2 split 4096 1352+point 2 split 4096 1353)/2)
    have hp : lowerPayment 1352 = (170744273463:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1352+point 2 split 4096 1353)/2 = (83261951:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((83261951:ℝ)/33751040)/ClassicalSixthBranch.v ((83261951:ℝ)/33751040) = (709448432619:ℝ)/355647791128 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1352
  · change lowerPayment 1353 ≤ lowerValue ((point 2 split 4096 1353+point 2 split 4096 1354)/2)
    have hp : lowerPayment 1353 = (170845811875:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1353+point 2 split 4096 1354)/2 = (416368017:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((416368017:ℝ)/168755200)/ClassicalSixthBranch.v ((416368017:ℝ)/168755200) = (141874223789:ℝ)/71119956648 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1353
  · change lowerPayment 1354 ≤ lowerValue ((point 2 split 4096 1354+point 2 split 4096 1355)/2)
    have hp : lowerPayment 1354 = (170947327455:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1354+point 2 split 4096 1355)/2 = (416426279:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((416426279:ℝ)/168755200)/ClassicalSixthBranch.v ((416426279:ℝ)/168755200) = (709293805271:ℝ)/355551775352 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1354
  · change lowerPayment 1355 ≤ lowerValue ((point 2 split 4096 1355+point 2 split 4096 1356)/2)
    have hp : lowerPayment 1355 = (171048820229:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1355+point 2 split 4096 1356)/2 = (416484541:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((416484541:ℝ)/168755200)/ClassicalSixthBranch.v ((416484541:ℝ)/168755200) = (709216491597:ℝ)/355503767464 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1355
  · change lowerPayment 1356 ≤ lowerValue ((point 2 split 4096 1356+point 2 split 4096 1357)/2)
    have hp : lowerPayment 1356 = (171150290217:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1356+point 2 split 4096 1357)/2 = (416542803:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((416542803:ℝ)/168755200)/ClassicalSixthBranch.v ((416542803:ℝ)/168755200) = (709139177923:ℝ)/355455759576 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1356
  · change lowerPayment 1357 ≤ lowerValue ((point 2 split 4096 1357+point 2 split 4096 1358)/2)
    have hp : lowerPayment 1357 = (171251737444:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1357+point 2 split 4096 1358)/2 = (83320213:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((83320213:ℝ)/33751040)/ClassicalSixthBranch.v ((83320213:ℝ)/33751040) = (709061864249:ℝ)/355407751688 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1357
  · change lowerPayment 1358 ≤ lowerValue ((point 2 split 4096 1358+point 2 split 4096 1359)/2)
    have hp : lowerPayment 1358 = (171353161934:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1358+point 2 split 4096 1359)/2 = (416659327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((416659327:ℝ)/168755200)/ClassicalSixthBranch.v ((416659327:ℝ)/168755200) = (28359382023:ℝ)/14214389752 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1358
  · change lowerPayment 1359 ≤ lowerValue ((point 2 split 4096 1359+point 2 split 4096 1360)/2)
    have hp : lowerPayment 1359 = (171454563708:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1359+point 2 split 4096 1360)/2 = (416717589:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((416717589:ℝ)/168755200)/ClassicalSixthBranch.v ((416717589:ℝ)/168755200) = (708907236901:ℝ)/355311735912 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1359
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_084
