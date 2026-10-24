import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints083
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_083 (j : Fin 16) : lowerPayment (16*83+j.val) ≤
    lowerValue ((point 2 split 4096 (16*83+j.val)+point 2 split 4096 (16*83+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1328 ≤ lowerValue ((point 2 split 4096 1328+point 2 split 4096 1329)/2)
    have hp : lowerPayment 1328 = (168300441568:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1328+point 2 split 4096 1329)/2 = (414911467:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((414911467:ℝ)/168755200)/ClassicalSixthBranch.v ((414911467:ℝ)/168755200) = (142260792159:ℝ)/71359996088 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1328
  · change lowerPayment 1329 ≤ lowerValue ((point 2 split 4096 1329+point 2 split 4096 1330)/2)
    have hp : lowerPayment 1329 = (168402534938:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1329+point 2 split 4096 1330)/2 = (414969729:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((414969729:ℝ)/168755200)/ClassicalSixthBranch.v ((414969729:ℝ)/168755200) = (711226647121:ℝ)/356751972552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1329
  · change lowerPayment 1330 ≤ lowerValue ((point 2 split 4096 1330+point 2 split 4096 1331)/2)
    have hp : lowerPayment 1330 = (168504604914:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1330+point 2 split 4096 1331)/2 = (415027991:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((415027991:ℝ)/168755200)/ClassicalSixthBranch.v ((415027991:ℝ)/168755200) = (711149333447:ℝ)/356703964664 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1330
  · change lowerPayment 1331 ≤ lowerValue ((point 2 split 4096 1331+point 2 split 4096 1332)/2)
    have hp : lowerPayment 1331 = (168606651520:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1331+point 2 split 4096 1332)/2 = (415086253:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((415086253:ℝ)/168755200)/ClassicalSixthBranch.v ((415086253:ℝ)/168755200) = (711072019773:ℝ)/356655956776 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1331
  · change lowerPayment 1332 ≤ lowerValue ((point 2 split 4096 1332+point 2 split 4096 1333)/2)
    have hp : lowerPayment 1332 = (168708674780:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1332+point 2 split 4096 1333)/2 = (83028903:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((83028903:ℝ)/33751040)/ClassicalSixthBranch.v ((83028903:ℝ)/33751040) = (710994706099:ℝ)/356607948888 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1332
  · change lowerPayment 1333 ≤ lowerValue ((point 2 split 4096 1333+point 2 split 4096 1334)/2)
    have hp : lowerPayment 1333 = (168810674718:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1333+point 2 split 4096 1334)/2 = (415202777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((415202777:ℝ)/168755200)/ClassicalSixthBranch.v ((415202777:ℝ)/168755200) = (28436695697:ℝ)/14262397640 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1333
  · change lowerPayment 1334 ≤ lowerValue ((point 2 split 4096 1334+point 2 split 4096 1335)/2)
    have hp : lowerPayment 1334 = (168912651356:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1334+point 2 split 4096 1335)/2 = (415261039:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((415261039:ℝ)/168755200)/ClassicalSixthBranch.v ((415261039:ℝ)/168755200) = (710840078751:ℝ)/356511933112 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1334
  · change lowerPayment 1335 ≤ lowerValue ((point 2 split 4096 1335+point 2 split 4096 1336)/2)
    have hp : lowerPayment 1335 = (169014604718:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1335+point 2 split 4096 1336)/2 = (415319301:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((415319301:ℝ)/168755200)/ClassicalSixthBranch.v ((415319301:ℝ)/168755200) = (710762765077:ℝ)/356463925224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1335
  · change lowerPayment 1336 ≤ lowerValue ((point 2 split 4096 1336+point 2 split 4096 1337)/2)
    have hp : lowerPayment 1336 = (169116534829:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1336+point 2 split 4096 1337)/2 = (415377563:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((415377563:ℝ)/168755200)/ClassicalSixthBranch.v ((415377563:ℝ)/168755200) = (710685451403:ℝ)/356415917336 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1336
  · change lowerPayment 1337 ≤ lowerValue ((point 2 split 4096 1337+point 2 split 4096 1338)/2)
    have hp : lowerPayment 1337 = (169218441711:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1337+point 2 split 4096 1338)/2 = (16617433:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((16617433:ℝ)/6750208)/ClassicalSixthBranch.v ((16617433:ℝ)/6750208) = (710608137729:ℝ)/356367909448 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1337
  · change lowerPayment 1338 ≤ lowerValue ((point 2 split 4096 1338+point 2 split 4096 1339)/2)
    have hp : lowerPayment 1338 = (169320325388:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1338+point 2 split 4096 1339)/2 = (415494087:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((415494087:ℝ)/168755200)/ClassicalSixthBranch.v ((415494087:ℝ)/168755200) = (142106164811:ℝ)/71263980312 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1338
  · change lowerPayment 1339 ≤ lowerValue ((point 2 split 4096 1339+point 2 split 4096 1340)/2)
    have hp : lowerPayment 1339 = (169422185883:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1339+point 2 split 4096 1340)/2 = (415552349:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((415552349:ℝ)/168755200)/ClassicalSixthBranch.v ((415552349:ℝ)/168755200) = (710453510381:ℝ)/356271893672 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1339
  · change lowerPayment 1340 ≤ lowerValue ((point 2 split 4096 1340+point 2 split 4096 1341)/2)
    have hp : lowerPayment 1340 = (169524023220:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1340+point 2 split 4096 1341)/2 = (415610611:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((415610611:ℝ)/168755200)/ClassicalSixthBranch.v ((415610611:ℝ)/168755200) = (710376196707:ℝ)/356223885784 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1340
  · change lowerPayment 1341 ≤ lowerValue ((point 2 split 4096 1341+point 2 split 4096 1342)/2)
    have hp : lowerPayment 1341 = (169625837423:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1341+point 2 split 4096 1342)/2 = (415668873:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((415668873:ℝ)/168755200)/ClassicalSixthBranch.v ((415668873:ℝ)/168755200) = (710298883033:ℝ)/356175877896 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1341
  · change lowerPayment 1342 ≤ lowerValue ((point 2 split 4096 1342+point 2 split 4096 1343)/2)
    have hp : lowerPayment 1342 = (169727628515:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1342+point 2 split 4096 1343)/2 = (83145427:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((83145427:ℝ)/33751040)/ClassicalSixthBranch.v ((83145427:ℝ)/33751040) = (710221569359:ℝ)/356127870008 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1342
  · change lowerPayment 1343 ≤ lowerValue ((point 2 split 4096 1343+point 2 split 4096 1344)/2)
    have hp : lowerPayment 1343 = (169829396518:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1343+point 2 split 4096 1344)/2 = (415785397:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((415785397:ℝ)/168755200)/ClassicalSixthBranch.v ((415785397:ℝ)/168755200) = (142028851137:ℝ)/71215972424 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1343
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_083
