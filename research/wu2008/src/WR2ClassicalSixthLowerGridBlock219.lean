import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints219
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_219 (j : Fin 16) : lowerPayment (16*219+j.val) ≤
    lowerValue ((point 2 split 4096 (16*219+j.val)+point 2 split 4096 (16*219+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3504 ≤ lowerValue ((point 2 split 4096 3504+point 2 split 4096 3505)/2)
    have hp : lowerPayment 3504 = (366796071012:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3504+point 2 split 4096 3505)/2 = (541689579:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((541689579:ℝ)/168755200)/ClassicalSixthBranch.v ((541689579:ℝ)/168755200) = (543069406171:ℝ)/252334816152 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3504
  · change lowerPayment 3505 ≤ lowerValue ((point 2 split 4096 3505+point 2 split 4096 3506)/2)
    have hp : lowerPayment 3505 = (366888781738:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3505+point 2 split 4096 3506)/2 = (541747841:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((541747841:ℝ)/168755200)/ClassicalSixthBranch.v ((541747841:ℝ)/168755200) = (542992092497:ℝ)/252286808264 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3505
  · change lowerPayment 3506 ≤ lowerValue ((point 2 split 4096 3506+point 2 split 4096 3507)/2)
    have hp : lowerPayment 3506 = (366981504543:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3506+point 2 split 4096 3507)/2 = (541806103:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((541806103:ℝ)/168755200)/ClassicalSixthBranch.v ((541806103:ℝ)/168755200) = (542914778823:ℝ)/252238800376 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3506
  · change lowerPayment 3507 ≤ lowerValue ((point 2 split 4096 3507+point 2 split 4096 3508)/2)
    have hp : lowerPayment 3507 = (367074239444:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3507+point 2 split 4096 3508)/2 = (108372873:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((108372873:ℝ)/33751040)/ClassicalSixthBranch.v ((108372873:ℝ)/33751040) = (542837465149:ℝ)/252190792488 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3507
  · change lowerPayment 3508 ≤ lowerValue ((point 2 split 4096 3508+point 2 split 4096 3509)/2)
    have hp : lowerPayment 3508 = (367166986455:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3508+point 2 split 4096 3509)/2 = (541922627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((541922627:ℝ)/168755200)/ClassicalSixthBranch.v ((541922627:ℝ)/168755200) = (21710406059:ℝ)/10085711384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3508
  · change lowerPayment 3509 ≤ lowerValue ((point 2 split 4096 3509+point 2 split 4096 3510)/2)
    have hp : lowerPayment 3509 = (367259745593:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3509+point 2 split 4096 3510)/2 = (541980889:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((541980889:ℝ)/168755200)/ClassicalSixthBranch.v ((541980889:ℝ)/168755200) = (542682837801:ℝ)/252094776712 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3509
  · change lowerPayment 3510 ≤ lowerValue ((point 2 split 4096 3510+point 2 split 4096 3511)/2)
    have hp : lowerPayment 3510 = (367352516872:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3510+point 2 split 4096 3511)/2 = (542039151:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((542039151:ℝ)/168755200)/ClassicalSixthBranch.v ((542039151:ℝ)/168755200) = (542605524127:ℝ)/252046768824 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3510
  · change lowerPayment 3511 ≤ lowerValue ((point 2 split 4096 3511+point 2 split 4096 3512)/2)
    have hp : lowerPayment 3511 = (367445300309:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3511+point 2 split 4096 3512)/2 = (542097413:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((542097413:ℝ)/168755200)/ClassicalSixthBranch.v ((542097413:ℝ)/168755200) = (542528210453:ℝ)/251998760936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3511
  · change lowerPayment 3512 ≤ lowerValue ((point 2 split 4096 3512+point 2 split 4096 3513)/2)
    have hp : lowerPayment 3512 = (367538095918:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3512+point 2 split 4096 3513)/2 = (21686227:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((21686227:ℝ)/6750208)/ClassicalSixthBranch.v ((21686227:ℝ)/6750208) = (542450896779:ℝ)/251950753048 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3512
  · change lowerPayment 3513 ≤ lowerValue ((point 2 split 4096 3513+point 2 split 4096 3514)/2)
    have hp : lowerPayment 3513 = (367630903716:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3513+point 2 split 4096 3514)/2 = (542213937:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((542213937:ℝ)/168755200)/ClassicalSixthBranch.v ((542213937:ℝ)/168755200) = (108474716621:ℝ)/50380549032 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3513
  · change lowerPayment 3514 ≤ lowerValue ((point 2 split 4096 3514+point 2 split 4096 3515)/2)
    have hp : lowerPayment 3514 = (367723723718:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3514+point 2 split 4096 3515)/2 = (542272199:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((542272199:ℝ)/168755200)/ClassicalSixthBranch.v ((542272199:ℝ)/168755200) = (542296269431:ℝ)/251854737272 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3514
  · change lowerPayment 3515 ≤ lowerValue ((point 2 split 4096 3515+point 2 split 4096 3516)/2)
    have hp : lowerPayment 3515 = (367816555940:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3515+point 2 split 4096 3516)/2 = (542330461:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((542330461:ℝ)/168755200)/ClassicalSixthBranch.v ((542330461:ℝ)/168755200) = (542218955757:ℝ)/251806729384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3515
  · change lowerPayment 3516 ≤ lowerValue ((point 2 split 4096 3516+point 2 split 4096 3517)/2)
    have hp : lowerPayment 3516 = (367909400397:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3516+point 2 split 4096 3517)/2 = (542388723:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((542388723:ℝ)/168755200)/ClassicalSixthBranch.v ((542388723:ℝ)/168755200) = (542141642083:ℝ)/251758721496 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3516
  · change lowerPayment 3517 ≤ lowerValue ((point 2 split 4096 3517+point 2 split 4096 3518)/2)
    have hp : lowerPayment 3517 = (368002257104:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3517+point 2 split 4096 3518)/2 = (108489397:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((108489397:ℝ)/33751040)/ClassicalSixthBranch.v ((108489397:ℝ)/33751040) = (542064328409:ℝ)/251710713608 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3517
  · change lowerPayment 3518 ≤ lowerValue ((point 2 split 4096 3518+point 2 split 4096 3519)/2)
    have hp : lowerPayment 3518 = (368095126078:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3518+point 2 split 4096 3519)/2 = (542505247:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((542505247:ℝ)/168755200)/ClassicalSixthBranch.v ((542505247:ℝ)/168755200) = (108397402947:ℝ)/50332541144 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3518
  · change lowerPayment 3519 ≤ lowerValue ((point 2 split 4096 3519+point 2 split 4096 3520)/2)
    have hp : lowerPayment 3519 = (368188007335:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3519+point 2 split 4096 3520)/2 = (542563509:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((542563509:ℝ)/168755200)/ClassicalSixthBranch.v ((542563509:ℝ)/168755200) = (541909701061:ℝ)/251614697832 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3519
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_219
