import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints094
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_094 (j : Fin 16) : lowerPayment (16*94+j.val) ≤
    lowerValue ((point 2 split 4096 (16*94+j.val)+point 2 split 4096 (16*94+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1504 ≤ lowerValue ((point 2 split 4096 1504+point 2 split 4096 1505)/2)
    have hp : lowerPayment 1504 = (185929145299:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1504+point 2 split 4096 1505)/2 = (425165579:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((425165579:ℝ)/168755200)/ClassicalSixthBranch.v ((425165579:ℝ)/168755200) = (697696754171:ℝ)/348350592152 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1504
  · change lowerPayment 1505 ≤ lowerValue ((point 2 split 4096 1505+point 2 split 4096 1506)/2)
    have hp : lowerPayment 1505 = (186027472244:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1505+point 2 split 4096 1506)/2 = (425223841:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((425223841:ℝ)/168755200)/ClassicalSixthBranch.v ((425223841:ℝ)/168755200) = (697619440497:ℝ)/348302584264 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1505
  · change lowerPayment 1506 ≤ lowerValue ((point 2 split 4096 1506+point 2 split 4096 1507)/2)
    have hp : lowerPayment 1506 = (186125779733:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1506+point 2 split 4096 1507)/2 = (425282103:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((425282103:ℝ)/168755200)/ClassicalSixthBranch.v ((425282103:ℝ)/168755200) = (697542126823:ℝ)/348254576376 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1506
  · change lowerPayment 1507 ≤ lowerValue ((point 2 split 4096 1507+point 2 split 4096 1508)/2)
    have hp : lowerPayment 1507 = (186224067790:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1507+point 2 split 4096 1508)/2 = (85068073:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((85068073:ℝ)/33751040)/ClassicalSixthBranch.v ((85068073:ℝ)/33751040) = (697464813149:ℝ)/348206568488 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1507
  · change lowerPayment 1508 ≤ lowerValue ((point 2 split 4096 1508+point 2 split 4096 1509)/2)
    have hp : lowerPayment 1508 = (186322336435:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1508+point 2 split 4096 1509)/2 = (425398627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((425398627:ℝ)/168755200)/ClassicalSixthBranch.v ((425398627:ℝ)/168755200) = (27895499979:ℝ)/13926342424 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1508
  · change lowerPayment 1509 ≤ lowerValue ((point 2 split 4096 1509+point 2 split 4096 1510)/2)
    have hp : lowerPayment 1509 = (186420585689:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1509+point 2 split 4096 1510)/2 = (425456889:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((425456889:ℝ)/168755200)/ClassicalSixthBranch.v ((425456889:ℝ)/168755200) = (697310185801:ℝ)/348110552712 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1509
  · change lowerPayment 1510 ≤ lowerValue ((point 2 split 4096 1510+point 2 split 4096 1511)/2)
    have hp : lowerPayment 1510 = (186518815573:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1510+point 2 split 4096 1511)/2 = (425515151:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((425515151:ℝ)/168755200)/ClassicalSixthBranch.v ((425515151:ℝ)/168755200) = (697232872127:ℝ)/348062544824 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1510
  · change lowerPayment 1511 ≤ lowerValue ((point 2 split 4096 1511+point 2 split 4096 1512)/2)
    have hp : lowerPayment 1511 = (186617026109:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1511+point 2 split 4096 1512)/2 = (425573413:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((425573413:ℝ)/168755200)/ClassicalSixthBranch.v ((425573413:ℝ)/168755200) = (697155558453:ℝ)/348014536936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1511
  · change lowerPayment 1512 ≤ lowerValue ((point 2 split 4096 1512+point 2 split 4096 1513)/2)
    have hp : lowerPayment 1512 = (186715217318:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1512+point 2 split 4096 1513)/2 = (17025267:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((17025267:ℝ)/6750208)/ClassicalSixthBranch.v ((17025267:ℝ)/6750208) = (697078244779:ℝ)/347966529048 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1512
  · change lowerPayment 1513 ≤ lowerValue ((point 2 split 4096 1513+point 2 split 4096 1514)/2)
    have hp : lowerPayment 1513 = (186813389220:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1513+point 2 split 4096 1514)/2 = (425689937:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((425689937:ℝ)/168755200)/ClassicalSixthBranch.v ((425689937:ℝ)/168755200) = (139400186221:ℝ)/69583704232 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1513
  · change lowerPayment 1514 ≤ lowerValue ((point 2 split 4096 1514+point 2 split 4096 1515)/2)
    have hp : lowerPayment 1514 = (186911541838:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1514+point 2 split 4096 1515)/2 = (425748199:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((425748199:ℝ)/168755200)/ClassicalSixthBranch.v ((425748199:ℝ)/168755200) = (696923617431:ℝ)/347870513272 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1514
  · change lowerPayment 1515 ≤ lowerValue ((point 2 split 4096 1515+point 2 split 4096 1516)/2)
    have hp : lowerPayment 1515 = (187009675192:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1515+point 2 split 4096 1516)/2 = (425806461:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((425806461:ℝ)/168755200)/ClassicalSixthBranch.v ((425806461:ℝ)/168755200) = (696846303757:ℝ)/347822505384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1515
  · change lowerPayment 1516 ≤ lowerValue ((point 2 split 4096 1516+point 2 split 4096 1517)/2)
    have hp : lowerPayment 1516 = (187107789303:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1516+point 2 split 4096 1517)/2 = (425864723:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((425864723:ℝ)/168755200)/ClassicalSixthBranch.v ((425864723:ℝ)/168755200) = (696768990083:ℝ)/347774497496 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1516
  · change lowerPayment 1517 ≤ lowerValue ((point 2 split 4096 1517+point 2 split 4096 1518)/2)
    have hp : lowerPayment 1517 = (187205884192:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1517+point 2 split 4096 1518)/2 = (85184597:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((85184597:ℝ)/33751040)/ClassicalSixthBranch.v ((85184597:ℝ)/33751040) = (696691676409:ℝ)/347726489608 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1517
  · change lowerPayment 1518 ≤ lowerValue ((point 2 split 4096 1518+point 2 split 4096 1519)/2)
    have hp : lowerPayment 1518 = (187303959881:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1518+point 2 split 4096 1519)/2 = (425981247:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((425981247:ℝ)/168755200)/ClassicalSixthBranch.v ((425981247:ℝ)/168755200) = (139322872547:ℝ)/69535696344 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1518
  · change lowerPayment 1519 ≤ lowerValue ((point 2 split 4096 1519+point 2 split 4096 1520)/2)
    have hp : lowerPayment 1519 = (187402016391:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1519+point 2 split 4096 1520)/2 = (426039509:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((426039509:ℝ)/168755200)/ClassicalSixthBranch.v ((426039509:ℝ)/168755200) = (696537049061:ℝ)/347630473832 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1519
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_094
