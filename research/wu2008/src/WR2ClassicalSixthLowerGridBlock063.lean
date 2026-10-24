import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints063
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_063 (j : Fin 16) : lowerPayment (16*63+j.val) ≤
    lowerValue ((point 2 split 4096 (16*63+j.val)+point 2 split 4096 (16*63+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1008 ≤ lowerValue ((point 2 split 4096 1008+point 2 split 4096 1009)/2)
    have hp : lowerPayment 1008 = (134291723008:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1008+point 2 split 4096 1009)/2 = (396267627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((396267627:ℝ)/168755200)/ClassicalSixthBranch.v ((396267627:ℝ)/168755200) = (29441773459:ℝ)/14886500184 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1008
  · change lowerPayment 1009 ≤ lowerValue ((point 2 split 4096 1009+point 2 split 4096 1010)/2)
    have hp : lowerPayment 1009 = (134402605799:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1009+point 2 split 4096 1010)/2 = (396325889:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((396325889:ℝ)/168755200)/ClassicalSixthBranch.v ((396325889:ℝ)/168755200) = (735967022801:ℝ)/372114496712 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1009
  · change lowerPayment 1010 ≤ lowerValue ((point 2 split 4096 1010+point 2 split 4096 1011)/2)
    have hp : lowerPayment 1010 = (134513456767:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1010+point 2 split 4096 1011)/2 = (396384151:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((396384151:ℝ)/168755200)/ClassicalSixthBranch.v ((396384151:ℝ)/168755200) = (735889709127:ℝ)/372066488824 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1010
  · change lowerPayment 1011 ≤ lowerValue ((point 2 split 4096 1011+point 2 split 4096 1012)/2)
    have hp : lowerPayment 1011 = (134624275941:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1011+point 2 split 4096 1012)/2 = (396442413:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((396442413:ℝ)/168755200)/ClassicalSixthBranch.v ((396442413:ℝ)/168755200) = (735812395453:ℝ)/372018480936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1011
  · change lowerPayment 1012 ≤ lowerValue ((point 2 split 4096 1012+point 2 split 4096 1013)/2)
    have hp : lowerPayment 1012 = (134735063350:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1012+point 2 split 4096 1013)/2 = (15860027:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((15860027:ℝ)/6750208)/ClassicalSixthBranch.v ((15860027:ℝ)/6750208) = (735735081779:ℝ)/371970473048 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1012
  · change lowerPayment 1013 ≤ lowerValue ((point 2 split 4096 1013+point 2 split 4096 1014)/2)
    have hp : lowerPayment 1013 = (134845819024:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1013+point 2 split 4096 1014)/2 = (396558937:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((396558937:ℝ)/168755200)/ClassicalSixthBranch.v ((396558937:ℝ)/168755200) = (147131553621:ℝ)/74384493032 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1013
  · change lowerPayment 1014 ≤ lowerValue ((point 2 split 4096 1014+point 2 split 4096 1015)/2)
    have hp : lowerPayment 1014 = (134956542992:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1014+point 2 split 4096 1015)/2 = (396617199:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((396617199:ℝ)/168755200)/ClassicalSixthBranch.v ((396617199:ℝ)/168755200) = (735580454431:ℝ)/371874457272 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1014
  · change lowerPayment 1015 ≤ lowerValue ((point 2 split 4096 1015+point 2 split 4096 1016)/2)
    have hp : lowerPayment 1015 = (135067235283:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1015+point 2 split 4096 1016)/2 = (396675461:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((396675461:ℝ)/168755200)/ClassicalSixthBranch.v ((396675461:ℝ)/168755200) = (735503140757:ℝ)/371826449384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1015
  · change lowerPayment 1016 ≤ lowerValue ((point 2 split 4096 1016+point 2 split 4096 1017)/2)
    have hp : lowerPayment 1016 = (135177895927:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1016+point 2 split 4096 1017)/2 = (396733723:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((396733723:ℝ)/168755200)/ClassicalSixthBranch.v ((396733723:ℝ)/168755200) = (735425827083:ℝ)/371778441496 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1016
  · change lowerPayment 1017 ≤ lowerValue ((point 2 split 4096 1017+point 2 split 4096 1018)/2)
    have hp : lowerPayment 1017 = (135288524954:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1017+point 2 split 4096 1018)/2 = (79358397:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((79358397:ℝ)/33751040)/ClassicalSixthBranch.v ((79358397:ℝ)/33751040) = (735348513409:ℝ)/371730433608 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1017
  · change lowerPayment 1018 ≤ lowerValue ((point 2 split 4096 1018+point 2 split 4096 1019)/2)
    have hp : lowerPayment 1018 = (135399122391:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1018+point 2 split 4096 1019)/2 = (396850247:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((396850247:ℝ)/168755200)/ClassicalSixthBranch.v ((396850247:ℝ)/168755200) = (147054239947:ℝ)/74336485144 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1018
  · change lowerPayment 1019 ≤ lowerValue ((point 2 split 4096 1019+point 2 split 4096 1020)/2)
    have hp : lowerPayment 1019 = (135509688269:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1019+point 2 split 4096 1020)/2 = (396908509:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((396908509:ℝ)/168755200)/ClassicalSixthBranch.v ((396908509:ℝ)/168755200) = (735193886061:ℝ)/371634417832 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1019
  · change lowerPayment 1020 ≤ lowerValue ((point 2 split 4096 1020+point 2 split 4096 1021)/2)
    have hp : lowerPayment 1020 = (135620222617:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1020+point 2 split 4096 1021)/2 = (396966771:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((396966771:ℝ)/168755200)/ClassicalSixthBranch.v ((396966771:ℝ)/168755200) = (735116572387:ℝ)/371586409944 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1020
  · change lowerPayment 1021 ≤ lowerValue ((point 2 split 4096 1021+point 2 split 4096 1022)/2)
    have hp : lowerPayment 1021 = (135730725464:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1021+point 2 split 4096 1022)/2 = (397025033:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((397025033:ℝ)/168755200)/ClassicalSixthBranch.v ((397025033:ℝ)/168755200) = (735039258713:ℝ)/371538402056 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1021
  · change lowerPayment 1022 ≤ lowerValue ((point 2 split 4096 1022+point 2 split 4096 1023)/2)
    have hp : lowerPayment 1022 = (135841196839:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1022+point 2 split 4096 1023)/2 = (79416659:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((79416659:ℝ)/33751040)/ClassicalSixthBranch.v ((79416659:ℝ)/33751040) = (734961945039:ℝ)/371490394168 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1022
  · change lowerPayment 1023 ≤ lowerValue ((point 2 split 4096 1023+point 2 split 4096 1024)/2)
    have hp : lowerPayment 1023 = (135951636771:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1023+point 2 split 4096 1024)/2 = (397141557:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((397141557:ℝ)/168755200)/ClassicalSixthBranch.v ((397141557:ℝ)/168755200) = (146976926273:ℝ)/74288477256 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1023
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_063
