import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints059
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_059 (j : Fin 16) : lowerPayment (16*59+j.val) ≤
    lowerValue ((point 2 split 4096 (16*59+j.val)+point 2 split 4096 (16*59+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 944 ≤ lowerValue ((point 2 split 4096 944+point 2 split 4096 945)/2)
    have hp : lowerPayment 944 = (127127668507:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 944+point 2 split 4096 945)/2 = (392538859:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((392538859:ℝ)/168755200)/ClassicalSixthBranch.v ((392538859:ℝ)/168755200) = (740992411611:ℝ)/375235009432 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_944
  · change lowerPayment 945 ≤ lowerValue ((point 2 split 4096 945+point 2 split 4096 946)/2)
    have hp : lowerPayment 945 = (127240650203:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 945+point 2 split 4096 946)/2 = (392597121:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((392597121:ℝ)/168755200)/ClassicalSixthBranch.v ((392597121:ℝ)/168755200) = (740915097937:ℝ)/375187001544 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_945
  · change lowerPayment 946 ≤ lowerValue ((point 2 split 4096 946+point 2 split 4096 947)/2)
    have hp : lowerPayment 946 = (127353598146:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 946+point 2 split 4096 947)/2 = (392655383:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((392655383:ℝ)/168755200)/ClassicalSixthBranch.v ((392655383:ℝ)/168755200) = (740837784263:ℝ)/375138993656 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_946
  · change lowerPayment 947 ≤ lowerValue ((point 2 split 4096 947+point 2 split 4096 948)/2)
    have hp : lowerPayment 947 = (127466512368:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 947+point 2 split 4096 948)/2 = (78542729:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((78542729:ℝ)/33751040)/ClassicalSixthBranch.v ((78542729:ℝ)/33751040) = (740760470589:ℝ)/375090985768 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_947
  · change lowerPayment 948 ≤ lowerValue ((point 2 split 4096 948+point 2 split 4096 949)/2)
    have hp : lowerPayment 948 = (127579392898:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 948+point 2 split 4096 949)/2 = (392771907:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((392771907:ℝ)/168755200)/ClassicalSixthBranch.v ((392771907:ℝ)/168755200) = (148136631383:ℝ)/75008595576 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_948
  · change lowerPayment 949 ≤ lowerValue ((point 2 split 4096 949+point 2 split 4096 950)/2)
    have hp : lowerPayment 949 = (127692239769:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 949+point 2 split 4096 950)/2 = (392830169:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((392830169:ℝ)/168755200)/ClassicalSixthBranch.v ((392830169:ℝ)/168755200) = (740605843241:ℝ)/374994969992 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_949
  · change lowerPayment 950 ≤ lowerValue ((point 2 split 4096 950+point 2 split 4096 951)/2)
    have hp : lowerPayment 950 = (127805053010:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 950+point 2 split 4096 951)/2 = (392888431:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((392888431:ℝ)/168755200)/ClassicalSixthBranch.v ((392888431:ℝ)/168755200) = (740528529567:ℝ)/374946962104 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_950
  · change lowerPayment 951 ≤ lowerValue ((point 2 split 4096 951+point 2 split 4096 952)/2)
    have hp : lowerPayment 951 = (127917832653:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 951+point 2 split 4096 952)/2 = (392946693:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((392946693:ℝ)/168755200)/ClassicalSixthBranch.v ((392946693:ℝ)/168755200) = (740451215893:ℝ)/374898954216 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_951
  · change lowerPayment 952 ≤ lowerValue ((point 2 split 4096 952+point 2 split 4096 953)/2)
    have hp : lowerPayment 952 = (128030578728:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 952+point 2 split 4096 953)/2 = (78600991:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((78600991:ℝ)/33751040)/ClassicalSixthBranch.v ((78600991:ℝ)/33751040) = (740373902219:ℝ)/374850946328 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_952
  · change lowerPayment 953 ≤ lowerValue ((point 2 split 4096 953+point 2 split 4096 954)/2)
    have hp : lowerPayment 953 = (128143291266:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 953+point 2 split 4096 954)/2 = (393063217:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((393063217:ℝ)/168755200)/ClassicalSixthBranch.v ((393063217:ℝ)/168755200) = (148059317709:ℝ)/74960587688 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_953
  · change lowerPayment 954 ≤ lowerValue ((point 2 split 4096 954+point 2 split 4096 955)/2)
    have hp : lowerPayment 954 = (128255970298:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 954+point 2 split 4096 955)/2 = (393121479:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((393121479:ℝ)/168755200)/ClassicalSixthBranch.v ((393121479:ℝ)/168755200) = (740219274871:ℝ)/374754930552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_954
  · change lowerPayment 955 ≤ lowerValue ((point 2 split 4096 955+point 2 split 4096 956)/2)
    have hp : lowerPayment 955 = (128368615854:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 955+point 2 split 4096 956)/2 = (393179741:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((393179741:ℝ)/168755200)/ClassicalSixthBranch.v ((393179741:ℝ)/168755200) = (740141961197:ℝ)/374706922664 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_955
  · change lowerPayment 956 ≤ lowerValue ((point 2 split 4096 956+point 2 split 4096 957)/2)
    have hp : lowerPayment 956 = (128481227965:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 956+point 2 split 4096 957)/2 = (393238003:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((393238003:ℝ)/168755200)/ClassicalSixthBranch.v ((393238003:ℝ)/168755200) = (740064647523:ℝ)/374658914776 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_956
  · change lowerPayment 957 ≤ lowerValue ((point 2 split 4096 957+point 2 split 4096 958)/2)
    have hp : lowerPayment 957 = (128593806661:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 957+point 2 split 4096 958)/2 = (78659253:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((78659253:ℝ)/33751040)/ClassicalSixthBranch.v ((78659253:ℝ)/33751040) = (739987333849:ℝ)/374610906888 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_957
  · change lowerPayment 958 ≤ lowerValue ((point 2 split 4096 958+point 2 split 4096 959)/2)
    have hp : lowerPayment 958 = (128706351974:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 958+point 2 split 4096 959)/2 = (393354527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((393354527:ℝ)/168755200)/ClassicalSixthBranch.v ((393354527:ℝ)/168755200) = (29596400807:ℝ)/14982515960 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_958
  · change lowerPayment 959 ≤ lowerValue ((point 2 split 4096 959+point 2 split 4096 960)/2)
    have hp : lowerPayment 959 = (128818863934:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 959+point 2 split 4096 960)/2 = (393412789:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((393412789:ℝ)/168755200)/ClassicalSixthBranch.v ((393412789:ℝ)/168755200) = (739832706501:ℝ)/374514891112 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_959
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_059
