import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints225
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_225 (j : Fin 16) : lowerPayment (16*225+j.val) ≤
    lowerValue ((point 2 split 4096 (16*225+j.val)+point 2 split 4096 (16*225+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3600 ≤ lowerValue ((point 2 split 4096 3600+point 2 split 4096 3601)/2)
    have hp : lowerPayment 3600 = (375753619651:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3600+point 2 split 4096 3601)/2 = (547282731:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((547282731:ℝ)/168755200)/ClassicalSixthBranch.v ((547282731:ℝ)/168755200) = (535647293467:ℝ)/247726058904 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3600
  · change lowerPayment 3601 ≤ lowerValue ((point 2 split 4096 3601+point 2 split 4096 3602)/2)
    have hp : lowerPayment 3601 = (375847561559:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3601+point 2 split 4096 3602)/2 = (547340993:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((547340993:ℝ)/168755200)/ClassicalSixthBranch.v ((547340993:ℝ)/168755200) = (535569979793:ℝ)/247678051016 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3601
  · change lowerPayment 3602 ≤ lowerValue ((point 2 split 4096 3602+point 2 split 4096 3603)/2)
    have hp : lowerPayment 3602 = (375941517061:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3602+point 2 split 4096 3603)/2 = (109479851:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((109479851:ℝ)/33751040)/ClassicalSixthBranch.v ((109479851:ℝ)/33751040) = (535492666119:ℝ)/247630043128 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3602
  · change lowerPayment 3603 ≤ lowerValue ((point 2 split 4096 3603+point 2 split 4096 3604)/2)
    have hp : lowerPayment 3603 = (376035486173:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3603+point 2 split 4096 3604)/2 = (547457517:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((547457517:ℝ)/168755200)/ClassicalSixthBranch.v ((547457517:ℝ)/168755200) = (107083070489:ℝ)/49516407048 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3603
  · change lowerPayment 3604 ≤ lowerValue ((point 2 split 4096 3604+point 2 split 4096 3605)/2)
    have hp : lowerPayment 3604 = (376129468910:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3604+point 2 split 4096 3605)/2 = (547515779:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((547515779:ℝ)/168755200)/ClassicalSixthBranch.v ((547515779:ℝ)/168755200) = (535338038771:ℝ)/247534027352 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3604
  · change lowerPayment 3605 ≤ lowerValue ((point 2 split 4096 3605+point 2 split 4096 3606)/2)
    have hp : lowerPayment 3605 = (376223465288:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3605+point 2 split 4096 3606)/2 = (547574041:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((547574041:ℝ)/168755200)/ClassicalSixthBranch.v ((547574041:ℝ)/168755200) = (535260725097:ℝ)/247486019464 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3605
  · change lowerPayment 3606 ≤ lowerValue ((point 2 split 4096 3606+point 2 split 4096 3607)/2)
    have hp : lowerPayment 3606 = (376317475324:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3606+point 2 split 4096 3607)/2 = (547632303:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((547632303:ℝ)/168755200)/ClassicalSixthBranch.v ((547632303:ℝ)/168755200) = (535183411423:ℝ)/247438011576 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3606
  · change lowerPayment 3607 ≤ lowerValue ((point 2 split 4096 3607+point 2 split 4096 3608)/2)
    have hp : lowerPayment 3607 = (376411499034:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3607+point 2 split 4096 3608)/2 = (109538113:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((109538113:ℝ)/33751040)/ClassicalSixthBranch.v ((109538113:ℝ)/33751040) = (535106097749:ℝ)/247390003688 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3607
  · change lowerPayment 3608 ≤ lowerValue ((point 2 split 4096 3608+point 2 split 4096 3609)/2)
    have hp : lowerPayment 3608 = (376505536433:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3608+point 2 split 4096 3609)/2 = (547748827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((547748827:ℝ)/168755200)/ClassicalSixthBranch.v ((547748827:ℝ)/168755200) = (21401151363:ℝ)/9893679832 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3608
  · change lowerPayment 3609 ≤ lowerValue ((point 2 split 4096 3609+point 2 split 4096 3610)/2)
    have hp : lowerPayment 3609 = (376599587538:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3609+point 2 split 4096 3610)/2 = (547807089:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((547807089:ℝ)/168755200)/ClassicalSixthBranch.v ((547807089:ℝ)/168755200) = (534951470401:ℝ)/247293987912 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3609
  · change lowerPayment 3610 ≤ lowerValue ((point 2 split 4096 3610+point 2 split 4096 3611)/2)
    have hp : lowerPayment 3610 = (376693652364:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3610+point 2 split 4096 3611)/2 = (547865351:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((547865351:ℝ)/168755200)/ClassicalSixthBranch.v ((547865351:ℝ)/168755200) = (534874156727:ℝ)/247245980024 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3610
  · change lowerPayment 3611 ≤ lowerValue ((point 2 split 4096 3611+point 2 split 4096 3612)/2)
    have hp : lowerPayment 3611 = (376787730929:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3611+point 2 split 4096 3612)/2 = (547923613:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((547923613:ℝ)/168755200)/ClassicalSixthBranch.v ((547923613:ℝ)/168755200) = (534796843053:ℝ)/247197972136 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3611
  · change lowerPayment 3612 ≤ lowerValue ((point 2 split 4096 3612+point 2 split 4096 3613)/2)
    have hp : lowerPayment 3612 = (376881823247:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3612+point 2 split 4096 3613)/2 = (21919275:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((21919275:ℝ)/6750208)/ClassicalSixthBranch.v ((21919275:ℝ)/6750208) = (534719529379:ℝ)/247149964248 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3612
  · change lowerPayment 3613 ≤ lowerValue ((point 2 split 4096 3613+point 2 split 4096 3614)/2)
    have hp : lowerPayment 3613 = (376975929335:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3613+point 2 split 4096 3614)/2 = (548040137:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((548040137:ℝ)/168755200)/ClassicalSixthBranch.v ((548040137:ℝ)/168755200) = (106928443141:ℝ)/49420391272 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3613
  · change lowerPayment 3614 ≤ lowerValue ((point 2 split 4096 3614+point 2 split 4096 3615)/2)
    have hp : lowerPayment 3614 = (377070049209:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3614+point 2 split 4096 3615)/2 = (548098399:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((548098399:ℝ)/168755200)/ClassicalSixthBranch.v ((548098399:ℝ)/168755200) = (534564902031:ℝ)/247053948472 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3614
  · change lowerPayment 3615 ≤ lowerValue ((point 2 split 4096 3615+point 2 split 4096 3616)/2)
    have hp : lowerPayment 3615 = (377164182885:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3615+point 2 split 4096 3616)/2 = (548156661:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((548156661:ℝ)/168755200)/ClassicalSixthBranch.v ((548156661:ℝ)/168755200) = (534487588357:ℝ)/247005940584 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3615
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_225
