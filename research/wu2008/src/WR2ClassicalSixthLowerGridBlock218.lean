import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints218
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_218 (j : Fin 16) : lowerPayment (16*218+j.val) ≤
    lowerValue ((point 2 split 4096 (16*218+j.val)+point 2 split 4096 (16*218+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3488 ≤ lowerValue ((point 2 split 4096 3488+point 2 split 4096 3489)/2)
    have hp : lowerPayment 3488 = (365314329563:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3488+point 2 split 4096 3489)/2 = (540757387:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((540757387:ℝ)/168755200)/ClassicalSixthBranch.v ((540757387:ℝ)/168755200) = (108861284991:ℝ)/50620588472 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3488
  · change lowerPayment 3489 ≤ lowerValue ((point 2 split 4096 3489+point 2 split 4096 3490)/2)
    have hp : lowerPayment 3489 = (365406849125:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3489+point 2 split 4096 3490)/2 = (540815649:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((540815649:ℝ)/168755200)/ClassicalSixthBranch.v ((540815649:ℝ)/168755200) = (544229111281:ℝ)/253054934472 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3489
  · change lowerPayment 3490 ≤ lowerValue ((point 2 split 4096 3490+point 2 split 4096 3491)/2)
    have hp : lowerPayment 3490 = (365499380518:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3490+point 2 split 4096 3491)/2 = (540873911:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((540873911:ℝ)/168755200)/ClassicalSixthBranch.v ((540873911:ℝ)/168755200) = (544151797607:ℝ)/253006926584 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3490
  · change lowerPayment 3491 ≤ lowerValue ((point 2 split 4096 3491+point 2 split 4096 3492)/2)
    have hp : lowerPayment 3491 = (365591923758:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3491+point 2 split 4096 3492)/2 = (540932173:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((540932173:ℝ)/168755200)/ClassicalSixthBranch.v ((540932173:ℝ)/168755200) = (544074483933:ℝ)/252958918696 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3491
  · change lowerPayment 3492 ≤ lowerValue ((point 2 split 4096 3492+point 2 split 4096 3493)/2)
    have hp : lowerPayment 3492 = (365684478861:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3492+point 2 split 4096 3493)/2 = (108198087:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((108198087:ℝ)/33751040)/ClassicalSixthBranch.v ((108198087:ℝ)/33751040) = (543997170259:ℝ)/252910910808 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3492
  · change lowerPayment 3493 ≤ lowerValue ((point 2 split 4096 3493+point 2 split 4096 3494)/2)
    have hp : lowerPayment 3493 = (365777045842:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3493+point 2 split 4096 3494)/2 = (541048697:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((541048697:ℝ)/168755200)/ClassicalSixthBranch.v ((541048697:ℝ)/168755200) = (108783971317:ℝ)/50572580584 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3493
  · change lowerPayment 3494 ≤ lowerValue ((point 2 split 4096 3494+point 2 split 4096 3495)/2)
    have hp : lowerPayment 3494 = (365869624717:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3494+point 2 split 4096 3495)/2 = (541106959:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((541106959:ℝ)/168755200)/ClassicalSixthBranch.v ((541106959:ℝ)/168755200) = (543842542911:ℝ)/252814895032 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3494
  · change lowerPayment 3495 ≤ lowerValue ((point 2 split 4096 3495+point 2 split 4096 3496)/2)
    have hp : lowerPayment 3495 = (365962215500:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3495+point 2 split 4096 3496)/2 = (541165221:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((541165221:ℝ)/168755200)/ClassicalSixthBranch.v ((541165221:ℝ)/168755200) = (543765229237:ℝ)/252766887144 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3495
  · change lowerPayment 3496 ≤ lowerValue ((point 2 split 4096 3496+point 2 split 4096 3497)/2)
    have hp : lowerPayment 3496 = (366054818208:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3496+point 2 split 4096 3497)/2 = (541223483:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((541223483:ℝ)/168755200)/ClassicalSixthBranch.v ((541223483:ℝ)/168755200) = (543687915563:ℝ)/252718879256 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3496
  · change lowerPayment 3497 ≤ lowerValue ((point 2 split 4096 3497+point 2 split 4096 3498)/2)
    have hp : lowerPayment 3497 = (366147432856:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3497+point 2 split 4096 3498)/2 = (108256349:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((108256349:ℝ)/33751040)/ClassicalSixthBranch.v ((108256349:ℝ)/33751040) = (543610601889:ℝ)/252670871368 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3497
  · change lowerPayment 3498 ≤ lowerValue ((point 2 split 4096 3498+point 2 split 4096 3499)/2)
    have hp : lowerPayment 3498 = (366240059459:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3498+point 2 split 4096 3499)/2 = (541340007:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((541340007:ℝ)/168755200)/ClassicalSixthBranch.v ((541340007:ℝ)/168755200) = (108706657643:ℝ)/50524572696 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3498
  · change lowerPayment 3499 ≤ lowerValue ((point 2 split 4096 3499+point 2 split 4096 3500)/2)
    have hp : lowerPayment 3499 = (366332698033:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3499+point 2 split 4096 3500)/2 = (541398269:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((541398269:ℝ)/168755200)/ClassicalSixthBranch.v ((541398269:ℝ)/168755200) = (543455974541:ℝ)/252574855592 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3499
  · change lowerPayment 3500 ≤ lowerValue ((point 2 split 4096 3500+point 2 split 4096 3501)/2)
    have hp : lowerPayment 3500 = (366425348594:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3500+point 2 split 4096 3501)/2 = (541456531:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((541456531:ℝ)/168755200)/ClassicalSixthBranch.v ((541456531:ℝ)/168755200) = (543378660867:ℝ)/252526847704 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3500
  · change lowerPayment 3501 ≤ lowerValue ((point 2 split 4096 3501+point 2 split 4096 3502)/2)
    have hp : lowerPayment 3501 = (366518011157:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3501+point 2 split 4096 3502)/2 = (541514793:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((541514793:ℝ)/168755200)/ClassicalSixthBranch.v ((541514793:ℝ)/168755200) = (543301347193:ℝ)/252478839816 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3501
  · change lowerPayment 3502 ≤ lowerValue ((point 2 split 4096 3502+point 2 split 4096 3503)/2)
    have hp : lowerPayment 3502 = (366610685737:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3502+point 2 split 4096 3503)/2 = (108314611:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((108314611:ℝ)/33751040)/ClassicalSixthBranch.v ((108314611:ℝ)/33751040) = (543224033519:ℝ)/252430831928 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3502
  · change lowerPayment 3503 ≤ lowerValue ((point 2 split 4096 3503+point 2 split 4096 3504)/2)
    have hp : lowerPayment 3503 = (366703372350:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3503+point 2 split 4096 3504)/2 = (541631317:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((541631317:ℝ)/168755200)/ClassicalSixthBranch.v ((541631317:ℝ)/168755200) = (108629343969:ℝ)/50476564808 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3503
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_218
