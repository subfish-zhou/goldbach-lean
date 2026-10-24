import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints229
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_229 (j : Fin 16) : lowerPayment (16*229+j.val) ≤
    lowerValue ((point 2 split 4096 (16*229+j.val)+point 2 split 4096 (16*229+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3664 ≤ lowerValue ((point 2 split 4096 3664+point 2 split 4096 3665)/2)
    have hp : lowerPayment 3664 = (381793976977:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3664+point 2 split 4096 3665)/2 = (551011499:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((551011499:ℝ)/168755200)/ClassicalSixthBranch.v ((551011499:ℝ)/168755200) = (530699218331:ℝ)/244653554072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3664
  · change lowerPayment 3665 ≤ lowerValue ((point 2 split 4096 3665+point 2 split 4096 3666)/2)
    have hp : lowerPayment 3665 = (381888821385:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3665+point 2 split 4096 3666)/2 = (551069761:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((551069761:ℝ)/168755200)/ClassicalSixthBranch.v ((551069761:ℝ)/168755200) = (530621904657:ℝ)/244605546184 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3665
  · change lowerPayment 3666 ≤ lowerValue ((point 2 split 4096 3666+point 2 split 4096 3667)/2)
    have hp : lowerPayment 3666 = (381983680422:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3666+point 2 split 4096 3667)/2 = (551128023:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((551128023:ℝ)/168755200)/ClassicalSixthBranch.v ((551128023:ℝ)/168755200) = (530544590983:ℝ)/244557538296 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3666
  · change lowerPayment 3667 ≤ lowerValue ((point 2 split 4096 3667+point 2 split 4096 3668)/2)
    have hp : lowerPayment 3667 = (382078554106:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3667+point 2 split 4096 3668)/2 = (110237257:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((110237257:ℝ)/33751040)/ClassicalSixthBranch.v ((110237257:ℝ)/33751040) = (530467277309:ℝ)/244509530408 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3667
  · change lowerPayment 3668 ≤ lowerValue ((point 2 split 4096 3668+point 2 split 4096 3669)/2)
    have hp : lowerPayment 3668 = (382173442453:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3668+point 2 split 4096 3669)/2 = (551244547:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((551244547:ℝ)/168755200)/ClassicalSixthBranch.v ((551244547:ℝ)/168755200) = (106077992727:ℝ)/48892304504 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3668
  · change lowerPayment 3669 ≤ lowerValue ((point 2 split 4096 3669+point 2 split 4096 3670)/2)
    have hp : lowerPayment 3669 = (382268345478:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3669+point 2 split 4096 3670)/2 = (551302809:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((551302809:ℝ)/168755200)/ClassicalSixthBranch.v ((551302809:ℝ)/168755200) = (530312649961:ℝ)/244413514632 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3669
  · change lowerPayment 3670 ≤ lowerValue ((point 2 split 4096 3670+point 2 split 4096 3671)/2)
    have hp : lowerPayment 3670 = (382363263198:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3670+point 2 split 4096 3671)/2 = (551361071:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((551361071:ℝ)/168755200)/ClassicalSixthBranch.v ((551361071:ℝ)/168755200) = (530235336287:ℝ)/244365506744 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3670
  · change lowerPayment 3671 ≤ lowerValue ((point 2 split 4096 3671+point 2 split 4096 3672)/2)
    have hp : lowerPayment 3671 = (382458195630:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3671+point 2 split 4096 3672)/2 = (551419333:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((551419333:ℝ)/168755200)/ClassicalSixthBranch.v ((551419333:ℝ)/168755200) = (530158022613:ℝ)/244317498856 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3671
  · change lowerPayment 3672 ≤ lowerValue ((point 2 split 4096 3672+point 2 split 4096 3673)/2)
    have hp : lowerPayment 3672 = (382553142791:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3672+point 2 split 4096 3673)/2 = (110295519:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((110295519:ℝ)/33751040)/ClassicalSixthBranch.v ((110295519:ℝ)/33751040) = (530080708939:ℝ)/244269490968 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3672
  · change lowerPayment 3673 ≤ lowerValue ((point 2 split 4096 3673+point 2 split 4096 3674)/2)
    have hp : lowerPayment 3673 = (382648104695:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3673+point 2 split 4096 3674)/2 = (551535857:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((551535857:ℝ)/168755200)/ClassicalSixthBranch.v ((551535857:ℝ)/168755200) = (106000679053:ℝ)/48844296616 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3673
  · change lowerPayment 3674 ≤ lowerValue ((point 2 split 4096 3674+point 2 split 4096 3675)/2)
    have hp : lowerPayment 3674 = (382743081361:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3674+point 2 split 4096 3675)/2 = (551594119:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((551594119:ℝ)/168755200)/ClassicalSixthBranch.v ((551594119:ℝ)/168755200) = (529926081591:ℝ)/244173475192 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3674
  · change lowerPayment 3675 ≤ lowerValue ((point 2 split 4096 3675+point 2 split 4096 3676)/2)
    have hp : lowerPayment 3675 = (382838072804:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3675+point 2 split 4096 3676)/2 = (551652381:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((551652381:ℝ)/168755200)/ClassicalSixthBranch.v ((551652381:ℝ)/168755200) = (529848767917:ℝ)/244125467304 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3675
  · change lowerPayment 3676 ≤ lowerValue ((point 2 split 4096 3676+point 2 split 4096 3677)/2)
    have hp : lowerPayment 3676 = (382933079040:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3676+point 2 split 4096 3677)/2 = (551710643:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((551710643:ℝ)/168755200)/ClassicalSixthBranch.v ((551710643:ℝ)/168755200) = (529771454243:ℝ)/244077459416 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3676
  · change lowerPayment 3677 ≤ lowerValue ((point 2 split 4096 3677+point 2 split 4096 3678)/2)
    have hp : lowerPayment 3677 = (383028100087:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3677+point 2 split 4096 3678)/2 = (110353781:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((110353781:ℝ)/33751040)/ClassicalSixthBranch.v ((110353781:ℝ)/33751040) = (529694140569:ℝ)/244029451528 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3677
  · change lowerPayment 3678 ≤ lowerValue ((point 2 split 4096 3678+point 2 split 4096 3679)/2)
    have hp : lowerPayment 3678 = (383123135961:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3678+point 2 split 4096 3679)/2 = (551827167:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((551827167:ℝ)/168755200)/ClassicalSixthBranch.v ((551827167:ℝ)/168755200) = (105923365379:ℝ)/48796288728 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3678
  · change lowerPayment 3679 ≤ lowerValue ((point 2 split 4096 3679+point 2 split 4096 3680)/2)
    have hp : lowerPayment 3679 = (383218186677:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3679+point 2 split 4096 3680)/2 = (551885429:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((551885429:ℝ)/168755200)/ClassicalSixthBranch.v ((551885429:ℝ)/168755200) = (529539513221:ℝ)/243933435752 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3679
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_229
