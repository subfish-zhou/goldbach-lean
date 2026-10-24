import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints231
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_231 (j : Fin 16) : lowerPayment (16*231+j.val) ≤
    lowerValue ((point 2 split 4096 (16*231+j.val)+point 2 split 4096 (16*231+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3696 ≤ lowerValue ((point 2 split 4096 3696+point 2 split 4096 3697)/2)
    have hp : lowerPayment 3696 = (384836335825:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3696+point 2 split 4096 3697)/2 = (552875883:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((552875883:ℝ)/168755200)/ClassicalSixthBranch.v ((552875883:ℝ)/168755200) = (528225180763:ℝ)/243117301656 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3696
  · change lowerPayment 3697 ≤ lowerValue ((point 2 split 4096 3697+point 2 split 4096 3698)/2)
    have hp : lowerPayment 3697 = (384931656537:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3697+point 2 split 4096 3698)/2 = (110586829:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((110586829:ℝ)/33751040)/ClassicalSixthBranch.v ((110586829:ℝ)/33751040) = (528147867089:ℝ)/243069293768 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3697
  · change lowerPayment 3698 ≤ lowerValue ((point 2 split 4096 3698+point 2 split 4096 3699)/2)
    have hp : lowerPayment 3698 = (385026992407:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3698+point 2 split 4096 3699)/2 = (552992407:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((552992407:ℝ)/168755200)/ClassicalSixthBranch.v ((552992407:ℝ)/168755200) = (105614110683:ℝ)/48604257176 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3698
  · change lowerPayment 3699 ≤ lowerValue ((point 2 split 4096 3699+point 2 split 4096 3700)/2)
    have hp : lowerPayment 3699 = (385122343449:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3699+point 2 split 4096 3700)/2 = (553050669:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((553050669:ℝ)/168755200)/ClassicalSixthBranch.v ((553050669:ℝ)/168755200) = (527993239741:ℝ)/242973277992 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3699
  · change lowerPayment 3700 ≤ lowerValue ((point 2 split 4096 3700+point 2 split 4096 3701)/2)
    have hp : lowerPayment 3700 = (385217709682:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3700+point 2 split 4096 3701)/2 = (553108931:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((553108931:ℝ)/168755200)/ClassicalSixthBranch.v ((553108931:ℝ)/168755200) = (527915926067:ℝ)/242925270104 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3700
  · change lowerPayment 3701 ≤ lowerValue ((point 2 split 4096 3701+point 2 split 4096 3702)/2)
    have hp : lowerPayment 3701 = (385313091121:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3701+point 2 split 4096 3702)/2 = (553167193:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((553167193:ℝ)/168755200)/ClassicalSixthBranch.v ((553167193:ℝ)/168755200) = (527838612393:ℝ)/242877262216 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3701
  · change lowerPayment 3702 ≤ lowerValue ((point 2 split 4096 3702+point 2 split 4096 3703)/2)
    have hp : lowerPayment 3702 = (385408487783:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3702+point 2 split 4096 3703)/2 = (110645091:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((110645091:ℝ)/33751040)/ClassicalSixthBranch.v ((110645091:ℝ)/33751040) = (527761298719:ℝ)/242829254328 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3702
  · change lowerPayment 3703 ≤ lowerValue ((point 2 split 4096 3703+point 2 split 4096 3704)/2)
    have hp : lowerPayment 3703 = (385503899685:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3703+point 2 split 4096 3704)/2 = (553283717:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((553283717:ℝ)/168755200)/ClassicalSixthBranch.v ((553283717:ℝ)/168755200) = (105536797009:ℝ)/48556249288 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3703
  · change lowerPayment 3704 ≤ lowerValue ((point 2 split 4096 3704+point 2 split 4096 3705)/2)
    have hp : lowerPayment 3704 = (385599326844:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3704+point 2 split 4096 3705)/2 = (553341979:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((553341979:ℝ)/168755200)/ClassicalSixthBranch.v ((553341979:ℝ)/168755200) = (527606671371:ℝ)/242733238552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3704
  · change lowerPayment 3705 ≤ lowerValue ((point 2 split 4096 3705+point 2 split 4096 3706)/2)
    have hp : lowerPayment 3705 = (385694769275:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3705+point 2 split 4096 3706)/2 = (553400241:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((553400241:ℝ)/168755200)/ClassicalSixthBranch.v ((553400241:ℝ)/168755200) = (527529357697:ℝ)/242685230664 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3705
  · change lowerPayment 3706 ≤ lowerValue ((point 2 split 4096 3706+point 2 split 4096 3707)/2)
    have hp : lowerPayment 3706 = (385790226996:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3706+point 2 split 4096 3707)/2 = (553458503:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((553458503:ℝ)/168755200)/ClassicalSixthBranch.v ((553458503:ℝ)/168755200) = (527452044023:ℝ)/242637222776 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3706
  · change lowerPayment 3707 ≤ lowerValue ((point 2 split 4096 3707+point 2 split 4096 3708)/2)
    have hp : lowerPayment 3707 = (385885700023:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3707+point 2 split 4096 3708)/2 = (110703353:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((110703353:ℝ)/33751040)/ClassicalSixthBranch.v ((110703353:ℝ)/33751040) = (527374730349:ℝ)/242589214888 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3707
  · change lowerPayment 3708 ≤ lowerValue ((point 2 split 4096 3708+point 2 split 4096 3709)/2)
    have hp : lowerPayment 3708 = (385981188373:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3708+point 2 split 4096 3709)/2 = (553575027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((553575027:ℝ)/168755200)/ClassicalSixthBranch.v ((553575027:ℝ)/168755200) = (21091896667:ℝ)/9701648280 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3708
  · change lowerPayment 3709 ≤ lowerValue ((point 2 split 4096 3709+point 2 split 4096 3710)/2)
    have hp : lowerPayment 3709 = (386076692062:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3709+point 2 split 4096 3710)/2 = (553633289:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((553633289:ℝ)/168755200)/ClassicalSixthBranch.v ((553633289:ℝ)/168755200) = (527220103001:ℝ)/242493199112 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3709
  · change lowerPayment 3710 ≤ lowerValue ((point 2 split 4096 3710+point 2 split 4096 3711)/2)
    have hp : lowerPayment 3710 = (386172211108:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3710+point 2 split 4096 3711)/2 = (553691551:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((553691551:ℝ)/168755200)/ClassicalSixthBranch.v ((553691551:ℝ)/168755200) = (527142789327:ℝ)/242445191224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3710
  · change lowerPayment 3711 ≤ lowerValue ((point 2 split 4096 3711+point 2 split 4096 3712)/2)
    have hp : lowerPayment 3711 = (386267745526:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3711+point 2 split 4096 3712)/2 = (553749813:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((553749813:ℝ)/168755200)/ClassicalSixthBranch.v ((553749813:ℝ)/168755200) = (527065475653:ℝ)/242397183336 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3711
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_231
