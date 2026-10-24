import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints238
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_238 (j : Fin 16) : upperPayment (16*238+j.val) ≤
    upperValue ((point split endpoint 4096 (16*238+j.val)+point split endpoint 4096 (16*238+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3808 ≤ upperValue ((point split endpoint 4096 3808+point split endpoint 4096 3809)/2)
    have hp : upperPayment 3808 = (46802640764:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3808+point split endpoint 4096 3809)/2 = (671935327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((671935327:ℝ)/168755200)*ClassicalSixthBranch.v ((671935327:ℝ)/168755200)/ClassicalSixthBranch.r = (78560135634897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3808
  · change upperPayment 3809 ≤ upperValue ((point split endpoint 4096 3809+point split endpoint 4096 3810)/2)
    have hp : upperPayment 3809 = (46645734145:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3809+point split endpoint 4096 3810)/2 = (671960477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((671960477:ℝ)/168755200)*ClassicalSixthBranch.v ((671960477:ℝ)/168755200)/ClassicalSixthBranch.r = (78541828008281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3809
  · change upperPayment 3810 ≤ upperValue ((point split endpoint 4096 3810+point split endpoint 4096 3811)/2)
    have hp : upperPayment 3810 = (46488787504:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3810+point split endpoint 4096 3811)/2 = (671985627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((671985627:ℝ)/168755200)*ClassicalSixthBranch.v ((671985627:ℝ)/168755200)/ClassicalSixthBranch.r = (78523522405737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3810
  · change upperPayment 3811 ≤ upperValue ((point split endpoint 4096 3811+point split endpoint 4096 3812)/2)
    have hp : upperPayment 3811 = (46331800832:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3811+point split endpoint 4096 3812)/2 = (672010777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((672010777:ℝ)/168755200)*ClassicalSixthBranch.v ((672010777:ℝ)/168755200)/ClassicalSixthBranch.r = (78505218827265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3811
  · change upperPayment 3812 ≤ upperValue ((point split endpoint 4096 3812+point split endpoint 4096 3813)/2)
    have hp : upperPayment 3812 = (46174774118:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3812+point split endpoint 4096 3813)/2 = (672035927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((672035927:ℝ)/168755200)*ClassicalSixthBranch.v ((672035927:ℝ)/168755200)/ClassicalSixthBranch.r = (78486917272865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3812
  · change upperPayment 3813 ≤ upperValue ((point split endpoint 4096 3813+point split endpoint 4096 3814)/2)
    have hp : upperPayment 3813 = (46017707350:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3813+point split endpoint 4096 3814)/2 = (672061077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((672061077:ℝ)/168755200)*ClassicalSixthBranch.v ((672061077:ℝ)/168755200)/ClassicalSixthBranch.r = (78468617742537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3813
  · change upperPayment 3814 ≤ upperValue ((point split endpoint 4096 3814+point split endpoint 4096 3815)/2)
    have hp : upperPayment 3814 = (45860600518:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3814+point split endpoint 4096 3815)/2 = (6525109:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((6525109:ℝ)/1638400)*ClassicalSixthBranch.v ((6525109:ℝ)/1638400)/ClassicalSixthBranch.r = (761653594527:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3814
  · change upperPayment 3815 ≤ upperValue ((point split endpoint 4096 3815+point split endpoint 4096 3816)/2)
    have hp : upperPayment 3815 = (45703453611:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3815+point split endpoint 4096 3816)/2 = (672111377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((672111377:ℝ)/168755200)*ClassicalSixthBranch.v ((672111377:ℝ)/168755200)/ClassicalSixthBranch.r = (78432024754097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3815
  · change upperPayment 3816 ≤ upperValue ((point split endpoint 4096 3816+point split endpoint 4096 3817)/2)
    have hp : upperPayment 3816 = (45546266618:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3816+point split endpoint 4096 3817)/2 = (672136527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((672136527:ℝ)/168755200)*ClassicalSixthBranch.v ((672136527:ℝ)/168755200)/ClassicalSixthBranch.r = (78413731295985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3816
  · change upperPayment 3817 ≤ upperValue ((point split endpoint 4096 3817+point split endpoint 4096 3818)/2)
    have hp : upperPayment 3817 = (45389039529:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3817+point split endpoint 4096 3818)/2 = (672161677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((672161677:ℝ)/168755200)*ClassicalSixthBranch.v ((672161677:ℝ)/168755200)/ClassicalSixthBranch.r = (78395439861945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3817
  · change upperPayment 3818 ≤ upperValue ((point split endpoint 4096 3818+point split endpoint 4096 3819)/2)
    have hp : upperPayment 3818 = (45231772332:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3818+point split endpoint 4096 3819)/2 = (672186827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((672186827:ℝ)/168755200)*ClassicalSixthBranch.v ((672186827:ℝ)/168755200)/ClassicalSixthBranch.r = (78377150451977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3818
  · change upperPayment 3819 ≤ upperValue ((point split endpoint 4096 3819+point split endpoint 4096 3820)/2)
    have hp : upperPayment 3819 = (45074465016:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3819+point split endpoint 4096 3820)/2 = (672211977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((672211977:ℝ)/168755200)*ClassicalSixthBranch.v ((672211977:ℝ)/168755200)/ClassicalSixthBranch.r = (78358863066081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3819
  · change upperPayment 3820 ≤ upperValue ((point split endpoint 4096 3820+point split endpoint 4096 3821)/2)
    have hp : upperPayment 3820 = (44917117571:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3820+point split endpoint 4096 3821)/2 = (672237127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((672237127:ℝ)/168755200)*ClassicalSixthBranch.v ((672237127:ℝ)/168755200)/ClassicalSixthBranch.r = (78340577704257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3820
  · change upperPayment 3821 ≤ upperValue ((point split endpoint 4096 3821+point split endpoint 4096 3822)/2)
    have hp : upperPayment 3821 = (44759729987:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3821+point split endpoint 4096 3822)/2 = (672262277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((672262277:ℝ)/168755200)*ClassicalSixthBranch.v ((672262277:ℝ)/168755200)/ClassicalSixthBranch.r = (78322294366505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3821
  · change upperPayment 3822 ≤ upperValue ((point split endpoint 4096 3822+point split endpoint 4096 3823)/2)
    have hp : upperPayment 3822 = (44602302251:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3822+point split endpoint 4096 3823)/2 = (672287427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((672287427:ℝ)/168755200)*ClassicalSixthBranch.v ((672287427:ℝ)/168755200)/ClassicalSixthBranch.r = (78304013052825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3822
  · change upperPayment 3823 ≤ upperValue ((point split endpoint 4096 3823+point split endpoint 4096 3824)/2)
    have hp : upperPayment 3823 = (44444834353:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3823+point split endpoint 4096 3824)/2 = (672312577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((672312577:ℝ)/168755200)*ClassicalSixthBranch.v ((672312577:ℝ)/168755200)/ClassicalSixthBranch.r = (78285733763217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3823
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_238
