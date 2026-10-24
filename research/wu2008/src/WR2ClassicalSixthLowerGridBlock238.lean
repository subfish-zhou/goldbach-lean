import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints238
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_238 (j : Fin 16) : lowerPayment (16*238+j.val) ≤
    lowerValue ((point 2 split 4096 (16*238+j.val)+point 2 split 4096 (16*238+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3808 ≤ lowerValue ((point 2 split 4096 3808+point 2 split 4096 3809)/2)
    have hp : lowerPayment 3808 = (395610287588:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3808+point 2 split 4096 3809)/2 = (559401227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((559401227:ℝ)/168755200)/ClassicalSixthBranch.v ((559401227:ℝ)/168755200) = (20782641971:ℝ)/9509616728 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3808
  · change lowerPayment 3809 ≤ lowerValue ((point 2 split 4096 3809+point 2 split 4096 3810)/2)
    have hp : lowerPayment 3809 = (395707410358:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3809+point 2 split 4096 3810)/2 = (559459489:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((559459489:ℝ)/168755200)/ClassicalSixthBranch.v ((559459489:ℝ)/168755200) = (519488735601:ℝ)/237692410312 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3809
  · change lowerPayment 3810 ≤ lowerValue ((point 2 split 4096 3810+point 2 split 4096 3811)/2)
    have hp : lowerPayment 3810 = (395804550181:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3810+point 2 split 4096 3811)/2 = (559517751:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((559517751:ℝ)/168755200)/ClassicalSixthBranch.v ((559517751:ℝ)/168755200) = (519411421927:ℝ)/237644402424 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3810
  · change lowerPayment 3811 ≤ lowerValue ((point 2 split 4096 3811+point 2 split 4096 3812)/2)
    have hp : lowerPayment 3811 = (395901707075:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3811+point 2 split 4096 3812)/2 = (559576013:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((559576013:ℝ)/168755200)/ClassicalSixthBranch.v ((559576013:ℝ)/168755200) = (519334108253:ℝ)/237596394536 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3811
  · change lowerPayment 3812 ≤ lowerValue ((point 2 split 4096 3812+point 2 split 4096 3813)/2)
    have hp : lowerPayment 3812 = (395998881058:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3812+point 2 split 4096 3813)/2 = (22385371:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((22385371:ℝ)/6750208)/ClassicalSixthBranch.v ((22385371:ℝ)/6750208) = (519256794579:ℝ)/237548386648 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3812
  · change lowerPayment 3813 ≤ lowerValue ((point 2 split 4096 3813+point 2 split 4096 3814)/2)
    have hp : lowerPayment 3813 = (396096072146:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3813+point 2 split 4096 3814)/2 = (559692537:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((559692537:ℝ)/168755200)/ClassicalSixthBranch.v ((559692537:ℝ)/168755200) = (103835896181:ℝ)/47500075752 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3813
  · change lowerPayment 3814 ≤ lowerValue ((point 2 split 4096 3814+point 2 split 4096 3815)/2)
    have hp : lowerPayment 3814 = (396193280358:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3814+point 2 split 4096 3815)/2 = (559750799:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((559750799:ℝ)/168755200)/ClassicalSixthBranch.v ((559750799:ℝ)/168755200) = (519102167231:ℝ)/237452370872 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3814
  · change lowerPayment 3815 ≤ lowerValue ((point 2 split 4096 3815+point 2 split 4096 3816)/2)
    have hp : lowerPayment 3815 = (396290505710:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3815+point 2 split 4096 3816)/2 = (559809061:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((559809061:ℝ)/168755200)/ClassicalSixthBranch.v ((559809061:ℝ)/168755200) = (519024853557:ℝ)/237404362984 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3815
  · change lowerPayment 3816 ≤ lowerValue ((point 2 split 4096 3816+point 2 split 4096 3817)/2)
    have hp : lowerPayment 3816 = (396387748220:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3816+point 2 split 4096 3817)/2 = (559867323:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((559867323:ℝ)/168755200)/ClassicalSixthBranch.v ((559867323:ℝ)/168755200) = (518947539883:ℝ)/237356355096 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3816
  · change lowerPayment 3817 ≤ lowerValue ((point 2 split 4096 3817+point 2 split 4096 3818)/2)
    have hp : lowerPayment 3817 = (396485007906:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3817+point 2 split 4096 3818)/2 = (111985117:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((111985117:ℝ)/33751040)/ClassicalSixthBranch.v ((111985117:ℝ)/33751040) = (518870226209:ℝ)/237308347208 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3817
  · change lowerPayment 3818 ≤ lowerValue ((point 2 split 4096 3818+point 2 split 4096 3819)/2)
    have hp : lowerPayment 3818 = (396582284784:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3818+point 2 split 4096 3819)/2 = (559983847:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((559983847:ℝ)/168755200)/ClassicalSixthBranch.v ((559983847:ℝ)/168755200) = (103758582507:ℝ)/47452067864 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3818
  · change lowerPayment 3819 ≤ lowerValue ((point 2 split 4096 3819+point 2 split 4096 3820)/2)
    have hp : lowerPayment 3819 = (396679578871:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3819+point 2 split 4096 3820)/2 = (560042109:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((560042109:ℝ)/168755200)/ClassicalSixthBranch.v ((560042109:ℝ)/168755200) = (518715598861:ℝ)/237212331432 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3819
  · change lowerPayment 3820 ≤ lowerValue ((point 2 split 4096 3820+point 2 split 4096 3821)/2)
    have hp : lowerPayment 3820 = (396776890187:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3820+point 2 split 4096 3821)/2 = (560100371:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((560100371:ℝ)/168755200)/ClassicalSixthBranch.v ((560100371:ℝ)/168755200) = (518638285187:ℝ)/237164323544 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3820
  · change lowerPayment 3821 ≤ lowerValue ((point 2 split 4096 3821+point 2 split 4096 3822)/2)
    have hp : lowerPayment 3821 = (396874218747:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3821+point 2 split 4096 3822)/2 = (560158633:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((560158633:ℝ)/168755200)/ClassicalSixthBranch.v ((560158633:ℝ)/168755200) = (518560971513:ℝ)/237116315656 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3821
  · change lowerPayment 3822 ≤ lowerValue ((point 2 split 4096 3822+point 2 split 4096 3823)/2)
    have hp : lowerPayment 3822 = (396971564569:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3822+point 2 split 4096 3823)/2 = (112043379:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((112043379:ℝ)/33751040)/ClassicalSixthBranch.v ((112043379:ℝ)/33751040) = (518483657839:ℝ)/237068307768 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3822
  · change lowerPayment 3823 ≤ lowerValue ((point 2 split 4096 3823+point 2 split 4096 3824)/2)
    have hp : lowerPayment 3823 = (397068927671:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3823+point 2 split 4096 3824)/2 = (560275157:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((560275157:ℝ)/168755200)/ClassicalSixthBranch.v ((560275157:ℝ)/168755200) = (103681268833:ℝ)/47404059976 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3823
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_238
