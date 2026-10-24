import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints242
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_242 (j : Fin 16) : lowerPayment (16*242+j.val) ≤
    lowerValue ((point 2 split 4096 (16*242+j.val)+point 2 split 4096 (16*242+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3872 ≤ lowerValue ((point 2 split 4096 3872+point 2 split 4096 3873)/2)
    have hp : lowerPayment 3872 = (401861251942:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3872+point 2 split 4096 3873)/2 = (112625999:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((112625999:ℝ)/33751040)/ClassicalSixthBranch.v ((112625999:ℝ)/33751040) = (514617974139:ℝ)/234667913368 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3872
  · change lowerPayment 3873 ≤ lowerValue ((point 2 split 4096 3873+point 2 split 4096 3874)/2)
    have hp : lowerPayment 3873 = (401959501398:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3873+point 2 split 4096 3874)/2 = (563188257:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((563188257:ℝ)/168755200)/ClassicalSixthBranch.v ((563188257:ℝ)/168755200) = (102908132093:ℝ)/46923981096 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3873
  · change lowerPayment 3874 ≤ lowerValue ((point 2 split 4096 3874+point 2 split 4096 3875)/2)
    have hp : lowerPayment 3874 = (402057769031:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3874+point 2 split 4096 3875)/2 = (563246519:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((563246519:ℝ)/168755200)/ClassicalSixthBranch.v ((563246519:ℝ)/168755200) = (514463346791:ℝ)/234571897592 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3874
  · change lowerPayment 3875 ≤ lowerValue ((point 2 split 4096 3875+point 2 split 4096 3876)/2)
    have hp : lowerPayment 3875 = (402156054861:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3875+point 2 split 4096 3876)/2 = (563304781:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((563304781:ℝ)/168755200)/ClassicalSixthBranch.v ((563304781:ℝ)/168755200) = (514386033117:ℝ)/234523889704 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3875
  · change lowerPayment 3876 ≤ lowerValue ((point 2 split 4096 3876+point 2 split 4096 3877)/2)
    have hp : lowerPayment 3876 = (402254358904:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3876+point 2 split 4096 3877)/2 = (563363043:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((563363043:ℝ)/168755200)/ClassicalSixthBranch.v ((563363043:ℝ)/168755200) = (514308719443:ℝ)/234475881816 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3876
  · change lowerPayment 3877 ≤ lowerValue ((point 2 split 4096 3877+point 2 split 4096 3878)/2)
    have hp : lowerPayment 3877 = (402352681178:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3877+point 2 split 4096 3878)/2 = (112684261:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((112684261:ℝ)/33751040)/ClassicalSixthBranch.v ((112684261:ℝ)/33751040) = (514231405769:ℝ)/234427873928 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3877
  · change lowerPayment 3878 ≤ lowerValue ((point 2 split 4096 3878+point 2 split 4096 3879)/2)
    have hp : lowerPayment 3878 = (402451021701:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3878+point 2 split 4096 3879)/2 = (563479567:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((563479567:ℝ)/168755200)/ClassicalSixthBranch.v ((563479567:ℝ)/168755200) = (102830818419:ℝ)/46875973208 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3878
  · change lowerPayment 3879 ≤ lowerValue ((point 2 split 4096 3879+point 2 split 4096 3880)/2)
    have hp : lowerPayment 3879 = (402549380492:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3879+point 2 split 4096 3880)/2 = (563537829:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((563537829:ℝ)/168755200)/ClassicalSixthBranch.v ((563537829:ℝ)/168755200) = (514076778421:ℝ)/234331858152 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3879
  · change lowerPayment 3880 ≤ lowerValue ((point 2 split 4096 3880+point 2 split 4096 3881)/2)
    have hp : lowerPayment 3880 = (402647757567:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3880+point 2 split 4096 3881)/2 = (563596091:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((563596091:ℝ)/168755200)/ClassicalSixthBranch.v ((563596091:ℝ)/168755200) = (513999464747:ℝ)/234283850264 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3880
  · change lowerPayment 3881 ≤ lowerValue ((point 2 split 4096 3881+point 2 split 4096 3882)/2)
    have hp : lowerPayment 3881 = (402746152945:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3881+point 2 split 4096 3882)/2 = (563654353:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((563654353:ℝ)/168755200)/ClassicalSixthBranch.v ((563654353:ℝ)/168755200) = (513922151073:ℝ)/234235842376 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3881
  · change lowerPayment 3882 ≤ lowerValue ((point 2 split 4096 3882+point 2 split 4096 3883)/2)
    have hp : lowerPayment 3882 = (402844566644:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3882+point 2 split 4096 3883)/2 = (112742523:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((112742523:ℝ)/33751040)/ClassicalSixthBranch.v ((112742523:ℝ)/33751040) = (513844837399:ℝ)/234187834488 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3882
  · change lowerPayment 3883 ≤ lowerValue ((point 2 split 4096 3883+point 2 split 4096 3884)/2)
    have hp : lowerPayment 3883 = (402942998682:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3883+point 2 split 4096 3884)/2 = (563770877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((563770877:ℝ)/168755200)/ClassicalSixthBranch.v ((563770877:ℝ)/168755200) = (20550700949:ℝ)/9365593064 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3883
  · change lowerPayment 3884 ≤ lowerValue ((point 2 split 4096 3884+point 2 split 4096 3885)/2)
    have hp : lowerPayment 3884 = (403041449075:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3884+point 2 split 4096 3885)/2 = (563829139:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((563829139:ℝ)/168755200)/ClassicalSixthBranch.v ((563829139:ℝ)/168755200) = (513690210051:ℝ)/234091818712 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3884
  · change lowerPayment 3885 ≤ lowerValue ((point 2 split 4096 3885+point 2 split 4096 3886)/2)
    have hp : lowerPayment 3885 = (403139917844:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3885+point 2 split 4096 3886)/2 = (563887401:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((563887401:ℝ)/168755200)/ClassicalSixthBranch.v ((563887401:ℝ)/168755200) = (513612896377:ℝ)/234043810824 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3885
  · change lowerPayment 3886 ≤ lowerValue ((point 2 split 4096 3886+point 2 split 4096 3887)/2)
    have hp : lowerPayment 3886 = (403238405004:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3886+point 2 split 4096 3887)/2 = (563945663:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((563945663:ℝ)/168755200)/ClassicalSixthBranch.v ((563945663:ℝ)/168755200) = (513535582703:ℝ)/233995802936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3886
  · change lowerPayment 3887 ≤ lowerValue ((point 2 split 4096 3887+point 2 split 4096 3888)/2)
    have hp : lowerPayment 3887 = (403336910574:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3887+point 2 split 4096 3888)/2 = (22560157:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((22560157:ℝ)/6750208)/ClassicalSixthBranch.v ((22560157:ℝ)/6750208) = (513458269029:ℝ)/233947795048 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3887
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_242
