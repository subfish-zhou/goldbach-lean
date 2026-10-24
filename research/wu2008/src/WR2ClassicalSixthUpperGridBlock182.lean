import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints182
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_182 (j : Fin 16) : upperPayment (16*182+j.val) ≤
    upperValue ((point split endpoint 4096 (16*182+j.val)+point split endpoint 4096 (16*182+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2912 ≤ upperValue ((point split endpoint 4096 2912+point split endpoint 4096 2913)/2)
    have hp : upperPayment 2912 = (172496339695:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2912+point split endpoint 4096 2913)/2 = (649400927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((649400927:ℝ)/168755200)*ClassicalSixthBranch.v ((649400927:ℝ)/168755200)/ClassicalSixthBranch.r = (95777154560465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2912
  · change upperPayment 2913 ≤ upperValue ((point split endpoint 4096 2913+point split endpoint 4096 2914)/2)
    have hp : upperPayment 2913 = (172371439392:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2913+point split endpoint 4096 2914)/2 = (649426077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((649426077:ℝ)/168755200)*ClassicalSixthBranch.v ((649426077:ℝ)/168755200)/ClassicalSixthBranch.r = (95757033365337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2913
  · change upperPayment 2914 ≤ upperValue ((point split endpoint 4096 2914+point split endpoint 4096 2915)/2)
    have hp : upperPayment 2914 = (172246507159:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2914+point split endpoint 4096 2915)/2 = (649451227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((649451227:ℝ)/168755200)*ClassicalSixthBranch.v ((649451227:ℝ)/168755200)/ClassicalSixthBranch.r = (95736914194281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2914
  · change upperPayment 2915 ≤ upperValue ((point split endpoint 4096 2915+point split endpoint 4096 2916)/2)
    have hp : upperPayment 2915 = (172121542989:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2915+point split endpoint 4096 2916)/2 = (649476377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((649476377:ℝ)/168755200)*ClassicalSixthBranch.v ((649476377:ℝ)/168755200)/ClassicalSixthBranch.r = (95716797047297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2915
  · change upperPayment 2916 ≤ upperValue ((point split endpoint 4096 2916+point split endpoint 4096 2917)/2)
    have hp : upperPayment 2916 = (171996546875:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2916+point split endpoint 4096 2917)/2 = (649501527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((649501527:ℝ)/168755200)*ClassicalSixthBranch.v ((649501527:ℝ)/168755200)/ClassicalSixthBranch.r = (95696681924385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2916
  · change upperPayment 2917 ≤ upperValue ((point split endpoint 4096 2917+point split endpoint 4096 2918)/2)
    have hp : upperPayment 2917 = (171871518809:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2917+point split endpoint 4096 2918)/2 = (649526677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((649526677:ℝ)/168755200)*ClassicalSixthBranch.v ((649526677:ℝ)/168755200)/ClassicalSixthBranch.r = (95676568825545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2917
  · change upperPayment 2918 ≤ upperValue ((point split endpoint 4096 2918+point split endpoint 4096 2919)/2)
    have hp : upperPayment 2918 = (171746458783:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2918+point split endpoint 4096 2919)/2 = (649551827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((649551827:ℝ)/168755200)*ClassicalSixthBranch.v ((649551827:ℝ)/168755200)/ClassicalSixthBranch.r = (95656457750777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2918
  · change upperPayment 2919 ≤ upperValue ((point split endpoint 4096 2919+point split endpoint 4096 2920)/2)
    have hp : upperPayment 2919 = (171621366790:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2919+point split endpoint 4096 2920)/2 = (649576977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((649576977:ℝ)/168755200)*ClassicalSixthBranch.v ((649576977:ℝ)/168755200)/ClassicalSixthBranch.r = (95636348700081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2919
  · change upperPayment 2920 ≤ upperValue ((point split endpoint 4096 2920+point split endpoint 4096 2921)/2)
    have hp : upperPayment 2920 = (171496242823:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2920+point split endpoint 4096 2921)/2 = (649602127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((649602127:ℝ)/168755200)*ClassicalSixthBranch.v ((649602127:ℝ)/168755200)/ClassicalSixthBranch.r = (95616241673457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2920
  · change upperPayment 2921 ≤ upperValue ((point split endpoint 4096 2921+point split endpoint 4096 2922)/2)
    have hp : upperPayment 2921 = (171371086874:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2921+point split endpoint 4096 2922)/2 = (649627277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((649627277:ℝ)/168755200)*ClassicalSixthBranch.v ((649627277:ℝ)/168755200)/ClassicalSixthBranch.r = (95596136670905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2921
  · change upperPayment 2922 ≤ upperValue ((point split endpoint 4096 2922+point split endpoint 4096 2923)/2)
    have hp : upperPayment 2922 = (171245898936:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2922+point split endpoint 4096 2923)/2 = (649652427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((649652427:ℝ)/168755200)*ClassicalSixthBranch.v ((649652427:ℝ)/168755200)/ClassicalSixthBranch.r = (95576033692425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2922
  · change upperPayment 2923 ≤ upperValue ((point split endpoint 4096 2923+point split endpoint 4096 2924)/2)
    have hp : upperPayment 2923 = (171120679001:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2923+point split endpoint 4096 2924)/2 = (649677577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((649677577:ℝ)/168755200)*ClassicalSixthBranch.v ((649677577:ℝ)/168755200)/ClassicalSixthBranch.r = (95555932738017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2923
  · change upperPayment 2924 ≤ upperValue ((point split endpoint 4096 2924+point split endpoint 4096 2925)/2)
    have hp : upperPayment 2924 = (170995427061:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2924+point split endpoint 4096 2925)/2 = (649702727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((649702727:ℝ)/168755200)*ClassicalSixthBranch.v ((649702727:ℝ)/168755200)/ClassicalSixthBranch.r = (95535833807681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2924
  · change upperPayment 2925 ≤ upperValue ((point split endpoint 4096 2925+point split endpoint 4096 2926)/2)
    have hp : upperPayment 2925 = (170870143110:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2925+point split endpoint 4096 2926)/2 = (649727877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((649727877:ℝ)/168755200)*ClassicalSixthBranch.v ((649727877:ℝ)/168755200)/ClassicalSixthBranch.r = (95515736901417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2925
  · change upperPayment 2926 ≤ upperValue ((point split endpoint 4096 2926+point split endpoint 4096 2927)/2)
    have hp : upperPayment 2926 = (170744827139:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2926+point split endpoint 4096 2927)/2 = (649753027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((649753027:ℝ)/168755200)*ClassicalSixthBranch.v ((649753027:ℝ)/168755200)/ClassicalSixthBranch.r = (95495642019225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2926
  · change upperPayment 2927 ≤ upperValue ((point split endpoint 4096 2927+point split endpoint 4096 2928)/2)
    have hp : upperPayment 2927 = (170619479141:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2927+point split endpoint 4096 2928)/2 = (649778177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((649778177:ℝ)/168755200)*ClassicalSixthBranch.v ((649778177:ℝ)/168755200)/ClassicalSixthBranch.r = (95475549161105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2927
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_182
