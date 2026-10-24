import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints182
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_182 (j : Fin 16) : lowerPayment (16*182+j.val) ≤
    lowerValue ((point 2 split 4096 (16*182+j.val)+point 2 split 4096 (16*182+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2912 ≤ lowerValue ((point 2 split 4096 2912+point 2 split 4096 2913)/2)
    have hp : lowerPayment 2912 = (313510579637:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2912+point 2 split 4096 2913)/2 = (20287939:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((20287939:ℝ)/6750208)/ClassicalSixthBranch.v ((20287939:ℝ)/6750208) = (588839101179:ℝ)/280755485848 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2912
  · change lowerPayment 2913 ≤ lowerValue ((point 2 split 4096 2913+point 2 split 4096 2914)/2)
    have hp : lowerPayment 2913 = (313598746546:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2913+point 2 split 4096 2914)/2 = (507256737:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((507256737:ℝ)/168755200)/ClassicalSixthBranch.v ((507256737:ℝ)/168755200) = (117752357501:ℝ)/56141495592 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2913
  · change lowerPayment 2914 ≤ lowerValue ((point 2 split 4096 2914+point 2 split 4096 2915)/2)
    have hp : lowerPayment 2914 = (313686916880:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2914+point 2 split 4096 2915)/2 = (507314999:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((507314999:ℝ)/168755200)/ClassicalSixthBranch.v ((507314999:ℝ)/168755200) = (588684473831:ℝ)/280659470072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2914
  · change lowerPayment 2915 ≤ lowerValue ((point 2 split 4096 2915+point 2 split 4096 2916)/2)
    have hp : lowerPayment 2915 = (313775090654:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2915+point 2 split 4096 2916)/2 = (507373261:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((507373261:ℝ)/168755200)/ClassicalSixthBranch.v ((507373261:ℝ)/168755200) = (588607160157:ℝ)/280611462184 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2915
  · change lowerPayment 2916 ≤ lowerValue ((point 2 split 4096 2916+point 2 split 4096 2917)/2)
    have hp : lowerPayment 2916 = (313863267881:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2916+point 2 split 4096 2917)/2 = (507431523:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((507431523:ℝ)/168755200)/ClassicalSixthBranch.v ((507431523:ℝ)/168755200) = (588529846483:ℝ)/280563454296 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2916
  · change lowerPayment 2917 ≤ lowerValue ((point 2 split 4096 2917+point 2 split 4096 2918)/2)
    have hp : lowerPayment 2917 = (313951448576:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2917+point 2 split 4096 2918)/2 = (101497957:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((101497957:ℝ)/33751040)/ClassicalSixthBranch.v ((101497957:ℝ)/33751040) = (588452532809:ℝ)/280515446408 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2917
  · change lowerPayment 2918 ≤ lowerValue ((point 2 split 4096 2918+point 2 split 4096 2919)/2)
    have hp : lowerPayment 2918 = (314039632753:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2918+point 2 split 4096 2919)/2 = (507548047:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((507548047:ℝ)/168755200)/ClassicalSixthBranch.v ((507548047:ℝ)/168755200) = (117675043827:ℝ)/56093487704 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2918
  · change lowerPayment 2919 ≤ lowerValue ((point 2 split 4096 2919+point 2 split 4096 2920)/2)
    have hp : lowerPayment 2919 = (314127820426:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2919+point 2 split 4096 2920)/2 = (507606309:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((507606309:ℝ)/168755200)/ClassicalSixthBranch.v ((507606309:ℝ)/168755200) = (588297905461:ℝ)/280419430632 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2919
  · change lowerPayment 2920 ≤ lowerValue ((point 2 split 4096 2920+point 2 split 4096 2921)/2)
    have hp : lowerPayment 2920 = (314216011609:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2920+point 2 split 4096 2921)/2 = (507664571:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((507664571:ℝ)/168755200)/ClassicalSixthBranch.v ((507664571:ℝ)/168755200) = (588220591787:ℝ)/280371422744 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2920
  · change lowerPayment 2921 ≤ lowerValue ((point 2 split 4096 2921+point 2 split 4096 2922)/2)
    have hp : lowerPayment 2921 = (314304206315:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2921+point 2 split 4096 2922)/2 = (507722833:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((507722833:ℝ)/168755200)/ClassicalSixthBranch.v ((507722833:ℝ)/168755200) = (588143278113:ℝ)/280323414856 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2921
  · change lowerPayment 2922 ≤ lowerValue ((point 2 split 4096 2922+point 2 split 4096 2923)/2)
    have hp : lowerPayment 2922 = (314392404561:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2922+point 2 split 4096 2923)/2 = (101556219:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((101556219:ℝ)/33751040)/ClassicalSixthBranch.v ((101556219:ℝ)/33751040) = (588065964439:ℝ)/280275406968 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2922
  · change lowerPayment 2923 ≤ lowerValue ((point 2 split 4096 2923+point 2 split 4096 2924)/2)
    have hp : lowerPayment 2923 = (314480606358:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2923+point 2 split 4096 2924)/2 = (507839357:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((507839357:ℝ)/168755200)/ClassicalSixthBranch.v ((507839357:ℝ)/168755200) = (117597730153:ℝ)/56045479816 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2923
  · change lowerPayment 2924 ≤ lowerValue ((point 2 split 4096 2924+point 2 split 4096 2925)/2)
    have hp : lowerPayment 2924 = (314568811722:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2924+point 2 split 4096 2925)/2 = (507897619:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((507897619:ℝ)/168755200)/ClassicalSixthBranch.v ((507897619:ℝ)/168755200) = (587911337091:ℝ)/280179391192 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2924
  · change lowerPayment 2925 ≤ lowerValue ((point 2 split 4096 2925+point 2 split 4096 2926)/2)
    have hp : lowerPayment 2925 = (314657020666:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2925+point 2 split 4096 2926)/2 = (507955881:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((507955881:ℝ)/168755200)/ClassicalSixthBranch.v ((507955881:ℝ)/168755200) = (587834023417:ℝ)/280131383304 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2925
  · change lowerPayment 2926 ≤ lowerValue ((point 2 split 4096 2926+point 2 split 4096 2927)/2)
    have hp : lowerPayment 2926 = (314745233206:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2926+point 2 split 4096 2927)/2 = (508014143:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((508014143:ℝ)/168755200)/ClassicalSixthBranch.v ((508014143:ℝ)/168755200) = (587756709743:ℝ)/280083375416 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2926
  · change lowerPayment 2927 ≤ lowerValue ((point 2 split 4096 2927+point 2 split 4096 2928)/2)
    have hp : lowerPayment 2927 = (314833449354:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2927+point 2 split 4096 2928)/2 = (101614481:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((101614481:ℝ)/33751040)/ClassicalSixthBranch.v ((101614481:ℝ)/33751040) = (587679396069:ℝ)/280035367528 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2927
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_182
