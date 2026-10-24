import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints184
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_184 (j : Fin 16) : lowerPayment (16*184+j.val) ≤
    lowerValue ((point 2 split 4096 (16*184+j.val)+point 2 split 4096 (16*184+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2944 ≤ lowerValue ((point 2 split 4096 2944+point 2 split 4096 2945)/2)
    have hp : lowerPayment 2944 = (316333689707:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2944+point 2 split 4096 2945)/2 = (509062859:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((509062859:ℝ)/168755200)/ClassicalSixthBranch.v ((509062859:ℝ)/168755200) = (586365063611:ℝ)/279219233432 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2944
  · change lowerPayment 2945 ≤ lowerValue ((point 2 split 4096 2945+point 2 split 4096 2946)/2)
    have hp : lowerPayment 2945 = (316421973229:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2945+point 2 split 4096 2946)/2 = (509121121:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((509121121:ℝ)/168755200)/ClassicalSixthBranch.v ((509121121:ℝ)/168755200) = (586287749937:ℝ)/279171225544 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2945
  · change lowerPayment 2946 ≤ lowerValue ((point 2 split 4096 2946+point 2 split 4096 2947)/2)
    have hp : lowerPayment 2946 = (316510260628:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2946+point 2 split 4096 2947)/2 = (509179383:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((509179383:ℝ)/168755200)/ClassicalSixthBranch.v ((509179383:ℝ)/168755200) = (586210436263:ℝ)/279123217656 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2946
  · change lowerPayment 2947 ≤ lowerValue ((point 2 split 4096 2947+point 2 split 4096 2948)/2)
    have hp : lowerPayment 2947 = (316598551919:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2947+point 2 split 4096 2948)/2 = (101847529:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((101847529:ℝ)/33751040)/ClassicalSixthBranch.v ((101847529:ℝ)/33751040) = (586133122589:ℝ)/279075209768 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2947
  · change lowerPayment 2948 ≤ lowerValue ((point 2 split 4096 2948+point 2 split 4096 2949)/2)
    have hp : lowerPayment 2948 = (316686847115:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2948+point 2 split 4096 2949)/2 = (509295907:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((509295907:ℝ)/168755200)/ClassicalSixthBranch.v ((509295907:ℝ)/168755200) = (117211161783:ℝ)/55805440376 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2948
  · change lowerPayment 2949 ≤ lowerValue ((point 2 split 4096 2949+point 2 split 4096 2950)/2)
    have hp : lowerPayment 2949 = (316775146230:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2949+point 2 split 4096 2950)/2 = (509354169:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((509354169:ℝ)/168755200)/ClassicalSixthBranch.v ((509354169:ℝ)/168755200) = (585978495241:ℝ)/278979193992 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2949
  · change lowerPayment 2950 ≤ lowerValue ((point 2 split 4096 2950+point 2 split 4096 2951)/2)
    have hp : lowerPayment 2950 = (316863449280:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2950+point 2 split 4096 2951)/2 = (509412431:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((509412431:ℝ)/168755200)/ClassicalSixthBranch.v ((509412431:ℝ)/168755200) = (585901181567:ℝ)/278931186104 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2950
  · change lowerPayment 2951 ≤ lowerValue ((point 2 split 4096 2951+point 2 split 4096 2952)/2)
    have hp : lowerPayment 2951 = (316951756277:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2951+point 2 split 4096 2952)/2 = (509470693:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((509470693:ℝ)/168755200)/ClassicalSixthBranch.v ((509470693:ℝ)/168755200) = (585823867893:ℝ)/278883178216 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2951
  · change lowerPayment 2952 ≤ lowerValue ((point 2 split 4096 2952+point 2 split 4096 2953)/2)
    have hp : lowerPayment 2952 = (317040067236:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2952+point 2 split 4096 2953)/2 = (101905791:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((101905791:ℝ)/33751040)/ClassicalSixthBranch.v ((101905791:ℝ)/33751040) = (585746554219:ℝ)/278835170328 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2952
  · change lowerPayment 2953 ≤ lowerValue ((point 2 split 4096 2953+point 2 split 4096 2954)/2)
    have hp : lowerPayment 2953 = (317128382171:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2953+point 2 split 4096 2954)/2 = (509587217:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((509587217:ℝ)/168755200)/ClassicalSixthBranch.v ((509587217:ℝ)/168755200) = (117133848109:ℝ)/55757432488 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2953
  · change lowerPayment 2954 ≤ lowerValue ((point 2 split 4096 2954+point 2 split 4096 2955)/2)
    have hp : lowerPayment 2954 = (317216701097:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2954+point 2 split 4096 2955)/2 = (509645479:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((509645479:ℝ)/168755200)/ClassicalSixthBranch.v ((509645479:ℝ)/168755200) = (585591926871:ℝ)/278739154552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2954
  · change lowerPayment 2955 ≤ lowerValue ((point 2 split 4096 2955+point 2 split 4096 2956)/2)
    have hp : lowerPayment 2955 = (317305024027:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2955+point 2 split 4096 2956)/2 = (509703741:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((509703741:ℝ)/168755200)/ClassicalSixthBranch.v ((509703741:ℝ)/168755200) = (585514613197:ℝ)/278691146664 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2955
  · change lowerPayment 2956 ≤ lowerValue ((point 2 split 4096 2956+point 2 split 4096 2957)/2)
    have hp : lowerPayment 2956 = (317393350975:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2956+point 2 split 4096 2957)/2 = (509762003:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((509762003:ℝ)/168755200)/ClassicalSixthBranch.v ((509762003:ℝ)/168755200) = (585437299523:ℝ)/278643138776 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2956
  · change lowerPayment 2957 ≤ lowerValue ((point 2 split 4096 2957+point 2 split 4096 2958)/2)
    have hp : lowerPayment 2957 = (317481681956:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2957+point 2 split 4096 2958)/2 = (101964053:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((101964053:ℝ)/33751040)/ClassicalSixthBranch.v ((101964053:ℝ)/33751040) = (585359985849:ℝ)/278595130888 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2957
  · change lowerPayment 2958 ≤ lowerValue ((point 2 split 4096 2958+point 2 split 4096 2959)/2)
    have hp : lowerPayment 2958 = (317570016984:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2958+point 2 split 4096 2959)/2 = (509878527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((509878527:ℝ)/168755200)/ClassicalSixthBranch.v ((509878527:ℝ)/168755200) = (23411306887:ℝ)/11141884920 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2958
  · change lowerPayment 2959 ≤ lowerValue ((point 2 split 4096 2959+point 2 split 4096 2960)/2)
    have hp : lowerPayment 2959 = (317658356073:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2959+point 2 split 4096 2960)/2 = (509936789:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((509936789:ℝ)/168755200)/ClassicalSixthBranch.v ((509936789:ℝ)/168755200) = (585205358501:ℝ)/278499115112 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2959
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_184
