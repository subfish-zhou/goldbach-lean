import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints065
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_065 (j : Fin 16) : lowerPayment (16*65+j.val) ≤
    lowerValue ((point 2 split 4096 (16*65+j.val)+point 2 split 4096 (16*65+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1040 ≤ lowerValue ((point 2 split 4096 1040+point 2 split 4096 1041)/2)
    have hp : lowerPayment 1040 = (137824333045:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1040+point 2 split 4096 1041)/2 = (398132011:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((398132011:ℝ)/168755200)/ClassicalSixthBranch.v ((398132011:ℝ)/168755200) = (733570298907:ℝ)/370626252184 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1040
  · change lowerPayment 1041 ≤ lowerValue ((point 2 split 4096 1041+point 2 split 4096 1042)/2)
    have hp : lowerPayment 1041 = (137934211971:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1041+point 2 split 4096 1042)/2 = (398190273:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((398190273:ℝ)/168755200)/ClassicalSixthBranch.v ((398190273:ℝ)/168755200) = (733492985233:ℝ)/370578244296 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1041
  · change lowerPayment 1042 ≤ lowerValue ((point 2 split 4096 1042+point 2 split 4096 1043)/2)
    have hp : lowerPayment 1042 = (138044060005:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1042+point 2 split 4096 1043)/2 = (79649707:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((79649707:ℝ)/33751040)/ClassicalSixthBranch.v ((79649707:ℝ)/33751040) = (733415671559:ℝ)/370530236408 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1042
  · change lowerPayment 1043 ≤ lowerValue ((point 2 split 4096 1043+point 2 split 4096 1044)/2)
    have hp : lowerPayment 1043 = (138153877175:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1043+point 2 split 4096 1044)/2 = (398306797:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((398306797:ℝ)/168755200)/ClassicalSixthBranch.v ((398306797:ℝ)/168755200) = (146667671577:ℝ)/74096445704 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1043
  · change lowerPayment 1044 ≤ lowerValue ((point 2 split 4096 1044+point 2 split 4096 1045)/2)
    have hp : lowerPayment 1044 = (138263663509:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1044+point 2 split 4096 1045)/2 = (398365059:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((398365059:ℝ)/168755200)/ClassicalSixthBranch.v ((398365059:ℝ)/168755200) = (733261044211:ℝ)/370434220632 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1044
  · change lowerPayment 1045 ≤ lowerValue ((point 2 split 4096 1045+point 2 split 4096 1046)/2)
    have hp : lowerPayment 1045 = (138373419037:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1045+point 2 split 4096 1046)/2 = (398423321:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((398423321:ℝ)/168755200)/ClassicalSixthBranch.v ((398423321:ℝ)/168755200) = (733183730537:ℝ)/370386212744 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1045
  · change lowerPayment 1046 ≤ lowerValue ((point 2 split 4096 1046+point 2 split 4096 1047)/2)
    have hp : lowerPayment 1046 = (138483143787:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1046+point 2 split 4096 1047)/2 = (398481583:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((398481583:ℝ)/168755200)/ClassicalSixthBranch.v ((398481583:ℝ)/168755200) = (733106416863:ℝ)/370338204856 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1046
  · change lowerPayment 1047 ≤ lowerValue ((point 2 split 4096 1047+point 2 split 4096 1048)/2)
    have hp : lowerPayment 1047 = (138592837788:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1047+point 2 split 4096 1048)/2 = (79707969:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((79707969:ℝ)/33751040)/ClassicalSixthBranch.v ((79707969:ℝ)/33751040) = (733029103189:ℝ)/370290196968 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1047
  · change lowerPayment 1048 ≤ lowerValue ((point 2 split 4096 1048+point 2 split 4096 1049)/2)
    have hp : lowerPayment 1048 = (138702501068:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1048+point 2 split 4096 1049)/2 = (398598107:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((398598107:ℝ)/168755200)/ClassicalSixthBranch.v ((398598107:ℝ)/168755200) = (146590357903:ℝ)/74048437816 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1048
  · change lowerPayment 1049 ≤ lowerValue ((point 2 split 4096 1049+point 2 split 4096 1050)/2)
    have hp : lowerPayment 1049 = (138812133657:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1049+point 2 split 4096 1050)/2 = (398656369:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((398656369:ℝ)/168755200)/ClassicalSixthBranch.v ((398656369:ℝ)/168755200) = (732874475841:ℝ)/370194181192 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1049
  · change lowerPayment 1050 ≤ lowerValue ((point 2 split 4096 1050+point 2 split 4096 1051)/2)
    have hp : lowerPayment 1050 = (138921735582:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1050+point 2 split 4096 1051)/2 = (398714631:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((398714631:ℝ)/168755200)/ClassicalSixthBranch.v ((398714631:ℝ)/168755200) = (732797162167:ℝ)/370146173304 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1050
  · change lowerPayment 1051 ≤ lowerValue ((point 2 split 4096 1051+point 2 split 4096 1052)/2)
    have hp : lowerPayment 1051 = (139031306872:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1051+point 2 split 4096 1052)/2 = (398772893:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((398772893:ℝ)/168755200)/ClassicalSixthBranch.v ((398772893:ℝ)/168755200) = (732719848493:ℝ)/370098165416 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1051
  · change lowerPayment 1052 ≤ lowerValue ((point 2 split 4096 1052+point 2 split 4096 1053)/2)
    have hp : lowerPayment 1052 = (139140847556:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1052+point 2 split 4096 1053)/2 = (79766231:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((79766231:ℝ)/33751040)/ClassicalSixthBranch.v ((79766231:ℝ)/33751040) = (732642534819:ℝ)/370050157528 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1052
  · change lowerPayment 1053 ≤ lowerValue ((point 2 split 4096 1053+point 2 split 4096 1054)/2)
    have hp : lowerPayment 1053 = (139250357662:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1053+point 2 split 4096 1054)/2 = (398889417:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((398889417:ℝ)/168755200)/ClassicalSixthBranch.v ((398889417:ℝ)/168755200) = (146513044229:ℝ)/74000429928 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1053
  · change lowerPayment 1054 ≤ lowerValue ((point 2 split 4096 1054+point 2 split 4096 1055)/2)
    have hp : lowerPayment 1054 = (139359837219:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1054+point 2 split 4096 1055)/2 = (398947679:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((398947679:ℝ)/168755200)/ClassicalSixthBranch.v ((398947679:ℝ)/168755200) = (732487907471:ℝ)/369954141752 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1054
  · change lowerPayment 1055 ≤ lowerValue ((point 2 split 4096 1055+point 2 split 4096 1056)/2)
    have hp : lowerPayment 1055 = (139469286255:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1055+point 2 split 4096 1056)/2 = (399005941:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((399005941:ℝ)/168755200)/ClassicalSixthBranch.v ((399005941:ℝ)/168755200) = (732410593797:ℝ)/369906133864 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1055
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_065
