import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints067
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_067 (j : Fin 16) : lowerPayment (16*67+j.val) ≤
    lowerValue ((point 2 split 4096 (16*67+j.val)+point 2 split 4096 (16*67+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1072 ≤ lowerValue ((point 2 split 4096 1072+point 2 split 4096 1073)/2)
    have hp : lowerPayment 1072 = (141325277705:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1072+point 2 split 4096 1073)/2 = (79999279:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((79999279:ℝ)/33751040)/ClassicalSixthBranch.v ((79999279:ℝ)/33751040) = (731096261339:ℝ)/369089999768 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1072
  · change lowerPayment 1073 ≤ lowerValue ((point 2 split 4096 1073+point 2 split 4096 1074)/2)
    have hp : lowerPayment 1073 = (141434182216:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1073+point 2 split 4096 1074)/2 = (400054657:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((400054657:ℝ)/168755200)/ClassicalSixthBranch.v ((400054657:ℝ)/168755200) = (146203789533:ℝ)/73808398376 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1073
  · change lowerPayment 1074 ≤ lowerValue ((point 2 split 4096 1074+point 2 split 4096 1075)/2)
    have hp : lowerPayment 1074 = (141543056743:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1074+point 2 split 4096 1075)/2 = (400112919:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((400112919:ℝ)/168755200)/ClassicalSixthBranch.v ((400112919:ℝ)/168755200) = (730941633991:ℝ)/368993983992 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1074
  · change lowerPayment 1075 ≤ lowerValue ((point 2 split 4096 1075+point 2 split 4096 1076)/2)
    have hp : lowerPayment 1075 = (141651901316:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1075+point 2 split 4096 1076)/2 = (400171181:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((400171181:ℝ)/168755200)/ClassicalSixthBranch.v ((400171181:ℝ)/168755200) = (730864320317:ℝ)/368945976104 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1075
  · change lowerPayment 1076 ≤ lowerValue ((point 2 split 4096 1076+point 2 split 4096 1077)/2)
    have hp : lowerPayment 1076 = (141760715961:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1076+point 2 split 4096 1077)/2 = (400229443:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((400229443:ℝ)/168755200)/ClassicalSixthBranch.v ((400229443:ℝ)/168755200) = (730787006643:ℝ)/368897968216 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1076
  · change lowerPayment 1077 ≤ lowerValue ((point 2 split 4096 1077+point 2 split 4096 1078)/2)
    have hp : lowerPayment 1077 = (141869500707:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1077+point 2 split 4096 1078)/2 = (80057541:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((80057541:ℝ)/33751040)/ClassicalSixthBranch.v ((80057541:ℝ)/33751040) = (730709692969:ℝ)/368849960328 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1077
  · change lowerPayment 1078 ≤ lowerValue ((point 2 split 4096 1078+point 2 split 4096 1079)/2)
    have hp : lowerPayment 1078 = (141978255581:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1078+point 2 split 4096 1079)/2 = (400345967:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((400345967:ℝ)/168755200)/ClassicalSixthBranch.v ((400345967:ℝ)/168755200) = (146126475859:ℝ)/73760390488 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1078
  · change lowerPayment 1079 ≤ lowerValue ((point 2 split 4096 1079+point 2 split 4096 1080)/2)
    have hp : lowerPayment 1079 = (142086980613:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1079+point 2 split 4096 1080)/2 = (400404229:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((400404229:ℝ)/168755200)/ClassicalSixthBranch.v ((400404229:ℝ)/168755200) = (730555065621:ℝ)/368753944552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1079
  · change lowerPayment 1080 ≤ lowerValue ((point 2 split 4096 1080+point 2 split 4096 1081)/2)
    have hp : lowerPayment 1080 = (142195675829:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1080+point 2 split 4096 1081)/2 = (400462491:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((400462491:ℝ)/168755200)/ClassicalSixthBranch.v ((400462491:ℝ)/168755200) = (730477751947:ℝ)/368705936664 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1080
  · change lowerPayment 1081 ≤ lowerValue ((point 2 split 4096 1081+point 2 split 4096 1082)/2)
    have hp : lowerPayment 1081 = (142304341258:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1081+point 2 split 4096 1082)/2 = (3888551:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((3888551:ℝ)/1638400)/ClassicalSixthBranch.v ((3888551:ℝ)/1638400) = (7091266391:ℝ)/3579203192 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1081
  · change lowerPayment 1082 ≤ lowerValue ((point 2 split 4096 1082+point 2 split 4096 1083)/2)
    have hp : lowerPayment 1082 = (142412976928:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1082+point 2 split 4096 1083)/2 = (80115803:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((80115803:ℝ)/33751040)/ClassicalSixthBranch.v ((80115803:ℝ)/33751040) = (730323124599:ℝ)/368609920888 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1082
  · change lowerPayment 1083 ≤ lowerValue ((point 2 split 4096 1083+point 2 split 4096 1084)/2)
    have hp : lowerPayment 1083 = (142521582866:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1083+point 2 split 4096 1084)/2 = (400637277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((400637277:ℝ)/168755200)/ClassicalSixthBranch.v ((400637277:ℝ)/168755200) = (29209832437:ℝ)/14742476520 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1083
  · change lowerPayment 1084 ≤ lowerValue ((point 2 split 4096 1084+point 2 split 4096 1085)/2)
    have hp : lowerPayment 1084 = (142630159101:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1084+point 2 split 4096 1085)/2 = (400695539:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((400695539:ℝ)/168755200)/ClassicalSixthBranch.v ((400695539:ℝ)/168755200) = (730168497251:ℝ)/368513905112 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1084
  · change lowerPayment 1085 ≤ lowerValue ((point 2 split 4096 1085+point 2 split 4096 1086)/2)
    have hp : lowerPayment 1085 = (142738705660:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1085+point 2 split 4096 1086)/2 = (400753801:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((400753801:ℝ)/168755200)/ClassicalSixthBranch.v ((400753801:ℝ)/168755200) = (730091183577:ℝ)/368465897224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1085
  · change lowerPayment 1086 ≤ lowerValue ((point 2 split 4096 1086+point 2 split 4096 1087)/2)
    have hp : lowerPayment 1086 = (142847222572:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1086+point 2 split 4096 1087)/2 = (400812063:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((400812063:ℝ)/168755200)/ClassicalSixthBranch.v ((400812063:ℝ)/168755200) = (730013869903:ℝ)/368417889336 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1086
  · change lowerPayment 1087 ≤ lowerValue ((point 2 split 4096 1087+point 2 split 4096 1088)/2)
    have hp : lowerPayment 1087 = (142955709863:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1087+point 2 split 4096 1088)/2 = (16034813:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((16034813:ℝ)/6750208)/ClassicalSixthBranch.v ((16034813:ℝ)/6750208) = (729936556229:ℝ)/368369881448 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1087
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_067
