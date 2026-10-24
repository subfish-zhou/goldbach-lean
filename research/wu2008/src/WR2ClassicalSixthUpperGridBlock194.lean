import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints194
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_194 (j : Fin 16) : upperPayment (16*194+j.val) ≤
    upperValue ((point split endpoint 4096 (16*194+j.val)+point split endpoint 4096 (16*194+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3104 ≤ upperValue ((point split endpoint 4096 3104+point split endpoint 4096 3105)/2)
    have hp : upperPayment 3104 = (147921174244:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3104+point split endpoint 4096 3105)/2 = (654229727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((654229727:ℝ)/168755200)*ClassicalSixthBranch.v ((654229727:ℝ)/168755200)/ClassicalSixthBranch.r = (91950998480081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3104
  · change upperPayment 3105 ≤ upperValue ((point split endpoint 4096 3105+point split endpoint 4096 3106)/2)
    have hp : upperPayment 3105 = (147790002853:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3105+point split endpoint 4096 3106)/2 = (654254877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((654254877:ℝ)/168755200)*ClassicalSixthBranch.v ((654254877:ℝ)/168755200)/ClassicalSixthBranch.r = (91931265906777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3105
  · change upperPayment 3106 ≤ upperValue ((point split endpoint 4096 3106+point split endpoint 4096 3107)/2)
    have hp : upperPayment 3106 = (147658798041:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3106+point split endpoint 4096 3107)/2 = (654280027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((654280027:ℝ)/168755200)*ClassicalSixthBranch.v ((654280027:ℝ)/168755200)/ClassicalSixthBranch.r = (91911535357545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3106
  · change upperPayment 3107 ≤ upperValue ((point split endpoint 4096 3107+point split endpoint 4096 3108)/2)
    have hp : upperPayment 3107 = (147527559799:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3107+point split endpoint 4096 3108)/2 = (654305177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((654305177:ℝ)/168755200)*ClassicalSixthBranch.v ((654305177:ℝ)/168755200)/ClassicalSixthBranch.r = (91891806832385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3107
  · change upperPayment 3108 ≤ upperValue ((point split endpoint 4096 3108+point split endpoint 4096 3109)/2)
    have hp : upperPayment 3108 = (147396288120:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3108+point split endpoint 4096 3109)/2 = (654330327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((654330327:ℝ)/168755200)*ClassicalSixthBranch.v ((654330327:ℝ)/168755200)/ClassicalSixthBranch.r = (91872080331297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3108
  · change upperPayment 3109 ≤ upperValue ((point split endpoint 4096 3109+point split endpoint 4096 3110)/2)
    have hp : upperPayment 3109 = (147264982995:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3109+point split endpoint 4096 3110)/2 = (654355477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((654355477:ℝ)/168755200)*ClassicalSixthBranch.v ((654355477:ℝ)/168755200)/ClassicalSixthBranch.r = (91852355854281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3109
  · change upperPayment 3110 ≤ upperValue ((point split endpoint 4096 3110+point split endpoint 4096 3111)/2)
    have hp : upperPayment 3110 = (147133644416:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3110+point split endpoint 4096 3111)/2 = (654380627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((654380627:ℝ)/168755200)*ClassicalSixthBranch.v ((654380627:ℝ)/168755200)/ClassicalSixthBranch.r = (91832633401337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3110
  · change upperPayment 3111 ≤ upperValue ((point split endpoint 4096 3111+point split endpoint 4096 3112)/2)
    have hp : upperPayment 3111 = (147002272375:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3111+point split endpoint 4096 3112)/2 = (654405777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((654405777:ℝ)/168755200)*ClassicalSixthBranch.v ((654405777:ℝ)/168755200)/ClassicalSixthBranch.r = (91812912972465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3111
  · change upperPayment 3112 ≤ upperValue ((point split endpoint 4096 3112+point split endpoint 4096 3113)/2)
    have hp : upperPayment 3112 = (146870866864:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3112+point split endpoint 4096 3113)/2 = (654430927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((654430927:ℝ)/168755200)*ClassicalSixthBranch.v ((654430927:ℝ)/168755200)/ClassicalSixthBranch.r = (91793194567665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3112
  · change upperPayment 3113 ≤ upperValue ((point split endpoint 4096 3113+point split endpoint 4096 3114)/2)
    have hp : upperPayment 3113 = (146739427875:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3113+point split endpoint 4096 3114)/2 = (654456077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((654456077:ℝ)/168755200)*ClassicalSixthBranch.v ((654456077:ℝ)/168755200)/ClassicalSixthBranch.r = (91773478186937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3113
  · change upperPayment 3114 ≤ upperValue ((point split endpoint 4096 3114+point split endpoint 4096 3115)/2)
    have hp : upperPayment 3114 = (146607955400:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3114+point split endpoint 4096 3115)/2 = (654481227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((654481227:ℝ)/168755200)*ClassicalSixthBranch.v ((654481227:ℝ)/168755200)/ClassicalSixthBranch.r = (91753763830281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3114
  · change upperPayment 3115 ≤ upperValue ((point split endpoint 4096 3115+point split endpoint 4096 3116)/2)
    have hp : upperPayment 3115 = (146476449431:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3115+point split endpoint 4096 3116)/2 = (654506377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((654506377:ℝ)/168755200)*ClassicalSixthBranch.v ((654506377:ℝ)/168755200)/ClassicalSixthBranch.r = (91734051497697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3115
  · change upperPayment 3116 ≤ upperValue ((point split endpoint 4096 3116+point split endpoint 4096 3117)/2)
    have hp : upperPayment 3116 = (146344909959:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3116+point split endpoint 4096 3117)/2 = (654531527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((654531527:ℝ)/168755200)*ClassicalSixthBranch.v ((654531527:ℝ)/168755200)/ClassicalSixthBranch.r = (91714341189185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3116
  · change upperPayment 3117 ≤ upperValue ((point split endpoint 4096 3117+point split endpoint 4096 3118)/2)
    have hp : upperPayment 3117 = (146213336977:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3117+point split endpoint 4096 3118)/2 = (654556677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((654556677:ℝ)/168755200)*ClassicalSixthBranch.v ((654556677:ℝ)/168755200)/ClassicalSixthBranch.r = (890239154415:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3117
  · change upperPayment 3118 ≤ upperValue ((point split endpoint 4096 3118+point split endpoint 4096 3119)/2)
    have hp : upperPayment 3118 = (146081730476:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3118+point split endpoint 4096 3119)/2 = (654581827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((654581827:ℝ)/168755200)*ClassicalSixthBranch.v ((654581827:ℝ)/168755200)/ClassicalSixthBranch.r = (91674926644377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3118
  · change upperPayment 3119 ≤ upperValue ((point split endpoint 4096 3119+point split endpoint 4096 3120)/2)
    have hp : upperPayment 3119 = (145950090449:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3119+point split endpoint 4096 3120)/2 = (654606977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((654606977:ℝ)/168755200)*ClassicalSixthBranch.v ((654606977:ℝ)/168755200)/ClassicalSixthBranch.r = (91655222408081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3119
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_194
