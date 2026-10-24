import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints254
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_254 (j : Fin 16) : upperPayment (16*254+j.val) ≤
    upperValue ((point split endpoint 4096 (16*254+j.val)+point split endpoint 4096 (16*254+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 4064 ≤ upperValue ((point split endpoint 4096 4064+point split endpoint 4096 4065)/2)
    have hp : upperPayment 4064 = (5297521272:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4064+point split endpoint 4096 4065)/2 = (678373727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((678373727:ℝ)/168755200)*ClassicalSixthBranch.v ((678373727:ℝ)/168755200)/ClassicalSixthBranch.r = (73939448931281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4064
  · change upperPayment 4065 ≤ upperValue ((point split endpoint 4096 4065+point split endpoint 4096 4066)/2)
    have hp : upperPayment 4065 = (5130002793:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4065+point split endpoint 4096 4066)/2 = (678398877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((678398877:ℝ)/168755200)*ClassicalSixthBranch.v ((678398877:ℝ)/168755200)/ClassicalSixthBranch.r = (73921659467097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4065
  · change upperPayment 4066 ≤ upperValue ((point split endpoint 4096 4066+point split endpoint 4096 4067)/2)
    have hp : upperPayment 4066 = (4962441363:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4066+point split endpoint 4096 4067)/2 = (678424027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((678424027:ℝ)/168755200)*ClassicalSixthBranch.v ((678424027:ℝ)/168755200)/ClassicalSixthBranch.r = (73903872026985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4066
  · change upperPayment 4067 ≤ upperValue ((point split endpoint 4096 4067+point split endpoint 4096 4068)/2)
    have hp : upperPayment 4067 = (4794836972:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4067+point split endpoint 4096 4068)/2 = (678449177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((678449177:ℝ)/168755200)*ClassicalSixthBranch.v ((678449177:ℝ)/168755200)/ClassicalSixthBranch.r = (73886086610945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4067
  · change upperPayment 4068 ≤ upperValue ((point split endpoint 4096 4068+point split endpoint 4096 4069)/2)
    have hp : upperPayment 4068 = (4627189608:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4068+point split endpoint 4096 4069)/2 = (678474327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((678474327:ℝ)/168755200)*ClassicalSixthBranch.v ((678474327:ℝ)/168755200)/ClassicalSixthBranch.r = (73868303218977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4068
  · change upperPayment 4069 ≤ upperValue ((point split endpoint 4096 4069+point split endpoint 4096 4070)/2)
    have hp : upperPayment 4069 = (4459499257:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4069+point split endpoint 4096 4070)/2 = (678499477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((678499477:ℝ)/168755200)*ClassicalSixthBranch.v ((678499477:ℝ)/168755200)/ClassicalSixthBranch.r = (73850521851081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4069
  · change upperPayment 4070 ≤ upperValue ((point split endpoint 4096 4070+point split endpoint 4096 4071)/2)
    have hp : upperPayment 4070 = (4291765909:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4070+point split endpoint 4096 4071)/2 = (678524627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((678524627:ℝ)/168755200)*ClassicalSixthBranch.v ((678524627:ℝ)/168755200)/ClassicalSixthBranch.r = (73832742507257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4070
  · change upperPayment 4071 ≤ upperValue ((point split endpoint 4096 4071+point split endpoint 4096 4072)/2)
    have hp : upperPayment 4071 = (4123989551:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4071+point split endpoint 4096 4072)/2 = (678549777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((678549777:ℝ)/168755200)*ClassicalSixthBranch.v ((678549777:ℝ)/168755200)/ClassicalSixthBranch.r = (73814965187505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4071
  · change upperPayment 4072 ≤ upperValue ((point split endpoint 4096 4072+point split endpoint 4096 4073)/2)
    have hp : upperPayment 4072 = (3956170170:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4072+point split endpoint 4096 4073)/2 = (678574927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((678574927:ℝ)/168755200)*ClassicalSixthBranch.v ((678574927:ℝ)/168755200)/ClassicalSixthBranch.r = (73797189891825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4072
  · change upperPayment 4073 ≤ upperValue ((point split endpoint 4096 4073+point split endpoint 4096 4074)/2)
    have hp : upperPayment 4073 = (3788307755:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4073+point split endpoint 4096 4074)/2 = (678600077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((678600077:ℝ)/168755200)*ClassicalSixthBranch.v ((678600077:ℝ)/168755200)/ClassicalSixthBranch.r = (73779416620217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4073
  · change upperPayment 4074 ≤ upperValue ((point split endpoint 4096 4074+point split endpoint 4096 4075)/2)
    have hp : upperPayment 4074 = (3620402294:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4074+point split endpoint 4096 4075)/2 = (678625227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((678625227:ℝ)/168755200)*ClassicalSixthBranch.v ((678625227:ℝ)/168755200)/ClassicalSixthBranch.r = (73761645372681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4074
  · change upperPayment 4075 ≤ upperValue ((point split endpoint 4096 4075+point split endpoint 4096 4076)/2)
    have hp : upperPayment 4075 = (3452453774:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4075+point split endpoint 4096 4076)/2 = (678650377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((678650377:ℝ)/168755200)*ClassicalSixthBranch.v ((678650377:ℝ)/168755200)/ClassicalSixthBranch.r = (73743876149217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4075
  · change upperPayment 4076 ≤ upperValue ((point split endpoint 4096 4076+point split endpoint 4096 4077)/2)
    have hp : upperPayment 4076 = (3284462184:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4076+point split endpoint 4096 4077)/2 = (678675527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((678675527:ℝ)/168755200)*ClassicalSixthBranch.v ((678675527:ℝ)/168755200)/ClassicalSixthBranch.r = (73726108949825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4076
  · change upperPayment 4077 ≤ upperValue ((point split endpoint 4096 4077+point split endpoint 4096 4078)/2)
    have hp : upperPayment 4077 = (3116427511:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4077+point split endpoint 4096 4078)/2 = (678700677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((678700677:ℝ)/168755200)*ClassicalSixthBranch.v ((678700677:ℝ)/168755200)/ClassicalSixthBranch.r = (73708343774505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4077
  · change upperPayment 4078 ≤ upperValue ((point split endpoint 4096 4078+point split endpoint 4096 4079)/2)
    have hp : upperPayment 4078 = (2948349742:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4078+point split endpoint 4096 4079)/2 = (678725827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((678725827:ℝ)/168755200)*ClassicalSixthBranch.v ((678725827:ℝ)/168755200)/ClassicalSixthBranch.r = (73690580623257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4078
  · change upperPayment 4079 ≤ upperValue ((point split endpoint 4096 4079+point split endpoint 4096 4080)/2)
    have hp : upperPayment 4079 = (2780228867:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4079+point split endpoint 4096 4080)/2 = (678750977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((678750977:ℝ)/168755200)*ClassicalSixthBranch.v ((678750977:ℝ)/168755200)/ClassicalSixthBranch.r = (73672819496081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4079
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_254
