import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints253
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_253 (j : Fin 16) : upperPayment (16*253+j.val) ≤
    upperValue ((point split endpoint 4096 (16*253+j.val)+point split endpoint 4096 (16*253+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 4048 ≤ upperValue ((point split endpoint 4096 4048+point split endpoint 4096 4049)/2)
    have hp : upperPayment 4048 = (7971985652:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4048+point split endpoint 4096 4049)/2 = (677971327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((677971327:ℝ)/168755200)*ClassicalSixthBranch.v ((677971327:ℝ)/168755200)/ClassicalSixthBranch.r = (74224355632017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4048
  · change upperPayment 4049 ≤ upperValue ((point split endpoint 4096 4049+point split endpoint 4096 4050)/2)
    have hp : upperPayment 4049 = (7805152726:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4049+point split endpoint 4096 4050)/2 = (677996477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((677996477:ℝ)/168755200)*ClassicalSixthBranch.v ((677996477:ℝ)/168755200)/ClassicalSixthBranch.r = (74206533782681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4049
  · change upperPayment 4050 ≤ upperValue ((point split endpoint 4096 4050+point split endpoint 4096 4051)/2)
    have hp : upperPayment 4050 = (7638277042:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4050+point split endpoint 4096 4051)/2 = (678021627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((678021627:ℝ)/168755200)*ClassicalSixthBranch.v ((678021627:ℝ)/168755200)/ClassicalSixthBranch.r = (74188713957417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4050
  · change upperPayment 4051 ≤ upperValue ((point split endpoint 4096 4051+point split endpoint 4096 4052)/2)
    have hp : upperPayment 4051 = (7471358590:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4051+point split endpoint 4096 4052)/2 = (678046777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((678046777:ℝ)/168755200)*ClassicalSixthBranch.v ((678046777:ℝ)/168755200)/ClassicalSixthBranch.r = (74170896156225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4051
  · change upperPayment 4052 ≤ upperValue ((point split endpoint 4096 4052+point split endpoint 4096 4053)/2)
    have hp : upperPayment 4052 = (7304397357:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4052+point split endpoint 4096 4053)/2 = (678071927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((678071927:ℝ)/168755200)*ClassicalSixthBranch.v ((678071927:ℝ)/168755200)/ClassicalSixthBranch.r = (74153080379105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4052
  · change upperPayment 4053 ≤ upperValue ((point split endpoint 4096 4053+point split endpoint 4096 4054)/2)
    have hp : upperPayment 4053 = (7137393331:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4053+point split endpoint 4096 4054)/2 = (678097077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((678097077:ℝ)/168755200)*ClassicalSixthBranch.v ((678097077:ℝ)/168755200)/ClassicalSixthBranch.r = (74135266626057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4053
  · change upperPayment 4054 ≤ upperValue ((point split endpoint 4096 4054+point split endpoint 4096 4055)/2)
    have hp : upperPayment 4054 = (6970346500:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4054+point split endpoint 4096 4055)/2 = (678122227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((678122227:ℝ)/168755200)*ClassicalSixthBranch.v ((678122227:ℝ)/168755200)/ClassicalSixthBranch.r = (74117454897081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4054
  · change upperPayment 4055 ≤ upperValue ((point split endpoint 4096 4055+point split endpoint 4096 4056)/2)
    have hp : upperPayment 4055 = (6803256852:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4055+point split endpoint 4096 4056)/2 = (678147377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((678147377:ℝ)/168755200)*ClassicalSixthBranch.v ((678147377:ℝ)/168755200)/ClassicalSixthBranch.r = (74099645192177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4055
  · change upperPayment 4056 ≤ upperValue ((point split endpoint 4096 4056+point split endpoint 4096 4057)/2)
    have hp : upperPayment 4056 = (6636124375:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4056+point split endpoint 4096 4057)/2 = (678172527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((678172527:ℝ)/168755200)*ClassicalSixthBranch.v ((678172527:ℝ)/168755200)/ClassicalSixthBranch.r = (74081837511345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4056
  · change upperPayment 4057 ≤ upperValue ((point split endpoint 4096 4057+point split endpoint 4096 4058)/2)
    have hp : upperPayment 4057 = (6468949057:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4057+point split endpoint 4096 4058)/2 = (678197677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((678197677:ℝ)/168755200)*ClassicalSixthBranch.v ((678197677:ℝ)/168755200)/ClassicalSixthBranch.r = (74064031854585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4057
  · change upperPayment 4058 ≤ upperValue ((point split endpoint 4096 4058+point split endpoint 4096 4059)/2)
    have hp : upperPayment 4058 = (6301730886:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4058+point split endpoint 4096 4059)/2 = (678222827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((678222827:ℝ)/168755200)*ClassicalSixthBranch.v ((678222827:ℝ)/168755200)/ClassicalSixthBranch.r = (74046228221897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4058
  · change upperPayment 4059 ≤ upperValue ((point split endpoint 4096 4059+point split endpoint 4096 4060)/2)
    have hp : upperPayment 4059 = (6134469850:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4059+point split endpoint 4096 4060)/2 = (678247977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((678247977:ℝ)/168755200)*ClassicalSixthBranch.v ((678247977:ℝ)/168755200)/ClassicalSixthBranch.r = (74028426613281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4059
  · change upperPayment 4060 ≤ upperValue ((point split endpoint 4096 4060+point split endpoint 4096 4061)/2)
    have hp : upperPayment 4060 = (5967165937:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4060+point split endpoint 4096 4061)/2 = (678273127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((678273127:ℝ)/168755200)*ClassicalSixthBranch.v ((678273127:ℝ)/168755200)/ClassicalSixthBranch.r = (74010627028737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4060
  · change upperPayment 4061 ≤ upperValue ((point split endpoint 4096 4061+point split endpoint 4096 4062)/2)
    have hp : upperPayment 4061 = (5799819135:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4061+point split endpoint 4096 4062)/2 = (678298277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((678298277:ℝ)/168755200)*ClassicalSixthBranch.v ((678298277:ℝ)/168755200)/ClassicalSixthBranch.r = (73992829468265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4061
  · change upperPayment 4062 ≤ upperValue ((point split endpoint 4096 4062+point split endpoint 4096 4063)/2)
    have hp : upperPayment 4062 = (5632429431:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4062+point split endpoint 4096 4063)/2 = (678323427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((678323427:ℝ)/168755200)*ClassicalSixthBranch.v ((678323427:ℝ)/168755200)/ClassicalSixthBranch.r = (73975033931865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4062
  · change upperPayment 4063 ≤ upperValue ((point split endpoint 4096 4063+point split endpoint 4096 4064)/2)
    have hp : upperPayment 4063 = (5464996815:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4063+point split endpoint 4096 4064)/2 = (678348577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((678348577:ℝ)/168755200)*ClassicalSixthBranch.v ((678348577:ℝ)/168755200)/ClassicalSixthBranch.r = (73957240419537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4063
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_253
