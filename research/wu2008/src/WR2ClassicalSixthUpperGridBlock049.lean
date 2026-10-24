import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints049
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_049 (j : Fin 16) : upperPayment (16*49+j.val) ≤
    upperValue ((point split endpoint 4096 (16*49+j.val)+point split endpoint 4096 (16*49+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 784 ≤ upperValue ((point split endpoint 4096 784+point split endpoint 4096 785)/2)
    have hp : upperPayment 784 = (375781257202:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 784+point split endpoint 4096 785)/2 = (595881727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((595881727:ℝ)/168755200)*ClassicalSixthBranch.v ((595881727:ℝ)/168755200)/ClassicalSixthBranch.r = (143180099035281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_784
  · change upperPayment 785 ≤ upperValue ((point split endpoint 4096 785+point split endpoint 4096 786)/2)
    have hp : upperPayment 785 = (375711338934:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 785+point split endpoint 4096 786)/2 = (595906877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((595906877:ℝ)/168755200)*ClassicalSixthBranch.v ((595906877:ℝ)/168755200)/ClassicalSixthBranch.r = (143155670614937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_785
  · change upperPayment 786 ≤ upperValue ((point split endpoint 4096 786+point split endpoint 4096 787)/2)
    have hp : upperPayment 786 = (375641399389:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 786+point split endpoint 4096 787)/2 = (595932027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((595932027:ℝ)/168755200)*ClassicalSixthBranch.v ((595932027:ℝ)/168755200)/ClassicalSixthBranch.r = (143131244218665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_786
  · change upperPayment 787 ≤ upperValue ((point split endpoint 4096 787+point split endpoint 4096 788)/2)
    have hp : upperPayment 787 = (375571438564:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 787+point split endpoint 4096 788)/2 = (595957177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((595957177:ℝ)/168755200)*ClassicalSixthBranch.v ((595957177:ℝ)/168755200)/ClassicalSixthBranch.r = (143106819846465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_787
  · change upperPayment 788 ≤ upperValue ((point split endpoint 4096 788+point split endpoint 4096 789)/2)
    have hp : upperPayment 788 = (375501456456:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 788+point split endpoint 4096 789)/2 = (595982327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((595982327:ℝ)/168755200)*ClassicalSixthBranch.v ((595982327:ℝ)/168755200)/ClassicalSixthBranch.r = (143082397498337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_788
  · change upperPayment 789 ≤ upperValue ((point split endpoint 4096 789+point split endpoint 4096 790)/2)
    have hp : upperPayment 789 = (375431453061:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 789+point split endpoint 4096 790)/2 = (596007477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((596007477:ℝ)/168755200)*ClassicalSixthBranch.v ((596007477:ℝ)/168755200)/ClassicalSixthBranch.r = (143057977174281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_789
  · change upperPayment 790 ≤ upperValue ((point split endpoint 4096 790+point split endpoint 4096 791)/2)
    have hp : upperPayment 790 = (375361428377:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 790+point split endpoint 4096 791)/2 = (596032627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((596032627:ℝ)/168755200)*ClassicalSixthBranch.v ((596032627:ℝ)/168755200)/ClassicalSixthBranch.r = (143033558874297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_790
  · change upperPayment 791 ≤ upperValue ((point split endpoint 4096 791+point split endpoint 4096 792)/2)
    have hp : upperPayment 791 = (375291382401:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 791+point split endpoint 4096 792)/2 = (596057777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((596057777:ℝ)/168755200)*ClassicalSixthBranch.v ((596057777:ℝ)/168755200)/ClassicalSixthBranch.r = (143009142598385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_791
  · change upperPayment 792 ≤ upperValue ((point split endpoint 4096 792+point split endpoint 4096 793)/2)
    have hp : upperPayment 792 = (375221315129:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 792+point split endpoint 4096 793)/2 = (596082927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((596082927:ℝ)/168755200)*ClassicalSixthBranch.v ((596082927:ℝ)/168755200)/ClassicalSixthBranch.r = (142984728346545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_792
  · change upperPayment 793 ≤ upperValue ((point split endpoint 4096 793+point split endpoint 4096 794)/2)
    have hp : upperPayment 793 = (375151226558:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 793+point split endpoint 4096 794)/2 = (596108077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((596108077:ℝ)/168755200)*ClassicalSixthBranch.v ((596108077:ℝ)/168755200)/ClassicalSixthBranch.r = (142960316118777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_793
  · change upperPayment 794 ≤ upperValue ((point split endpoint 4096 794+point split endpoint 4096 795)/2)
    have hp : upperPayment 794 = (375081116686:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 794+point split endpoint 4096 795)/2 = (596133227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((596133227:ℝ)/168755200)*ClassicalSixthBranch.v ((596133227:ℝ)/168755200)/ClassicalSixthBranch.r = (142935905915081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_794
  · change upperPayment 795 ≤ upperValue ((point split endpoint 4096 795+point split endpoint 4096 796)/2)
    have hp : upperPayment 795 = (375010985508:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 795+point split endpoint 4096 796)/2 = (596158377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((596158377:ℝ)/168755200)*ClassicalSixthBranch.v ((596158377:ℝ)/168755200)/ClassicalSixthBranch.r = (142911497735457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_795
  · change upperPayment 796 ≤ upperValue ((point split endpoint 4096 796+point split endpoint 4096 797)/2)
    have hp : upperPayment 796 = (374940833023:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 796+point split endpoint 4096 797)/2 = (596183527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((596183527:ℝ)/168755200)*ClassicalSixthBranch.v ((596183527:ℝ)/168755200)/ClassicalSixthBranch.r = (142887091579905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_796
  · change upperPayment 797 ≤ upperValue ((point split endpoint 4096 797+point split endpoint 4096 798)/2)
    have hp : upperPayment 797 = (374870659226:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 797+point split endpoint 4096 798)/2 = (596208677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((596208677:ℝ)/168755200)*ClassicalSixthBranch.v ((596208677:ℝ)/168755200)/ClassicalSixthBranch.r = (142862687448425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_797
  · change upperPayment 798 ≤ upperValue ((point split endpoint 4096 798+point split endpoint 4096 799)/2)
    have hp : upperPayment 798 = (374800464115:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 798+point split endpoint 4096 799)/2 = (596233827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((596233827:ℝ)/168755200)*ClassicalSixthBranch.v ((596233827:ℝ)/168755200)/ClassicalSixthBranch.r = (142838285341017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_798
  · change upperPayment 799 ≤ upperValue ((point split endpoint 4096 799+point split endpoint 4096 800)/2)
    have hp : upperPayment 799 = (374730247686:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 799+point split endpoint 4096 800)/2 = (596258977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((596258977:ℝ)/168755200)*ClassicalSixthBranch.v ((596258977:ℝ)/168755200)/ClassicalSixthBranch.r = (142813885257681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_799
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_049
