import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints219
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_219 (j : Fin 16) : upperPayment (16*219+j.val) ≤
    upperValue ((point split endpoint 4096 (16*219+j.val)+point split endpoint 4096 (16*219+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3504 ≤ upperValue ((point split endpoint 4096 3504+point split endpoint 4096 3505)/2)
    have hp : upperPayment 3504 = (92696461113:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3504+point split endpoint 4096 3505)/2 = (664289727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((664289727:ℝ)/168755200)*ClassicalSixthBranch.v ((664289727:ℝ)/168755200)/ClassicalSixthBranch.r = (84219490104081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3504
  · change upperPayment 3505 ≤ upperValue ((point split endpoint 4096 3505+point split endpoint 4096 3506)/2)
    have hp : upperPayment 3505 = (92551239892:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3505+point split endpoint 4096 3506)/2 = (6449659:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((6449659:ℝ)/1638400)*ClassicalSixthBranch.v ((6449659:ℝ)/1638400)/ClassicalSixthBranch.r = (817481234559:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3505
  · change upperPayment 3506 ≤ upperValue ((point split endpoint 4096 3506+point split endpoint 4096 3507)/2)
    have hp : upperPayment 3506 = (92405981738:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3506+point split endpoint 4096 3507)/2 = (664340027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((664340027:ℝ)/168755200)*ClassicalSixthBranch.v ((664340027:ℝ)/168755200)/ClassicalSixthBranch.r = (84181646239145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3506
  · change upperPayment 3507 ≤ upperValue ((point split endpoint 4096 3507+point split endpoint 4096 3508)/2)
    have hp : upperPayment 3507 = (92260686642:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3507+point split endpoint 4096 3508)/2 = (664365177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((664365177:ℝ)/168755200)*ClassicalSixthBranch.v ((664365177:ℝ)/168755200)/ClassicalSixthBranch.r = (84162727342785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3507
  · change upperPayment 3508 ≤ upperValue ((point split endpoint 4096 3508+point split endpoint 4096 3509)/2)
    have hp : upperPayment 3508 = (92115354594:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3508+point split endpoint 4096 3509)/2 = (664390327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((664390327:ℝ)/168755200)*ClassicalSixthBranch.v ((664390327:ℝ)/168755200)/ClassicalSixthBranch.r = (84143810470497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3508
  · change upperPayment 3509 ≤ upperValue ((point split endpoint 4096 3509+point split endpoint 4096 3510)/2)
    have hp : upperPayment 3509 = (91969985584:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3509+point split endpoint 4096 3510)/2 = (664415477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((664415477:ℝ)/168755200)*ClassicalSixthBranch.v ((664415477:ℝ)/168755200)/ClassicalSixthBranch.r = (84124895622281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3509
  · change upperPayment 3510 ≤ upperValue ((point split endpoint 4096 3510+point split endpoint 4096 3511)/2)
    have hp : upperPayment 3510 = (91824579604:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3510+point split endpoint 4096 3511)/2 = (664440627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((664440627:ℝ)/168755200)*ClassicalSixthBranch.v ((664440627:ℝ)/168755200)/ClassicalSixthBranch.r = (84105982798137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3510
  · change upperPayment 3511 ≤ upperValue ((point split endpoint 4096 3511+point split endpoint 4096 3512)/2)
    have hp : upperPayment 3511 = (91679136643:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3511+point split endpoint 4096 3512)/2 = (664465777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((664465777:ℝ)/168755200)*ClassicalSixthBranch.v ((664465777:ℝ)/168755200)/ClassicalSixthBranch.r = (84087071998065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3511
  · change upperPayment 3512 ≤ upperValue ((point split endpoint 4096 3512+point split endpoint 4096 3513)/2)
    have hp : upperPayment 3512 = (91533656692:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3512+point split endpoint 4096 3513)/2 = (664490927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((664490927:ℝ)/168755200)*ClassicalSixthBranch.v ((664490927:ℝ)/168755200)/ClassicalSixthBranch.r = (84068163222065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3512
  · change upperPayment 3513 ≤ upperValue ((point split endpoint 4096 3513+point split endpoint 4096 3514)/2)
    have hp : upperPayment 3513 = (91388139742:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3513+point split endpoint 4096 3514)/2 = (664516077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((664516077:ℝ)/168755200)*ClassicalSixthBranch.v ((664516077:ℝ)/168755200)/ClassicalSixthBranch.r = (84049256470137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3513
  · change upperPayment 3514 ≤ upperValue ((point split endpoint 4096 3514+point split endpoint 4096 3515)/2)
    have hp : upperPayment 3514 = (91242585782:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3514+point split endpoint 4096 3515)/2 = (664541227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((664541227:ℝ)/168755200)*ClassicalSixthBranch.v ((664541227:ℝ)/168755200)/ClassicalSixthBranch.r = (84030351742281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3514
  · change upperPayment 3515 ≤ upperValue ((point split endpoint 4096 3515+point split endpoint 4096 3516)/2)
    have hp : upperPayment 3515 = (91096994804:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3515+point split endpoint 4096 3516)/2 = (664566377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((664566377:ℝ)/168755200)*ClassicalSixthBranch.v ((664566377:ℝ)/168755200)/ClassicalSixthBranch.r = (84011449038497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3515
  · change upperPayment 3516 ≤ upperValue ((point split endpoint 4096 3516+point split endpoint 4096 3517)/2)
    have hp : upperPayment 3516 = (90951366797:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3516+point split endpoint 4096 3517)/2 = (664591527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((664591527:ℝ)/168755200)*ClassicalSixthBranch.v ((664591527:ℝ)/168755200)/ClassicalSixthBranch.r = (83992548358785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3516
  · change upperPayment 3517 ≤ upperValue ((point split endpoint 4096 3517+point split endpoint 4096 3518)/2)
    have hp : upperPayment 3517 = (90805701753:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3517+point split endpoint 4096 3518)/2 = (664616677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((664616677:ℝ)/168755200)*ClassicalSixthBranch.v ((664616677:ℝ)/168755200)/ClassicalSixthBranch.r = (83973649703145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3517
  · change upperPayment 3518 ≤ upperValue ((point split endpoint 4096 3518+point split endpoint 4096 3519)/2)
    have hp : upperPayment 3518 = (90659999661:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3518+point split endpoint 4096 3519)/2 = (664641827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((664641827:ℝ)/168755200)*ClassicalSixthBranch.v ((664641827:ℝ)/168755200)/ClassicalSixthBranch.r = (83954753071577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3518
  · change upperPayment 3519 ≤ upperValue ((point split endpoint 4096 3519+point split endpoint 4096 3520)/2)
    have hp : upperPayment 3519 = (90514260512:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3519+point split endpoint 4096 3520)/2 = (664666977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((664666977:ℝ)/168755200)*ClassicalSixthBranch.v ((664666977:ℝ)/168755200)/ClassicalSixthBranch.r = (83935858464081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3519
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_219
