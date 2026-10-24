import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints224
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_224 (j : Fin 16) : upperPayment (16*224+j.val) ≤
    upperValue ((point split endpoint 4096 (16*224+j.val)+point split endpoint 4096 (16*224+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3584 ≤ upperValue ((point split endpoint 4096 3584+point split endpoint 4096 3585)/2)
    have hp : upperPayment 3584 = (80961266749:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3584+point split endpoint 4096 3585)/2 = (666301727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((666301727:ℝ)/168755200)*ClassicalSixthBranch.v ((666301727:ℝ)/168755200)/ClassicalSixthBranch.r = (82712050611281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3584
  · change upperPayment 3585 ≤ upperValue ((point split endpoint 4096 3585+point split endpoint 4096 3586)/2)
    have hp : upperPayment 3585 = (80813060471:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3585+point split endpoint 4096 3586)/2 = (666326877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((666326877:ℝ)/168755200)*ClassicalSixthBranch.v ((666326877:ℝ)/168755200)/ClassicalSixthBranch.r = (82693289592537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3585
  · change upperPayment 3586 ≤ upperValue ((point split endpoint 4096 3586+point split endpoint 4096 3587)/2)
    have hp : upperPayment 3586 = (80664816486:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3586+point split endpoint 4096 3587)/2 = (666352027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((666352027:ℝ)/168755200)*ClassicalSixthBranch.v ((666352027:ℝ)/168755200)/ClassicalSixthBranch.r = (82674530597865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3586
  · change upperPayment 3587 ≤ upperValue ((point split endpoint 4096 3587+point split endpoint 4096 3588)/2)
    have hp : upperPayment 3587 = (80516534783:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3587+point split endpoint 4096 3588)/2 = (666377177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((666377177:ℝ)/168755200)*ClassicalSixthBranch.v ((666377177:ℝ)/168755200)/ClassicalSixthBranch.r = (82655773627265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3587
  · change upperPayment 3588 ≤ upperValue ((point split endpoint 4096 3588+point split endpoint 4096 3589)/2)
    have hp : upperPayment 3588 = (80368215353:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3588+point split endpoint 4096 3589)/2 = (666402327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((666402327:ℝ)/168755200)*ClassicalSixthBranch.v ((666402327:ℝ)/168755200)/ClassicalSixthBranch.r = (82637018680737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3588
  · change upperPayment 3589 ≤ upperValue ((point split endpoint 4096 3589+point split endpoint 4096 3590)/2)
    have hp : upperPayment 3589 = (80219858186:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3589+point split endpoint 4096 3590)/2 = (666427477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((666427477:ℝ)/168755200)*ClassicalSixthBranch.v ((666427477:ℝ)/168755200)/ClassicalSixthBranch.r = (82618265758281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3589
  · change upperPayment 3590 ≤ upperValue ((point split endpoint 4096 3590+point split endpoint 4096 3591)/2)
    have hp : upperPayment 3590 = (80071463272:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3590+point split endpoint 4096 3591)/2 = (666452627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((666452627:ℝ)/168755200)*ClassicalSixthBranch.v ((666452627:ℝ)/168755200)/ClassicalSixthBranch.r = (82599514859897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3590
  · change upperPayment 3591 ≤ upperValue ((point split endpoint 4096 3591+point split endpoint 4096 3592)/2)
    have hp : upperPayment 3591 = (79923030601:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3591+point split endpoint 4096 3592)/2 = (666477777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((666477777:ℝ)/168755200)*ClassicalSixthBranch.v ((666477777:ℝ)/168755200)/ClassicalSixthBranch.r = (82580765985585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3591
  · change upperPayment 3592 ≤ upperValue ((point split endpoint 4096 3592+point split endpoint 4096 3593)/2)
    have hp : upperPayment 3592 = (79774560163:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3592+point split endpoint 4096 3593)/2 = (666502927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((666502927:ℝ)/168755200)*ClassicalSixthBranch.v ((666502927:ℝ)/168755200)/ClassicalSixthBranch.r = (82562019135345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3592
  · change upperPayment 3593 ≤ upperValue ((point split endpoint 4096 3593+point split endpoint 4096 3594)/2)
    have hp : upperPayment 3593 = (79626051948:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3593+point split endpoint 4096 3594)/2 = (666528077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((666528077:ℝ)/168755200)*ClassicalSixthBranch.v ((666528077:ℝ)/168755200)/ClassicalSixthBranch.r = (82543274309177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3593
  · change upperPayment 3594 ≤ upperValue ((point split endpoint 4096 3594+point split endpoint 4096 3595)/2)
    have hp : upperPayment 3594 = (79477505947:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3594+point split endpoint 4096 3595)/2 = (666553227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((666553227:ℝ)/168755200)*ClassicalSixthBranch.v ((666553227:ℝ)/168755200)/ClassicalSixthBranch.r = (82524531507081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3594
  · change upperPayment 3595 ≤ upperValue ((point split endpoint 4096 3595+point split endpoint 4096 3596)/2)
    have hp : upperPayment 3595 = (79328922150:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3595+point split endpoint 4096 3596)/2 = (666578377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((666578377:ℝ)/168755200)*ClassicalSixthBranch.v ((666578377:ℝ)/168755200)/ClassicalSixthBranch.r = (82505790729057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3595
  · change upperPayment 3596 ≤ upperValue ((point split endpoint 4096 3596+point split endpoint 4096 3597)/2)
    have hp : upperPayment 3596 = (79180300546:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3596+point split endpoint 4096 3597)/2 = (666603527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((666603527:ℝ)/168755200)*ClassicalSixthBranch.v ((666603527:ℝ)/168755200)/ClassicalSixthBranch.r = (82487051975105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3596
  · change upperPayment 3597 ≤ upperValue ((point split endpoint 4096 3597+point split endpoint 4096 3598)/2)
    have hp : upperPayment 3597 = (79031641126:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3597+point split endpoint 4096 3598)/2 = (666628677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((666628677:ℝ)/168755200)*ClassicalSixthBranch.v ((666628677:ℝ)/168755200)/ClassicalSixthBranch.r = (82468315245225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3597
  · change upperPayment 3598 ≤ upperValue ((point split endpoint 4096 3598+point split endpoint 4096 3599)/2)
    have hp : upperPayment 3598 = (78882943880:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3598+point split endpoint 4096 3599)/2 = (666653827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((666653827:ℝ)/168755200)*ClassicalSixthBranch.v ((666653827:ℝ)/168755200)/ClassicalSixthBranch.r = (82449580539417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3598
  · change upperPayment 3599 ≤ upperValue ((point split endpoint 4096 3599+point split endpoint 4096 3600)/2)
    have hp : upperPayment 3599 = (78734208799:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3599+point split endpoint 4096 3600)/2 = (666678977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((666678977:ℝ)/168755200)*ClassicalSixthBranch.v ((666678977:ℝ)/168755200)/ClassicalSixthBranch.r = (82430847857681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3599
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_224
