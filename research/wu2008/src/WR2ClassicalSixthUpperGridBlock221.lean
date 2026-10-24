import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints221
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_221 (j : Fin 16) : upperPayment (16*221+j.val) ≤
    upperValue ((point split endpoint 4096 (16*221+j.val)+point split endpoint 4096 (16*221+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3536 ≤ upperValue ((point split endpoint 4096 3536+point split endpoint 4096 3537)/2)
    have hp : upperPayment 3536 = (88031015971:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3536+point split endpoint 4096 3537)/2 = (665094527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((665094527:ℝ)/168755200)*ClassicalSixthBranch.v ((665094527:ℝ)/168755200)/ClassicalSixthBranch.r = (83614959819665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3536
  · change upperPayment 3537 ≤ upperValue ((point split endpoint 4096 3537+point split endpoint 4096 3538)/2)
    have hp : upperPayment 3537 = (87884608155:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3537+point split endpoint 4096 3538)/2 = (665119677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((665119677:ℝ)/168755200)*ClassicalSixthBranch.v ((665119677:ℝ)/168755200)/ClassicalSixthBranch.r = (83596101645465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3537
  · change upperPayment 3538 ≤ upperValue ((point split endpoint 4096 3538+point split endpoint 4096 3539)/2)
    have hp : upperPayment 3538 = (87738163100:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3538+point split endpoint 4096 3539)/2 = (665144827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((665144827:ℝ)/168755200)*ClassicalSixthBranch.v ((665144827:ℝ)/168755200)/ClassicalSixthBranch.r = (83577245495337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3538
  · change upperPayment 3539 ≤ upperValue ((point split endpoint 4096 3539+point split endpoint 4096 3540)/2)
    have hp : upperPayment 3539 = (87591680795:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3539+point split endpoint 4096 3540)/2 = (665169977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((665169977:ℝ)/168755200)*ClassicalSixthBranch.v ((665169977:ℝ)/168755200)/ClassicalSixthBranch.r = (83558391369281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3539
  · change upperPayment 3540 ≤ upperValue ((point split endpoint 4096 3540+point split endpoint 4096 3541)/2)
    have hp : upperPayment 3540 = (87445161231:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3540+point split endpoint 4096 3541)/2 = (665195127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((665195127:ℝ)/168755200)*ClassicalSixthBranch.v ((665195127:ℝ)/168755200)/ClassicalSixthBranch.r = (83539539267297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3540
  · change upperPayment 3541 ≤ upperValue ((point split endpoint 4096 3541+point split endpoint 4096 3542)/2)
    have hp : upperPayment 3541 = (87298604399:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3541+point split endpoint 4096 3542)/2 = (665220277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((665220277:ℝ)/168755200)*ClassicalSixthBranch.v ((665220277:ℝ)/168755200)/ClassicalSixthBranch.r = (83520689189385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3541
  · change upperPayment 3542 ≤ upperValue ((point split endpoint 4096 3542+point split endpoint 4096 3543)/2)
    have hp : upperPayment 3542 = (87152010289:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3542+point split endpoint 4096 3543)/2 = (665245427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((665245427:ℝ)/168755200)*ClassicalSixthBranch.v ((665245427:ℝ)/168755200)/ClassicalSixthBranch.r = (83501841135545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3542
  · change upperPayment 3543 ≤ upperValue ((point split endpoint 4096 3543+point split endpoint 4096 3544)/2)
    have hp : upperPayment 3543 = (87005378890:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3543+point split endpoint 4096 3544)/2 = (665270577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((665270577:ℝ)/168755200)*ClassicalSixthBranch.v ((665270577:ℝ)/168755200)/ClassicalSixthBranch.r = (83482995105777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3543
  · change upperPayment 3544 ≤ upperValue ((point split endpoint 4096 3544+point split endpoint 4096 3545)/2)
    have hp : upperPayment 3544 = (86858710194:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3544+point split endpoint 4096 3545)/2 = (665295727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((665295727:ℝ)/168755200)*ClassicalSixthBranch.v ((665295727:ℝ)/168755200)/ClassicalSixthBranch.r = (83464151100081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3544
  · change upperPayment 3545 ≤ upperValue ((point split endpoint 4096 3545+point split endpoint 4096 3546)/2)
    have hp : upperPayment 3545 = (86712004191:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3545+point split endpoint 4096 3546)/2 = (665320877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((665320877:ℝ)/168755200)*ClassicalSixthBranch.v ((665320877:ℝ)/168755200)/ClassicalSixthBranch.r = (83445309118457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3545
  · change upperPayment 3546 ≤ upperValue ((point split endpoint 4096 3546+point split endpoint 4096 3547)/2)
    have hp : upperPayment 3546 = (86565260870:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3546+point split endpoint 4096 3547)/2 = (665346027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((665346027:ℝ)/168755200)*ClassicalSixthBranch.v ((665346027:ℝ)/168755200)/ClassicalSixthBranch.r = (83426469160905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3546
  · change upperPayment 3547 ≤ upperValue ((point split endpoint 4096 3547+point split endpoint 4096 3548)/2)
    have hp : upperPayment 3547 = (86418480223:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3547+point split endpoint 4096 3548)/2 = (665371177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((665371177:ℝ)/168755200)*ClassicalSixthBranch.v ((665371177:ℝ)/168755200)/ClassicalSixthBranch.r = (83407631227425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3547
  · change upperPayment 3548 ≤ upperValue ((point split endpoint 4096 3548+point split endpoint 4096 3549)/2)
    have hp : upperPayment 3548 = (86271662240:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3548+point split endpoint 4096 3549)/2 = (665396327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((665396327:ℝ)/168755200)*ClassicalSixthBranch.v ((665396327:ℝ)/168755200)/ClassicalSixthBranch.r = (83388795318017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3548
  · change upperPayment 3549 ≤ upperValue ((point split endpoint 4096 3549+point split endpoint 4096 3550)/2)
    have hp : upperPayment 3549 = (86124806910:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3549+point split endpoint 4096 3550)/2 = (665421477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((665421477:ℝ)/168755200)*ClassicalSixthBranch.v ((665421477:ℝ)/168755200)/ClassicalSixthBranch.r = (83369961432681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3549
  · change upperPayment 3550 ≤ upperValue ((point split endpoint 4096 3550+point split endpoint 4096 3551)/2)
    have hp : upperPayment 3550 = (85977914225:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3550+point split endpoint 4096 3551)/2 = (665446627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((665446627:ℝ)/168755200)*ClassicalSixthBranch.v ((665446627:ℝ)/168755200)/ClassicalSixthBranch.r = (83351129571417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3550
  · change upperPayment 3551 ≤ upperValue ((point split endpoint 4096 3551+point split endpoint 4096 3552)/2)
    have hp : upperPayment 3551 = (85830984175:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3551+point split endpoint 4096 3552)/2 = (665471777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((665471777:ℝ)/168755200)*ClassicalSixthBranch.v ((665471777:ℝ)/168755200)/ClassicalSixthBranch.r = (83332299734225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3551
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_221
