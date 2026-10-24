import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints031
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_031 (j : Fin 16) : upperPayment (16*31+j.val) ≤
    upperValue ((point split endpoint 4096 (16*31+j.val)+point split endpoint 4096 (16*31+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 496 ≤ upperValue ((point split endpoint 4096 496+point split endpoint 4096 497)/2)
    have hp : upperPayment 496 = (395044327154:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 496+point split endpoint 4096 497)/2 = (588638527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((588638527:ℝ)/168755200)*ClassicalSixthBranch.v ((588638527:ℝ)/168755200)/ClassicalSixthBranch.r = (150299717874705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_496
  · change upperPayment 497 ≤ upperValue ((point split endpoint 4096 497+point split endpoint 4096 498)/2)
    have hp : upperPayment 497 = (394980413130:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 497+point split endpoint 4096 498)/2 = (588663677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((588663677:ℝ)/168755200)*ClassicalSixthBranch.v ((588663677:ℝ)/168755200)/ClassicalSixthBranch.r = (150274706521625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_497
  · change upperPayment 498 ≤ upperValue ((point split endpoint 4096 498+point split endpoint 4096 499)/2)
    have hp : upperPayment 498 = (394916478665:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 498+point split endpoint 4096 499)/2 = (588688827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((588688827:ℝ)/168755200)*ClassicalSixthBranch.v ((588688827:ℝ)/168755200)/ClassicalSixthBranch.r = (150249697192617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_498
  · change upperPayment 499 ≤ upperValue ((point split endpoint 4096 499+point split endpoint 4096 500)/2)
    have hp : upperPayment 499 = (394852523757:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 499+point split endpoint 4096 500)/2 = (588713977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((588713977:ℝ)/168755200)*ClassicalSixthBranch.v ((588713977:ℝ)/168755200)/ClassicalSixthBranch.r = (150224689887681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_499
  · change upperPayment 500 ≤ upperValue ((point split endpoint 4096 500+point split endpoint 4096 501)/2)
    have hp : upperPayment 500 = (394788548403:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 500+point split endpoint 4096 501)/2 = (588739127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((588739127:ℝ)/168755200)*ClassicalSixthBranch.v ((588739127:ℝ)/168755200)/ClassicalSixthBranch.r = (150199684606817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_500
  · change upperPayment 501 ≤ upperValue ((point split endpoint 4096 501+point split endpoint 4096 502)/2)
    have hp : upperPayment 501 = (394724552600:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 501+point split endpoint 4096 502)/2 = (588764277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((588764277:ℝ)/168755200)*ClassicalSixthBranch.v ((588764277:ℝ)/168755200)/ClassicalSixthBranch.r = (150174681350025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_501
  · change upperPayment 502 ≤ upperValue ((point split endpoint 4096 502+point split endpoint 4096 503)/2)
    have hp : upperPayment 502 = (394660536346:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 502+point split endpoint 4096 503)/2 = (588789427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((588789427:ℝ)/168755200)*ClassicalSixthBranch.v ((588789427:ℝ)/168755200)/ClassicalSixthBranch.r = (150149680117305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_502
  · change upperPayment 503 ≤ upperValue ((point split endpoint 4096 503+point split endpoint 4096 504)/2)
    have hp : upperPayment 503 = (394596499637:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 503+point split endpoint 4096 504)/2 = (588814577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((588814577:ℝ)/168755200)*ClassicalSixthBranch.v ((588814577:ℝ)/168755200)/ClassicalSixthBranch.r = (150124680908657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_503
  · change upperPayment 504 ≤ upperValue ((point split endpoint 4096 504+point split endpoint 4096 505)/2)
    have hp : upperPayment 504 = (394532442471:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 504+point split endpoint 4096 505)/2 = (588839727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((588839727:ℝ)/168755200)*ClassicalSixthBranch.v ((588839727:ℝ)/168755200)/ClassicalSixthBranch.r = (150099683724081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_504
  · change upperPayment 505 ≤ upperValue ((point split endpoint 4096 505+point split endpoint 4096 506)/2)
    have hp : upperPayment 505 = (394468364846:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 505+point split endpoint 4096 506)/2 = (588864877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((588864877:ℝ)/168755200)*ClassicalSixthBranch.v ((588864877:ℝ)/168755200)/ClassicalSixthBranch.r = (150074688563577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_505
  · change upperPayment 506 ≤ upperValue ((point split endpoint 4096 506+point split endpoint 4096 507)/2)
    have hp : upperPayment 506 = (394404266758:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 506+point split endpoint 4096 507)/2 = (588890027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((588890027:ℝ)/168755200)*ClassicalSixthBranch.v ((588890027:ℝ)/168755200)/ClassicalSixthBranch.r = (150049695427145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_506
  · change upperPayment 507 ≤ upperValue ((point split endpoint 4096 507+point split endpoint 4096 508)/2)
    have hp : upperPayment 507 = (394340148205:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 507+point split endpoint 4096 508)/2 = (588915177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((588915177:ℝ)/168755200)*ClassicalSixthBranch.v ((588915177:ℝ)/168755200)/ClassicalSixthBranch.r = (150024704314785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_507
  · change upperPayment 508 ≤ upperValue ((point split endpoint 4096 508+point split endpoint 4096 509)/2)
    have hp : upperPayment 508 = (394276009184:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 508+point split endpoint 4096 509)/2 = (588940327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((588940327:ℝ)/168755200)*ClassicalSixthBranch.v ((588940327:ℝ)/168755200)/ClassicalSixthBranch.r = (149999715226497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_508
  · change upperPayment 509 ≤ upperValue ((point split endpoint 4096 509+point split endpoint 4096 510)/2)
    have hp : upperPayment 509 = (394211849692:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 509+point split endpoint 4096 510)/2 = (588965477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((588965477:ℝ)/168755200)*ClassicalSixthBranch.v ((588965477:ℝ)/168755200)/ClassicalSixthBranch.r = (149974728162281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_509
  · change upperPayment 510 ≤ upperValue ((point split endpoint 4096 510+point split endpoint 4096 511)/2)
    have hp : upperPayment 510 = (394147669727:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 510+point split endpoint 4096 511)/2 = (588990627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((588990627:ℝ)/168755200)*ClassicalSixthBranch.v ((588990627:ℝ)/168755200)/ClassicalSixthBranch.r = (149949743122137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_510
  · change upperPayment 511 ≤ upperValue ((point split endpoint 4096 511+point split endpoint 4096 512)/2)
    have hp : upperPayment 511 = (394083469286:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 511+point split endpoint 4096 512)/2 = (589015777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((589015777:ℝ)/168755200)*ClassicalSixthBranch.v ((589015777:ℝ)/168755200)/ClassicalSixthBranch.r = (149924760106065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_511
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_031
