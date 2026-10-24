import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints044
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_044 (j : Fin 16) : upperPayment (16*44+j.val) ≤
    upperValue ((point split endpoint 4096 (16*44+j.val)+point split endpoint 4096 (16*44+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 704 ≤ upperValue ((point split endpoint 4096 704+point split endpoint 4096 705)/2)
    have hp : upperPayment 704 = (381306053284:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 704+point split endpoint 4096 705)/2 = (593869727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((593869727:ℝ)/168755200)*ClassicalSixthBranch.v ((593869727:ℝ)/168755200)/ClassicalSixthBranch.r = (145140930656081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_704
  · change upperPayment 705 ≤ upperValue ((point split endpoint 4096 705+point split endpoint 4096 706)/2)
    have hp : upperPayment 705 = (381237827250:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 705+point split endpoint 4096 706)/2 = (593894877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((593894877:ℝ)/168755200)*ClassicalSixthBranch.v ((593894877:ℝ)/168755200)/ClassicalSixthBranch.r = (145116340309977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_705
  · change upperPayment 706 ≤ upperValue ((point split endpoint 4096 706+point split endpoint 4096 707)/2)
    have hp : upperPayment 706 = (381169580183:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 706+point split endpoint 4096 707)/2 = (593920027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((593920027:ℝ)/168755200)*ClassicalSixthBranch.v ((593920027:ℝ)/168755200)/ClassicalSixthBranch.r = (145091751987945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_706
  · change upperPayment 707 ≤ upperValue ((point split endpoint 4096 707+point split endpoint 4096 708)/2)
    have hp : upperPayment 707 = (381101312080:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 707+point split endpoint 4096 708)/2 = (593945177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((593945177:ℝ)/168755200)*ClassicalSixthBranch.v ((593945177:ℝ)/168755200)/ClassicalSixthBranch.r = (145067165689985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_707
  · change upperPayment 708 ≤ upperValue ((point split endpoint 4096 708+point split endpoint 4096 709)/2)
    have hp : upperPayment 708 = (381033022937:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 708+point split endpoint 4096 709)/2 = (593970327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((593970327:ℝ)/168755200)*ClassicalSixthBranch.v ((593970327:ℝ)/168755200)/ClassicalSixthBranch.r = (145042581416097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_708
  · change upperPayment 709 ≤ upperValue ((point split endpoint 4096 709+point split endpoint 4096 710)/2)
    have hp : upperPayment 709 = (380964712752:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 709+point split endpoint 4096 710)/2 = (593995477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((593995477:ℝ)/168755200)*ClassicalSixthBranch.v ((593995477:ℝ)/168755200)/ClassicalSixthBranch.r = (145017999166281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_709
  · change upperPayment 710 ≤ upperValue ((point split endpoint 4096 710+point split endpoint 4096 711)/2)
    have hp : upperPayment 710 = (380896381521:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 710+point split endpoint 4096 711)/2 = (594020627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((594020627:ℝ)/168755200)*ClassicalSixthBranch.v ((594020627:ℝ)/168755200)/ClassicalSixthBranch.r = (144993418940537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_710
  · change upperPayment 711 ≤ upperValue ((point split endpoint 4096 711+point split endpoint 4096 712)/2)
    have hp : upperPayment 711 = (380828029242:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 711+point split endpoint 4096 712)/2 = (594045777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((594045777:ℝ)/168755200)*ClassicalSixthBranch.v ((594045777:ℝ)/168755200)/ClassicalSixthBranch.r = (144968840738865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_711
  · change upperPayment 712 ≤ upperValue ((point split endpoint 4096 712+point split endpoint 4096 713)/2)
    have hp : upperPayment 712 = (380759655912:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 712+point split endpoint 4096 713)/2 = (594070927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((594070927:ℝ)/168755200)*ClassicalSixthBranch.v ((594070927:ℝ)/168755200)/ClassicalSixthBranch.r = (144944264561265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_712
  · change upperPayment 713 ≤ upperValue ((point split endpoint 4096 713+point split endpoint 4096 714)/2)
    have hp : upperPayment 713 = (380691261528:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 713+point split endpoint 4096 714)/2 = (594096077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((594096077:ℝ)/168755200)*ClassicalSixthBranch.v ((594096077:ℝ)/168755200)/ClassicalSixthBranch.r = (144919690407737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_713
  · change upperPayment 714 ≤ upperValue ((point split endpoint 4096 714+point split endpoint 4096 715)/2)
    have hp : upperPayment 714 = (380622846086:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 714+point split endpoint 4096 715)/2 = (594121227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((594121227:ℝ)/168755200)*ClassicalSixthBranch.v ((594121227:ℝ)/168755200)/ClassicalSixthBranch.r = (144895118278281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_714
  · change upperPayment 715 ≤ upperValue ((point split endpoint 4096 715+point split endpoint 4096 716)/2)
    have hp : upperPayment 715 = (380554409583:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 715+point split endpoint 4096 716)/2 = (594146377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((594146377:ℝ)/168755200)*ClassicalSixthBranch.v ((594146377:ℝ)/168755200)/ClassicalSixthBranch.r = (144870548172897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_715
  · change upperPayment 716 ≤ upperValue ((point split endpoint 4096 716+point split endpoint 4096 717)/2)
    have hp : upperPayment 716 = (380485952018:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 716+point split endpoint 4096 717)/2 = (594171527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((594171527:ℝ)/168755200)*ClassicalSixthBranch.v ((594171527:ℝ)/168755200)/ClassicalSixthBranch.r = (144845980091585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_716
  · change upperPayment 717 ≤ upperValue ((point split endpoint 4096 717+point split endpoint 4096 718)/2)
    have hp : upperPayment 717 = (380417473386:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 717+point split endpoint 4096 718)/2 = (594196677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((594196677:ℝ)/168755200)*ClassicalSixthBranch.v ((594196677:ℝ)/168755200)/ClassicalSixthBranch.r = (144821414034345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_717
  · change upperPayment 718 ≤ upperValue ((point split endpoint 4096 718+point split endpoint 4096 719)/2)
    have hp : upperPayment 718 = (380348973684:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 718+point split endpoint 4096 719)/2 = (594221827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((594221827:ℝ)/168755200)*ClassicalSixthBranch.v ((594221827:ℝ)/168755200)/ClassicalSixthBranch.r = (144796850001177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_718
  · change upperPayment 719 ≤ upperValue ((point split endpoint 4096 719+point split endpoint 4096 720)/2)
    have hp : upperPayment 719 = (380280452910:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 719+point split endpoint 4096 720)/2 = (594246977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((594246977:ℝ)/168755200)*ClassicalSixthBranch.v ((594246977:ℝ)/168755200)/ClassicalSixthBranch.r = (144772287992081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_719
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_044
