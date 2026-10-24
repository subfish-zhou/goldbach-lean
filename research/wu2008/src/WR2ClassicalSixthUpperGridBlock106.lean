import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints106
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_106 (j : Fin 16) : upperPayment (16*106+j.val) ≤
    upperValue ((point split endpoint 4096 (16*106+j.val)+point split endpoint 4096 (16*106+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1696 ≤ upperValue ((point split endpoint 4096 1696+point split endpoint 4096 1697)/2)
    have hp : upperPayment 1696 = (302743782489:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1696+point split endpoint 4096 1697)/2 = (618818527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((618818527:ℝ)/168755200)*ClassicalSixthBranch.v ((618818527:ℝ)/168755200)/ClassicalSixthBranch.r = (121742211575505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1696
  · change upperPayment 1697 ≤ upperValue ((point split endpoint 4096 1697+point split endpoint 4096 1698)/2)
    have hp : upperPayment 1697 = (302652981904:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1697+point split endpoint 4096 1698)/2 = (618843677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((618843677:ℝ)/168755200)*ClassicalSixthBranch.v ((618843677:ℝ)/168755200)/ClassicalSixthBranch.r = (121719629108825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1697
  · change upperPayment 1698 ≤ upperValue ((point split endpoint 4096 1698+point split endpoint 4096 1699)/2)
    have hp : upperPayment 1698 = (302562156574:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1698+point split endpoint 4096 1699)/2 = (618868827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((618868827:ℝ)/168755200)*ClassicalSixthBranch.v ((618868827:ℝ)/168755200)/ClassicalSixthBranch.r = (121697048666217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1698
  · change upperPayment 1699 ≤ upperValue ((point split endpoint 4096 1699+point split endpoint 4096 1700)/2)
    have hp : upperPayment 1699 = (302471306495:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1699+point split endpoint 4096 1700)/2 = (618893977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((618893977:ℝ)/168755200)*ClassicalSixthBranch.v ((618893977:ℝ)/168755200)/ClassicalSixthBranch.r = (121674470247681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1699
  · change upperPayment 1700 ≤ upperValue ((point split endpoint 4096 1700+point split endpoint 4096 1701)/2)
    have hp : upperPayment 1700 = (302380431661:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1700+point split endpoint 4096 1701)/2 = (618919127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((618919127:ℝ)/168755200)*ClassicalSixthBranch.v ((618919127:ℝ)/168755200)/ClassicalSixthBranch.r = (121651893853217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1700
  · change upperPayment 1701 ≤ upperValue ((point split endpoint 4096 1701+point split endpoint 4096 1702)/2)
    have hp : upperPayment 1701 = (302289532068:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1701+point split endpoint 4096 1702)/2 = (618944277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((618944277:ℝ)/168755200)*ClassicalSixthBranch.v ((618944277:ℝ)/168755200)/ClassicalSixthBranch.r = (121629319482825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1701
  · change upperPayment 1702 ≤ upperValue ((point split endpoint 4096 1702+point split endpoint 4096 1703)/2)
    have hp : upperPayment 1702 = (302198607712:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1702+point split endpoint 4096 1703)/2 = (618969427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((618969427:ℝ)/168755200)*ClassicalSixthBranch.v ((618969427:ℝ)/168755200)/ClassicalSixthBranch.r = (121606747136505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1702
  · change upperPayment 1703 ≤ upperValue ((point split endpoint 4096 1703+point split endpoint 4096 1704)/2)
    have hp : upperPayment 1703 = (302107658588:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1703+point split endpoint 4096 1704)/2 = (618994577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((618994577:ℝ)/168755200)*ClassicalSixthBranch.v ((618994577:ℝ)/168755200)/ClassicalSixthBranch.r = (121584176814257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1703
  · change upperPayment 1704 ≤ upperValue ((point split endpoint 4096 1704+point split endpoint 4096 1705)/2)
    have hp : upperPayment 1704 = (302016684692:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1704+point split endpoint 4096 1705)/2 = (619019727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((619019727:ℝ)/168755200)*ClassicalSixthBranch.v ((619019727:ℝ)/168755200)/ClassicalSixthBranch.r = (121561608516081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1704
  · change upperPayment 1705 ≤ upperValue ((point split endpoint 4096 1705+point split endpoint 4096 1706)/2)
    have hp : upperPayment 1705 = (301925686018:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1705+point split endpoint 4096 1706)/2 = (619044877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((619044877:ℝ)/168755200)*ClassicalSixthBranch.v ((619044877:ℝ)/168755200)/ClassicalSixthBranch.r = (121539042241977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1705
  · change upperPayment 1706 ≤ upperValue ((point split endpoint 4096 1706+point split endpoint 4096 1707)/2)
    have hp : upperPayment 1706 = (301834662562:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1706+point split endpoint 4096 1707)/2 = (619070027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((619070027:ℝ)/168755200)*ClassicalSixthBranch.v ((619070027:ℝ)/168755200)/ClassicalSixthBranch.r = (121516477991945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1706
  · change upperPayment 1707 ≤ upperValue ((point split endpoint 4096 1707+point split endpoint 4096 1708)/2)
    have hp : upperPayment 1707 = (301743614320:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1707+point split endpoint 4096 1708)/2 = (619095177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((619095177:ℝ)/168755200)*ClassicalSixthBranch.v ((619095177:ℝ)/168755200)/ClassicalSixthBranch.r = (121493915765985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1707
  · change upperPayment 1708 ≤ upperValue ((point split endpoint 4096 1708+point split endpoint 4096 1709)/2)
    have hp : upperPayment 1708 = (301652541288:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1708+point split endpoint 4096 1709)/2 = (619120327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((619120327:ℝ)/168755200)*ClassicalSixthBranch.v ((619120327:ℝ)/168755200)/ClassicalSixthBranch.r = (121471355564097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1708
  · change upperPayment 1709 ≤ upperValue ((point split endpoint 4096 1709+point split endpoint 4096 1710)/2)
    have hp : upperPayment 1709 = (301561443459:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1709+point split endpoint 4096 1710)/2 = (619145477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((619145477:ℝ)/168755200)*ClassicalSixthBranch.v ((619145477:ℝ)/168755200)/ClassicalSixthBranch.r = (121448797386281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1709
  · change upperPayment 1710 ≤ upperValue ((point split endpoint 4096 1710+point split endpoint 4096 1711)/2)
    have hp : upperPayment 1710 = (301470320831:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1710+point split endpoint 4096 1711)/2 = (619170627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((619170627:ℝ)/168755200)*ClassicalSixthBranch.v ((619170627:ℝ)/168755200)/ClassicalSixthBranch.r = (121426241232537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1710
  · change upperPayment 1711 ≤ upperValue ((point split endpoint 4096 1711+point split endpoint 4096 1712)/2)
    have hp : upperPayment 1711 = (301379173398:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1711+point split endpoint 4096 1712)/2 = (619195777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((619195777:ℝ)/168755200)*ClassicalSixthBranch.v ((619195777:ℝ)/168755200)/ClassicalSixthBranch.r = (121403687102865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1711
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_106
