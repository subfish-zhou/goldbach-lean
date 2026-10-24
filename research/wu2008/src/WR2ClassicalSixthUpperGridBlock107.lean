import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints107
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_107 (j : Fin 16) : upperPayment (16*107+j.val) ≤
    upperValue ((point split endpoint 4096 (16*107+j.val)+point split endpoint 4096 (16*107+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1712 ≤ upperValue ((point split endpoint 4096 1712+point split endpoint 4096 1713)/2)
    have hp : upperPayment 1712 = (301288001155:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1712+point split endpoint 4096 1713)/2 = (619220927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((619220927:ℝ)/168755200)*ClassicalSixthBranch.v ((619220927:ℝ)/168755200)/ClassicalSixthBranch.r = (121381134997265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1712
  · change upperPayment 1713 ≤ upperValue ((point split endpoint 4096 1713+point split endpoint 4096 1714)/2)
    have hp : upperPayment 1713 = (301196804099:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1713+point split endpoint 4096 1714)/2 = (619246077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((619246077:ℝ)/168755200)*ClassicalSixthBranch.v ((619246077:ℝ)/168755200)/ClassicalSixthBranch.r = (121358584915737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1713
  · change upperPayment 1714 ≤ upperValue ((point split endpoint 4096 1714+point split endpoint 4096 1715)/2)
    have hp : upperPayment 1714 = (301105582224:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1714+point split endpoint 4096 1715)/2 = (619271227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((619271227:ℝ)/168755200)*ClassicalSixthBranch.v ((619271227:ℝ)/168755200)/ClassicalSixthBranch.r = (121336036858281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1714
  · change upperPayment 1715 ≤ upperValue ((point split endpoint 4096 1715+point split endpoint 4096 1716)/2)
    have hp : upperPayment 1715 = (301014335526:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1715+point split endpoint 4096 1716)/2 = (619296377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((619296377:ℝ)/168755200)*ClassicalSixthBranch.v ((619296377:ℝ)/168755200)/ClassicalSixthBranch.r = (121313490824897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1715
  · change upperPayment 1716 ≤ upperValue ((point split endpoint 4096 1716+point split endpoint 4096 1717)/2)
    have hp : upperPayment 1716 = (300923064000:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1716+point split endpoint 4096 1717)/2 = (619321527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((619321527:ℝ)/168755200)*ClassicalSixthBranch.v ((619321527:ℝ)/168755200)/ClassicalSixthBranch.r = (121290946815585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1716
  · change upperPayment 1717 ≤ upperValue ((point split endpoint 4096 1717+point split endpoint 4096 1718)/2)
    have hp : upperPayment 1717 = (300831767641:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1717+point split endpoint 4096 1718)/2 = (619346677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((619346677:ℝ)/168755200)*ClassicalSixthBranch.v ((619346677:ℝ)/168755200)/ClassicalSixthBranch.r = (121268404830345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1717
  · change upperPayment 1718 ≤ upperValue ((point split endpoint 4096 1718+point split endpoint 4096 1719)/2)
    have hp : upperPayment 1718 = (300740446446:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1718+point split endpoint 4096 1719)/2 = (619371827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((619371827:ℝ)/168755200)*ClassicalSixthBranch.v ((619371827:ℝ)/168755200)/ClassicalSixthBranch.r = (121245864869177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1718
  · change upperPayment 1719 ≤ upperValue ((point split endpoint 4096 1719+point split endpoint 4096 1720)/2)
    have hp : upperPayment 1719 = (300649100409:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1719+point split endpoint 4096 1720)/2 = (619396977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((619396977:ℝ)/168755200)*ClassicalSixthBranch.v ((619396977:ℝ)/168755200)/ClassicalSixthBranch.r = (121223326932081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1719
  · change upperPayment 1720 ≤ upperValue ((point split endpoint 4096 1720+point split endpoint 4096 1721)/2)
    have hp : upperPayment 1720 = (300557729526:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1720+point split endpoint 4096 1721)/2 = (619422127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((619422127:ℝ)/168755200)*ClassicalSixthBranch.v ((619422127:ℝ)/168755200)/ClassicalSixthBranch.r = (121200791019057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1720
  · change upperPayment 1721 ≤ upperValue ((point split endpoint 4096 1721+point split endpoint 4096 1722)/2)
    have hp : upperPayment 1721 = (300466333793:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1721+point split endpoint 4096 1722)/2 = (619447277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((619447277:ℝ)/168755200)*ClassicalSixthBranch.v ((619447277:ℝ)/168755200)/ClassicalSixthBranch.r = (121178257130105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1721
  · change upperPayment 1722 ≤ upperValue ((point split endpoint 4096 1722+point split endpoint 4096 1723)/2)
    have hp : upperPayment 1722 = (300374913203:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1722+point split endpoint 4096 1723)/2 = (619472427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((619472427:ℝ)/168755200)*ClassicalSixthBranch.v ((619472427:ℝ)/168755200)/ClassicalSixthBranch.r = (121155725265225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1722
  · change upperPayment 1723 ≤ upperValue ((point split endpoint 4096 1723+point split endpoint 4096 1724)/2)
    have hp : upperPayment 1723 = (300283467754:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1723+point split endpoint 4096 1724)/2 = (619497577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((619497577:ℝ)/168755200)*ClassicalSixthBranch.v ((619497577:ℝ)/168755200)/ClassicalSixthBranch.r = (121133195424417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1723
  · change upperPayment 1724 ≤ upperValue ((point split endpoint 4096 1724+point split endpoint 4096 1725)/2)
    have hp : upperPayment 1724 = (300191997440:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1724+point split endpoint 4096 1725)/2 = (619522727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((619522727:ℝ)/168755200)*ClassicalSixthBranch.v ((619522727:ℝ)/168755200)/ClassicalSixthBranch.r = (121110667607681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1724
  · change upperPayment 1725 ≤ upperValue ((point split endpoint 4096 1725+point split endpoint 4096 1726)/2)
    have hp : upperPayment 1725 = (300100502257:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1725+point split endpoint 4096 1726)/2 = (619547877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((619547877:ℝ)/168755200)*ClassicalSixthBranch.v ((619547877:ℝ)/168755200)/ClassicalSixthBranch.r = (121088141815017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1725
  · change upperPayment 1726 ≤ upperValue ((point split endpoint 4096 1726+point split endpoint 4096 1727)/2)
    have hp : upperPayment 1726 = (300008982199:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1726+point split endpoint 4096 1727)/2 = (619573027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((619573027:ℝ)/168755200)*ClassicalSixthBranch.v ((619573027:ℝ)/168755200)/ClassicalSixthBranch.r = (121065618046425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1726
  · change upperPayment 1727 ≤ upperValue ((point split endpoint 4096 1727+point split endpoint 4096 1728)/2)
    have hp : upperPayment 1727 = (299917437264:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1727+point split endpoint 4096 1728)/2 = (619598177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((619598177:ℝ)/168755200)*ClassicalSixthBranch.v ((619598177:ℝ)/168755200)/ClassicalSixthBranch.r = (121043096301905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1727
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_107
