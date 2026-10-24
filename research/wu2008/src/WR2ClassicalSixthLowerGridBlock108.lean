import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints108
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_108 (j : Fin 16) : lowerPayment (16*108+j.val) ≤
    lowerValue ((point 2 split 4096 (16*108+j.val)+point 2 split 4096 (16*108+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1728 ≤ lowerValue ((point 2 split 4096 1728+point 2 split 4096 1729)/2)
    have hp : lowerPayment 1728 = (207506529464:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1728+point 2 split 4096 1729)/2 = (438216267:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((438216267:ℝ)/168755200)/ClassicalSixthBranch.v ((438216267:ℝ)/168755200) = (136075698239:ℝ)/67519365048 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1728
  · change lowerPayment 1729 ≤ lowerValue ((point 2 split 4096 1729+point 2 split 4096 1730)/2)
    have hp : lowerPayment 1729 = (207601007559:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1729+point 2 split 4096 1730)/2 = (438274529:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((438274529:ℝ)/168755200)/ClassicalSixthBranch.v ((438274529:ℝ)/168755200) = (680301177521:ℝ)/337548817352 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1729
  · change lowerPayment 1730 ≤ lowerValue ((point 2 split 4096 1730+point 2 split 4096 1731)/2)
    have hp : lowerPayment 1730 = (207695470674:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1730+point 2 split 4096 1731)/2 = (438332791:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((438332791:ℝ)/168755200)/ClassicalSixthBranch.v ((438332791:ℝ)/168755200) = (680223863847:ℝ)/337500809464 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1730
  · change lowerPayment 1731 ≤ lowerValue ((point 2 split 4096 1731+point 2 split 4096 1732)/2)
    have hp : lowerPayment 1731 = (207789918829:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1731+point 2 split 4096 1732)/2 = (438391053:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((438391053:ℝ)/168755200)/ClassicalSixthBranch.v ((438391053:ℝ)/168755200) = (680146550173:ℝ)/337452801576 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1731
  · change lowerPayment 1732 ≤ lowerValue ((point 2 split 4096 1732+point 2 split 4096 1733)/2)
    have hp : lowerPayment 1732 = (207884352041:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1732+point 2 split 4096 1733)/2 = (87689863:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((87689863:ℝ)/33751040)/ClassicalSixthBranch.v ((87689863:ℝ)/33751040) = (680069236499:ℝ)/337404793688 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1732
  · change lowerPayment 1733 ≤ lowerValue ((point 2 split 4096 1733+point 2 split 4096 1734)/2)
    have hp : lowerPayment 1733 = (207978770330:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1733+point 2 split 4096 1734)/2 = (438507577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((438507577:ℝ)/168755200)/ClassicalSixthBranch.v ((438507577:ℝ)/168755200) = (27199676913:ℝ)/13494271432 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1733
  · change lowerPayment 1734 ≤ lowerValue ((point 2 split 4096 1734+point 2 split 4096 1735)/2)
    have hp : lowerPayment 1734 = (208073173715:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1734+point 2 split 4096 1735)/2 = (438565839:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((438565839:ℝ)/168755200)/ClassicalSixthBranch.v ((438565839:ℝ)/168755200) = (679914609151:ℝ)/337308777912 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1734
  · change lowerPayment 1735 ≤ lowerValue ((point 2 split 4096 1735+point 2 split 4096 1736)/2)
    have hp : lowerPayment 1735 = (208167562214:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1735+point 2 split 4096 1736)/2 = (438624101:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((438624101:ℝ)/168755200)/ClassicalSixthBranch.v ((438624101:ℝ)/168755200) = (679837295477:ℝ)/337260770024 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1735
  · change lowerPayment 1736 ≤ lowerValue ((point 2 split 4096 1736+point 2 split 4096 1737)/2)
    have hp : lowerPayment 1736 = (208261935846:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1736+point 2 split 4096 1737)/2 = (438682363:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((438682363:ℝ)/168755200)/ClassicalSixthBranch.v ((438682363:ℝ)/168755200) = (679759981803:ℝ)/337212762136 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1736
  · change lowerPayment 1737 ≤ lowerValue ((point 2 split 4096 1737+point 2 split 4096 1738)/2)
    have hp : lowerPayment 1737 = (208356294630:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1737+point 2 split 4096 1738)/2 = (17549625:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((17549625:ℝ)/6750208)/ClassicalSixthBranch.v ((17549625:ℝ)/6750208) = (679682668129:ℝ)/337164754248 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1737
  · change lowerPayment 1738 ≤ lowerValue ((point 2 split 4096 1738+point 2 split 4096 1739)/2)
    have hp : lowerPayment 1738 = (208450638585:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1738+point 2 split 4096 1739)/2 = (438798887:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((438798887:ℝ)/168755200)/ClassicalSixthBranch.v ((438798887:ℝ)/168755200) = (135921070891:ℝ)/67423349272 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1738
  · change lowerPayment 1739 ≤ lowerValue ((point 2 split 4096 1739+point 2 split 4096 1740)/2)
    have hp : lowerPayment 1739 = (208544967729:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1739+point 2 split 4096 1740)/2 = (438857149:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((438857149:ℝ)/168755200)/ClassicalSixthBranch.v ((438857149:ℝ)/168755200) = (679528040781:ℝ)/337068738472 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1739
  · change lowerPayment 1740 ≤ lowerValue ((point 2 split 4096 1740+point 2 split 4096 1741)/2)
    have hp : lowerPayment 1740 = (208639282082:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1740+point 2 split 4096 1741)/2 = (438915411:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((438915411:ℝ)/168755200)/ClassicalSixthBranch.v ((438915411:ℝ)/168755200) = (679450727107:ℝ)/337020730584 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1740
  · change lowerPayment 1741 ≤ lowerValue ((point 2 split 4096 1741+point 2 split 4096 1742)/2)
    have hp : lowerPayment 1741 = (208733581661:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1741+point 2 split 4096 1742)/2 = (438973673:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((438973673:ℝ)/168755200)/ClassicalSixthBranch.v ((438973673:ℝ)/168755200) = (679373413433:ℝ)/336972722696 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1741
  · change lowerPayment 1742 ≤ lowerValue ((point 2 split 4096 1742+point 2 split 4096 1743)/2)
    have hp : lowerPayment 1742 = (208827866486:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1742+point 2 split 4096 1743)/2 = (87806387:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((87806387:ℝ)/33751040)/ClassicalSixthBranch.v ((87806387:ℝ)/33751040) = (679296099759:ℝ)/336924714808 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1742
  · change lowerPayment 1743 ≤ lowerValue ((point 2 split 4096 1743+point 2 split 4096 1744)/2)
    have hp : lowerPayment 1743 = (208922136575:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1743+point 2 split 4096 1744)/2 = (439090197:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((439090197:ℝ)/168755200)/ClassicalSixthBranch.v ((439090197:ℝ)/168755200) = (135843757217:ℝ)/67375341384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1743
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_108
