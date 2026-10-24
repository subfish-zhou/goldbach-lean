import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints107
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_107 (j : Fin 16) : lowerPayment (16*107+j.val) ≤
    lowerValue ((point 2 split 4096 (16*107+j.val)+point 2 split 4096 (16*107+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1712 ≤ lowerValue ((point 2 split 4096 1712+point 2 split 4096 1713)/2)
    have hp : lowerPayment 1712 = (205992827304:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1712+point 2 split 4096 1713)/2 = (17491363:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((17491363:ℝ)/6750208)/ClassicalSixthBranch.v ((17491363:ℝ)/6750208) = (681615509979:ℝ)/338364951448 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1712
  · change lowerPayment 1713 ≤ lowerValue ((point 2 split 4096 1713+point 2 split 4096 1714)/2)
    have hp : lowerPayment 1713 = (206087547642:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1713+point 2 split 4096 1714)/2 = (437342337:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((437342337:ℝ)/168755200)/ClassicalSixthBranch.v ((437342337:ℝ)/168755200) = (136307639261:ℝ)/67663388712 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1713
  · change lowerPayment 1714 ≤ lowerValue ((point 2 split 4096 1714+point 2 split 4096 1715)/2)
    have hp : lowerPayment 1714 = (206182252699:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1714+point 2 split 4096 1715)/2 = (437400599:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((437400599:ℝ)/168755200)/ClassicalSixthBranch.v ((437400599:ℝ)/168755200) = (681460882631:ℝ)/338268935672 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1714
  · change lowerPayment 1715 ≤ lowerValue ((point 2 split 4096 1715+point 2 split 4096 1716)/2)
    have hp : lowerPayment 1715 = (206276942492:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1715+point 2 split 4096 1716)/2 = (437458861:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((437458861:ℝ)/168755200)/ClassicalSixthBranch.v ((437458861:ℝ)/168755200) = (681383568957:ℝ)/338220927784 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1715
  · change lowerPayment 1716 ≤ lowerValue ((point 2 split 4096 1716+point 2 split 4096 1717)/2)
    have hp : lowerPayment 1716 = (206371617040:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1716+point 2 split 4096 1717)/2 = (437517123:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((437517123:ℝ)/168755200)/ClassicalSixthBranch.v ((437517123:ℝ)/168755200) = (681306255283:ℝ)/338172919896 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1716
  · change lowerPayment 1717 ≤ lowerValue ((point 2 split 4096 1717+point 2 split 4096 1718)/2)
    have hp : lowerPayment 1717 = (206466276364:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1717+point 2 split 4096 1718)/2 = (87515077:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((87515077:ℝ)/33751040)/ClassicalSixthBranch.v ((87515077:ℝ)/33751040) = (681228941609:ℝ)/338124912008 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1717
  · change lowerPayment 1718 ≤ lowerValue ((point 2 split 4096 1718+point 2 split 4096 1719)/2)
    have hp : lowerPayment 1718 = (206560920481:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1718+point 2 split 4096 1719)/2 = (437633647:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((437633647:ℝ)/168755200)/ClassicalSixthBranch.v ((437633647:ℝ)/168755200) = (136230325587:ℝ)/67615380824 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1718
  · change lowerPayment 1719 ≤ lowerValue ((point 2 split 4096 1719+point 2 split 4096 1720)/2)
    have hp : lowerPayment 1719 = (206655549411:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1719+point 2 split 4096 1720)/2 = (437691909:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((437691909:ℝ)/168755200)/ClassicalSixthBranch.v ((437691909:ℝ)/168755200) = (681074314261:ℝ)/338028896232 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1719
  · change lowerPayment 1720 ≤ lowerValue ((point 2 split 4096 1720+point 2 split 4096 1721)/2)
    have hp : lowerPayment 1720 = (206750163172:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1720+point 2 split 4096 1721)/2 = (437750171:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((437750171:ℝ)/168755200)/ClassicalSixthBranch.v ((437750171:ℝ)/168755200) = (680997000587:ℝ)/337980888344 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1720
  · change lowerPayment 1721 ≤ lowerValue ((point 2 split 4096 1721+point 2 split 4096 1722)/2)
    have hp : lowerPayment 1721 = (206844761783:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1721+point 2 split 4096 1722)/2 = (437808433:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((437808433:ℝ)/168755200)/ClassicalSixthBranch.v ((437808433:ℝ)/168755200) = (680919686913:ℝ)/337932880456 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1721
  · change lowerPayment 1722 ≤ lowerValue ((point 2 split 4096 1722+point 2 split 4096 1723)/2)
    have hp : lowerPayment 1722 = (206939345264:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1722+point 2 split 4096 1723)/2 = (87573339:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((87573339:ℝ)/33751040)/ClassicalSixthBranch.v ((87573339:ℝ)/33751040) = (680842373239:ℝ)/337884872568 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1722
  · change lowerPayment 1723 ≤ lowerValue ((point 2 split 4096 1723+point 2 split 4096 1724)/2)
    have hp : lowerPayment 1723 = (207033913633:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1723+point 2 split 4096 1724)/2 = (437924957:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((437924957:ℝ)/168755200)/ClassicalSixthBranch.v ((437924957:ℝ)/168755200) = (136153011913:ℝ)/67567372936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1723
  · change lowerPayment 1724 ≤ lowerValue ((point 2 split 4096 1724+point 2 split 4096 1725)/2)
    have hp : lowerPayment 1724 = (207128466910:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1724+point 2 split 4096 1725)/2 = (437983219:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((437983219:ℝ)/168755200)/ClassicalSixthBranch.v ((437983219:ℝ)/168755200) = (680687745891:ℝ)/337788856792 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1724
  · change lowerPayment 1725 ≤ lowerValue ((point 2 split 4096 1725+point 2 split 4096 1726)/2)
    have hp : lowerPayment 1725 = (207223005112:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1725+point 2 split 4096 1726)/2 = (438041481:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((438041481:ℝ)/168755200)/ClassicalSixthBranch.v ((438041481:ℝ)/168755200) = (680610432217:ℝ)/337740848904 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1725
  · change lowerPayment 1726 ≤ lowerValue ((point 2 split 4096 1726+point 2 split 4096 1727)/2)
    have hp : lowerPayment 1726 = (207317528259:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1726+point 2 split 4096 1727)/2 = (438099743:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((438099743:ℝ)/168755200)/ClassicalSixthBranch.v ((438099743:ℝ)/168755200) = (680533118543:ℝ)/337692841016 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1726
  · change lowerPayment 1727 ≤ lowerValue ((point 2 split 4096 1727+point 2 split 4096 1728)/2)
    have hp : lowerPayment 1727 = (207412036370:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1727+point 2 split 4096 1728)/2 = (87631601:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((87631601:ℝ)/33751040)/ClassicalSixthBranch.v ((87631601:ℝ)/33751040) = (680455804869:ℝ)/337644833128 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1727
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_107
