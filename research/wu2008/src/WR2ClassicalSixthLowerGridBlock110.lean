import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints110
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_110 (j : Fin 16) : lowerPayment (16*110+j.val) ≤
    lowerValue ((point 2 split 4096 (16*110+j.val)+point 2 split 4096 (16*110+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1760 ≤ lowerValue ((point 2 split 4096 1760+point 2 split 4096 1761)/2)
    have hp : lowerPayment 1760 = (210522491630:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1760+point 2 split 4096 1761)/2 = (440080651:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((440080651:ℝ)/168755200)/ClassicalSixthBranch.v ((440080651:ℝ)/168755200) = (677904453627:ℝ)/336060572824 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1760
  · change lowerPayment 1761 ≤ lowerValue ((point 2 split 4096 1761+point 2 split 4096 1762)/2)
    have hp : lowerPayment 1761 = (210616499668:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1761+point 2 split 4096 1762)/2 = (440138913:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((440138913:ℝ)/168755200)/ClassicalSixthBranch.v ((440138913:ℝ)/168755200) = (677827139953:ℝ)/336012564936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1761
  · change lowerPayment 1762 ≤ lowerValue ((point 2 split 4096 1762+point 2 split 4096 1763)/2)
    have hp : lowerPayment 1762 = (210710493324:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1762+point 2 split 4096 1763)/2 = (17607887:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((17607887:ℝ)/6750208)/ClassicalSixthBranch.v ((17607887:ℝ)/6750208) = (677749826279:ℝ)/335964557048 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1762
  · change lowerPayment 1763 ≤ lowerValue ((point 2 split 4096 1763+point 2 split 4096 1764)/2)
    have hp : lowerPayment 1763 = (210804472617:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1763+point 2 split 4096 1764)/2 = (440255437:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((440255437:ℝ)/168755200)/ClassicalSixthBranch.v ((440255437:ℝ)/168755200) = (135534502521:ℝ)/67183309832 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1763
  · change lowerPayment 1764 ≤ lowerValue ((point 2 split 4096 1764+point 2 split 4096 1765)/2)
    have hp : lowerPayment 1764 = (210898437565:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1764+point 2 split 4096 1765)/2 = (440313699:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((440313699:ℝ)/168755200)/ClassicalSixthBranch.v ((440313699:ℝ)/168755200) = (677595198931:ℝ)/335868541272 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1764
  · change lowerPayment 1765 ≤ lowerValue ((point 2 split 4096 1765+point 2 split 4096 1766)/2)
    have hp : lowerPayment 1765 = (210992388187:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1765+point 2 split 4096 1766)/2 = (440371961:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((440371961:ℝ)/168755200)/ClassicalSixthBranch.v ((440371961:ℝ)/168755200) = (677517885257:ℝ)/335820533384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1765
  · change lowerPayment 1766 ≤ lowerValue ((point 2 split 4096 1766+point 2 split 4096 1767)/2)
    have hp : lowerPayment 1766 = (211086324501:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1766+point 2 split 4096 1767)/2 = (440430223:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((440430223:ℝ)/168755200)/ClassicalSixthBranch.v ((440430223:ℝ)/168755200) = (677440571583:ℝ)/335772525496 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1766
  · change lowerPayment 1767 ≤ lowerValue ((point 2 split 4096 1767+point 2 split 4096 1768)/2)
    have hp : lowerPayment 1767 = (211180246526:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1767+point 2 split 4096 1768)/2 = (88097697:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((88097697:ℝ)/33751040)/ClassicalSixthBranch.v ((88097697:ℝ)/33751040) = (677363257909:ℝ)/335724517608 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1767
  · change lowerPayment 1768 ≤ lowerValue ((point 2 split 4096 1768+point 2 split 4096 1769)/2)
    have hp : lowerPayment 1768 = (211274154281:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1768+point 2 split 4096 1769)/2 = (440546747:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((440546747:ℝ)/168755200)/ClassicalSixthBranch.v ((440546747:ℝ)/168755200) = (135457188847:ℝ)/67135301944 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1768
  · change lowerPayment 1769 ≤ lowerValue ((point 2 split 4096 1769+point 2 split 4096 1770)/2)
    have hp : lowerPayment 1769 = (211368047783:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1769+point 2 split 4096 1770)/2 = (440605009:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((440605009:ℝ)/168755200)/ClassicalSixthBranch.v ((440605009:ℝ)/168755200) = (677208630561:ℝ)/335628501832 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1769
  · change lowerPayment 1770 ≤ lowerValue ((point 2 split 4096 1770+point 2 split 4096 1771)/2)
    have hp : lowerPayment 1770 = (211461927052:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1770+point 2 split 4096 1771)/2 = (440663271:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((440663271:ℝ)/168755200)/ClassicalSixthBranch.v ((440663271:ℝ)/168755200) = (677131316887:ℝ)/335580493944 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1770
  · change lowerPayment 1771 ≤ lowerValue ((point 2 split 4096 1771+point 2 split 4096 1772)/2)
    have hp : lowerPayment 1771 = (211555792105:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1771+point 2 split 4096 1772)/2 = (440721533:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((440721533:ℝ)/168755200)/ClassicalSixthBranch.v ((440721533:ℝ)/168755200) = (677054003213:ℝ)/335532486056 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1771
  · change lowerPayment 1772 ≤ lowerValue ((point 2 split 4096 1772+point 2 split 4096 1773)/2)
    have hp : lowerPayment 1772 = (211649642962:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1772+point 2 split 4096 1773)/2 = (88155959:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((88155959:ℝ)/33751040)/ClassicalSixthBranch.v ((88155959:ℝ)/33751040) = (676976689539:ℝ)/335484478168 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1772
  · change lowerPayment 1773 ≤ lowerValue ((point 2 split 4096 1773+point 2 split 4096 1774)/2)
    have hp : lowerPayment 1773 = (211743479640:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1773+point 2 split 4096 1774)/2 = (440838057:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((440838057:ℝ)/168755200)/ClassicalSixthBranch.v ((440838057:ℝ)/168755200) = (135379875173:ℝ)/67087294056 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1773
  · change lowerPayment 1774 ≤ lowerValue ((point 2 split 4096 1774+point 2 split 4096 1775)/2)
    have hp : lowerPayment 1774 = (211837302159:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1774+point 2 split 4096 1775)/2 = (440896319:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((440896319:ℝ)/168755200)/ClassicalSixthBranch.v ((440896319:ℝ)/168755200) = (676822062191:ℝ)/335388462392 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1774
  · change lowerPayment 1775 ≤ lowerValue ((point 2 split 4096 1775+point 2 split 4096 1776)/2)
    have hp : lowerPayment 1775 = (211931110536:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1775+point 2 split 4096 1776)/2 = (440954581:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((440954581:ℝ)/168755200)/ClassicalSixthBranch.v ((440954581:ℝ)/168755200) = (676744748517:ℝ)/335340454504 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1775
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_110
