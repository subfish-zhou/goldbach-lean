import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints109
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_109 (j : Fin 16) : lowerPayment (16*109+j.val) ≤
    lowerValue ((point 2 split 4096 (16*109+j.val)+point 2 split 4096 (16*109+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1744 ≤ lowerValue ((point 2 split 4096 1744+point 2 split 4096 1745)/2)
    have hp : lowerPayment 1744 = (209016391947:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1744+point 2 split 4096 1745)/2 = (439148459:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((439148459:ℝ)/168755200)/ClassicalSixthBranch.v ((439148459:ℝ)/168755200) = (679141472411:ℝ)/336828699032 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1744
  · change lowerPayment 1745 ≤ lowerValue ((point 2 split 4096 1745+point 2 split 4096 1746)/2)
    have hp : lowerPayment 1745 = (209110632621:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1745+point 2 split 4096 1746)/2 = (439206721:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((439206721:ℝ)/168755200)/ClassicalSixthBranch.v ((439206721:ℝ)/168755200) = (679064158737:ℝ)/336780691144 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1745
  · change lowerPayment 1746 ≤ lowerValue ((point 2 split 4096 1746+point 2 split 4096 1747)/2)
    have hp : lowerPayment 1746 = (209204858616:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1746+point 2 split 4096 1747)/2 = (439264983:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((439264983:ℝ)/168755200)/ClassicalSixthBranch.v ((439264983:ℝ)/168755200) = (678986845063:ℝ)/336732683256 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1746
  · change lowerPayment 1747 ≤ lowerValue ((point 2 split 4096 1747+point 2 split 4096 1748)/2)
    have hp : lowerPayment 1747 = (209299069949:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1747+point 2 split 4096 1748)/2 = (87864649:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((87864649:ℝ)/33751040)/ClassicalSixthBranch.v ((87864649:ℝ)/33751040) = (678909531389:ℝ)/336684675368 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1747
  · change lowerPayment 1748 ≤ lowerValue ((point 2 split 4096 1748+point 2 split 4096 1749)/2)
    have hp : lowerPayment 1748 = (209393266641:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1748+point 2 split 4096 1749)/2 = (439381507:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((439381507:ℝ)/168755200)/ClassicalSixthBranch.v ((439381507:ℝ)/168755200) = (135766443543:ℝ)/67327333496 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1748
  · change lowerPayment 1749 ≤ lowerValue ((point 2 split 4096 1749+point 2 split 4096 1750)/2)
    have hp : lowerPayment 1749 = (209487448709:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1749+point 2 split 4096 1750)/2 = (439439769:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((439439769:ℝ)/168755200)/ClassicalSixthBranch.v ((439439769:ℝ)/168755200) = (678754904041:ℝ)/336588659592 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1749
  · change lowerPayment 1750 ≤ lowerValue ((point 2 split 4096 1750+point 2 split 4096 1751)/2)
    have hp : lowerPayment 1750 = (209581616172:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1750+point 2 split 4096 1751)/2 = (439498031:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((439498031:ℝ)/168755200)/ClassicalSixthBranch.v ((439498031:ℝ)/168755200) = (678677590367:ℝ)/336540651704 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1750
  · change lowerPayment 1751 ≤ lowerValue ((point 2 split 4096 1751+point 2 split 4096 1752)/2)
    have hp : lowerPayment 1751 = (209675769048:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1751+point 2 split 4096 1752)/2 = (439556293:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((439556293:ℝ)/168755200)/ClassicalSixthBranch.v ((439556293:ℝ)/168755200) = (678600276693:ℝ)/336492643816 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1751
  · change lowerPayment 1752 ≤ lowerValue ((point 2 split 4096 1752+point 2 split 4096 1753)/2)
    have hp : lowerPayment 1752 = (209769907357:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1752+point 2 split 4096 1753)/2 = (87922911:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((87922911:ℝ)/33751040)/ClassicalSixthBranch.v ((87922911:ℝ)/33751040) = (678522963019:ℝ)/336444635928 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1752
  · change lowerPayment 1753 ≤ lowerValue ((point 2 split 4096 1753+point 2 split 4096 1754)/2)
    have hp : lowerPayment 1753 = (209864031118:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1753+point 2 split 4096 1754)/2 = (439672817:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((439672817:ℝ)/168755200)/ClassicalSixthBranch.v ((439672817:ℝ)/168755200) = (135689129869:ℝ)/67279325608 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1753
  · change lowerPayment 1754 ≤ lowerValue ((point 2 split 4096 1754+point 2 split 4096 1755)/2)
    have hp : lowerPayment 1754 = (209958140347:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1754+point 2 split 4096 1755)/2 = (439731079:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((439731079:ℝ)/168755200)/ClassicalSixthBranch.v ((439731079:ℝ)/168755200) = (678368335671:ℝ)/336348620152 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1754
  · change lowerPayment 1755 ≤ lowerValue ((point 2 split 4096 1755+point 2 split 4096 1756)/2)
    have hp : lowerPayment 1755 = (210052235065:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1755+point 2 split 4096 1756)/2 = (439789341:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((439789341:ℝ)/168755200)/ClassicalSixthBranch.v ((439789341:ℝ)/168755200) = (678291021997:ℝ)/336300612264 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1755
  · change lowerPayment 1756 ≤ lowerValue ((point 2 split 4096 1756+point 2 split 4096 1757)/2)
    have hp : lowerPayment 1756 = (210146315290:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1756+point 2 split 4096 1757)/2 = (439847603:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((439847603:ℝ)/168755200)/ClassicalSixthBranch.v ((439847603:ℝ)/168755200) = (678213708323:ℝ)/336252604376 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1756
  · change lowerPayment 1757 ≤ lowerValue ((point 2 split 4096 1757+point 2 split 4096 1758)/2)
    have hp : lowerPayment 1757 = (210240381041:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1757+point 2 split 4096 1758)/2 = (87981173:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((87981173:ℝ)/33751040)/ClassicalSixthBranch.v ((87981173:ℝ)/33751040) = (678136394649:ℝ)/336204596488 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1757
  · change lowerPayment 1758 ≤ lowerValue ((point 2 split 4096 1758+point 2 split 4096 1759)/2)
    have hp : lowerPayment 1758 = (210334432335:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1758+point 2 split 4096 1759)/2 = (439964127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((439964127:ℝ)/168755200)/ClassicalSixthBranch.v ((439964127:ℝ)/168755200) = (27122363239:ℝ)/13446263544 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1758
  · change lowerPayment 1759 ≤ lowerValue ((point 2 split 4096 1759+point 2 split 4096 1760)/2)
    have hp : lowerPayment 1759 = (210428469192:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1759+point 2 split 4096 1760)/2 = (440022389:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((440022389:ℝ)/168755200)/ClassicalSixthBranch.v ((440022389:ℝ)/168755200) = (677981767301:ℝ)/336108580712 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1759
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_109
