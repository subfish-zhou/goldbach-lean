import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints049
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_049 (j : Fin 16) : lowerPayment (16*49+j.val) ≤
    lowerValue ((point 2 split 4096 (16*49+j.val)+point 2 split 4096 (16*49+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 784 ≤ lowerValue ((point 2 split 4096 784+point 2 split 4096 785)/2)
    have hp : lowerPayment 784 = (108593707801:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 784+point 2 split 4096 785)/2 = (383216939:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((383216939:ℝ)/168755200)/ClassicalSixthBranch.v ((383216939:ℝ)/168755200) = (753362599451:ℝ)/382916271512 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_784
  · change lowerPayment 785 ≤ lowerValue ((point 2 split 4096 785+point 2 split 4096 786)/2)
    have hp : lowerPayment 785 = (108712504521:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 785+point 2 split 4096 786)/2 = (383275201:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((383275201:ℝ)/168755200)/ClassicalSixthBranch.v ((383275201:ℝ)/168755200) = (753285285777:ℝ)/382868263624 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_785
  · change lowerPayment 786 ≤ lowerValue ((point 2 split 4096 786+point 2 split 4096 787)/2)
    have hp : lowerPayment 786 = (108831262229:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 786+point 2 split 4096 787)/2 = (383333463:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((383333463:ℝ)/168755200)/ClassicalSixthBranch.v ((383333463:ℝ)/168755200) = (753207972103:ℝ)/382820255736 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_786
  · change lowerPayment 787 ≤ lowerValue ((point 2 split 4096 787+point 2 split 4096 788)/2)
    have hp : lowerPayment 787 = (108949980959:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 787+point 2 split 4096 788)/2 = (15335669:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((15335669:ℝ)/6750208)/ClassicalSixthBranch.v ((15335669:ℝ)/6750208) = (753130658429:ℝ)/382772247848 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_787
  · change lowerPayment 788 ≤ lowerValue ((point 2 split 4096 788+point 2 split 4096 789)/2)
    have hp : lowerPayment 788 = (109068660747:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 788+point 2 split 4096 789)/2 = (383449987:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((383449987:ℝ)/168755200)/ClassicalSixthBranch.v ((383449987:ℝ)/168755200) = (150610668951:ℝ)/76544847992 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_788
  · change lowerPayment 789 ≤ lowerValue ((point 2 split 4096 789+point 2 split 4096 790)/2)
    have hp : lowerPayment 789 = (109187301628:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 789+point 2 split 4096 790)/2 = (383508249:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((383508249:ℝ)/168755200)/ClassicalSixthBranch.v ((383508249:ℝ)/168755200) = (752976031081:ℝ)/382676232072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_789
  · change lowerPayment 790 ≤ lowerValue ((point 2 split 4096 790+point 2 split 4096 791)/2)
    have hp : lowerPayment 790 = (109305903636:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 790+point 2 split 4096 791)/2 = (383566511:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((383566511:ℝ)/168755200)/ClassicalSixthBranch.v ((383566511:ℝ)/168755200) = (752898717407:ℝ)/382628224184 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_790
  · change lowerPayment 791 ≤ lowerValue ((point 2 split 4096 791+point 2 split 4096 792)/2)
    have hp : lowerPayment 791 = (109424466807:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 791+point 2 split 4096 792)/2 = (383624773:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((383624773:ℝ)/168755200)/ClassicalSixthBranch.v ((383624773:ℝ)/168755200) = (752821403733:ℝ)/382580216296 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_791
  · change lowerPayment 792 ≤ lowerValue ((point 2 split 4096 792+point 2 split 4096 793)/2)
    have hp : lowerPayment 792 = (109542991175:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 792+point 2 split 4096 793)/2 = (76736607:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((76736607:ℝ)/33751040)/ClassicalSixthBranch.v ((76736607:ℝ)/33751040) = (752744090059:ℝ)/382532208408 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_792
  · change lowerPayment 793 ≤ lowerValue ((point 2 split 4096 793+point 2 split 4096 794)/2)
    have hp : lowerPayment 793 = (109661476775:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 793+point 2 split 4096 794)/2 = (383741297:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((383741297:ℝ)/168755200)/ClassicalSixthBranch.v ((383741297:ℝ)/168755200) = (150533355277:ℝ)/76496840104 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_793
  · change lowerPayment 794 ≤ lowerValue ((point 2 split 4096 794+point 2 split 4096 795)/2)
    have hp : lowerPayment 794 = (109779923642:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 794+point 2 split 4096 795)/2 = (383799559:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((383799559:ℝ)/168755200)/ClassicalSixthBranch.v ((383799559:ℝ)/168755200) = (752589462711:ℝ)/382436192632 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_794
  · change lowerPayment 795 ≤ lowerValue ((point 2 split 4096 795+point 2 split 4096 796)/2)
    have hp : lowerPayment 795 = (109898331810:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 795+point 2 split 4096 796)/2 = (383857821:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((383857821:ℝ)/168755200)/ClassicalSixthBranch.v ((383857821:ℝ)/168755200) = (752512149037:ℝ)/382388184744 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_795
  · change lowerPayment 796 ≤ lowerValue ((point 2 split 4096 796+point 2 split 4096 797)/2)
    have hp : lowerPayment 796 = (110016701315:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 796+point 2 split 4096 797)/2 = (383916083:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((383916083:ℝ)/168755200)/ClassicalSixthBranch.v ((383916083:ℝ)/168755200) = (752434835363:ℝ)/382340176856 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_796
  · change lowerPayment 797 ≤ lowerValue ((point 2 split 4096 797+point 2 split 4096 798)/2)
    have hp : lowerPayment 797 = (110135032191:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 797+point 2 split 4096 798)/2 = (76794869:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((76794869:ℝ)/33751040)/ClassicalSixthBranch.v ((76794869:ℝ)/33751040) = (752357521689:ℝ)/382292168968 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_797
  · change lowerPayment 798 ≤ lowerValue ((point 2 split 4096 798+point 2 split 4096 799)/2)
    have hp : lowerPayment 798 = (110253324473:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 798+point 2 split 4096 799)/2 = (384032607:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((384032607:ℝ)/168755200)/ClassicalSixthBranch.v ((384032607:ℝ)/168755200) = (150456041603:ℝ)/76448832216 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_798
  · change lowerPayment 799 ≤ lowerValue ((point 2 split 4096 799+point 2 split 4096 800)/2)
    have hp : lowerPayment 799 = (110371578195:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 799+point 2 split 4096 800)/2 = (384090869:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((384090869:ℝ)/168755200)/ClassicalSixthBranch.v ((384090869:ℝ)/168755200) = (752202894341:ℝ)/382196153192 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_799
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_049
