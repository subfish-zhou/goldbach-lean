import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints046
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_046 (j : Fin 16) : lowerPayment (16*46+j.val) ≤
    lowerValue ((point 2 split 4096 (16*46+j.val)+point 2 split 4096 (16*46+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 736 ≤ lowerValue ((point 2 split 4096 736+point 2 split 4096 737)/2)
    have hp : lowerPayment 736 = (102844893978:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 736+point 2 split 4096 737)/2 = (380420363:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((380420363:ℝ)/168755200)/ClassicalSixthBranch.v ((380420363:ℝ)/168755200) = (757073655803:ℝ)/385220650136 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_736
  · change lowerPayment 737 ≤ lowerValue ((point 2 split 4096 737+point 2 split 4096 738)/2)
    have hp : lowerPayment 737 = (102965604992:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 737+point 2 split 4096 738)/2 = (15219145:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((15219145:ℝ)/6750208)/ClassicalSixthBranch.v ((15219145:ℝ)/6750208) = (756996342129:ℝ)/385172642248 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_737
  · change lowerPayment 738 ≤ lowerValue ((point 2 split 4096 738+point 2 split 4096 739)/2)
    have hp : lowerPayment 738 = (103086275279:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 738+point 2 split 4096 739)/2 = (380536887:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((380536887:ℝ)/168755200)/ClassicalSixthBranch.v ((380536887:ℝ)/168755200) = (151383805691:ℝ)/77024926872 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_738
  · change lowerPayment 739 ≤ lowerValue ((point 2 split 4096 739+point 2 split 4096 740)/2)
    have hp : lowerPayment 739 = (103206904878:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 739+point 2 split 4096 740)/2 = (380595149:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((380595149:ℝ)/168755200)/ClassicalSixthBranch.v ((380595149:ℝ)/168755200) = (756841714781:ℝ)/385076626472 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_739
  · change lowerPayment 740 ≤ lowerValue ((point 2 split 4096 740+point 2 split 4096 741)/2)
    have hp : lowerPayment 740 = (103327493824:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 740+point 2 split 4096 741)/2 = (380653411:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((380653411:ℝ)/168755200)/ClassicalSixthBranch.v ((380653411:ℝ)/168755200) = (756764401107:ℝ)/385028618584 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_740
  · change lowerPayment 741 ≤ lowerValue ((point 2 split 4096 741+point 2 split 4096 742)/2)
    have hp : lowerPayment 741 = (103448042153:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 741+point 2 split 4096 742)/2 = (380711673:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((380711673:ℝ)/168755200)/ClassicalSixthBranch.v ((380711673:ℝ)/168755200) = (756687087433:ℝ)/384980610696 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_741
  · change lowerPayment 742 ≤ lowerValue ((point 2 split 4096 742+point 2 split 4096 743)/2)
    have hp : lowerPayment 742 = (103568549903:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 742+point 2 split 4096 743)/2 = (76153987:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((76153987:ℝ)/33751040)/ClassicalSixthBranch.v ((76153987:ℝ)/33751040) = (756609773759:ℝ)/384932602808 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_742
  · change lowerPayment 743 ≤ lowerValue ((point 2 split 4096 743+point 2 split 4096 744)/2)
    have hp : lowerPayment 743 = (103689017108:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 743+point 2 split 4096 744)/2 = (380828197:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((380828197:ℝ)/168755200)/ClassicalSixthBranch.v ((380828197:ℝ)/168755200) = (151306492017:ℝ)/76976918984 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_743
  · change lowerPayment 744 ≤ lowerValue ((point 2 split 4096 744+point 2 split 4096 745)/2)
    have hp : lowerPayment 744 = (103809443806:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 744+point 2 split 4096 745)/2 = (380886459:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((380886459:ℝ)/168755200)/ClassicalSixthBranch.v ((380886459:ℝ)/168755200) = (756455146411:ℝ)/384836587032 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_744
  · change lowerPayment 745 ≤ lowerValue ((point 2 split 4096 745+point 2 split 4096 746)/2)
    have hp : lowerPayment 745 = (103929830033:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 745+point 2 split 4096 746)/2 = (380944721:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((380944721:ℝ)/168755200)/ClassicalSixthBranch.v ((380944721:ℝ)/168755200) = (756377832737:ℝ)/384788579144 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_745
  · change lowerPayment 746 ≤ lowerValue ((point 2 split 4096 746+point 2 split 4096 747)/2)
    have hp : lowerPayment 746 = (104050175824:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 746+point 2 split 4096 747)/2 = (381002983:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((381002983:ℝ)/168755200)/ClassicalSixthBranch.v ((381002983:ℝ)/168755200) = (756300519063:ℝ)/384740571256 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_746
  · change lowerPayment 747 ≤ lowerValue ((point 2 split 4096 747+point 2 split 4096 748)/2)
    have hp : lowerPayment 747 = (104170481216:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 747+point 2 split 4096 748)/2 = (76212249:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((76212249:ℝ)/33751040)/ClassicalSixthBranch.v ((76212249:ℝ)/33751040) = (756223205389:ℝ)/384692563368 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_747
  · change lowerPayment 748 ≤ lowerValue ((point 2 split 4096 748+point 2 split 4096 749)/2)
    have hp : lowerPayment 748 = (104290746245:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 748+point 2 split 4096 749)/2 = (381119507:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((381119507:ℝ)/168755200)/ClassicalSixthBranch.v ((381119507:ℝ)/168755200) = (151229178343:ℝ)/76928911096 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_748
  · change lowerPayment 749 ≤ lowerValue ((point 2 split 4096 749+point 2 split 4096 750)/2)
    have hp : lowerPayment 749 = (104410970947:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 749+point 2 split 4096 750)/2 = (381177769:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((381177769:ℝ)/168755200)/ClassicalSixthBranch.v ((381177769:ℝ)/168755200) = (756068578041:ℝ)/384596547592 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_749
  · change lowerPayment 750 ≤ lowerValue ((point 2 split 4096 750+point 2 split 4096 751)/2)
    have hp : lowerPayment 750 = (104531155359:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 750+point 2 split 4096 751)/2 = (381236031:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((381236031:ℝ)/168755200)/ClassicalSixthBranch.v ((381236031:ℝ)/168755200) = (755991264367:ℝ)/384548539704 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_750
  · change lowerPayment 751 ≤ lowerValue ((point 2 split 4096 751+point 2 split 4096 752)/2)
    have hp : lowerPayment 751 = (104651299516:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 751+point 2 split 4096 752)/2 = (381294293:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((381294293:ℝ)/168755200)/ClassicalSixthBranch.v ((381294293:ℝ)/168755200) = (755913950693:ℝ)/384500531816 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_751
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_046
