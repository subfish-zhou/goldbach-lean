import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints057
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_057 (j : Fin 16) : lowerPayment (16*57+j.val) ≤
    lowerValue ((point 2 split 4096 (16*57+j.val)+point 2 split 4096 (16*57+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 912 ≤ lowerValue ((point 2 split 4096 912+point 2 split 4096 913)/2)
    have hp : lowerPayment 912 = (123494246934:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 912+point 2 split 4096 913)/2 = (15626979:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((15626979:ℝ)/6750208)/ClassicalSixthBranch.v ((15626979:ℝ)/6750208) = (743466449179:ℝ)/376771261848 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_912
  · change lowerPayment 913 ≤ lowerValue ((point 2 split 4096 913+point 2 split 4096 914)/2)
    have hp : lowerPayment 913 = (123608325151:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 913+point 2 split 4096 914)/2 = (390732737:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((390732737:ℝ)/168755200)/ClassicalSixthBranch.v ((390732737:ℝ)/168755200) = (148677827101:ℝ)/75344650792 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_913
  · change lowerPayment 914 ≤ lowerValue ((point 2 split 4096 914+point 2 split 4096 915)/2)
    have hp : lowerPayment 914 = (123722368615:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 914+point 2 split 4096 915)/2 = (390790999:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((390790999:ℝ)/168755200)/ClassicalSixthBranch.v ((390790999:ℝ)/168755200) = (743311821831:ℝ)/376675246072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_914
  · change lowerPayment 915 ≤ lowerValue ((point 2 split 4096 915+point 2 split 4096 916)/2)
    have hp : lowerPayment 915 = (123836377358:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 915+point 2 split 4096 916)/2 = (390849261:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((390849261:ℝ)/168755200)/ClassicalSixthBranch.v ((390849261:ℝ)/168755200) = (743234508157:ℝ)/376627238184 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_915
  · change lowerPayment 916 ≤ lowerValue ((point 2 split 4096 916+point 2 split 4096 917)/2)
    have hp : lowerPayment 916 = (123950351412:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 916+point 2 split 4096 917)/2 = (390907523:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((390907523:ℝ)/168755200)/ClassicalSixthBranch.v ((390907523:ℝ)/168755200) = (743157194483:ℝ)/376579230296 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_916
  · change lowerPayment 917 ≤ lowerValue ((point 2 split 4096 917+point 2 split 4096 918)/2)
    have hp : lowerPayment 917 = (124064290807:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 917+point 2 split 4096 918)/2 = (78193157:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((78193157:ℝ)/33751040)/ClassicalSixthBranch.v ((78193157:ℝ)/33751040) = (743079880809:ℝ)/376531222408 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_917
  · change lowerPayment 918 ≤ lowerValue ((point 2 split 4096 918+point 2 split 4096 919)/2)
    have hp : lowerPayment 918 = (124178195576:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 918+point 2 split 4096 919)/2 = (391024047:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((391024047:ℝ)/168755200)/ClassicalSixthBranch.v ((391024047:ℝ)/168755200) = (148600513427:ℝ)/75296642904 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_918
  · change lowerPayment 919 ≤ lowerValue ((point 2 split 4096 919+point 2 split 4096 920)/2)
    have hp : lowerPayment 919 = (124292065750:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 919+point 2 split 4096 920)/2 = (391082309:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((391082309:ℝ)/168755200)/ClassicalSixthBranch.v ((391082309:ℝ)/168755200) = (742925253461:ℝ)/376435206632 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_919
  · change lowerPayment 920 ≤ lowerValue ((point 2 split 4096 920+point 2 split 4096 921)/2)
    have hp : lowerPayment 920 = (124405901361:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 920+point 2 split 4096 921)/2 = (391140571:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((391140571:ℝ)/168755200)/ClassicalSixthBranch.v ((391140571:ℝ)/168755200) = (742847939787:ℝ)/376387198744 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_920
  · change lowerPayment 921 ≤ lowerValue ((point 2 split 4096 921+point 2 split 4096 922)/2)
    have hp : lowerPayment 921 = (124519702440:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 921+point 2 split 4096 922)/2 = (391198833:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((391198833:ℝ)/168755200)/ClassicalSixthBranch.v ((391198833:ℝ)/168755200) = (742770626113:ℝ)/376339190856 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_921
  · change lowerPayment 922 ≤ lowerValue ((point 2 split 4096 922+point 2 split 4096 923)/2)
    have hp : lowerPayment 922 = (124633469019:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 922+point 2 split 4096 923)/2 = (78251419:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((78251419:ℝ)/33751040)/ClassicalSixthBranch.v ((78251419:ℝ)/33751040) = (742693312439:ℝ)/376291182968 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_922
  · change lowerPayment 923 ≤ lowerValue ((point 2 split 4096 923+point 2 split 4096 924)/2)
    have hp : lowerPayment 923 = (124747201128:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 923+point 2 split 4096 924)/2 = (391315357:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((391315357:ℝ)/168755200)/ClassicalSixthBranch.v ((391315357:ℝ)/168755200) = (295274751:ℝ)/149599672 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_923
  · change lowerPayment 924 ≤ lowerValue ((point 2 split 4096 924+point 2 split 4096 925)/2)
    have hp : lowerPayment 924 = (124860898800:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 924+point 2 split 4096 925)/2 = (391373619:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((391373619:ℝ)/168755200)/ClassicalSixthBranch.v ((391373619:ℝ)/168755200) = (742538685091:ℝ)/376195167192 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_924
  · change lowerPayment 925 ≤ lowerValue ((point 2 split 4096 925+point 2 split 4096 926)/2)
    have hp : lowerPayment 925 = (124974562066:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 925+point 2 split 4096 926)/2 = (391431881:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((391431881:ℝ)/168755200)/ClassicalSixthBranch.v ((391431881:ℝ)/168755200) = (742461371417:ℝ)/376147159304 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_925
  · change lowerPayment 926 ≤ lowerValue ((point 2 split 4096 926+point 2 split 4096 927)/2)
    have hp : lowerPayment 926 = (125088190957:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 926+point 2 split 4096 927)/2 = (391490143:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((391490143:ℝ)/168755200)/ClassicalSixthBranch.v ((391490143:ℝ)/168755200) = (742384057743:ℝ)/376099151416 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_926
  · change lowerPayment 927 ≤ lowerValue ((point 2 split 4096 927+point 2 split 4096 928)/2)
    have hp : lowerPayment 927 = (125201785505:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 927+point 2 split 4096 928)/2 = (78309681:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((78309681:ℝ)/33751040)/ClassicalSixthBranch.v ((78309681:ℝ)/33751040) = (742306744069:ℝ)/376051143528 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_927
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_057
