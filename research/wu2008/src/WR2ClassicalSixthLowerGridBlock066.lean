import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints066
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_066 (j : Fin 16) : lowerPayment (16*66+j.val) ≤
    lowerValue ((point 2 split 4096 (16*66+j.val)+point 2 split 4096 (16*66+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1056 ≤ lowerValue ((point 2 split 4096 1056+point 2 split 4096 1057)/2)
    have hp : lowerPayment 1056 = (139578704799:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1056+point 2 split 4096 1057)/2 = (399064203:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((399064203:ℝ)/168755200)/ClassicalSixthBranch.v ((399064203:ℝ)/168755200) = (732333280123:ℝ)/369858125976 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1056
  · change lowerPayment 1057 ≤ lowerValue ((point 2 split 4096 1057+point 2 split 4096 1058)/2)
    have hp : lowerPayment 1057 = (139688092880:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1057+point 2 split 4096 1058)/2 = (79824493:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((79824493:ℝ)/33751040)/ClassicalSixthBranch.v ((79824493:ℝ)/33751040) = (732255966449:ℝ)/369810118088 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1057
  · change lowerPayment 1058 ≤ lowerValue ((point 2 split 4096 1058+point 2 split 4096 1059)/2)
    have hp : lowerPayment 1058 = (139797450524:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1058+point 2 split 4096 1059)/2 = (399180727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((399180727:ℝ)/168755200)/ClassicalSixthBranch.v ((399180727:ℝ)/168755200) = (29287146111:ℝ)/14790484408 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1058
  · change lowerPayment 1059 ≤ lowerValue ((point 2 split 4096 1059+point 2 split 4096 1060)/2)
    have hp : lowerPayment 1059 = (139906777762:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1059+point 2 split 4096 1060)/2 = (399238989:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((399238989:ℝ)/168755200)/ClassicalSixthBranch.v ((399238989:ℝ)/168755200) = (732101339101:ℝ)/369714102312 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1059
  · change lowerPayment 1060 ≤ lowerValue ((point 2 split 4096 1060+point 2 split 4096 1061)/2)
    have hp : lowerPayment 1060 = (140016074622:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1060+point 2 split 4096 1061)/2 = (399297251:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((399297251:ℝ)/168755200)/ClassicalSixthBranch.v ((399297251:ℝ)/168755200) = (732024025427:ℝ)/369666094424 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1060
  · change lowerPayment 1061 ≤ lowerValue ((point 2 split 4096 1061+point 2 split 4096 1062)/2)
    have hp : lowerPayment 1061 = (140125341131:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1061+point 2 split 4096 1062)/2 = (399355513:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((399355513:ℝ)/168755200)/ClassicalSixthBranch.v ((399355513:ℝ)/168755200) = (731946711753:ℝ)/369618086536 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1061
  · change lowerPayment 1062 ≤ lowerValue ((point 2 split 4096 1062+point 2 split 4096 1063)/2)
    have hp : lowerPayment 1062 = (140234577318:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1062+point 2 split 4096 1063)/2 = (15976551:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((15976551:ℝ)/6750208)/ClassicalSixthBranch.v ((15976551:ℝ)/6750208) = (731869398079:ℝ)/369570078648 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1062
  · change lowerPayment 1063 ≤ lowerValue ((point 2 split 4096 1063+point 2 split 4096 1064)/2)
    have hp : lowerPayment 1063 = (140343783211:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1063+point 2 split 4096 1064)/2 = (399472037:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((399472037:ℝ)/168755200)/ClassicalSixthBranch.v ((399472037:ℝ)/168755200) = (146358416881:ℝ)/73904414152 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1063
  · change lowerPayment 1064 ≤ lowerValue ((point 2 split 4096 1064+point 2 split 4096 1065)/2)
    have hp : lowerPayment 1064 = (140452958839:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1064+point 2 split 4096 1065)/2 = (399530299:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((399530299:ℝ)/168755200)/ClassicalSixthBranch.v ((399530299:ℝ)/168755200) = (731714770731:ℝ)/369474062872 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1064
  · change lowerPayment 1065 ≤ lowerValue ((point 2 split 4096 1065+point 2 split 4096 1066)/2)
    have hp : lowerPayment 1065 = (140562104231:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1065+point 2 split 4096 1066)/2 = (399588561:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((399588561:ℝ)/168755200)/ClassicalSixthBranch.v ((399588561:ℝ)/168755200) = (731637457057:ℝ)/369426054984 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1065
  · change lowerPayment 1066 ≤ lowerValue ((point 2 split 4096 1066+point 2 split 4096 1067)/2)
    have hp : lowerPayment 1066 = (140671219413:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1066+point 2 split 4096 1067)/2 = (399646823:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((399646823:ℝ)/168755200)/ClassicalSixthBranch.v ((399646823:ℝ)/168755200) = (731560143383:ℝ)/369378047096 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1066
  · change lowerPayment 1067 ≤ lowerValue ((point 2 split 4096 1067+point 2 split 4096 1068)/2)
    have hp : lowerPayment 1067 = (140780304415:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1067+point 2 split 4096 1068)/2 = (79941017:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((79941017:ℝ)/33751040)/ClassicalSixthBranch.v ((79941017:ℝ)/33751040) = (731482829709:ℝ)/369330039208 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1067
  · change lowerPayment 1068 ≤ lowerValue ((point 2 split 4096 1068+point 2 split 4096 1069)/2)
    have hp : lowerPayment 1068 = (140889359265:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1068+point 2 split 4096 1069)/2 = (399763347:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((399763347:ℝ)/168755200)/ClassicalSixthBranch.v ((399763347:ℝ)/168755200) = (146281103207:ℝ)/73856406264 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1068
  · change lowerPayment 1069 ≤ lowerValue ((point 2 split 4096 1069+point 2 split 4096 1070)/2)
    have hp : lowerPayment 1069 = (140998383990:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1069+point 2 split 4096 1070)/2 = (399821609:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((399821609:ℝ)/168755200)/ClassicalSixthBranch.v ((399821609:ℝ)/168755200) = (731328202361:ℝ)/369234023432 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1069
  · change lowerPayment 1070 ≤ lowerValue ((point 2 split 4096 1070+point 2 split 4096 1071)/2)
    have hp : lowerPayment 1070 = (141107378620:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1070+point 2 split 4096 1071)/2 = (399879871:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((399879871:ℝ)/168755200)/ClassicalSixthBranch.v ((399879871:ℝ)/168755200) = (731250888687:ℝ)/369186015544 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1070
  · change lowerPayment 1071 ≤ lowerValue ((point 2 split 4096 1071+point 2 split 4096 1072)/2)
    have hp : lowerPayment 1071 = (141216343182:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1071+point 2 split 4096 1072)/2 = (399938133:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((399938133:ℝ)/168755200)/ClassicalSixthBranch.v ((399938133:ℝ)/168755200) = (731173575013:ℝ)/369138007656 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1071
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_066
