import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints004
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_004 (j : Fin 16) : lowerPayment (16*4+j.val) ≤
    lowerValue ((point 2 split 4096 (16*4+j.val)+point 2 split 4096 (16*4+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 64 ≤ lowerValue ((point 2 split 4096 64+point 2 split 4096 65)/2)
    have hp : lowerPayment 64 = (10364095495:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 64+point 2 split 4096 65)/2 = (341268299:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((341268299:ℝ)/168755200)/ClassicalSixthBranch.v ((341268299:ℝ)/168755200) = (809028444731:ℝ)/417481950872 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_64
  · change lowerPayment 65 ≤ lowerValue ((point 2 split 4096 65+point 2 split 4096 66)/2)
    have hp : lowerPayment 65 = (10522296168:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 65+point 2 split 4096 66)/2 = (341326561:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((341326561:ℝ)/168755200)/ClassicalSixthBranch.v ((341326561:ℝ)/168755200) = (808951131057:ℝ)/417433942984 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_65
  · change lowerPayment 66 ≤ lowerValue ((point 2 split 4096 66+point 2 split 4096 67)/2)
    have hp : lowerPayment 66 = (10680422557:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 66+point 2 split 4096 67)/2 = (341384823:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((341384823:ℝ)/168755200)/ClassicalSixthBranch.v ((341384823:ℝ)/168755200) = (808873817383:ℝ)/417385935096 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_66
  · change lowerPayment 67 ≤ lowerValue ((point 2 split 4096 67+point 2 split 4096 68)/2)
    have hp : lowerPayment 67 = (10838474730:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 67+point 2 split 4096 68)/2 = (68288617:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((68288617:ℝ)/33751040)/ClassicalSixthBranch.v ((68288617:ℝ)/33751040) = (808796503709:ℝ)/417337927208 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_67
  · change lowerPayment 68 ≤ lowerValue ((point 2 split 4096 68+point 2 split 4096 69)/2)
    have hp : lowerPayment 68 = (10996452754:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 68+point 2 split 4096 69)/2 = (341501347:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((341501347:ℝ)/168755200)/ClassicalSixthBranch.v ((341501347:ℝ)/168755200) = (161743838007:ℝ)/83457983864 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_68
  · change lowerPayment 69 ≤ lowerValue ((point 2 split 4096 69+point 2 split 4096 70)/2)
    have hp : lowerPayment 69 = (11154356698:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 69+point 2 split 4096 70)/2 = (341559609:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((341559609:ℝ)/168755200)/ClassicalSixthBranch.v ((341559609:ℝ)/168755200) = (808641876361:ℝ)/417241911432 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_69
  · change lowerPayment 70 ≤ lowerValue ((point 2 split 4096 70+point 2 split 4096 71)/2)
    have hp : lowerPayment 70 = (11312186629:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 70+point 2 split 4096 71)/2 = (341617871:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((341617871:ℝ)/168755200)/ClassicalSixthBranch.v ((341617871:ℝ)/168755200) = (808564562687:ℝ)/417193903544 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_70
  · change lowerPayment 71 ≤ lowerValue ((point 2 split 4096 71+point 2 split 4096 72)/2)
    have hp : lowerPayment 71 = (11469942615:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 71+point 2 split 4096 72)/2 = (341676133:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((341676133:ℝ)/168755200)/ClassicalSixthBranch.v ((341676133:ℝ)/168755200) = (808487249013:ℝ)/417145895656 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_71
  · change lowerPayment 72 ≤ lowerValue ((point 2 split 4096 72+point 2 split 4096 73)/2)
    have hp : lowerPayment 72 = (11627624723:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 72+point 2 split 4096 73)/2 = (68346879:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((68346879:ℝ)/33751040)/ClassicalSixthBranch.v ((68346879:ℝ)/33751040) = (808409935339:ℝ)/417097887768 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_72
  · change lowerPayment 73 ≤ lowerValue ((point 2 split 4096 73+point 2 split 4096 74)/2)
    have hp : lowerPayment 73 = (11785233021:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 73+point 2 split 4096 74)/2 = (341792657:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((341792657:ℝ)/168755200)/ClassicalSixthBranch.v ((341792657:ℝ)/168755200) = (161666524333:ℝ)/83409975976 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_73
  · change lowerPayment 74 ≤ lowerValue ((point 2 split 4096 74+point 2 split 4096 75)/2)
    have hp : lowerPayment 74 = (11942767576:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 74+point 2 split 4096 75)/2 = (341850919:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((341850919:ℝ)/168755200)/ClassicalSixthBranch.v ((341850919:ℝ)/168755200) = (808255307991:ℝ)/417001871992 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_74
  · change lowerPayment 75 ≤ lowerValue ((point 2 split 4096 75+point 2 split 4096 76)/2)
    have hp : lowerPayment 75 = (12100228456:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 75+point 2 split 4096 76)/2 = (341909181:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((341909181:ℝ)/168755200)/ClassicalSixthBranch.v ((341909181:ℝ)/168755200) = (808177994317:ℝ)/416953864104 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_75
  · change lowerPayment 76 ≤ lowerValue ((point 2 split 4096 76+point 2 split 4096 77)/2)
    have hp : lowerPayment 76 = (12257615728:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 76+point 2 split 4096 77)/2 = (341967443:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((341967443:ℝ)/168755200)/ClassicalSixthBranch.v ((341967443:ℝ)/168755200) = (808100680643:ℝ)/416905856216 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_76
  · change lowerPayment 77 ≤ lowerValue ((point 2 split 4096 77+point 2 split 4096 78)/2)
    have hp : lowerPayment 77 = (12414929459:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 77+point 2 split 4096 78)/2 = (68405141:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((68405141:ℝ)/33751040)/ClassicalSixthBranch.v ((68405141:ℝ)/33751040) = (808023366969:ℝ)/416857848328 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_77
  · change lowerPayment 78 ≤ lowerValue ((point 2 split 4096 78+point 2 split 4096 79)/2)
    have hp : lowerPayment 78 = (12572169716:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 78+point 2 split 4096 79)/2 = (342083967:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((342083967:ℝ)/168755200)/ClassicalSixthBranch.v ((342083967:ℝ)/168755200) = (161589210659:ℝ)/83361968088 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_78
  · change lowerPayment 79 ≤ lowerValue ((point 2 split 4096 79+point 2 split 4096 80)/2)
    have hp : lowerPayment 79 = (12729336566:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 79+point 2 split 4096 80)/2 = (342142229:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((342142229:ℝ)/168755200)/ClassicalSixthBranch.v ((342142229:ℝ)/168755200) = (807868739621:ℝ)/416761832552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_79
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_004
