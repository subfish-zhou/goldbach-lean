import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints003
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_003 (j : Fin 16) : lowerPayment (16*3+j.val) ≤
    lowerValue ((point 2 split 4096 (16*3+j.val)+point 2 split 4096 (16*3+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 48 ≤ lowerValue ((point 2 split 4096 48+point 2 split 4096 49)/2)
    have hp : lowerPayment 48 = (7822726417:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 48+point 2 split 4096 49)/2 = (340336107:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((340336107:ℝ)/168755200)/ClassicalSixthBranch.v ((340336107:ℝ)/168755200) = (162053092703:ℝ)/83650015416 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_48
  · change lowerPayment 49 ≤ lowerValue ((point 2 split 4096 49+point 2 split 4096 50)/2)
    have hp : lowerPayment 49 = (7982124927:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 49+point 2 split 4096 50)/2 = (340394369:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((340394369:ℝ)/168755200)/ClassicalSixthBranch.v ((340394369:ℝ)/168755200) = (810188149841:ℝ)/418202069192 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_49
  · change lowerPayment 50 ≤ lowerValue ((point 2 split 4096 50+point 2 split 4096 51)/2)
    have hp : lowerPayment 50 = (8141448057:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 50+point 2 split 4096 51)/2 = (340452631:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((340452631:ℝ)/168755200)/ClassicalSixthBranch.v ((340452631:ℝ)/168755200) = (810110836167:ℝ)/418154061304 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_50
  · change lowerPayment 51 ≤ lowerValue ((point 2 split 4096 51+point 2 split 4096 52)/2)
    have hp : lowerPayment 51 = (8300695876:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 51+point 2 split 4096 52)/2 = (3305931:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((3305931:ℝ)/1638400)/ClassicalSixthBranch.v ((3305931:ℝ)/1638400) = (7864403131:ℝ)/4059282072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_51
  · change lowerPayment 52 ≤ lowerValue ((point 2 split 4096 52+point 2 split 4096 53)/2)
    have hp : lowerPayment 52 = (8459868453:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 52+point 2 split 4096 53)/2 = (68113831:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((68113831:ℝ)/33751040)/ClassicalSixthBranch.v ((68113831:ℝ)/33751040) = (809956208819:ℝ)/418058045528 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_52
  · change lowerPayment 53 ≤ lowerValue ((point 2 split 4096 53+point 2 split 4096 54)/2)
    have hp : lowerPayment 53 = (8618965857:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 53+point 2 split 4096 54)/2 = (340627417:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((340627417:ℝ)/168755200)/ClassicalSixthBranch.v ((340627417:ℝ)/168755200) = (161975779029:ℝ)/83602007528 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_53
  · change lowerPayment 54 ≤ lowerValue ((point 2 split 4096 54+point 2 split 4096 55)/2)
    have hp : lowerPayment 54 = (8777988156:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 54+point 2 split 4096 55)/2 = (340685679:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((340685679:ℝ)/168755200)/ClassicalSixthBranch.v ((340685679:ℝ)/168755200) = (809801581471:ℝ)/417962029752 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_54
  · change lowerPayment 55 ≤ lowerValue ((point 2 split 4096 55+point 2 split 4096 56)/2)
    have hp : lowerPayment 55 = (8936935419:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 55+point 2 split 4096 56)/2 = (340743941:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((340743941:ℝ)/168755200)/ClassicalSixthBranch.v ((340743941:ℝ)/168755200) = (809724267797:ℝ)/417914021864 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_55
  · change lowerPayment 56 ≤ lowerValue ((point 2 split 4096 56+point 2 split 4096 57)/2)
    have hp : lowerPayment 56 = (9095807716:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 56+point 2 split 4096 57)/2 = (340802203:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((340802203:ℝ)/168755200)/ClassicalSixthBranch.v ((340802203:ℝ)/168755200) = (809646954123:ℝ)/417866013976 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_56
  · change lowerPayment 57 ≤ lowerValue ((point 2 split 4096 57+point 2 split 4096 58)/2)
    have hp : lowerPayment 57 = (9254605114:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 57+point 2 split 4096 58)/2 = (68172093:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((68172093:ℝ)/33751040)/ClassicalSixthBranch.v ((68172093:ℝ)/33751040) = (809569640449:ℝ)/417818006088 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_57
  · change lowerPayment 58 ≤ lowerValue ((point 2 split 4096 58+point 2 split 4096 59)/2)
    have hp : lowerPayment 58 = (9413327682:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 58+point 2 split 4096 59)/2 = (340918727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((340918727:ℝ)/168755200)/ClassicalSixthBranch.v ((340918727:ℝ)/168755200) = (32379693071:ℝ)/16710799928 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_58
  · change lowerPayment 59 ≤ lowerValue ((point 2 split 4096 59+point 2 split 4096 60)/2)
    have hp : lowerPayment 59 = (9571975489:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 59+point 2 split 4096 60)/2 = (340976989:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((340976989:ℝ)/168755200)/ClassicalSixthBranch.v ((340976989:ℝ)/168755200) = (809415013101:ℝ)/417721990312 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_59
  · change lowerPayment 60 ≤ lowerValue ((point 2 split 4096 60+point 2 split 4096 61)/2)
    have hp : lowerPayment 60 = (9730548603:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 60+point 2 split 4096 61)/2 = (341035251:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((341035251:ℝ)/168755200)/ClassicalSixthBranch.v ((341035251:ℝ)/168755200) = (809337699427:ℝ)/417673982424 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_60
  · change lowerPayment 61 ≤ lowerValue ((point 2 split 4096 61+point 2 split 4096 62)/2)
    have hp : lowerPayment 61 = (9889047092:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 61+point 2 split 4096 62)/2 = (341093513:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((341093513:ℝ)/168755200)/ClassicalSixthBranch.v ((341093513:ℝ)/168755200) = (809260385753:ℝ)/417625974536 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_61
  · change lowerPayment 62 ≤ lowerValue ((point 2 split 4096 62+point 2 split 4096 63)/2)
    have hp : lowerPayment 62 = (10047471025:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 62+point 2 split 4096 63)/2 = (13646071:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((13646071:ℝ)/6750208)/ClassicalSixthBranch.v ((13646071:ℝ)/6750208) = (809183072079:ℝ)/417577966648 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_62
  · change lowerPayment 63 ≤ lowerValue ((point 2 split 4096 63+point 2 split 4096 64)/2)
    have hp : lowerPayment 63 = (10205820470:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 63+point 2 split 4096 64)/2 = (341210037:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((341210037:ℝ)/168755200)/ClassicalSixthBranch.v ((341210037:ℝ)/168755200) = (161821151681:ℝ)/83505991752 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_63
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_003
