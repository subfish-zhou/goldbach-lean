import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints001
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_001 (j : Fin 16) : lowerPayment (16*1+j.val) ≤
    lowerValue ((point 2 split 4096 (16*1+j.val)+point 2 split 4096 (16*1+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 16 ≤ lowerValue ((point 2 split 4096 16+point 2 split 4096 17)/2)
    have hp : lowerPayment 16 = (2681756374:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 16+point 2 split 4096 17)/2 = (338471723:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((338471723:ℝ)/168755200)/ClassicalSixthBranch.v ((338471723:ℝ)/168755200) = (812739501083:ℝ)/419786329496 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_16
  · change lowerPayment 17 ≤ lowerValue ((point 2 split 4096 17+point 2 split 4096 18)/2)
    have hp : lowerPayment 17 = (2843603943:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 17+point 2 split 4096 18)/2 = (67705997:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((67705997:ℝ)/33751040)/ClassicalSixthBranch.v ((67705997:ℝ)/33751040) = (812662187409:ℝ)/419738321608 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_17
  · change lowerPayment 18 ≤ lowerValue ((point 2 split 4096 18+point 2 split 4096 19)/2)
    have hp : lowerPayment 18 = (3005373883:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 18+point 2 split 4096 19)/2 = (338588247:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((338588247:ℝ)/168755200)/ClassicalSixthBranch.v ((338588247:ℝ)/168755200) = (162516974747:ℝ)/83938062744 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_18
  · change lowerPayment 19 ≤ lowerValue ((point 2 split 4096 19+point 2 split 4096 20)/2)
    have hp : lowerPayment 19 = (3167066266:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 19+point 2 split 4096 20)/2 = (338646509:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((338646509:ℝ)/168755200)/ClassicalSixthBranch.v ((338646509:ℝ)/168755200) = (812507560061:ℝ)/419642305832 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_19
  · change lowerPayment 20 ≤ lowerValue ((point 2 split 4096 20+point 2 split 4096 21)/2)
    have hp : lowerPayment 20 = (3328681164:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 20+point 2 split 4096 21)/2 = (338704771:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((338704771:ℝ)/168755200)/ClassicalSixthBranch.v ((338704771:ℝ)/168755200) = (812430246387:ℝ)/419594297944 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_20
  · change lowerPayment 21 ≤ lowerValue ((point 2 split 4096 21+point 2 split 4096 22)/2)
    have hp : lowerPayment 21 = (3490218648:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 21+point 2 split 4096 22)/2 = (338763033:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((338763033:ℝ)/168755200)/ClassicalSixthBranch.v ((338763033:ℝ)/168755200) = (812352932713:ℝ)/419546290056 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_21
  · change lowerPayment 22 ≤ lowerValue ((point 2 split 4096 22+point 2 split 4096 23)/2)
    have hp : lowerPayment 22 = (3651678789:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 22+point 2 split 4096 23)/2 = (67764259:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((67764259:ℝ)/33751040)/ClassicalSixthBranch.v ((67764259:ℝ)/33751040) = (812275619039:ℝ)/419498282168 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_22
  · change lowerPayment 23 ≤ lowerValue ((point 2 split 4096 23+point 2 split 4096 24)/2)
    have hp : lowerPayment 23 = (3813061657:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 23+point 2 split 4096 24)/2 = (338879557:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((338879557:ℝ)/168755200)/ClassicalSixthBranch.v ((338879557:ℝ)/168755200) = (162439661073:ℝ)/83890054856 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_23
  · change lowerPayment 24 ≤ lowerValue ((point 2 split 4096 24+point 2 split 4096 25)/2)
    have hp : lowerPayment 24 = (3974367324:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 24+point 2 split 4096 25)/2 = (338937819:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((338937819:ℝ)/168755200)/ClassicalSixthBranch.v ((338937819:ℝ)/168755200) = (812120991691:ℝ)/419402266392 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_24
  · change lowerPayment 25 ≤ lowerValue ((point 2 split 4096 25+point 2 split 4096 26)/2)
    have hp : lowerPayment 25 = (4135595862:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 25+point 2 split 4096 26)/2 = (338996081:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((338996081:ℝ)/168755200)/ClassicalSixthBranch.v ((338996081:ℝ)/168755200) = (812043678017:ℝ)/419354258504 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_25
  · change lowerPayment 26 ≤ lowerValue ((point 2 split 4096 26+point 2 split 4096 27)/2)
    have hp : lowerPayment 26 = (4296747340:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 26+point 2 split 4096 27)/2 = (339054343:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((339054343:ℝ)/168755200)/ClassicalSixthBranch.v ((339054343:ℝ)/168755200) = (811966364343:ℝ)/419306250616 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_26
  · change lowerPayment 27 ≤ lowerValue ((point 2 split 4096 27+point 2 split 4096 28)/2)
    have hp : lowerPayment 27 = (4457821830:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 27+point 2 split 4096 28)/2 = (67822521:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((67822521:ℝ)/33751040)/ClassicalSixthBranch.v ((67822521:ℝ)/33751040) = (811889050669:ℝ)/419258242728 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_27
  · change lowerPayment 28 ≤ lowerValue ((point 2 split 4096 28+point 2 split 4096 29)/2)
    have hp : lowerPayment 28 = (4618819402:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 28+point 2 split 4096 29)/2 = (339170867:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((339170867:ℝ)/168755200)/ClassicalSixthBranch.v ((339170867:ℝ)/168755200) = (162362347399:ℝ)/83842046968 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_28
  · change lowerPayment 29 ≤ lowerValue ((point 2 split 4096 29+point 2 split 4096 30)/2)
    have hp : lowerPayment 29 = (4779740128:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 29+point 2 split 4096 30)/2 = (339229129:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((339229129:ℝ)/168755200)/ClassicalSixthBranch.v ((339229129:ℝ)/168755200) = (811734423321:ℝ)/419162226952 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_29
  · change lowerPayment 30 ≤ lowerValue ((point 2 split 4096 30+point 2 split 4096 31)/2)
    have hp : lowerPayment 30 = (4940584076:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 30+point 2 split 4096 31)/2 = (339287391:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((339287391:ℝ)/168755200)/ClassicalSixthBranch.v ((339287391:ℝ)/168755200) = (811657109647:ℝ)/419114219064 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_30
  · change lowerPayment 31 ≤ lowerValue ((point 2 split 4096 31+point 2 split 4096 32)/2)
    have hp : lowerPayment 31 = (5101351319:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 31+point 2 split 4096 32)/2 = (339345653:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((339345653:ℝ)/168755200)/ClassicalSixthBranch.v ((339345653:ℝ)/168755200) = (811579795973:ℝ)/419066211176 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_31
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_001
