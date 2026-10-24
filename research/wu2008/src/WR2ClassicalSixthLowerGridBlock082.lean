import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints082
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_082 (j : Fin 16) : lowerPayment (16*82+j.val) ≤
    lowerValue ((point 2 split 4096 (16*82+j.val)+point 2 split 4096 (16*82+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1312 ≤ lowerValue ((point 2 split 4096 1312+point 2 split 4096 1313)/2)
    have hp : lowerPayment 1312 = (166663746818:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1312+point 2 split 4096 1313)/2 = (16559171:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((16559171:ℝ)/6750208)/ClassicalSixthBranch.v ((16559171:ℝ)/6750208) = (712540979579:ℝ)/357568106648 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1312
  · change lowerPayment 1313 ≤ lowerValue ((point 2 split 4096 1313+point 2 split 4096 1314)/2)
    have hp : lowerPayment 1313 = (166766217707:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1313+point 2 split 4096 1314)/2 = (414037537:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((414037537:ℝ)/168755200)/ClassicalSixthBranch.v ((414037537:ℝ)/168755200) = (142492733181:ℝ)/71504019752 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1313
  · change lowerPayment 1314 ≤ lowerValue ((point 2 split 4096 1314+point 2 split 4096 1315)/2)
    have hp : lowerPayment 1314 = (166868664822:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1314+point 2 split 4096 1315)/2 = (414095799:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((414095799:ℝ)/168755200)/ClassicalSixthBranch.v ((414095799:ℝ)/168755200) = (712386352231:ℝ)/357472090872 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1314
  · change lowerPayment 1315 ≤ lowerValue ((point 2 split 4096 1315+point 2 split 4096 1316)/2)
    have hp : lowerPayment 1315 = (166971088187:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1315+point 2 split 4096 1316)/2 = (414154061:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((414154061:ℝ)/168755200)/ClassicalSixthBranch.v ((414154061:ℝ)/168755200) = (712309038557:ℝ)/357424082984 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1315
  · change lowerPayment 1316 ≤ lowerValue ((point 2 split 4096 1316+point 2 split 4096 1317)/2)
    have hp : lowerPayment 1316 = (167073487827:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1316+point 2 split 4096 1317)/2 = (414212323:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((414212323:ℝ)/168755200)/ClassicalSixthBranch.v ((414212323:ℝ)/168755200) = (712231724883:ℝ)/357376075096 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1316
  · change lowerPayment 1317 ≤ lowerValue ((point 2 split 4096 1317+point 2 split 4096 1318)/2)
    have hp : lowerPayment 1317 = (167175863766:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1317+point 2 split 4096 1318)/2 = (82854117:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((82854117:ℝ)/33751040)/ClassicalSixthBranch.v ((82854117:ℝ)/33751040) = (712154411209:ℝ)/357328067208 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1317
  · change lowerPayment 1318 ≤ lowerValue ((point 2 split 4096 1318+point 2 split 4096 1319)/2)
    have hp : lowerPayment 1318 = (167278216026:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1318+point 2 split 4096 1319)/2 = (414328847:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((414328847:ℝ)/168755200)/ClassicalSixthBranch.v ((414328847:ℝ)/168755200) = (142415419507:ℝ)/71456011864 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1318
  · change lowerPayment 1319 ≤ lowerValue ((point 2 split 4096 1319+point 2 split 4096 1320)/2)
    have hp : lowerPayment 1319 = (167380544632:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1319+point 2 split 4096 1320)/2 = (414387109:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((414387109:ℝ)/168755200)/ClassicalSixthBranch.v ((414387109:ℝ)/168755200) = (711999783861:ℝ)/357232051432 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1319
  · change lowerPayment 1320 ≤ lowerValue ((point 2 split 4096 1320+point 2 split 4096 1321)/2)
    have hp : lowerPayment 1320 = (167482849608:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1320+point 2 split 4096 1321)/2 = (414445371:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((414445371:ℝ)/168755200)/ClassicalSixthBranch.v ((414445371:ℝ)/168755200) = (711922470187:ℝ)/357184043544 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1320
  · change lowerPayment 1321 ≤ lowerValue ((point 2 split 4096 1321+point 2 split 4096 1322)/2)
    have hp : lowerPayment 1321 = (167585130977:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1321+point 2 split 4096 1322)/2 = (414503633:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((414503633:ℝ)/168755200)/ClassicalSixthBranch.v ((414503633:ℝ)/168755200) = (711845156513:ℝ)/357136035656 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1321
  · change lowerPayment 1322 ≤ lowerValue ((point 2 split 4096 1322+point 2 split 4096 1323)/2)
    have hp : lowerPayment 1322 = (167687388764:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1322+point 2 split 4096 1323)/2 = (82912379:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((82912379:ℝ)/33751040)/ClassicalSixthBranch.v ((82912379:ℝ)/33751040) = (711767842839:ℝ)/357088027768 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1322
  · change lowerPayment 1323 ≤ lowerValue ((point 2 split 4096 1323+point 2 split 4096 1324)/2)
    have hp : lowerPayment 1323 = (167789622991:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1323+point 2 split 4096 1324)/2 = (414620157:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((414620157:ℝ)/168755200)/ClassicalSixthBranch.v ((414620157:ℝ)/168755200) = (142338105833:ℝ)/71408003976 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1323
  · change lowerPayment 1324 ≤ lowerValue ((point 2 split 4096 1324+point 2 split 4096 1325)/2)
    have hp : lowerPayment 1324 = (167891833682:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1324+point 2 split 4096 1325)/2 = (414678419:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((414678419:ℝ)/168755200)/ClassicalSixthBranch.v ((414678419:ℝ)/168755200) = (711613215491:ℝ)/356992011992 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1324
  · change lowerPayment 1325 ≤ lowerValue ((point 2 split 4096 1325+point 2 split 4096 1326)/2)
    have hp : lowerPayment 1325 = (167994020862:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1325+point 2 split 4096 1326)/2 = (414736681:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((414736681:ℝ)/168755200)/ClassicalSixthBranch.v ((414736681:ℝ)/168755200) = (711535901817:ℝ)/356944004104 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1325
  · change lowerPayment 1326 ≤ lowerValue ((point 2 split 4096 1326+point 2 split 4096 1327)/2)
    have hp : lowerPayment 1326 = (168096184554:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1326+point 2 split 4096 1327)/2 = (414794943:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((414794943:ℝ)/168755200)/ClassicalSixthBranch.v ((414794943:ℝ)/168755200) = (711458588143:ℝ)/356895996216 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1326
  · change lowerPayment 1327 ≤ lowerValue ((point 2 split 4096 1327+point 2 split 4096 1328)/2)
    have hp : lowerPayment 1327 = (168198324782:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1327+point 2 split 4096 1328)/2 = (82970641:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((82970641:ℝ)/33751040)/ClassicalSixthBranch.v ((82970641:ℝ)/33751040) = (711381274469:ℝ)/356847988328 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1327
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_082
