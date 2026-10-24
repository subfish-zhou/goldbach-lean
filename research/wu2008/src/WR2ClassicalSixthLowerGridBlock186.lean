import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints186
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_186 (j : Fin 16) : lowerPayment (16*186+j.val) ≤
    lowerValue ((point 2 split 4096 (16*186+j.val)+point 2 split 4096 (16*186+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2976 ≤ lowerValue ((point 2 split 4096 2976+point 2 split 4096 2977)/2)
    have hp : lowerPayment 2976 = (319160755607:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2976+point 2 split 4096 2977)/2 = (510927243:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((510927243:ℝ)/168755200)/ClassicalSixthBranch.v ((510927243:ℝ)/168755200) = (583891026043:ℝ)/277682981016 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2976
  · change lowerPayment 2977 ≤ lowerValue ((point 2 split 4096 2977+point 2 split 4096 2978)/2)
    have hp : lowerPayment 2977 = (319249170210:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2977+point 2 split 4096 2978)/2 = (102197101:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((102197101:ℝ)/33751040)/ClassicalSixthBranch.v ((102197101:ℝ)/33751040) = (583813712369:ℝ)/277634973128 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2977
  · change lowerPayment 2978 ≤ lowerValue ((point 2 split 4096 2978+point 2 split 4096 2979)/2)
    have hp : lowerPayment 2978 = (319337589144:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2978+point 2 split 4096 2979)/2 = (511043767:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((511043767:ℝ)/168755200)/ClassicalSixthBranch.v ((511043767:ℝ)/168755200) = (116747279739:ℝ)/55517393048 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2978
  · change lowerPayment 2979 ≤ lowerValue ((point 2 split 4096 2979+point 2 split 4096 2980)/2)
    have hp : lowerPayment 2979 = (319426012421:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2979+point 2 split 4096 2980)/2 = (511102029:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((511102029:ℝ)/168755200)/ClassicalSixthBranch.v ((511102029:ℝ)/168755200) = (583659085021:ℝ)/277538957352 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2979
  · change lowerPayment 2980 ≤ lowerValue ((point 2 split 4096 2980+point 2 split 4096 2981)/2)
    have hp : lowerPayment 2980 = (319514440056:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2980+point 2 split 4096 2981)/2 = (511160291:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((511160291:ℝ)/168755200)/ClassicalSixthBranch.v ((511160291:ℝ)/168755200) = (583581771347:ℝ)/277490949464 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2980
  · change lowerPayment 2981 ≤ lowerValue ((point 2 split 4096 2981+point 2 split 4096 2982)/2)
    have hp : lowerPayment 2981 = (319602872063:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2981+point 2 split 4096 2982)/2 = (511218553:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((511218553:ℝ)/168755200)/ClassicalSixthBranch.v ((511218553:ℝ)/168755200) = (583504457673:ℝ)/277442941576 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2981
  · change lowerPayment 2982 ≤ lowerValue ((point 2 split 4096 2982+point 2 split 4096 2983)/2)
    have hp : lowerPayment 2982 = (319691308457:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2982+point 2 split 4096 2983)/2 = (102255363:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((102255363:ℝ)/33751040)/ClassicalSixthBranch.v ((102255363:ℝ)/33751040) = (583427143999:ℝ)/277394933688 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2982
  · change lowerPayment 2983 ≤ lowerValue ((point 2 split 4096 2983+point 2 split 4096 2984)/2)
    have hp : lowerPayment 2983 = (319779749251:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2983+point 2 split 4096 2984)/2 = (511335077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((511335077:ℝ)/168755200)/ClassicalSixthBranch.v ((511335077:ℝ)/168755200) = (23333993213:ℝ)/11093877032 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2983
  · change lowerPayment 2984 ≤ lowerValue ((point 2 split 4096 2984+point 2 split 4096 2985)/2)
    have hp : lowerPayment 2984 = (319868194460:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2984+point 2 split 4096 2985)/2 = (511393339:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((511393339:ℝ)/168755200)/ClassicalSixthBranch.v ((511393339:ℝ)/168755200) = (583272516651:ℝ)/277298917912 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2984
  · change lowerPayment 2985 ≤ lowerValue ((point 2 split 4096 2985+point 2 split 4096 2986)/2)
    have hp : lowerPayment 2985 = (319956644097:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2985+point 2 split 4096 2986)/2 = (511451601:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((511451601:ℝ)/168755200)/ClassicalSixthBranch.v ((511451601:ℝ)/168755200) = (583195202977:ℝ)/277250910024 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2985
  · change lowerPayment 2986 ≤ lowerValue ((point 2 split 4096 2986+point 2 split 4096 2987)/2)
    have hp : lowerPayment 2986 = (320045098177:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2986+point 2 split 4096 2987)/2 = (511509863:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((511509863:ℝ)/168755200)/ClassicalSixthBranch.v ((511509863:ℝ)/168755200) = (583117889303:ℝ)/277202902136 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2986
  · change lowerPayment 2987 ≤ lowerValue ((point 2 split 4096 2987+point 2 split 4096 2988)/2)
    have hp : lowerPayment 2987 = (320133556714:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2987+point 2 split 4096 2988)/2 = (20462725:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((20462725:ℝ)/6750208)/ClassicalSixthBranch.v ((20462725:ℝ)/6750208) = (583040575629:ℝ)/277154894248 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2987
  · change lowerPayment 2988 ≤ lowerValue ((point 2 split 4096 2988+point 2 split 4096 2989)/2)
    have hp : lowerPayment 2988 = (320222019723:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2988+point 2 split 4096 2989)/2 = (511626387:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((511626387:ℝ)/168755200)/ClassicalSixthBranch.v ((511626387:ℝ)/168755200) = (116592652391:ℝ)/55421377272 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2988
  · change lowerPayment 2989 ≤ lowerValue ((point 2 split 4096 2989+point 2 split 4096 2990)/2)
    have hp : lowerPayment 2989 = (320310487217:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2989+point 2 split 4096 2990)/2 = (511684649:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((511684649:ℝ)/168755200)/ClassicalSixthBranch.v ((511684649:ℝ)/168755200) = (582885948281:ℝ)/277058878472 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2989
  · change lowerPayment 2990 ≤ lowerValue ((point 2 split 4096 2990+point 2 split 4096 2991)/2)
    have hp : lowerPayment 2990 = (320398959210:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2990+point 2 split 4096 2991)/2 = (511742911:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((511742911:ℝ)/168755200)/ClassicalSixthBranch.v ((511742911:ℝ)/168755200) = (582808634607:ℝ)/277010870584 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2990
  · change lowerPayment 2991 ≤ lowerValue ((point 2 split 4096 2991+point 2 split 4096 2992)/2)
    have hp : lowerPayment 2991 = (320487435717:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2991+point 2 split 4096 2992)/2 = (511801173:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((511801173:ℝ)/168755200)/ClassicalSixthBranch.v ((511801173:ℝ)/168755200) = (582731320933:ℝ)/276962862696 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2991
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_186
