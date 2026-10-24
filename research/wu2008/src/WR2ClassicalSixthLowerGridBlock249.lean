import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints249
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_249 (j : Fin 16) : lowerPayment (16*249+j.val) ≤
    lowerValue ((point 2 split 4096 (16*249+j.val)+point 2 split 4096 (16*249+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3984 ≤ lowerValue ((point 2 split 4096 3984+point 2 split 4096 3985)/2)
    have hp : lowerPayment 3984 = (412982295909:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3984+point 2 split 4096 3985)/2 = (569655339:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((569655339:ℝ)/168755200)/ClassicalSixthBranch.v ((569655339:ℝ)/168755200) = (505958842651:ℝ)/229291029912 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3984
  · change lowerPayment 3985 ≤ lowerValue ((point 2 split 4096 3985+point 2 split 4096 3986)/2)
    have hp : lowerPayment 3985 = (413082693902:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3985+point 2 split 4096 3986)/2 = (569713601:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((569713601:ℝ)/168755200)/ClassicalSixthBranch.v ((569713601:ℝ)/168755200) = (505881528977:ℝ)/229243022024 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3985
  · change lowerPayment 3986 ≤ lowerValue ((point 2 split 4096 3986+point 2 split 4096 3987)/2)
    have hp : lowerPayment 3986 = (413183112120:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3986+point 2 split 4096 3987)/2 = (569771863:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((569771863:ℝ)/168755200)/ClassicalSixthBranch.v ((569771863:ℝ)/168755200) = (505804215303:ℝ)/229195014136 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3986
  · change lowerPayment 3987 ≤ lowerValue ((point 2 split 4096 3987+point 2 split 4096 3988)/2)
    have hp : lowerPayment 3987 = (413283550582:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3987+point 2 split 4096 3988)/2 = (22793205:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((22793205:ℝ)/6750208)/ClassicalSixthBranch.v ((22793205:ℝ)/6750208) = (505726901629:ℝ)/229147006248 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3987
  · change lowerPayment 3988 ≤ lowerValue ((point 2 split 4096 3988+point 2 split 4096 3989)/2)
    have hp : lowerPayment 3988 = (413384009306:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3988+point 2 split 4096 3989)/2 = (569888387:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((569888387:ℝ)/168755200)/ClassicalSixthBranch.v ((569888387:ℝ)/168755200) = (101129917591:ℝ)/45819799672 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3988
  · change lowerPayment 3989 ≤ lowerValue ((point 2 split 4096 3989+point 2 split 4096 3990)/2)
    have hp : lowerPayment 3989 = (413484488311:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3989+point 2 split 4096 3990)/2 = (569946649:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((569946649:ℝ)/168755200)/ClassicalSixthBranch.v ((569946649:ℝ)/168755200) = (505572274281:ℝ)/229050990472 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3989
  · change lowerPayment 3990 ≤ lowerValue ((point 2 split 4096 3990+point 2 split 4096 3991)/2)
    have hp : lowerPayment 3990 = (413584987617:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3990+point 2 split 4096 3991)/2 = (570004911:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((570004911:ℝ)/168755200)/ClassicalSixthBranch.v ((570004911:ℝ)/168755200) = (505494960607:ℝ)/229002982584 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3990
  · change lowerPayment 3991 ≤ lowerValue ((point 2 split 4096 3991+point 2 split 4096 3992)/2)
    have hp : lowerPayment 3991 = (413685507241:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3991+point 2 split 4096 3992)/2 = (570063173:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((570063173:ℝ)/168755200)/ClassicalSixthBranch.v ((570063173:ℝ)/168755200) = (505417646933:ℝ)/228954974696 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3991
  · change lowerPayment 3992 ≤ lowerValue ((point 2 split 4096 3992+point 2 split 4096 3993)/2)
    have hp : lowerPayment 3992 = (413786047203:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3992+point 2 split 4096 3993)/2 = (114024287:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((114024287:ℝ)/33751040)/ClassicalSixthBranch.v ((114024287:ℝ)/33751040) = (505340333259:ℝ)/228906966808 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3992
  · change lowerPayment 3993 ≤ lowerValue ((point 2 split 4096 3993+point 2 split 4096 3994)/2)
    have hp : lowerPayment 3993 = (413886607521:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3993+point 2 split 4096 3994)/2 = (570179697:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((570179697:ℝ)/168755200)/ClassicalSixthBranch.v ((570179697:ℝ)/168755200) = (101052603917:ℝ)/45771791784 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3993
  · change lowerPayment 3994 ≤ lowerValue ((point 2 split 4096 3994+point 2 split 4096 3995)/2)
    have hp : lowerPayment 3994 = (413987188215:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3994+point 2 split 4096 3995)/2 = (570237959:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((570237959:ℝ)/168755200)/ClassicalSixthBranch.v ((570237959:ℝ)/168755200) = (505185705911:ℝ)/228810951032 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3994
  · change lowerPayment 3995 ≤ lowerValue ((point 2 split 4096 3995+point 2 split 4096 3996)/2)
    have hp : lowerPayment 3995 = (414087789303:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3995+point 2 split 4096 3996)/2 = (570296221:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((570296221:ℝ)/168755200)/ClassicalSixthBranch.v ((570296221:ℝ)/168755200) = (505108392237:ℝ)/228762943144 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3995
  · change lowerPayment 3996 ≤ lowerValue ((point 2 split 4096 3996+point 2 split 4096 3997)/2)
    have hp : lowerPayment 3996 = (414188410804:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3996+point 2 split 4096 3997)/2 = (570354483:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((570354483:ℝ)/168755200)/ClassicalSixthBranch.v ((570354483:ℝ)/168755200) = (505031078563:ℝ)/228714935256 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3996
  · change lowerPayment 3997 ≤ lowerValue ((point 2 split 4096 3997+point 2 split 4096 3998)/2)
    have hp : lowerPayment 3997 = (414289052737:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3997+point 2 split 4096 3998)/2 = (114082549:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((114082549:ℝ)/33751040)/ClassicalSixthBranch.v ((114082549:ℝ)/33751040) = (504953764889:ℝ)/228666927368 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3997
  · change lowerPayment 3998 ≤ lowerValue ((point 2 split 4096 3998+point 2 split 4096 3999)/2)
    have hp : lowerPayment 3998 = (414389715121:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3998+point 2 split 4096 3999)/2 = (570471007:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((570471007:ℝ)/168755200)/ClassicalSixthBranch.v ((570471007:ℝ)/168755200) = (100975290243:ℝ)/45723783896 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3998
  · change lowerPayment 3999 ≤ lowerValue ((point 2 split 4096 3999+point 2 split 4096 4000)/2)
    have hp : lowerPayment 3999 = (414490397975:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3999+point 2 split 4096 4000)/2 = (570529269:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((570529269:ℝ)/168755200)/ClassicalSixthBranch.v ((570529269:ℝ)/168755200) = (504799137541:ℝ)/228570911592 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3999
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_249
