import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints228
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_228 (j : Fin 16) : lowerPayment (16*228+j.val) ≤
    lowerValue ((point 2 split 4096 (16*228+j.val)+point 2 split 4096 (16*228+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3648 ≤ lowerValue ((point 2 split 4096 3648+point 2 split 4096 3649)/2)
    have hp : lowerPayment 3648 = (380278442748:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3648+point 2 split 4096 3649)/2 = (550079307:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((550079307:ℝ)/168755200)/ClassicalSixthBranch.v ((550079307:ℝ)/168755200) = (106387247423:ℝ)/49084336056 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3648
  · change lowerPayment 3649 ≤ lowerValue ((point 2 split 4096 3649+point 2 split 4096 3650)/2)
    have hp : lowerPayment 3649 = (380373055303:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3649+point 2 split 4096 3650)/2 = (550137569:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((550137569:ℝ)/168755200)/ClassicalSixthBranch.v ((550137569:ℝ)/168755200) = (531858923441:ℝ)/245373672392 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3649
  · change lowerPayment 3650 ≤ lowerValue ((point 2 split 4096 3650+point 2 split 4096 3651)/2)
    have hp : lowerPayment 3650 = (380467682227:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3650+point 2 split 4096 3651)/2 = (550195831:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((550195831:ℝ)/168755200)/ClassicalSixthBranch.v ((550195831:ℝ)/168755200) = (531781609767:ℝ)/245325664504 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3650
  · change lowerPayment 3651 ≤ lowerValue ((point 2 split 4096 3651+point 2 split 4096 3652)/2)
    have hp : lowerPayment 3651 = (380562323535:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3651+point 2 split 4096 3652)/2 = (550254093:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((550254093:ℝ)/168755200)/ClassicalSixthBranch.v ((550254093:ℝ)/168755200) = (531704296093:ℝ)/245277656616 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3651
  · change lowerPayment 3652 ≤ lowerValue ((point 2 split 4096 3652+point 2 split 4096 3653)/2)
    have hp : lowerPayment 3652 = (380656979245:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3652+point 2 split 4096 3653)/2 = (110062471:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((110062471:ℝ)/33751040)/ClassicalSixthBranch.v ((110062471:ℝ)/33751040) = (531626982419:ℝ)/245229648728 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3652
  · change lowerPayment 3653 ≤ lowerValue ((point 2 split 4096 3653+point 2 split 4096 3654)/2)
    have hp : lowerPayment 3653 = (380751649371:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3653+point 2 split 4096 3654)/2 = (550370617:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((550370617:ℝ)/168755200)/ClassicalSixthBranch.v ((550370617:ℝ)/168755200) = (106309933749:ℝ)/49036328168 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3653
  · change lowerPayment 3654 ≤ lowerValue ((point 2 split 4096 3654+point 2 split 4096 3655)/2)
    have hp : lowerPayment 3654 = (380846333932:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3654+point 2 split 4096 3655)/2 = (550428879:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((550428879:ℝ)/168755200)/ClassicalSixthBranch.v ((550428879:ℝ)/168755200) = (531472355071:ℝ)/245133632952 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3654
  · change lowerPayment 3655 ≤ lowerValue ((point 2 split 4096 3655+point 2 split 4096 3656)/2)
    have hp : lowerPayment 3655 = (380941032942:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3655+point 2 split 4096 3656)/2 = (550487141:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((550487141:ℝ)/168755200)/ClassicalSixthBranch.v ((550487141:ℝ)/168755200) = (531395041397:ℝ)/245085625064 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3655
  · change lowerPayment 3656 ≤ lowerValue ((point 2 split 4096 3656+point 2 split 4096 3657)/2)
    have hp : lowerPayment 3656 = (381035746419:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3656+point 2 split 4096 3657)/2 = (5345101:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((5345101:ℝ)/1638400)/ClassicalSixthBranch.v ((5345101:ℝ)/1638400) = (5158424541:ℝ)/2379005992 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3656
  · change lowerPayment 3657 ≤ lowerValue ((point 2 split 4096 3657+point 2 split 4096 3658)/2)
    have hp : lowerPayment 3657 = (381130474378:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3657+point 2 split 4096 3658)/2 = (110120733:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((110120733:ℝ)/33751040)/ClassicalSixthBranch.v ((110120733:ℝ)/33751040) = (531240414049:ℝ)/244989609288 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3657
  · change lowerPayment 3658 ≤ lowerValue ((point 2 split 4096 3658+point 2 split 4096 3659)/2)
    have hp : lowerPayment 3658 = (381225216836:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3658+point 2 split 4096 3659)/2 = (550661927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((550661927:ℝ)/168755200)/ClassicalSixthBranch.v ((550661927:ℝ)/168755200) = (21246524015:ℝ)/9797664056 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3658
  · change lowerPayment 3659 ≤ lowerValue ((point 2 split 4096 3659+point 2 split 4096 3660)/2)
    have hp : lowerPayment 3659 = (381319973810:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3659+point 2 split 4096 3660)/2 = (550720189:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((550720189:ℝ)/168755200)/ClassicalSixthBranch.v ((550720189:ℝ)/168755200) = (531085786701:ℝ)/244893593512 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3659
  · change lowerPayment 3660 ≤ lowerValue ((point 2 split 4096 3660+point 2 split 4096 3661)/2)
    have hp : lowerPayment 3660 = (381414745314:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3660+point 2 split 4096 3661)/2 = (550778451:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((550778451:ℝ)/168755200)/ClassicalSixthBranch.v ((550778451:ℝ)/168755200) = (531008473027:ℝ)/244845585624 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3660
  · change lowerPayment 3661 ≤ lowerValue ((point 2 split 4096 3661+point 2 split 4096 3662)/2)
    have hp : lowerPayment 3661 = (381509531367:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3661+point 2 split 4096 3662)/2 = (550836713:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((550836713:ℝ)/168755200)/ClassicalSixthBranch.v ((550836713:ℝ)/168755200) = (530931159353:ℝ)/244797577736 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3661
  · change lowerPayment 3662 ≤ lowerValue ((point 2 split 4096 3662+point 2 split 4096 3663)/2)
    have hp : lowerPayment 3662 = (381604331984:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3662+point 2 split 4096 3663)/2 = (22035799:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((22035799:ℝ)/6750208)/ClassicalSixthBranch.v ((22035799:ℝ)/6750208) = (530853845679:ℝ)/244749569848 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3662
  · change lowerPayment 3663 ≤ lowerValue ((point 2 split 4096 3663+point 2 split 4096 3664)/2)
    have hp : lowerPayment 3663 = (381699147182:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3663+point 2 split 4096 3664)/2 = (550953237:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((550953237:ℝ)/168755200)/ClassicalSixthBranch.v ((550953237:ℝ)/168755200) = (106155306401:ℝ)/48940312392 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3663
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_228
