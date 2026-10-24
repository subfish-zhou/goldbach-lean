import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints217
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_217 (j : Fin 16) : lowerPayment (16*217+j.val) ≤
    lowerValue ((point 2 split 4096 (16*217+j.val)+point 2 split 4096 (16*217+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3472 ≤ lowerValue ((point 2 split 4096 3472+point 2 split 4096 3473)/2)
    have hp : lowerPayment 3472 = (363835613068:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3472+point 2 split 4096 3473)/2 = (107965039:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((107965039:ℝ)/33751040)/ClassicalSixthBranch.v ((107965039:ℝ)/33751040) = (545543443739:ℝ)/253871068568 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3472
  · change lowerPayment 3473 ≤ lowerValue ((point 2 split 4096 3473+point 2 split 4096 3474)/2)
    have hp : lowerPayment 3473 = (363927945424:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3473+point 2 split 4096 3474)/2 = (539883457:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((539883457:ℝ)/168755200)/ClassicalSixthBranch.v ((539883457:ℝ)/168755200) = (109093226013:ℝ)/50764612136 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3473
  · change lowerPayment 3474 ≤ lowerValue ((point 2 split 4096 3474+point 2 split 4096 3475)/2)
    have hp : lowerPayment 3474 = (364020289365:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3474+point 2 split 4096 3475)/2 = (539941719:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((539941719:ℝ)/168755200)/ClassicalSixthBranch.v ((539941719:ℝ)/168755200) = (545388816391:ℝ)/253775052792 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3474
  · change lowerPayment 3475 ≤ lowerValue ((point 2 split 4096 3475+point 2 split 4096 3476)/2)
    have hp : lowerPayment 3475 = (364112644906:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3475+point 2 split 4096 3476)/2 = (539999981:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((539999981:ℝ)/168755200)/ClassicalSixthBranch.v ((539999981:ℝ)/168755200) = (545311502717:ℝ)/253727044904 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3475
  · change lowerPayment 3476 ≤ lowerValue ((point 2 split 4096 3476+point 2 split 4096 3477)/2)
    have hp : lowerPayment 3476 = (364205012063:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3476+point 2 split 4096 3477)/2 = (540058243:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((540058243:ℝ)/168755200)/ClassicalSixthBranch.v ((540058243:ℝ)/168755200) = (545234189043:ℝ)/253679037016 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3476
  · change lowerPayment 3477 ≤ lowerValue ((point 2 split 4096 3477+point 2 split 4096 3478)/2)
    have hp : lowerPayment 3477 = (364297390850:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3477+point 2 split 4096 3478)/2 = (108023301:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((108023301:ℝ)/33751040)/ClassicalSixthBranch.v ((108023301:ℝ)/33751040) = (545156875369:ℝ)/253631029128 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3477
  · change lowerPayment 3478 ≤ lowerValue ((point 2 split 4096 3478+point 2 split 4096 3479)/2)
    have hp : lowerPayment 3478 = (364389781284:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3478+point 2 split 4096 3479)/2 = (540174767:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((540174767:ℝ)/168755200)/ClassicalSixthBranch.v ((540174767:ℝ)/168755200) = (109015912339:ℝ)/50716604248 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3478
  · change lowerPayment 3479 ≤ lowerValue ((point 2 split 4096 3479+point 2 split 4096 3480)/2)
    have hp : lowerPayment 3479 = (364482183379:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3479+point 2 split 4096 3480)/2 = (540233029:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((540233029:ℝ)/168755200)/ClassicalSixthBranch.v ((540233029:ℝ)/168755200) = (545002248021:ℝ)/253535013352 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3479
  · change lowerPayment 3480 ≤ lowerValue ((point 2 split 4096 3480+point 2 split 4096 3481)/2)
    have hp : lowerPayment 3480 = (364574597152:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3480+point 2 split 4096 3481)/2 = (540291291:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((540291291:ℝ)/168755200)/ClassicalSixthBranch.v ((540291291:ℝ)/168755200) = (544924934347:ℝ)/253487005464 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3480
  · change lowerPayment 3481 ≤ lowerValue ((point 2 split 4096 3481+point 2 split 4096 3482)/2)
    have hp : lowerPayment 3481 = (364667022617:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3481+point 2 split 4096 3482)/2 = (540349553:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((540349553:ℝ)/168755200)/ClassicalSixthBranch.v ((540349553:ℝ)/168755200) = (544847620673:ℝ)/253438997576 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3481
  · change lowerPayment 3482 ≤ lowerValue ((point 2 split 4096 3482+point 2 split 4096 3483)/2)
    have hp : lowerPayment 3482 = (364759459790:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3482+point 2 split 4096 3483)/2 = (108081563:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((108081563:ℝ)/33751040)/ClassicalSixthBranch.v ((108081563:ℝ)/33751040) = (544770306999:ℝ)/253390989688 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3482
  · change lowerPayment 3483 ≤ lowerValue ((point 2 split 4096 3483+point 2 split 4096 3484)/2)
    have hp : lowerPayment 3483 = (364851908687:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3483+point 2 split 4096 3484)/2 = (540466077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((540466077:ℝ)/168755200)/ClassicalSixthBranch.v ((540466077:ℝ)/168755200) = (21787719733:ℝ)/10133719272 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3483
  · change lowerPayment 3484 ≤ lowerValue ((point 2 split 4096 3484+point 2 split 4096 3485)/2)
    have hp : lowerPayment 3484 = (364944369323:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3484+point 2 split 4096 3485)/2 = (540524339:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((540524339:ℝ)/168755200)/ClassicalSixthBranch.v ((540524339:ℝ)/168755200) = (544615679651:ℝ)/253294973912 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3484
  · change lowerPayment 3485 ≤ lowerValue ((point 2 split 4096 3485+point 2 split 4096 3486)/2)
    have hp : lowerPayment 3485 = (365036841713:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3485+point 2 split 4096 3486)/2 = (540582601:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((540582601:ℝ)/168755200)/ClassicalSixthBranch.v ((540582601:ℝ)/168755200) = (544538365977:ℝ)/253246966024 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3485
  · change lowerPayment 3486 ≤ lowerValue ((point 2 split 4096 3486+point 2 split 4096 3487)/2)
    have hp : lowerPayment 3486 = (365129325872:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3486+point 2 split 4096 3487)/2 = (540640863:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((540640863:ℝ)/168755200)/ClassicalSixthBranch.v ((540640863:ℝ)/168755200) = (544461052303:ℝ)/253198958136 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3486
  · change lowerPayment 3487 ≤ lowerValue ((point 2 split 4096 3487+point 2 split 4096 3488)/2)
    have hp : lowerPayment 3487 = (365221821817:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3487+point 2 split 4096 3488)/2 = (21627965:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((21627965:ℝ)/6750208)/ClassicalSixthBranch.v ((21627965:ℝ)/6750208) = (544383738629:ℝ)/253150950248 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3487
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_217
