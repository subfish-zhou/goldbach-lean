import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints035
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_035 (j : Fin 16) : lowerPayment (16*35+j.val) ≤
    lowerValue ((point 2 split 4096 (16*35+j.val)+point 2 split 4096 (16*35+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 560 ≤ lowerValue ((point 2 split 4096 560+point 2 split 4096 561)/2)
    have hp : lowerPayment 560 = (80930498625:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 560+point 2 split 4096 561)/2 = (370166251:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((370166251:ℝ)/168755200)/ClassicalSixthBranch.v ((370166251:ℝ)/168755200) = (770680862427:ℝ)/393670038424 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_560
  · change lowerPayment 561 ≤ lowerValue ((point 2 split 4096 561+point 2 split 4096 562)/2)
    have hp : lowerPayment 561 = (81058973229:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 561+point 2 split 4096 562)/2 = (370224513:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((370224513:ℝ)/168755200)/ClassicalSixthBranch.v ((370224513:ℝ)/168755200) = (770603548753:ℝ)/393622030536 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_561
  · change lowerPayment 562 ≤ lowerValue ((point 2 split 4096 562+point 2 split 4096 563)/2)
    have hp : lowerPayment 562 = (81187400203:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 562+point 2 split 4096 563)/2 = (14811311:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((14811311:ℝ)/6750208)/ClassicalSixthBranch.v ((14811311:ℝ)/6750208) = (770526235079:ℝ)/393574022648 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_562
  · change lowerPayment 563 ≤ lowerValue ((point 2 split 4096 563+point 2 split 4096 564)/2)
    have hp : lowerPayment 563 = (81315779589:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 563+point 2 split 4096 564)/2 = (370341037:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((370341037:ℝ)/168755200)/ClassicalSixthBranch.v ((370341037:ℝ)/168755200) = (154089784281:ℝ)/78705202952 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_563
  · change lowerPayment 564 ≤ lowerValue ((point 2 split 4096 564+point 2 split 4096 565)/2)
    have hp : lowerPayment 564 = (81444111429:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 564+point 2 split 4096 565)/2 = (370399299:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((370399299:ℝ)/168755200)/ClassicalSixthBranch.v ((370399299:ℝ)/168755200) = (770371607731:ℝ)/393478006872 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_564
  · change lowerPayment 565 ≤ lowerValue ((point 2 split 4096 565+point 2 split 4096 566)/2)
    have hp : lowerPayment 565 = (81572395766:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 565+point 2 split 4096 566)/2 = (370457561:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((370457561:ℝ)/168755200)/ClassicalSixthBranch.v ((370457561:ℝ)/168755200) = (770294294057:ℝ)/393429998984 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_565
  · change lowerPayment 566 ≤ lowerValue ((point 2 split 4096 566+point 2 split 4096 567)/2)
    have hp : lowerPayment 566 = (81700632642:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 566+point 2 split 4096 567)/2 = (3597241:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((3597241:ℝ)/1638400)/ClassicalSixthBranch.v ((3597241:ℝ)/1638400) = (7477834761:ℝ)/3819242632 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_566
  · change lowerPayment 567 ≤ lowerValue ((point 2 split 4096 567+point 2 split 4096 568)/2)
    have hp : lowerPayment 567 = (81828822098:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 567+point 2 split 4096 568)/2 = (74114817:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((74114817:ℝ)/33751040)/ClassicalSixthBranch.v ((74114817:ℝ)/33751040) = (770139666709:ℝ)/393333983208 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_567
  · change lowerPayment 568 ≤ lowerValue ((point 2 split 4096 568+point 2 split 4096 569)/2)
    have hp : lowerPayment 568 = (81956964178:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 568+point 2 split 4096 569)/2 = (370632347:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((370632347:ℝ)/168755200)/ClassicalSixthBranch.v ((370632347:ℝ)/168755200) = (154012470607:ℝ)/78657195064 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_568
  · change lowerPayment 569 ≤ lowerValue ((point 2 split 4096 569+point 2 split 4096 570)/2)
    have hp : lowerPayment 569 = (82085058922:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 569+point 2 split 4096 570)/2 = (370690609:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((370690609:ℝ)/168755200)/ClassicalSixthBranch.v ((370690609:ℝ)/168755200) = (769985039361:ℝ)/393237967432 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_569
  · change lowerPayment 570 ≤ lowerValue ((point 2 split 4096 570+point 2 split 4096 571)/2)
    have hp : lowerPayment 570 = (82213106373:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 570+point 2 split 4096 571)/2 = (370748871:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((370748871:ℝ)/168755200)/ClassicalSixthBranch.v ((370748871:ℝ)/168755200) = (769907725687:ℝ)/393189959544 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_570
  · change lowerPayment 571 ≤ lowerValue ((point 2 split 4096 571+point 2 split 4096 572)/2)
    have hp : lowerPayment 571 = (82341106573:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 571+point 2 split 4096 572)/2 = (370807133:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((370807133:ℝ)/168755200)/ClassicalSixthBranch.v ((370807133:ℝ)/168755200) = (769830412013:ℝ)/393141951656 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_571
  · change lowerPayment 572 ≤ lowerValue ((point 2 split 4096 572+point 2 split 4096 573)/2)
    have hp : lowerPayment 572 = (82469059563:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 572+point 2 split 4096 573)/2 = (74173079:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((74173079:ℝ)/33751040)/ClassicalSixthBranch.v ((74173079:ℝ)/33751040) = (769753098339:ℝ)/393093943768 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_572
  · change lowerPayment 573 ≤ lowerValue ((point 2 split 4096 573+point 2 split 4096 574)/2)
    have hp : lowerPayment 573 = (82596965386:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 573+point 2 split 4096 574)/2 = (370923657:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((370923657:ℝ)/168755200)/ClassicalSixthBranch.v ((370923657:ℝ)/168755200) = (153935156933:ℝ)/78609187176 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_573
  · change lowerPayment 574 ≤ lowerValue ((point 2 split 4096 574+point 2 split 4096 575)/2)
    have hp : lowerPayment 574 = (82724824084:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 574+point 2 split 4096 575)/2 = (370981919:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((370981919:ℝ)/168755200)/ClassicalSixthBranch.v ((370981919:ℝ)/168755200) = (769598470991:ℝ)/392997927992 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_574
  · change lowerPayment 575 ≤ lowerValue ((point 2 split 4096 575+point 2 split 4096 576)/2)
    have hp : lowerPayment 575 = (82852635698:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 575+point 2 split 4096 576)/2 = (371040181:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((371040181:ℝ)/168755200)/ClassicalSixthBranch.v ((371040181:ℝ)/168755200) = (769521157317:ℝ)/392949920104 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_575
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_035
