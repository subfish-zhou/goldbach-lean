import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints026
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_026 (j : Fin 16) (hj : 16*26+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*26+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*26+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 416) ≤ val WuPaper.ClassicalFourthData.Bq 416
    have hp : val WuPaper.ClassicalFourthData.Bq 416 = (47024690045107:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 416 = 47024690045107 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 416 = (263:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_416
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 417) ≤ val WuPaper.ClassicalFourthData.Bq 417
    have hp : val WuPaper.ClassicalFourthData.Bq 417 = (47126706187240:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 417 = 47126706187240 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 417 = (8417:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_417
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 418) ≤ val WuPaper.ClassicalFourthData.Bq 418
    have hp : val WuPaper.ClassicalFourthData.Bq 418 = (47228673736296:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 418 = 47228673736296 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 418 = (4209:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_418
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 419) ≤ val WuPaper.ClassicalFourthData.Bq 419
    have hp : val WuPaper.ClassicalFourthData.Bq 419 = (47330592720614:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 419 = 47330592720614 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 419 = (8419:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_419
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 420) ≤ val WuPaper.ClassicalFourthData.Bq 420
    have hp : val WuPaper.ClassicalFourthData.Bq 420 = (47432463168512:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 420 = 47432463168512 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 420 = (421:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_420
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 421) ≤ val WuPaper.ClassicalFourthData.Bq 421
    have hp : val WuPaper.ClassicalFourthData.Bq 421 = (47534285108285:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 421 = 47534285108285 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 421 = (8421:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_421
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 422) ≤ val WuPaper.ClassicalFourthData.Bq 422
    have hp : val WuPaper.ClassicalFourthData.Bq 422 = (47636058568209:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 422 = 47636058568209 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 422 = (4211:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_422
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 423) ≤ val WuPaper.ClassicalFourthData.Bq 423
    have hp : val WuPaper.ClassicalFourthData.Bq 423 = (47737783576540:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 423 = 47737783576540 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 423 = (8423:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_423
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 424) ≤ val WuPaper.ClassicalFourthData.Bq 424
    have hp : val WuPaper.ClassicalFourthData.Bq 424 = (47839460161512:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 424 = 47839460161512 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 424 = (1053:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_424
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 425) ≤ val WuPaper.ClassicalFourthData.Bq 425
    have hp : val WuPaper.ClassicalFourthData.Bq 425 = (47941088351337:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 425 = 47941088351337 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 425 = (337:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_425
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 426) ≤ val WuPaper.ClassicalFourthData.Bq 426
    have hp : val WuPaper.ClassicalFourthData.Bq 426 = (48042668174208:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 426 = 48042668174208 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 426 = (4213:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_426
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 427) ≤ val WuPaper.ClassicalFourthData.Bq 427
    have hp : val WuPaper.ClassicalFourthData.Bq 427 = (48144199658296:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 427 = 48144199658296 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 427 = (8427:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_427
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 428) ≤ val WuPaper.ClassicalFourthData.Bq 428
    have hp : val WuPaper.ClassicalFourthData.Bq 428 = (48245682831752:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 428 = 48245682831752 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 428 = (2107:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_428
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 429) ≤ val WuPaper.ClassicalFourthData.Bq 429
    have hp : val WuPaper.ClassicalFourthData.Bq 429 = (48347117722706:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 429 = 48347117722706 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 429 = (8429:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_429
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 430) ≤ val WuPaper.ClassicalFourthData.Bq 430
    have hp : val WuPaper.ClassicalFourthData.Bq 430 = (48448504359267:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 430 = 48448504359267 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 430 = (843:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_430
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 431) ≤ val WuPaper.ClassicalFourthData.Bq 431
    have hp : val WuPaper.ClassicalFourthData.Bq 431 = (48549842769523:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 431 = 48549842769523 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 431 = (8431:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_431
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_026
