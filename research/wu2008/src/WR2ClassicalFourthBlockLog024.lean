import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints024
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_024 (j : Fin 16) (hj : 16*24+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*24+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*24+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 384) ≤ val WuPaper.ClassicalFourthData.Bq 384
    have hp : val WuPaper.ClassicalFourthData.Bq 384 = (43734345670718:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 384 = 43734345670718 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 384 = (262:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_384
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 385) ≤ val WuPaper.ClassicalFourthData.Bq 385
    have hp : val WuPaper.ClassicalFourthData.Bq 385 = (43837931880385:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 385 = 43837931880385 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 385 = (1677:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_385
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 386) ≤ val WuPaper.ClassicalFourthData.Bq 386
    have hp : val WuPaper.ClassicalFourthData.Bq 386 = (43941468578968:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 386 = 43941468578968 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 386 = (4193:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_386
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 387) ≤ val WuPaper.ClassicalFourthData.Bq 387
    have hp : val WuPaper.ClassicalFourthData.Bq 387 = (44044955795487:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 387 = 44044955795487 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 387 = (8387:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_387
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 388) ≤ val WuPaper.ClassicalFourthData.Bq 388
    have hp : val WuPaper.ClassicalFourthData.Bq 388 = (44148393558939:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 388 = 44148393558939 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 388 = (2097:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_388
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 389) ≤ val WuPaper.ClassicalFourthData.Bq 389
    have hp : val WuPaper.ClassicalFourthData.Bq 389 = (44251781898299:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 389 = 44251781898299 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 389 = (8389:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_389
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 390) ≤ val WuPaper.ClassicalFourthData.Bq 390
    have hp : val WuPaper.ClassicalFourthData.Bq 390 = (44355120842522:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 390 = 44355120842522 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 390 = (839:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_390
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 391) ≤ val WuPaper.ClassicalFourthData.Bq 391
    have hp : val WuPaper.ClassicalFourthData.Bq 391 = (44458410420541:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 391 = 44458410420541 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 391 = (8391:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_391
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 392) ≤ val WuPaper.ClassicalFourthData.Bq 392
    have hp : val WuPaper.ClassicalFourthData.Bq 392 = (44561650661268:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 392 = 44561650661268 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 392 = (1049:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_392
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 393) ≤ val WuPaper.ClassicalFourthData.Bq 393
    have hp : val WuPaper.ClassicalFourthData.Bq 393 = (44664841593591:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 393 = 44664841593591 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 393 = (8393:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_393
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 394) ≤ val WuPaper.ClassicalFourthData.Bq 394
    have hp : val WuPaper.ClassicalFourthData.Bq 394 = (44767983246380:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 394 = 44767983246380 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 394 = (4197:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_394
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 395) ≤ val WuPaper.ClassicalFourthData.Bq 395
    have hp : val WuPaper.ClassicalFourthData.Bq 395 = (44871075648482:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 395 = 44871075648482 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 395 = (1679:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_395
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 396) ≤ val WuPaper.ClassicalFourthData.Bq 396
    have hp : val WuPaper.ClassicalFourthData.Bq 396 = (44974118828721:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 396 = 44974118828721 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 396 = (2099:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_396
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 397) ≤ val WuPaper.ClassicalFourthData.Bq 397
    have hp : val WuPaper.ClassicalFourthData.Bq 397 = (45077112815903:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 397 = 45077112815903 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 397 = (8397:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_397
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 398) ≤ val WuPaper.ClassicalFourthData.Bq 398
    have hp : val WuPaper.ClassicalFourthData.Bq 398 = (45180057638809:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 398 = 45180057638809 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 398 = (4199:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_398
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 399) ≤ val WuPaper.ClassicalFourthData.Bq 399
    have hp : val WuPaper.ClassicalFourthData.Bq 399 = (45282953326202:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 399 = 45282953326202 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 399 = (8399:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_399
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_024
