import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints151
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_151 (j : Fin 16) (hj : 16*151+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*151+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*151+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2416) ≤ val WuPaper.ClassicalFourthData.Bq 2416
    have hp : val WuPaper.ClassicalFourthData.Bq 2416 = (181451808542367:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2416 = 181451808542367 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2416 = (651:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2416
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2417) ≤ val WuPaper.ClassicalFourthData.Bq 2417
    have hp : val WuPaper.ClassicalFourthData.Bq 2417 = (181494233521547:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2417 = 181494233521547 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2417 = (10417:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2417
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2418) ≤ val WuPaper.ClassicalFourthData.Bq 2418
    have hp : val WuPaper.ClassicalFourthData.Bq 2418 = (181536641031974:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2418 = 181536641031974 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2418 = (5209:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2418
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2419) ≤ val WuPaper.ClassicalFourthData.Bq 2419
    have hp : val WuPaper.ClassicalFourthData.Bq 2419 = (181579031081582:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2419 = 181579031081582 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2419 = (10419:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2419
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2420) ≤ val WuPaper.ClassicalFourthData.Bq 2420
    have hp : val WuPaper.ClassicalFourthData.Bq 2420 = (181621403678303:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2420 = 181621403678303 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2420 = (521:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2420
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2421) ≤ val WuPaper.ClassicalFourthData.Bq 2421
    have hp : val WuPaper.ClassicalFourthData.Bq 2421 = (181663758830063:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2421 = 181663758830063 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2421 = (10421:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2421
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2422) ≤ val WuPaper.ClassicalFourthData.Bq 2422
    have hp : val WuPaper.ClassicalFourthData.Bq 2422 = (181706096544783:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2422 = 181706096544783 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2422 = (5211:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2422
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2423) ≤ val WuPaper.ClassicalFourthData.Bq 2423
    have hp : val WuPaper.ClassicalFourthData.Bq 2423 = (181748416830381:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2423 = 181748416830381 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2423 = (10423:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2423
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2424) ≤ val WuPaper.ClassicalFourthData.Bq 2424
    have hp : val WuPaper.ClassicalFourthData.Bq 2424 = (181790719694770:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2424 = 181790719694770 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2424 = (1303:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2424
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2425) ≤ val WuPaper.ClassicalFourthData.Bq 2425
    have hp : val WuPaper.ClassicalFourthData.Bq 2425 = (181833005145859:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2425 = 181833005145859 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2425 = (417:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2425
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2426) ≤ val WuPaper.ClassicalFourthData.Bq 2426
    have hp : val WuPaper.ClassicalFourthData.Bq 2426 = (181875273191551:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2426 = 181875273191551 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2426 = (5213:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2426
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2427) ≤ val WuPaper.ClassicalFourthData.Bq 2427
    have hp : val WuPaper.ClassicalFourthData.Bq 2427 = (181917523839747:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2427 = 181917523839747 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2427 = (10427:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2427
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2428) ≤ val WuPaper.ClassicalFourthData.Bq 2428
    have hp : val WuPaper.ClassicalFourthData.Bq 2428 = (181959757098342:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2428 = 181959757098342 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2428 = (2607:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2428
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2429) ≤ val WuPaper.ClassicalFourthData.Bq 2429
    have hp : val WuPaper.ClassicalFourthData.Bq 2429 = (182001972975227:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2429 = 182001972975227 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2429 = (10429:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2429
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2430) ≤ val WuPaper.ClassicalFourthData.Bq 2430
    have hp : val WuPaper.ClassicalFourthData.Bq 2430 = (182044171478289:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2430 = 182044171478289 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2430 = (1043:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2430
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2431) ≤ val WuPaper.ClassicalFourthData.Bq 2431
    have hp : val WuPaper.ClassicalFourthData.Bq 2431 = (182086352615411:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2431 = 182086352615411 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2431 = (10431:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2431
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_151
