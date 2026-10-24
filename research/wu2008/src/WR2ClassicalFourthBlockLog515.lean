import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints515
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_515 (j : Fin 16) (hj : 16*515+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*515+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*515+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8240) ≤ val WuPaper.ClassicalFourthData.Bq 8240
    have hp : val WuPaper.ClassicalFourthData.Bq 8240 = (275471654179428:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8240 = 275471654179428 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8240 = (203:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8240
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8241) ≤ val WuPaper.ClassicalFourthData.Bq 8241
    have hp : val WuPaper.ClassicalFourthData.Bq 8241 = (275474813614354:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8241 = 275474813614354 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8241 = (16241:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8241
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8242) ≤ val WuPaper.ClassicalFourthData.Bq 8242
    have hp : val WuPaper.ClassicalFourthData.Bq 8242 = (275477971016671:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8242 = 275477971016671 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8242 = (8121:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8242
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8243) ≤ val WuPaper.ClassicalFourthData.Bq 8243
    have hp : val WuPaper.ClassicalFourthData.Bq 8243 = (275481126387022:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8243 = 275481126387022 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8243 = (16243:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8243
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8244) ≤ val WuPaper.ClassicalFourthData.Bq 8244
    have hp : val WuPaper.ClassicalFourthData.Bq 8244 = (275484279726052:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8244 = 275484279726052 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8244 = (4061:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8244
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8245) ≤ val WuPaper.ClassicalFourthData.Bq 8245
    have hp : val WuPaper.ClassicalFourthData.Bq 8245 = (275487431034403:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8245 = 275487431034403 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8245 = (3249:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8245
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8246) ≤ val WuPaper.ClassicalFourthData.Bq 8246
    have hp : val WuPaper.ClassicalFourthData.Bq 8246 = (275490580312719:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8246 = 275490580312719 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8246 = (8123:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8246
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8247) ≤ val WuPaper.ClassicalFourthData.Bq 8247
    have hp : val WuPaper.ClassicalFourthData.Bq 8247 = (275493727561644:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8247 = 275493727561644 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8247 = (16247:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8247
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8248) ≤ val WuPaper.ClassicalFourthData.Bq 8248
    have hp : val WuPaper.ClassicalFourthData.Bq 8248 = (275496872781819:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8248 = 275496872781819 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8248 = (2031:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8248
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8249) ≤ val WuPaper.ClassicalFourthData.Bq 8249
    have hp : val WuPaper.ClassicalFourthData.Bq 8249 = (275500015973887:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8249 = 275500015973887 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8249 = (16249:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8249
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8250) ≤ val WuPaper.ClassicalFourthData.Bq 8250
    have hp : val WuPaper.ClassicalFourthData.Bq 8250 = (275503157138490:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8250 = 275503157138490 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8250 = (65:ℝ)/16 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8250
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8251) ≤ val WuPaper.ClassicalFourthData.Bq 8251
    have hp : val WuPaper.ClassicalFourthData.Bq 8251 = (275506296276272:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8251 = 275506296276272 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8251 = (16251:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8251
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8252) ≤ val WuPaper.ClassicalFourthData.Bq 8252
    have hp : val WuPaper.ClassicalFourthData.Bq 8252 = (275509433387873:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8252 = 275509433387873 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8252 = (4063:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8252
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8253) ≤ val WuPaper.ClassicalFourthData.Bq 8253
    have hp : val WuPaper.ClassicalFourthData.Bq 8253 = (275512568473935:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8253 = 275512568473935 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8253 = (16253:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8253
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8254) ≤ val WuPaper.ClassicalFourthData.Bq 8254
    have hp : val WuPaper.ClassicalFourthData.Bq 8254 = (275515701535100:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8254 = 275515701535100 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8254 = (8127:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8254
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8255) ≤ val WuPaper.ClassicalFourthData.Bq 8255
    have hp : val WuPaper.ClassicalFourthData.Bq 8255 = (275518832572009:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8255 = 275518832572009 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8255 = (3251:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8255
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_515
