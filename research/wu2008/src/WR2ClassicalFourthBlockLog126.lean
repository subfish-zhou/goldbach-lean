import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints126
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_126 (j : Fin 16) (hj : 16*126+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*126+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*126+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2016) ≤ val WuPaper.ClassicalFourthData.Bq 2016
    have hp : val WuPaper.ClassicalFourthData.Bq 2016 = (162990505402416:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2016 = 162990505402416 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2016 = (313:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2016
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2017) ≤ val WuPaper.ClassicalFourthData.Bq 2017
    have hp : val WuPaper.ClassicalFourthData.Bq 2017 = (163040605018798:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2017 = 163040605018798 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2017 = (10017:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2017
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2018) ≤ val WuPaper.ClassicalFourthData.Bq 2018
    have hp : val WuPaper.ClassicalFourthData.Bq 2018 = (163090683604697:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2018 = 163090683604697 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2018 = (5009:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2018
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2019) ≤ val WuPaper.ClassicalFourthData.Bq 2019
    have hp : val WuPaper.ClassicalFourthData.Bq 2019 = (163140741170075:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2019 = 163140741170075 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2019 = (10019:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2019
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2020) ≤ val WuPaper.ClassicalFourthData.Bq 2020
    have hp : val WuPaper.ClassicalFourthData.Bq 2020 = (163190777724886:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2020 = 163190777724886 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2020 = (501:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2020
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2021) ≤ val WuPaper.ClassicalFourthData.Bq 2021
    have hp : val WuPaper.ClassicalFourthData.Bq 2021 = (163240793279082:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2021 = 163240793279082 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2021 = (10021:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2021
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2022) ≤ val WuPaper.ClassicalFourthData.Bq 2022
    have hp : val WuPaper.ClassicalFourthData.Bq 2022 = (163290787842607:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2022 = 163290787842607 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2022 = (5011:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2022
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2023) ≤ val WuPaper.ClassicalFourthData.Bq 2023
    have hp : val WuPaper.ClassicalFourthData.Bq 2023 = (163340761425399:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2023 = 163340761425399 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2023 = (10023:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2023
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2024) ≤ val WuPaper.ClassicalFourthData.Bq 2024
    have hp : val WuPaper.ClassicalFourthData.Bq 2024 = (163390714037391:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2024 = 163390714037391 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2024 = (1253:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2024
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2025) ≤ val WuPaper.ClassicalFourthData.Bq 2025
    have hp : val WuPaper.ClassicalFourthData.Bq 2025 = (163440645688510:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2025 = 163440645688510 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2025 = (401:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2025
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2026) ≤ val WuPaper.ClassicalFourthData.Bq 2026
    have hp : val WuPaper.ClassicalFourthData.Bq 2026 = (163490556388677:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2026 = 163490556388677 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2026 = (5013:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2026
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2027) ≤ val WuPaper.ClassicalFourthData.Bq 2027
    have hp : val WuPaper.ClassicalFourthData.Bq 2027 = (163540446147808:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2027 = 163540446147808 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2027 = (10027:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2027
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2028) ≤ val WuPaper.ClassicalFourthData.Bq 2028
    have hp : val WuPaper.ClassicalFourthData.Bq 2028 = (163590314975812:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2028 = 163590314975812 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2028 = (2507:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2028
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2029) ≤ val WuPaper.ClassicalFourthData.Bq 2029
    have hp : val WuPaper.ClassicalFourthData.Bq 2029 = (163640162882592:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2029 = 163640162882592 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2029 = (10029:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2029
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2030) ≤ val WuPaper.ClassicalFourthData.Bq 2030
    have hp : val WuPaper.ClassicalFourthData.Bq 2030 = (163689989878048:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2030 = 163689989878048 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2030 = (1003:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2030
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2031) ≤ val WuPaper.ClassicalFourthData.Bq 2031
    have hp : val WuPaper.ClassicalFourthData.Bq 2031 = (163739795972071:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2031 = 163739795972071 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2031 = (10031:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2031
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_126
