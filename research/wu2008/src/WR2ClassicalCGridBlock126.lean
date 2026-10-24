import WR2ClassicalCPayments
import WR2ClassicalCPoints126
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_126 (j : Fin 16) : cPayment (16*126+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*126+j.val)+point (1327/200) 4096 (16*126+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2016 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2016+point (1327/200) 4096 2017)/2)
    have hp : cPayment 2016 = (68364363383:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2016+point (1327/200) 4096 2017)/2 = (5402191:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2016
  · change cPayment 2017 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2017+point (1327/200) 4096 2018)/2)
    have hp : cPayment 2017 = (68336274130:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2017+point (1327/200) 4096 2018)/2 = (1080649:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2017
  · change cPayment 2018 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2018+point (1327/200) 4096 2019)/2)
    have hp : cPayment 2018 = (68308169641:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2018+point (1327/200) 4096 2019)/2 = (5404299:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2018
  · change cPayment 2019 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2019+point (1327/200) 4096 2020)/2)
    have hp : cPayment 2019 = (68280049942:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2019+point (1327/200) 4096 2020)/2 = (5405353:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2019
  · change cPayment 2020 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2020+point (1327/200) 4096 2021)/2)
    have hp : cPayment 2020 = (68251915061:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2020+point (1327/200) 4096 2021)/2 = (5406407:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2020
  · change cPayment 2021 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2021+point (1327/200) 4096 2022)/2)
    have hp : cPayment 2021 = (68223765024:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2021+point (1327/200) 4096 2022)/2 = (5407461:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2021
  · change cPayment 2022 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2022+point (1327/200) 4096 2023)/2)
    have hp : cPayment 2022 = (68195599860:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2022+point (1327/200) 4096 2023)/2 = (1081703:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2022
  · change cPayment 2023 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2023+point (1327/200) 4096 2024)/2)
    have hp : cPayment 2023 = (68167419594:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2023+point (1327/200) 4096 2024)/2 = (5409569:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2023
  · change cPayment 2024 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2024+point (1327/200) 4096 2025)/2)
    have hp : cPayment 2024 = (68139224254:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2024+point (1327/200) 4096 2025)/2 = (5410623:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2024
  · change cPayment 2025 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2025+point (1327/200) 4096 2026)/2)
    have hp : cPayment 2025 = (68111013866:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2025+point (1327/200) 4096 2026)/2 = (5411677:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2025
  · change cPayment 2026 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2026+point (1327/200) 4096 2027)/2)
    have hp : cPayment 2026 = (68082788458:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2026+point (1327/200) 4096 2027)/2 = (5412731:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2026
  · change cPayment 2027 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2027+point (1327/200) 4096 2028)/2)
    have hp : cPayment 2027 = (68054548057:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2027+point (1327/200) 4096 2028)/2 = (1082757:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2027
  · change cPayment 2028 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2028+point (1327/200) 4096 2029)/2)
    have hp : cPayment 2028 = (68026292690:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2028+point (1327/200) 4096 2029)/2 = (5414839:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2028
  · change cPayment 2029 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2029+point (1327/200) 4096 2030)/2)
    have hp : cPayment 2029 = (67998022382:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2029+point (1327/200) 4096 2030)/2 = (5415893:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2029
  · change cPayment 2030 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2030+point (1327/200) 4096 2031)/2)
    have hp : cPayment 2030 = (67969737162:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2030+point (1327/200) 4096 2031)/2 = (5416947:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2030
  · change cPayment 2031 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2031+point (1327/200) 4096 2032)/2)
    have hp : cPayment 2031 = (67941437056:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2031+point (1327/200) 4096 2032)/2 = (5418001:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2031
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_126
