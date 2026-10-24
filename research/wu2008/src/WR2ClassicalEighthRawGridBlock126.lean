import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints126
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_126 (j : Fin 16) : upperValue ((point (16*126+j.val)+point ((16*126+j.val)+1))/2) ≤ payment (16*126+j.val) := by
  fin_cases j
  · change upperValue ((point (2016)+point ((2016)+1))/2) ≤ payment (2016)
    have hp : payment 2016 = (53572762681:ℝ)/1000000000000 := rfl
    have hx : (point 2016+point 2017)/2 = (5370691:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2016
  · change upperValue ((point (2017)+point ((2017)+1))/2) ≤ payment (2017)
    have hp : payment 2017 = (51871655947:ℝ)/1000000000000 := rfl
    have hx : (point 2017+point 2018)/2 = (1790915:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2017
  · change upperValue ((point (2018)+point ((2018)+1))/2) ≤ payment (2018)
    have hp : payment 2018 = (50170586430:ℝ)/1000000000000 := rfl
    have hx : (point 2018+point 2019)/2 = (5374799:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2018
  · change upperValue ((point (2019)+point ((2019)+1))/2) ≤ payment (2019)
    have hp : payment 2019 = (48469552904:ℝ)/1000000000000 := rfl
    have hx : (point 2019+point 2020)/2 = (5376853:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2019
  · change upperValue ((point (2020)+point ((2020)+1))/2) ≤ payment (2020)
    have hp : payment 2020 = (46768554143:ℝ)/1000000000000 := rfl
    have hx : (point 2020+point 2021)/2 = (1792969:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2020
  · change upperValue ((point (2021)+point ((2021)+1))/2) ≤ payment (2021)
    have hp : payment 2021 = (45067588923:ℝ)/1000000000000 := rfl
    have hx : (point 2021+point 2022)/2 = (5380961:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2021
  · change upperValue ((point (2022)+point ((2022)+1))/2) ≤ payment (2022)
    have hp : payment 2022 = (43366656016:ℝ)/1000000000000 := rfl
    have hx : (point 2022+point 2023)/2 = (5383015:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2022
  · change upperValue ((point (2023)+point ((2023)+1))/2) ≤ payment (2023)
    have hp : payment 2023 = (41665754199:ℝ)/1000000000000 := rfl
    have hx : (point 2023+point 2024)/2 = (1795023:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2023
  · change upperValue ((point (2024)+point ((2024)+1))/2) ≤ payment (2024)
    have hp : payment 2024 = (39964882248:ℝ)/1000000000000 := rfl
    have hx : (point 2024+point 2025)/2 = (5387123:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2024
  · change upperValue ((point (2025)+point ((2025)+1))/2) ≤ payment (2025)
    have hp : payment 2025 = (38264038938:ℝ)/1000000000000 := rfl
    have hx : (point 2025+point 2026)/2 = (5389177:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2025
  · change upperValue ((point (2026)+point ((2026)+1))/2) ≤ payment (2026)
    have hp : payment 2026 = (36563223046:ℝ)/1000000000000 := rfl
    have hx : (point 2026+point 2027)/2 = (1797077:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2026
  · change upperValue ((point (2027)+point ((2027)+1))/2) ≤ payment (2027)
    have hp : payment 2027 = (34862433349:ℝ)/1000000000000 := rfl
    have hx : (point 2027+point 2028)/2 = (5393285:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2027
  · change upperValue ((point (2028)+point ((2028)+1))/2) ≤ payment (2028)
    have hp : payment 2028 = (33161668624:ℝ)/1000000000000 := rfl
    have hx : (point 2028+point 2029)/2 = (5395339:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2028
  · change upperValue ((point (2029)+point ((2029)+1))/2) ≤ payment (2029)
    have hp : payment 2029 = (31460927651:ℝ)/1000000000000 := rfl
    have hx : (point 2029+point 2030)/2 = (1799131:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2029
  · change upperValue ((point (2030)+point ((2030)+1))/2) ≤ payment (2030)
    have hp : payment 2030 = (29760209205:ℝ)/1000000000000 := rfl
    have hx : (point 2030+point 2031)/2 = (5399447:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2030
  · change upperValue ((point (2031)+point ((2031)+1))/2) ≤ payment (2031)
    have hp : payment 2031 = (28059512067:ℝ)/1000000000000 := rfl
    have hx : (point 2031+point 2032)/2 = (5401501:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2031
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_126
