import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints126
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_126 (j : Fin 16) : upperPayment (16*126+j.val) ≤
    upperValue ((point split endpoint 4096 (16*126+j.val)+point split endpoint 4096 (16*126+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2016 ≤ upperValue ((point split endpoint 4096 2016+point split endpoint 4096 2017)/2)
    have hp : upperPayment 2016 = (272399022954:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2016+point split endpoint 4096 2017)/2 = (626866527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((626866527:ℝ)/168755200)*ClassicalSixthBranch.v ((626866527:ℝ)/168755200)/ClassicalSixthBranch.r = (114619130872785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2016
  · change upperPayment 2017 ≤ upperValue ((point split endpoint 4096 2017+point split endpoint 4096 2018)/2)
    have hp : upperPayment 2017 = (272300059914:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2017+point split endpoint 4096 2018)/2 = (626891677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((626891677:ℝ)/168755200)*ClassicalSixthBranch.v ((626891677:ℝ)/168755200)/ClassicalSixthBranch.r = (114597196109145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2017
  · change upperPayment 2018 ≤ upperValue ((point split endpoint 4096 2018+point split endpoint 4096 2019)/2)
    have hp : upperPayment 2018 = (272201070564:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2018+point split endpoint 4096 2019)/2 = (626916827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((626916827:ℝ)/168755200)*ClassicalSixthBranch.v ((626916827:ℝ)/168755200)/ClassicalSixthBranch.r = (114575263369577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2018
  · change upperPayment 2019 ≤ upperValue ((point split endpoint 4096 2019+point split endpoint 4096 2020)/2)
    have hp : upperPayment 2019 = (272102054900:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2019+point split endpoint 4096 2020)/2 = (626941977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((626941977:ℝ)/168755200)*ClassicalSixthBranch.v ((626941977:ℝ)/168755200)/ClassicalSixthBranch.r = (114553332654081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2019
  · change upperPayment 2020 ≤ upperValue ((point split endpoint 4096 2020+point split endpoint 4096 2021)/2)
    have hp : upperPayment 2020 = (272003012917:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2020+point split endpoint 4096 2021)/2 = (626967127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((626967127:ℝ)/168755200)*ClassicalSixthBranch.v ((626967127:ℝ)/168755200)/ClassicalSixthBranch.r = (114531403962657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2020
  · change upperPayment 2021 ≤ upperValue ((point split endpoint 4096 2021+point split endpoint 4096 2022)/2)
    have hp : upperPayment 2021 = (271903944610:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2021+point split endpoint 4096 2022)/2 = (626992277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((626992277:ℝ)/168755200)*ClassicalSixthBranch.v ((626992277:ℝ)/168755200)/ClassicalSixthBranch.r = (114509477295305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2021
  · change upperPayment 2022 ≤ upperValue ((point split endpoint 4096 2022+point split endpoint 4096 2023)/2)
    have hp : upperPayment 2022 = (271804849972:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2022+point split endpoint 4096 2023)/2 = (627017427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((627017427:ℝ)/168755200)*ClassicalSixthBranch.v ((627017427:ℝ)/168755200)/ClassicalSixthBranch.r = (114487552652025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2022
  · change upperPayment 2023 ≤ upperValue ((point split endpoint 4096 2023+point split endpoint 4096 2024)/2)
    have hp : upperPayment 2023 = (271705728999:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2023+point split endpoint 4096 2024)/2 = (627042577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((627042577:ℝ)/168755200)*ClassicalSixthBranch.v ((627042577:ℝ)/168755200)/ClassicalSixthBranch.r = (114465630032817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2023
  · change upperPayment 2024 ≤ upperValue ((point split endpoint 4096 2024+point split endpoint 4096 2025)/2)
    have hp : upperPayment 2024 = (271606581686:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2024+point split endpoint 4096 2025)/2 = (627067727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((627067727:ℝ)/168755200)*ClassicalSixthBranch.v ((627067727:ℝ)/168755200)/ClassicalSixthBranch.r = (114443709437681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2024
  · change upperPayment 2025 ≤ upperValue ((point split endpoint 4096 2025+point split endpoint 4096 2026)/2)
    have hp : upperPayment 2025 = (271507408028:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2025+point split endpoint 4096 2026)/2 = (627092877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((627092877:ℝ)/168755200)*ClassicalSixthBranch.v ((627092877:ℝ)/168755200)/ClassicalSixthBranch.r = (114421790866617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2025
  · change upperPayment 2026 ≤ upperValue ((point split endpoint 4096 2026+point split endpoint 4096 2027)/2)
    have hp : upperPayment 2026 = (271408208019:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2026+point split endpoint 4096 2027)/2 = (627118027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((627118027:ℝ)/168755200)*ClassicalSixthBranch.v ((627118027:ℝ)/168755200)/ClassicalSixthBranch.r = (114399874319625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2026
  · change upperPayment 2027 ≤ upperValue ((point split endpoint 4096 2027+point split endpoint 4096 2028)/2)
    have hp : upperPayment 2027 = (271308981653:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2027+point split endpoint 4096 2028)/2 = (627143177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((627143177:ℝ)/168755200)*ClassicalSixthBranch.v ((627143177:ℝ)/168755200)/ClassicalSixthBranch.r = (114377959796705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2027
  · change upperPayment 2028 ≤ upperValue ((point split endpoint 4096 2028+point split endpoint 4096 2029)/2)
    have hp : upperPayment 2028 = (271209728927:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2028+point split endpoint 4096 2029)/2 = (627168327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((627168327:ℝ)/168755200)*ClassicalSixthBranch.v ((627168327:ℝ)/168755200)/ClassicalSixthBranch.r = (114356047297857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2028
  · change upperPayment 2029 ≤ upperValue ((point split endpoint 4096 2029+point split endpoint 4096 2030)/2)
    have hp : upperPayment 2029 = (271110449834:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2029+point split endpoint 4096 2030)/2 = (627193477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((627193477:ℝ)/168755200)*ClassicalSixthBranch.v ((627193477:ℝ)/168755200)/ClassicalSixthBranch.r = (114334136823081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2029
  · change upperPayment 2030 ≤ upperValue ((point split endpoint 4096 2030+point split endpoint 4096 2031)/2)
    have hp : upperPayment 2030 = (271011144369:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2030+point split endpoint 4096 2031)/2 = (627218627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((627218627:ℝ)/168755200)*ClassicalSixthBranch.v ((627218627:ℝ)/168755200)/ClassicalSixthBranch.r = (114312228372377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2030
  · change upperPayment 2031 ≤ upperValue ((point split endpoint 4096 2031+point split endpoint 4096 2032)/2)
    have hp : upperPayment 2031 = (270911812528:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2031+point split endpoint 4096 2032)/2 = (627243777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((627243777:ℝ)/168755200)*ClassicalSixthBranch.v ((627243777:ℝ)/168755200)/ClassicalSixthBranch.r = (114290321945745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2031
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_126
