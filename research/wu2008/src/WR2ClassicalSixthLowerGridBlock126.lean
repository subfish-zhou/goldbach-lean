import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints126
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_126 (j : Fin 16) : lowerPayment (16*126+j.val) ≤
    lowerValue ((point 2 split 4096 (16*126+j.val)+point 2 split 4096 (16*126+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2016 ≤ lowerValue ((point 2 split 4096 2016+point 2 split 4096 2017)/2)
    have hp : lowerPayment 2016 = (234168896003:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2016+point 2 split 4096 2017)/2 = (454995723:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((454995723:ℝ)/168755200)/ClassicalSixthBranch.v ((454995723:ℝ)/168755200) = (658112153083:ℝ)/323770553496 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2016
  · change lowerPayment 2017 ≤ lowerValue ((point 2 split 4096 2017+point 2 split 4096 2018)/2)
    have hp : lowerPayment 2017 = (234259804645:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2017+point 2 split 4096 2018)/2 = (91010797:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((91010797:ℝ)/33751040)/ClassicalSixthBranch.v ((91010797:ℝ)/33751040) = (658034839409:ℝ)/323722545608 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2017
  · change lowerPayment 2018 ≤ lowerValue ((point 2 split 4096 2018+point 2 split 4096 2019)/2)
    have hp : lowerPayment 2018 = (234350703390:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2018+point 2 split 4096 2019)/2 = (455112247:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((455112247:ℝ)/168755200)/ClassicalSixthBranch.v ((455112247:ℝ)/168755200) = (131591505147:ℝ)/64734907544 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2018
  · change lowerPayment 2019 ≤ lowerValue ((point 2 split 4096 2019+point 2 split 4096 2020)/2)
    have hp : lowerPayment 2019 = (234441592254:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2019+point 2 split 4096 2020)/2 = (455170509:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((455170509:ℝ)/168755200)/ClassicalSixthBranch.v ((455170509:ℝ)/168755200) = (657880212061:ℝ)/323626529832 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2019
  · change lowerPayment 2020 ≤ lowerValue ((point 2 split 4096 2020+point 2 split 4096 2021)/2)
    have hp : lowerPayment 2020 = (234532471255:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2020+point 2 split 4096 2021)/2 = (455228771:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((455228771:ℝ)/168755200)/ClassicalSixthBranch.v ((455228771:ℝ)/168755200) = (657802898387:ℝ)/323578521944 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2020
  · change lowerPayment 2021 ≤ lowerValue ((point 2 split 4096 2021+point 2 split 4096 2022)/2)
    have hp : lowerPayment 2021 = (234623340407:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2021+point 2 split 4096 2022)/2 = (455287033:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((455287033:ℝ)/168755200)/ClassicalSixthBranch.v ((455287033:ℝ)/168755200) = (657725584713:ℝ)/323530514056 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2021
  · change lowerPayment 2022 ≤ lowerValue ((point 2 split 4096 2022+point 2 split 4096 2023)/2)
    have hp : lowerPayment 2022 = (234714199729:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2022+point 2 split 4096 2023)/2 = (91069059:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((91069059:ℝ)/33751040)/ClassicalSixthBranch.v ((91069059:ℝ)/33751040) = (657648271039:ℝ)/323482506168 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2022
  · change lowerPayment 2023 ≤ lowerValue ((point 2 split 4096 2023+point 2 split 4096 2024)/2)
    have hp : lowerPayment 2023 = (234805049237:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2023+point 2 split 4096 2024)/2 = (455403557:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((455403557:ℝ)/168755200)/ClassicalSixthBranch.v ((455403557:ℝ)/168755200) = (131514191473:ℝ)/64686899656 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2023
  · change lowerPayment 2024 ≤ lowerValue ((point 2 split 4096 2024+point 2 split 4096 2025)/2)
    have hp : lowerPayment 2024 = (234895888946:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2024+point 2 split 4096 2025)/2 = (455461819:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((455461819:ℝ)/168755200)/ClassicalSixthBranch.v ((455461819:ℝ)/168755200) = (657493643691:ℝ)/323386490392 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2024
  · change lowerPayment 2025 ≤ lowerValue ((point 2 split 4096 2025+point 2 split 4096 2026)/2)
    have hp : lowerPayment 2025 = (234986718875:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2025+point 2 split 4096 2026)/2 = (455520081:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((455520081:ℝ)/168755200)/ClassicalSixthBranch.v ((455520081:ℝ)/168755200) = (657416330017:ℝ)/323338482504 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2025
  · change lowerPayment 2026 ≤ lowerValue ((point 2 split 4096 2026+point 2 split 4096 2027)/2)
    have hp : lowerPayment 2026 = (235077539039:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2026+point 2 split 4096 2027)/2 = (455578343:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((455578343:ℝ)/168755200)/ClassicalSixthBranch.v ((455578343:ℝ)/168755200) = (657339016343:ℝ)/323290474616 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2026
  · change lowerPayment 2027 ≤ lowerValue ((point 2 split 4096 2027+point 2 split 4096 2028)/2)
    have hp : lowerPayment 2027 = (235168349454:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2027+point 2 split 4096 2028)/2 = (91127321:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((91127321:ℝ)/33751040)/ClassicalSixthBranch.v ((91127321:ℝ)/33751040) = (657261702669:ℝ)/323242466728 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2027
  · change lowerPayment 2028 ≤ lowerValue ((point 2 split 4096 2028+point 2 split 4096 2029)/2)
    have hp : lowerPayment 2028 = (235259150139:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2028+point 2 split 4096 2029)/2 = (455694867:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((455694867:ℝ)/168755200)/ClassicalSixthBranch.v ((455694867:ℝ)/168755200) = (131436877799:ℝ)/64638891768 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2028
  · change lowerPayment 2029 ≤ lowerValue ((point 2 split 4096 2029+point 2 split 4096 2030)/2)
    have hp : lowerPayment 2029 = (235349941108:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2029+point 2 split 4096 2030)/2 = (455753129:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((455753129:ℝ)/168755200)/ClassicalSixthBranch.v ((455753129:ℝ)/168755200) = (657107075321:ℝ)/323146450952 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2029
  · change lowerPayment 2030 ≤ lowerValue ((point 2 split 4096 2030+point 2 split 4096 2031)/2)
    have hp : lowerPayment 2030 = (235440722378:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2030+point 2 split 4096 2031)/2 = (455811391:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((455811391:ℝ)/168755200)/ClassicalSixthBranch.v ((455811391:ℝ)/168755200) = (657029761647:ℝ)/323098443064 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2030
  · change lowerPayment 2031 ≤ lowerValue ((point 2 split 4096 2031+point 2 split 4096 2032)/2)
    have hp : lowerPayment 2031 = (235531493967:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2031+point 2 split 4096 2032)/2 = (455869653:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((455869653:ℝ)/168755200)/ClassicalSixthBranch.v ((455869653:ℝ)/168755200) = (656952447973:ℝ)/323050435176 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2031
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_126
