import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints128
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_128 (j : Fin 16) : lowerPayment (16*128+j.val) ≤
    lowerValue ((point 2 split 4096 (16*128+j.val)+point 2 split 4096 (16*128+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2048 ≤ lowerValue ((point 2 split 4096 2048+point 2 split 4096 2049)/2)
    have hp : lowerPayment 2048 = (237073145620:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2048+point 2 split 4096 2049)/2 = (456860107:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((456860107:ℝ)/168755200)/ClassicalSixthBranch.v ((456860107:ℝ)/168755200) = (131127623103:ℝ)/64446860216 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2048
  · change lowerPayment 2049 ≤ lowerValue ((point 2 split 4096 2049+point 2 split 4096 2050)/2)
    have hp : lowerPayment 2049 = (237163745752:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2049+point 2 split 4096 2050)/2 = (456918369:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((456918369:ℝ)/168755200)/ClassicalSixthBranch.v ((456918369:ℝ)/168755200) = (655560801841:ℝ)/322186293192 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2049
  · change lowerPayment 2050 ≤ lowerValue ((point 2 split 4096 2050+point 2 split 4096 2051)/2)
    have hp : lowerPayment 2050 = (237254336516:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2050+point 2 split 4096 2051)/2 = (456976631:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((456976631:ℝ)/168755200)/ClassicalSixthBranch.v ((456976631:ℝ)/168755200) = (655483488167:ℝ)/322138285304 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2050
  · change lowerPayment 2051 ≤ lowerValue ((point 2 split 4096 2051+point 2 split 4096 2052)/2)
    have hp : lowerPayment 2051 = (237344917927:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2051+point 2 split 4096 2052)/2 = (457034893:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((457034893:ℝ)/168755200)/ClassicalSixthBranch.v ((457034893:ℝ)/168755200) = (655406174493:ℝ)/322090277416 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2051
  · change lowerPayment 2052 ≤ lowerValue ((point 2 split 4096 2052+point 2 split 4096 2053)/2)
    have hp : lowerPayment 2052 = (237435490001:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2052+point 2 split 4096 2053)/2 = (91418631:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((91418631:ℝ)/33751040)/ClassicalSixthBranch.v ((91418631:ℝ)/33751040) = (655328860819:ℝ)/322042269528 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2052
  · change lowerPayment 2053 ≤ lowerValue ((point 2 split 4096 2053+point 2 split 4096 2054)/2)
    have hp : lowerPayment 2053 = (237526052755:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2053+point 2 split 4096 2054)/2 = (457151417:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((457151417:ℝ)/168755200)/ClassicalSixthBranch.v ((457151417:ℝ)/168755200) = (131050309429:ℝ)/64398852328 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2053
  · change lowerPayment 2054 ≤ lowerValue ((point 2 split 4096 2054+point 2 split 4096 2055)/2)
    have hp : lowerPayment 2054 = (237616606206:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2054+point 2 split 4096 2055)/2 = (457209679:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((457209679:ℝ)/168755200)/ClassicalSixthBranch.v ((457209679:ℝ)/168755200) = (655174233471:ℝ)/321946253752 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2054
  · change lowerPayment 2055 ≤ lowerValue ((point 2 split 4096 2055+point 2 split 4096 2056)/2)
    have hp : lowerPayment 2055 = (237707150370:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2055+point 2 split 4096 2056)/2 = (457267941:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((457267941:ℝ)/168755200)/ClassicalSixthBranch.v ((457267941:ℝ)/168755200) = (655096919797:ℝ)/321898245864 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2055
  · change lowerPayment 2056 ≤ lowerValue ((point 2 split 4096 2056+point 2 split 4096 2057)/2)
    have hp : lowerPayment 2056 = (237797685263:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2056+point 2 split 4096 2057)/2 = (457326203:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((457326203:ℝ)/168755200)/ClassicalSixthBranch.v ((457326203:ℝ)/168755200) = (655019606123:ℝ)/321850237976 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2056
  · change lowerPayment 2057 ≤ lowerValue ((point 2 split 4096 2057+point 2 split 4096 2058)/2)
    have hp : lowerPayment 2057 = (237888210902:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2057+point 2 split 4096 2058)/2 = (91476893:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((91476893:ℝ)/33751040)/ClassicalSixthBranch.v ((91476893:ℝ)/33751040) = (654942292449:ℝ)/321802230088 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2057
  · change lowerPayment 2058 ≤ lowerValue ((point 2 split 4096 2058+point 2 split 4096 2059)/2)
    have hp : lowerPayment 2058 = (237978727302:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2058+point 2 split 4096 2059)/2 = (457442727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((457442727:ℝ)/168755200)/ClassicalSixthBranch.v ((457442727:ℝ)/168755200) = (26194599151:ℝ)/12870168888 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2058
  · change lowerPayment 2059 ≤ lowerValue ((point 2 split 4096 2059+point 2 split 4096 2060)/2)
    have hp : lowerPayment 2059 = (238069234481:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2059+point 2 split 4096 2060)/2 = (457500989:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((457500989:ℝ)/168755200)/ClassicalSixthBranch.v ((457500989:ℝ)/168755200) = (654787665101:ℝ)/321706214312 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2059
  · change lowerPayment 2060 ≤ lowerValue ((point 2 split 4096 2060+point 2 split 4096 2061)/2)
    have hp : lowerPayment 2060 = (238159732455:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2060+point 2 split 4096 2061)/2 = (457559251:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((457559251:ℝ)/168755200)/ClassicalSixthBranch.v ((457559251:ℝ)/168755200) = (654710351427:ℝ)/321658206424 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2060
  · change lowerPayment 2061 ≤ lowerValue ((point 2 split 4096 2061+point 2 split 4096 2062)/2)
    have hp : lowerPayment 2061 = (238250221239:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2061+point 2 split 4096 2062)/2 = (457617513:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((457617513:ℝ)/168755200)/ClassicalSixthBranch.v ((457617513:ℝ)/168755200) = (654633037753:ℝ)/321610198536 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2061
  · change lowerPayment 2062 ≤ lowerValue ((point 2 split 4096 2062+point 2 split 4096 2063)/2)
    have hp : lowerPayment 2062 = (238340700851:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2062+point 2 split 4096 2063)/2 = (18307031:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((18307031:ℝ)/6750208)/ClassicalSixthBranch.v ((18307031:ℝ)/6750208) = (654555724079:ℝ)/321562190648 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2062
  · change lowerPayment 2063 ≤ lowerValue ((point 2 split 4096 2063+point 2 split 4096 2064)/2)
    have hp : lowerPayment 2063 = (238431171307:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2063+point 2 split 4096 2064)/2 = (457734037:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((457734037:ℝ)/168755200)/ClassicalSixthBranch.v ((457734037:ℝ)/168755200) = (130895682081:ℝ)/64302836552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2063
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_128
