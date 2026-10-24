import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints253
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_253 (j : Fin 16) : lowerPayment (16*253+j.val) ≤
    lowerValue ((point 2 split 4096 (16*253+j.val)+point 2 split 4096 (16*253+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 4048 ≤ lowerValue ((point 2 split 4096 4048+point 2 split 4096 4049)/2)
    have hp : lowerPayment 4048 = (419449328891:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4048+point 2 split 4096 4049)/2 = (573384107:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((573384107:ℝ)/168755200)/ClassicalSixthBranch.v ((573384107:ℝ)/168755200) = (100202153503:ℝ)/45243705016 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4048
  · change lowerPayment 4049 ≤ lowerValue ((point 2 split 4096 4049+point 2 split 4096 4050)/2)
    have hp : lowerPayment 4049 = (419551059510:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4049+point 2 split 4096 4050)/2 = (573442369:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((573442369:ℝ)/168755200)/ClassicalSixthBranch.v ((573442369:ℝ)/168755200) = (500933453841:ℝ)/226170517192 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4049
  · change lowerPayment 4050 ≤ lowerValue ((point 2 split 4096 4050+point 2 split 4096 4051)/2)
    have hp : lowerPayment 4050 = (419652811575:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4050+point 2 split 4096 4051)/2 = (573500631:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((573500631:ℝ)/168755200)/ClassicalSixthBranch.v ((573500631:ℝ)/168755200) = (500856140167:ℝ)/226122509304 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4050
  · change lowerPayment 4051 ≤ lowerValue ((point 2 split 4096 4051+point 2 split 4096 4052)/2)
    have hp : lowerPayment 4051 = (419754585104:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4051+point 2 split 4096 4052)/2 = (573558893:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((573558893:ℝ)/168755200)/ClassicalSixthBranch.v ((573558893:ℝ)/168755200) = (500778826493:ℝ)/226074501416 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4051
  · change lowerPayment 4052 ≤ lowerValue ((point 2 split 4096 4052+point 2 split 4096 4053)/2)
    have hp : lowerPayment 4052 = (419856380117:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4052+point 2 split 4096 4053)/2 = (114723431:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((114723431:ℝ)/33751040)/ClassicalSixthBranch.v ((114723431:ℝ)/33751040) = (500701512819:ℝ)/226026493528 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4052
  · change lowerPayment 4053 ≤ lowerValue ((point 2 split 4096 4053+point 2 split 4096 4054)/2)
    have hp : lowerPayment 4053 = (419958196633:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4053+point 2 split 4096 4054)/2 = (573675417:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((573675417:ℝ)/168755200)/ClassicalSixthBranch.v ((573675417:ℝ)/168755200) = (100124839829:ℝ)/45195697128 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4053
  · change lowerPayment 4054 ≤ lowerValue ((point 2 split 4096 4054+point 2 split 4096 4055)/2)
    have hp : lowerPayment 4054 = (420060034673:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4054+point 2 split 4096 4055)/2 = (573733679:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((573733679:ℝ)/168755200)/ClassicalSixthBranch.v ((573733679:ℝ)/168755200) = (500546885471:ℝ)/225930477752 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4054
  · change lowerPayment 4055 ≤ lowerValue ((point 2 split 4096 4055+point 2 split 4096 4056)/2)
    have hp : lowerPayment 4055 = (420161894254:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4055+point 2 split 4096 4056)/2 = (573791941:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((573791941:ℝ)/168755200)/ClassicalSixthBranch.v ((573791941:ℝ)/168755200) = (500469571797:ℝ)/225882469864 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4055
  · change lowerPayment 4056 ≤ lowerValue ((point 2 split 4096 4056+point 2 split 4096 4057)/2)
    have hp : lowerPayment 4056 = (420263775397:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4056+point 2 split 4096 4057)/2 = (573850203:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((573850203:ℝ)/168755200)/ClassicalSixthBranch.v ((573850203:ℝ)/168755200) = (500392258123:ℝ)/225834461976 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4056
  · change lowerPayment 4057 ≤ lowerValue ((point 2 split 4096 4057+point 2 split 4096 4058)/2)
    have hp : lowerPayment 4057 = (420365678121:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4057+point 2 split 4096 4058)/2 = (114781693:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((114781693:ℝ)/33751040)/ClassicalSixthBranch.v ((114781693:ℝ)/33751040) = (500314944449:ℝ)/225786454088 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4057
  · change lowerPayment 4058 ≤ lowerValue ((point 2 split 4096 4058+point 2 split 4096 4059)/2)
    have hp : lowerPayment 4058 = (420467602446:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4058+point 2 split 4096 4059)/2 = (573966727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((573966727:ℝ)/168755200)/ClassicalSixthBranch.v ((573966727:ℝ)/168755200) = (20009505231:ℝ)/9029537848 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4058
  · change lowerPayment 4059 ≤ lowerValue ((point 2 split 4096 4059+point 2 split 4096 4060)/2)
    have hp : lowerPayment 4059 = (420569548391:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4059+point 2 split 4096 4060)/2 = (574024989:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((574024989:ℝ)/168755200)/ClassicalSixthBranch.v ((574024989:ℝ)/168755200) = (500160317101:ℝ)/225690438312 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4059
  · change lowerPayment 4060 ≤ lowerValue ((point 2 split 4096 4060+point 2 split 4096 4061)/2)
    have hp : lowerPayment 4060 = (420671515975:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4060+point 2 split 4096 4061)/2 = (574083251:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((574083251:ℝ)/168755200)/ClassicalSixthBranch.v ((574083251:ℝ)/168755200) = (500083003427:ℝ)/225642430424 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4060
  · change lowerPayment 4061 ≤ lowerValue ((point 2 split 4096 4061+point 2 split 4096 4062)/2)
    have hp : lowerPayment 4061 = (420773505218:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4061+point 2 split 4096 4062)/2 = (574141513:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((574141513:ℝ)/168755200)/ClassicalSixthBranch.v ((574141513:ℝ)/168755200) = (500005689753:ℝ)/225594422536 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4061
  · change lowerPayment 4062 ≤ lowerValue ((point 2 split 4096 4062+point 2 split 4096 4063)/2)
    have hp : lowerPayment 4062 = (420875516139:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4062+point 2 split 4096 4063)/2 = (22967991:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((22967991:ℝ)/6750208)/ClassicalSixthBranch.v ((22967991:ℝ)/6750208) = (499928376079:ℝ)/225546414648 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4062
  · change lowerPayment 4063 ≤ lowerValue ((point 2 split 4096 4063+point 2 split 4096 4064)/2)
    have hp : lowerPayment 4063 = (420977548759:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4063+point 2 split 4096 4064)/2 = (574258037:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((574258037:ℝ)/168755200)/ClassicalSixthBranch.v ((574258037:ℝ)/168755200) = (99970212481:ℝ)/45099681352 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4063
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_253
