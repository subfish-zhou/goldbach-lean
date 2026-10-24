import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints185
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_185 (j : Fin 16) : lowerPayment (16*185+j.val) ≤
    lowerValue ((point 2 split 4096 (16*185+j.val)+point 2 split 4096 (16*185+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2960 ≤ lowerValue ((point 2 split 4096 2960+point 2 split 4096 2961)/2)
    have hp : lowerPayment 2960 = (317746699237:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2960+point 2 split 4096 2961)/2 = (509995051:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((509995051:ℝ)/168755200)/ClassicalSixthBranch.v ((509995051:ℝ)/168755200) = (585128044827:ℝ)/278451107224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2960
  · change lowerPayment 2961 ≤ lowerValue ((point 2 split 4096 2961+point 2 split 4096 2962)/2)
    have hp : lowerPayment 2961 = (317835046490:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2961+point 2 split 4096 2962)/2 = (510053313:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((510053313:ℝ)/168755200)/ClassicalSixthBranch.v ((510053313:ℝ)/168755200) = (585050731153:ℝ)/278403099336 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2961
  · change lowerPayment 2962 ≤ lowerValue ((point 2 split 4096 2962+point 2 split 4096 2963)/2)
    have hp : lowerPayment 2962 = (317923397846:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2962+point 2 split 4096 2963)/2 = (20404463:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((20404463:ℝ)/6750208)/ClassicalSixthBranch.v ((20404463:ℝ)/6750208) = (584973417479:ℝ)/278355091448 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2962
  · change lowerPayment 2963 ≤ lowerValue ((point 2 split 4096 2963+point 2 split 4096 2964)/2)
    have hp : lowerPayment 2963 = (318011753320:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2963+point 2 split 4096 2964)/2 = (510169837:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((510169837:ℝ)/168755200)/ClassicalSixthBranch.v ((510169837:ℝ)/168755200) = (116979220761:ℝ)/55661416712 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2963
  · change lowerPayment 2964 ≤ lowerValue ((point 2 split 4096 2964+point 2 split 4096 2965)/2)
    have hp : lowerPayment 2964 = (318100112926:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2964+point 2 split 4096 2965)/2 = (510228099:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((510228099:ℝ)/168755200)/ClassicalSixthBranch.v ((510228099:ℝ)/168755200) = (584818790131:ℝ)/278259075672 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2964
  · change lowerPayment 2965 ≤ lowerValue ((point 2 split 4096 2965+point 2 split 4096 2966)/2)
    have hp : lowerPayment 2965 = (318188476677:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2965+point 2 split 4096 2966)/2 = (510286361:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((510286361:ℝ)/168755200)/ClassicalSixthBranch.v ((510286361:ℝ)/168755200) = (584741476457:ℝ)/278211067784 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2965
  · change lowerPayment 2966 ≤ lowerValue ((point 2 split 4096 2966+point 2 split 4096 2967)/2)
    have hp : lowerPayment 2966 = (318276844588:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2966+point 2 split 4096 2967)/2 = (510344623:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((510344623:ℝ)/168755200)/ClassicalSixthBranch.v ((510344623:ℝ)/168755200) = (584664162783:ℝ)/278163059896 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2966
  · change lowerPayment 2967 ≤ lowerValue ((point 2 split 4096 2967+point 2 split 4096 2968)/2)
    have hp : lowerPayment 2967 = (318365216673:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2967+point 2 split 4096 2968)/2 = (102080577:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((102080577:ℝ)/33751040)/ClassicalSixthBranch.v ((102080577:ℝ)/33751040) = (584586849109:ℝ)/278115052008 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2967
  · change lowerPayment 2968 ≤ lowerValue ((point 2 split 4096 2968+point 2 split 4096 2969)/2)
    have hp : lowerPayment 2968 = (318453592947:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2968+point 2 split 4096 2969)/2 = (510461147:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((510461147:ℝ)/168755200)/ClassicalSixthBranch.v ((510461147:ℝ)/168755200) = (116901907087:ℝ)/55613408824 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2968
  · change lowerPayment 2969 ≤ lowerValue ((point 2 split 4096 2969+point 2 split 4096 2970)/2)
    have hp : lowerPayment 2969 = (318541973423:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2969+point 2 split 4096 2970)/2 = (510519409:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((510519409:ℝ)/168755200)/ClassicalSixthBranch.v ((510519409:ℝ)/168755200) = (584432221761:ℝ)/278019036232 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2969
  · change lowerPayment 2970 ≤ lowerValue ((point 2 split 4096 2970+point 2 split 4096 2971)/2)
    have hp : lowerPayment 2970 = (318630358115:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2970+point 2 split 4096 2971)/2 = (510577671:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((510577671:ℝ)/168755200)/ClassicalSixthBranch.v ((510577671:ℝ)/168755200) = (584354908087:ℝ)/277971028344 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2970
  · change lowerPayment 2971 ≤ lowerValue ((point 2 split 4096 2971+point 2 split 4096 2972)/2)
    have hp : lowerPayment 2971 = (318718747038:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2971+point 2 split 4096 2972)/2 = (510635933:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((510635933:ℝ)/168755200)/ClassicalSixthBranch.v ((510635933:ℝ)/168755200) = (584277594413:ℝ)/277923020456 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2971
  · change lowerPayment 2972 ≤ lowerValue ((point 2 split 4096 2972+point 2 split 4096 2973)/2)
    have hp : lowerPayment 2972 = (318807140205:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2972+point 2 split 4096 2973)/2 = (102138839:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((102138839:ℝ)/33751040)/ClassicalSixthBranch.v ((102138839:ℝ)/33751040) = (584200280739:ℝ)/277875012568 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2972
  · change lowerPayment 2973 ≤ lowerValue ((point 2 split 4096 2973+point 2 split 4096 2974)/2)
    have hp : lowerPayment 2973 = (318895537632:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2973+point 2 split 4096 2974)/2 = (510752457:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((510752457:ℝ)/168755200)/ClassicalSixthBranch.v ((510752457:ℝ)/168755200) = (116824593413:ℝ)/55565400936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2973
  · change lowerPayment 2974 ≤ lowerValue ((point 2 split 4096 2974+point 2 split 4096 2975)/2)
    have hp : lowerPayment 2974 = (318983939332:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2974+point 2 split 4096 2975)/2 = (510810719:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((510810719:ℝ)/168755200)/ClassicalSixthBranch.v ((510810719:ℝ)/168755200) = (584045653391:ℝ)/277778996792 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2974
  · change lowerPayment 2975 ≤ lowerValue ((point 2 split 4096 2975+point 2 split 4096 2976)/2)
    have hp : lowerPayment 2975 = (319072345318:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2975+point 2 split 4096 2976)/2 = (510868981:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((510868981:ℝ)/168755200)/ClassicalSixthBranch.v ((510868981:ℝ)/168755200) = (583968339717:ℝ)/277730988904 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2975
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_185
