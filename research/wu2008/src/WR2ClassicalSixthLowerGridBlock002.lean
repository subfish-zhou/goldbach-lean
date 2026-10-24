import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints002
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_002 (j : Fin 16) : lowerPayment (16*2+j.val) ≤
    lowerValue ((point 2 split 4096 (16*2+j.val)+point 2 split 4096 (16*2+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 32 ≤ lowerValue ((point 2 split 4096 32+point 2 split 4096 33)/2)
    have hp : lowerPayment 32 = (5262041927:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 32+point 2 split 4096 33)/2 = (67880783:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((67880783:ℝ)/33751040)/ClassicalSixthBranch.v ((67880783:ℝ)/33751040) = (811502482299:ℝ)/419018203288 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_32
  · change lowerPayment 33 ≤ lowerValue ((point 2 split 4096 33+point 2 split 4096 34)/2)
    have hp : lowerPayment 33 = (5422655970:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 33+point 2 split 4096 34)/2 = (339462177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((339462177:ℝ)/168755200)/ClassicalSixthBranch.v ((339462177:ℝ)/168755200) = (32457006745:ℝ)/16758807816 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_33
  · change lowerPayment 34 ≤ lowerValue ((point 2 split 4096 34+point 2 split 4096 35)/2)
    have hp : lowerPayment 34 = (5583193517:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 34+point 2 split 4096 35)/2 = (339520439:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((339520439:ℝ)/168755200)/ClassicalSixthBranch.v ((339520439:ℝ)/168755200) = (811347854951:ℝ)/418922187512 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_34
  · change lowerPayment 35 ≤ lowerValue ((point 2 split 4096 35+point 2 split 4096 36)/2)
    have hp : lowerPayment 35 = (5743654640:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 35+point 2 split 4096 36)/2 = (339578701:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((339578701:ℝ)/168755200)/ClassicalSixthBranch.v ((339578701:ℝ)/168755200) = (811270541277:ℝ)/418874179624 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_35
  · change lowerPayment 36 ≤ lowerValue ((point 2 split 4096 36+point 2 split 4096 37)/2)
    have hp : lowerPayment 36 = (5904039409:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 36+point 2 split 4096 37)/2 = (339636963:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((339636963:ℝ)/168755200)/ClassicalSixthBranch.v ((339636963:ℝ)/168755200) = (811193227603:ℝ)/418826171736 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_36
  · change lowerPayment 37 ≤ lowerValue ((point 2 split 4096 37+point 2 split 4096 38)/2)
    have hp : lowerPayment 37 = (6064347893:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 37+point 2 split 4096 38)/2 = (13587809:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((13587809:ℝ)/6750208)/ClassicalSixthBranch.v ((13587809:ℝ)/6750208) = (811115913929:ℝ)/418778163848 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_37
  · change lowerPayment 38 ≤ lowerValue ((point 2 split 4096 38+point 2 split 4096 39)/2)
    have hp : lowerPayment 38 = (6224580163:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 38+point 2 split 4096 39)/2 = (339753487:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((339753487:ℝ)/168755200)/ClassicalSixthBranch.v ((339753487:ℝ)/168755200) = (162207720051:ℝ)/83746031192 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_38
  · change lowerPayment 39 ≤ lowerValue ((point 2 split 4096 39+point 2 split 4096 40)/2)
    have hp : lowerPayment 39 = (6384736289:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 39+point 2 split 4096 40)/2 = (339811749:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((339811749:ℝ)/168755200)/ClassicalSixthBranch.v ((339811749:ℝ)/168755200) = (810961286581:ℝ)/418682148072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_39
  · change lowerPayment 40 ≤ lowerValue ((point 2 split 4096 40+point 2 split 4096 41)/2)
    have hp : lowerPayment 40 = (6544816339:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 40+point 2 split 4096 41)/2 = (339870011:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((339870011:ℝ)/168755200)/ClassicalSixthBranch.v ((339870011:ℝ)/168755200) = (810883972907:ℝ)/418634140184 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_40
  · change lowerPayment 41 ≤ lowerValue ((point 2 split 4096 41+point 2 split 4096 42)/2)
    have hp : lowerPayment 41 = (6704820385:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 41+point 2 split 4096 42)/2 = (339928273:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((339928273:ℝ)/168755200)/ClassicalSixthBranch.v ((339928273:ℝ)/168755200) = (810806659233:ℝ)/418586132296 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_41
  · change lowerPayment 42 ≤ lowerValue ((point 2 split 4096 42+point 2 split 4096 43)/2)
    have hp : lowerPayment 42 = (6864748496:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 42+point 2 split 4096 43)/2 = (67997307:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((67997307:ℝ)/33751040)/ClassicalSixthBranch.v ((67997307:ℝ)/33751040) = (810729345559:ℝ)/418538124408 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_42
  · change lowerPayment 43 ≤ lowerValue ((point 2 split 4096 43+point 2 split 4096 44)/2)
    have hp : lowerPayment 43 = (7024600742:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 43+point 2 split 4096 44)/2 = (340044797:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((340044797:ℝ)/168755200)/ClassicalSixthBranch.v ((340044797:ℝ)/168755200) = (162130406377:ℝ)/83698023304 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_43
  · change lowerPayment 44 ≤ lowerValue ((point 2 split 4096 44+point 2 split 4096 45)/2)
    have hp : lowerPayment 44 = (7184377191:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 44+point 2 split 4096 45)/2 = (340103059:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((340103059:ℝ)/168755200)/ClassicalSixthBranch.v ((340103059:ℝ)/168755200) = (810574718211:ℝ)/418442108632 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_44
  · change lowerPayment 45 ≤ lowerValue ((point 2 split 4096 45+point 2 split 4096 46)/2)
    have hp : lowerPayment 45 = (7344077914:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 45+point 2 split 4096 46)/2 = (340161321:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((340161321:ℝ)/168755200)/ClassicalSixthBranch.v ((340161321:ℝ)/168755200) = (810497404537:ℝ)/418394100744 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_45
  · change lowerPayment 46 ≤ lowerValue ((point 2 split 4096 46+point 2 split 4096 47)/2)
    have hp : lowerPayment 46 = (7503702979:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 46+point 2 split 4096 47)/2 = (340219583:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((340219583:ℝ)/168755200)/ClassicalSixthBranch.v ((340219583:ℝ)/168755200) = (810420090863:ℝ)/418346092856 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_46
  · change lowerPayment 47 ≤ lowerValue ((point 2 split 4096 47+point 2 split 4096 48)/2)
    have hp : lowerPayment 47 = (7663252457:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 47+point 2 split 4096 48)/2 = (68055569:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((68055569:ℝ)/33751040)/ClassicalSixthBranch.v ((68055569:ℝ)/33751040) = (810342777189:ℝ)/418298084968 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_47
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_002
