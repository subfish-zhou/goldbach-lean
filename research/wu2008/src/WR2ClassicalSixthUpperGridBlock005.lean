import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints005
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_005 (j : Fin 16) : upperPayment (16*5+j.val) ≤
    upperValue ((point split endpoint 4096 (16*5+j.val)+point split endpoint 4096 (16*5+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 80 ≤ upperValue ((point split endpoint 4096 80+point split endpoint 4096 81)/2)
    have hp : upperPayment 80 = (419890787209:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 80+point split endpoint 4096 81)/2 = (578176127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((578176127:ℝ)/168755200)*ClassicalSixthBranch.v ((578176127:ℝ)/168755200)/ClassicalSixthBranch.r = (160880000664977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_80
  · change upperPayment 81 ≤ upperValue ((point split endpoint 4096 81+point split endpoint 4096 82)/2)
    have hp : upperPayment 81 = (419835156541:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 81+point split endpoint 4096 82)/2 = (578201277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((578201277:ℝ)/168755200)*ClassicalSixthBranch.v ((578201277:ℝ)/168755200)/ClassicalSixthBranch.r = (160854147297945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_81
  · change upperPayment 82 ≤ upperValue ((point split endpoint 4096 82+point split endpoint 4096 83)/2)
    have hp : upperPayment 82 = (419779506452:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 82+point split endpoint 4096 83)/2 = (578226427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((578226427:ℝ)/168755200)*ClassicalSixthBranch.v ((578226427:ℝ)/168755200)/ClassicalSixthBranch.r = (160828295954985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_82
  · change upperPayment 83 ≤ upperValue ((point split endpoint 4096 83+point split endpoint 4096 84)/2)
    have hp : upperPayment 83 = (419723836940:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 83+point split endpoint 4096 84)/2 = (578251577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((578251577:ℝ)/168755200)*ClassicalSixthBranch.v ((578251577:ℝ)/168755200)/ClassicalSixthBranch.r = (160802446636097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_83
  · change upperPayment 84 ≤ upperValue ((point split endpoint 4096 84+point split endpoint 4096 85)/2)
    have hp : upperPayment 84 = (419668148002:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 84+point split endpoint 4096 85)/2 = (578276727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((578276727:ℝ)/168755200)*ClassicalSixthBranch.v ((578276727:ℝ)/168755200)/ClassicalSixthBranch.r = (160776599341281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_84
  · change upperPayment 85 ≤ upperValue ((point split endpoint 4096 85+point split endpoint 4096 86)/2)
    have hp : upperPayment 85 = (419612439637:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 85+point split endpoint 4096 86)/2 = (578301877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((578301877:ℝ)/168755200)*ClassicalSixthBranch.v ((578301877:ℝ)/168755200)/ClassicalSixthBranch.r = (160750754070537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_85
  · change upperPayment 86 ≤ upperValue ((point split endpoint 4096 86+point split endpoint 4096 87)/2)
    have hp : upperPayment 86 = (419556711841:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 86+point split endpoint 4096 87)/2 = (578327027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((578327027:ℝ)/168755200)*ClassicalSixthBranch.v ((578327027:ℝ)/168755200)/ClassicalSixthBranch.r = (160724910823865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_86
  · change upperPayment 87 ≤ upperValue ((point split endpoint 4096 87+point split endpoint 4096 88)/2)
    have hp : upperPayment 87 = (419500964613:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 87+point split endpoint 4096 88)/2 = (578352177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((578352177:ℝ)/168755200)*ClassicalSixthBranch.v ((578352177:ℝ)/168755200)/ClassicalSixthBranch.r = (160699069601265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_87
  · change upperPayment 88 ≤ upperValue ((point split endpoint 4096 88+point split endpoint 4096 89)/2)
    have hp : upperPayment 88 = (419445197951:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 88+point split endpoint 4096 89)/2 = (578377327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((578377327:ℝ)/168755200)*ClassicalSixthBranch.v ((578377327:ℝ)/168755200)/ClassicalSixthBranch.r = (160673230402737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_88
  · change upperPayment 89 ≤ upperValue ((point split endpoint 4096 89+point split endpoint 4096 90)/2)
    have hp : upperPayment 89 = (419389411852:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 89+point split endpoint 4096 90)/2 = (578402477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((578402477:ℝ)/168755200)*ClassicalSixthBranch.v ((578402477:ℝ)/168755200)/ClassicalSixthBranch.r = (160647393228281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_89
  · change upperPayment 90 ≤ upperValue ((point split endpoint 4096 90+point split endpoint 4096 91)/2)
    have hp : upperPayment 90 = (419333606315:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 90+point split endpoint 4096 91)/2 = (578427627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((578427627:ℝ)/168755200)*ClassicalSixthBranch.v ((578427627:ℝ)/168755200)/ClassicalSixthBranch.r = (160621558077897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_90
  · change upperPayment 91 ≤ upperValue ((point split endpoint 4096 91+point split endpoint 4096 92)/2)
    have hp : upperPayment 91 = (419277781336:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 91+point split endpoint 4096 92)/2 = (578452777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((578452777:ℝ)/168755200)*ClassicalSixthBranch.v ((578452777:ℝ)/168755200)/ClassicalSixthBranch.r = (160595724951585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_91
  · change upperPayment 92 ≤ upperValue ((point split endpoint 4096 92+point split endpoint 4096 93)/2)
    have hp : upperPayment 92 = (419221936914:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 92+point split endpoint 4096 93)/2 = (578477927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((578477927:ℝ)/168755200)*ClassicalSixthBranch.v ((578477927:ℝ)/168755200)/ClassicalSixthBranch.r = (160569893849345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_92
  · change upperPayment 93 ≤ upperValue ((point split endpoint 4096 93+point split endpoint 4096 94)/2)
    have hp : upperPayment 93 = (419166073047:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 93+point split endpoint 4096 94)/2 = (578503077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((578503077:ℝ)/168755200)*ClassicalSixthBranch.v ((578503077:ℝ)/168755200)/ClassicalSixthBranch.r = (160544064771177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_93
  · change upperPayment 94 ≤ upperValue ((point split endpoint 4096 94+point split endpoint 4096 95)/2)
    have hp : upperPayment 94 = (419110189732:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 94+point split endpoint 4096 95)/2 = (578528227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((578528227:ℝ)/168755200)*ClassicalSixthBranch.v ((578528227:ℝ)/168755200)/ClassicalSixthBranch.r = (160518237717081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_94
  · change upperPayment 95 ≤ upperValue ((point split endpoint 4096 95+point split endpoint 4096 96)/2)
    have hp : upperPayment 95 = (419054286968:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 95+point split endpoint 4096 96)/2 = (578553377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((578553377:ℝ)/168755200)*ClassicalSixthBranch.v ((578553377:ℝ)/168755200)/ClassicalSixthBranch.r = (160492412687057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_95
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_005
