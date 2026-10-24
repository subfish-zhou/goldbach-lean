import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints017
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_017 (j : Fin 16) : upperPayment (16*17+j.val) ≤
    upperValue ((point split endpoint 4096 (16*17+j.val)+point split endpoint 4096 (16*17+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 272 ≤ upperValue ((point split endpoint 4096 272+point split endpoint 4096 273)/2)
    have hp : upperPayment 272 = (408850973839:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 272+point split endpoint 4096 273)/2 = (583004927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((583004927:ℝ)/168755200)*ClassicalSixthBranch.v ((583004927:ℝ)/168755200)/ClassicalSixthBranch.r = (155953267579025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_272
  · change upperPayment 273 ≤ upperValue ((point split endpoint 4096 273+point split endpoint 4096 274)/2)
    have hp : upperPayment 273 = (408791572608:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 273+point split endpoint 4096 274)/2 = (583030077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((583030077:ℝ)/168755200)*ClassicalSixthBranch.v ((583030077:ℝ)/168755200)/ClassicalSixthBranch.r = (155927802833817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_273
  · change upperPayment 274 ≤ upperValue ((point split endpoint 4096 274+point split endpoint 4096 275)/2)
    have hp : upperPayment 274 = (408732151512:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 274+point split endpoint 4096 275)/2 = (583055227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((583055227:ℝ)/168755200)*ClassicalSixthBranch.v ((583055227:ℝ)/168755200)/ClassicalSixthBranch.r = (155902340112681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_274
  · change upperPayment 275 ≤ upperValue ((point split endpoint 4096 275+point split endpoint 4096 276)/2)
    have hp : upperPayment 275 = (408672710548:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 275+point split endpoint 4096 276)/2 = (583080377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((583080377:ℝ)/168755200)*ClassicalSixthBranch.v ((583080377:ℝ)/168755200)/ClassicalSixthBranch.r = (155876879415617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_275
  · change upperPayment 276 ≤ upperValue ((point split endpoint 4096 276+point split endpoint 4096 277)/2)
    have hp : upperPayment 276 = (408613249715:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 276+point split endpoint 4096 277)/2 = (583105527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((583105527:ℝ)/168755200)*ClassicalSixthBranch.v ((583105527:ℝ)/168755200)/ClassicalSixthBranch.r = (155851420742625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_276
  · change upperPayment 277 ≤ upperValue ((point split endpoint 4096 277+point split endpoint 4096 278)/2)
    have hp : upperPayment 277 = (408553769008:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 277+point split endpoint 4096 278)/2 = (583130677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((583130677:ℝ)/168755200)*ClassicalSixthBranch.v ((583130677:ℝ)/168755200)/ClassicalSixthBranch.r = (155825964093705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_277
  · change upperPayment 278 ≤ upperValue ((point split endpoint 4096 278+point split endpoint 4096 279)/2)
    have hp : upperPayment 278 = (408494268427:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 278+point split endpoint 4096 279)/2 = (583155827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((583155827:ℝ)/168755200)*ClassicalSixthBranch.v ((583155827:ℝ)/168755200)/ClassicalSixthBranch.r = (155800509468857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_278
  · change upperPayment 279 ≤ upperValue ((point split endpoint 4096 279+point split endpoint 4096 280)/2)
    have hp : upperPayment 279 = (408434747969:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 279+point split endpoint 4096 280)/2 = (583180977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((583180977:ℝ)/168755200)*ClassicalSixthBranch.v ((583180977:ℝ)/168755200)/ClassicalSixthBranch.r = (155775056868081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_279
  · change upperPayment 280 ≤ upperValue ((point split endpoint 4096 280+point split endpoint 4096 281)/2)
    have hp : upperPayment 280 = (408375207631:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 280+point split endpoint 4096 281)/2 = (583206127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((583206127:ℝ)/168755200)*ClassicalSixthBranch.v ((583206127:ℝ)/168755200)/ClassicalSixthBranch.r = (155749606291377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_280
  · change upperPayment 281 ≤ upperValue ((point split endpoint 4096 281+point split endpoint 4096 282)/2)
    have hp : upperPayment 281 = (408315647410:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 281+point split endpoint 4096 282)/2 = (583231277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((583231277:ℝ)/168755200)*ClassicalSixthBranch.v ((583231277:ℝ)/168755200)/ClassicalSixthBranch.r = (155724157738745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_281
  · change upperPayment 282 ≤ upperValue ((point split endpoint 4096 282+point split endpoint 4096 283)/2)
    have hp : upperPayment 282 = (408256067305:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 282+point split endpoint 4096 283)/2 = (583256427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((583256427:ℝ)/168755200)*ClassicalSixthBranch.v ((583256427:ℝ)/168755200)/ClassicalSixthBranch.r = (155698711210185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_282
  · change upperPayment 283 ≤ upperValue ((point split endpoint 4096 283+point split endpoint 4096 284)/2)
    have hp : upperPayment 283 = (408196467312:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 283+point split endpoint 4096 284)/2 = (583281577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((583281577:ℝ)/168755200)*ClassicalSixthBranch.v ((583281577:ℝ)/168755200)/ClassicalSixthBranch.r = (155673266705697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_283
  · change upperPayment 284 ≤ upperValue ((point split endpoint 4096 284+point split endpoint 4096 285)/2)
    have hp : upperPayment 284 = (408136847430:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 284+point split endpoint 4096 285)/2 = (583306727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((583306727:ℝ)/168755200)*ClassicalSixthBranch.v ((583306727:ℝ)/168755200)/ClassicalSixthBranch.r = (155647824225281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_284
  · change upperPayment 285 ≤ upperValue ((point split endpoint 4096 285+point split endpoint 4096 286)/2)
    have hp : upperPayment 285 = (408077207656:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 285+point split endpoint 4096 286)/2 = (583331877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((583331877:ℝ)/168755200)*ClassicalSixthBranch.v ((583331877:ℝ)/168755200)/ClassicalSixthBranch.r = (155622383768937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_285
  · change upperPayment 286 ≤ upperValue ((point split endpoint 4096 286+point split endpoint 4096 287)/2)
    have hp : upperPayment 286 = (408017547988:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 286+point split endpoint 4096 287)/2 = (583357027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((583357027:ℝ)/168755200)*ClassicalSixthBranch.v ((583357027:ℝ)/168755200)/ClassicalSixthBranch.r = (155596945336665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_286
  · change upperPayment 287 ≤ upperValue ((point split endpoint 4096 287+point split endpoint 4096 288)/2)
    have hp : upperPayment 287 = (407957868423:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 287+point split endpoint 4096 288)/2 = (583382177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((583382177:ℝ)/168755200)*ClassicalSixthBranch.v ((583382177:ℝ)/168755200)/ClassicalSixthBranch.r = (155571508928465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_287
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_017
