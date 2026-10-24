import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints191
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_191 (j : Fin 16) : upperPayment (16*191+j.val) ≤
    upperValue ((point split endpoint 4096 (16*191+j.val)+point split endpoint 4096 (16*191+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3056 ≤ upperValue ((point split endpoint 4096 3056+point split endpoint 4096 3057)/2)
    have hp : upperPayment 3056 = (154178254908:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3056+point split endpoint 4096 3057)/2 = (653022527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((653022527:ℝ)/168755200)*ClassicalSixthBranch.v ((653022527:ℝ)/168755200)/ClassicalSixthBranch.r = (92900542307345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3056
  · change upperPayment 3057 ≤ upperValue ((point split endpoint 4096 3057+point split endpoint 4096 3058)/2)
    have hp : upperPayment 3057 = (154048678310:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3057+point split endpoint 4096 3058)/2 = (653047677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((653047677:ℝ)/168755200)*ClassicalSixthBranch.v ((653047677:ℝ)/168755200)/ClassicalSixthBranch.r = (92880712578585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3057
  · change upperPayment 3058 ≤ upperValue ((point split endpoint 4096 3058+point split endpoint 4096 3059)/2)
    have hp : upperPayment 3058 = (153919068674:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3058+point split endpoint 4096 3059)/2 = (653072827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((653072827:ℝ)/168755200)*ClassicalSixthBranch.v ((653072827:ℝ)/168755200)/ClassicalSixthBranch.r = (92860884873897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3058
  · change upperPayment 3059 ≤ upperValue ((point split endpoint 4096 3059+point split endpoint 4096 3060)/2)
    have hp : upperPayment 3059 = (153789425993:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3059+point split endpoint 4096 3060)/2 = (653097977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((653097977:ℝ)/168755200)*ClassicalSixthBranch.v ((653097977:ℝ)/168755200)/ClassicalSixthBranch.r = (92841059193281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3059
  · change upperPayment 3060 ≤ upperValue ((point split endpoint 4096 3060+point split endpoint 4096 3061)/2)
    have hp : upperPayment 3060 = (153659750259:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3060+point split endpoint 4096 3061)/2 = (653123127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((653123127:ℝ)/168755200)*ClassicalSixthBranch.v ((653123127:ℝ)/168755200)/ClassicalSixthBranch.r = (92821235536737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3060
  · change upperPayment 3061 ≤ upperValue ((point split endpoint 4096 3061+point split endpoint 4096 3062)/2)
    have hp : upperPayment 3061 = (153530041463:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3061+point split endpoint 4096 3062)/2 = (653148277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((653148277:ℝ)/168755200)*ClassicalSixthBranch.v ((653148277:ℝ)/168755200)/ClassicalSixthBranch.r = (92801413904265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3061
  · change upperPayment 3062 ≤ upperValue ((point split endpoint 4096 3062+point split endpoint 4096 3063)/2)
    have hp : upperPayment 3062 = (153400299598:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3062+point split endpoint 4096 3063)/2 = (653173427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((653173427:ℝ)/168755200)*ClassicalSixthBranch.v ((653173427:ℝ)/168755200)/ClassicalSixthBranch.r = (92781594295865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3062
  · change upperPayment 3063 ≤ upperValue ((point split endpoint 4096 3063+point split endpoint 4096 3064)/2)
    have hp : upperPayment 3063 = (153270524656:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3063+point split endpoint 4096 3064)/2 = (653198577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((653198577:ℝ)/168755200)*ClassicalSixthBranch.v ((653198577:ℝ)/168755200)/ClassicalSixthBranch.r = (92761776711537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3063
  · change upperPayment 3064 ≤ upperValue ((point split endpoint 4096 3064+point split endpoint 4096 3065)/2)
    have hp : upperPayment 3064 = (153140716629:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3064+point split endpoint 4096 3065)/2 = (653223727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((653223727:ℝ)/168755200)*ClassicalSixthBranch.v ((653223727:ℝ)/168755200)/ClassicalSixthBranch.r = (92741961151281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3064
  · change upperPayment 3065 ≤ upperValue ((point split endpoint 4096 3065+point split endpoint 4096 3066)/2)
    have hp : upperPayment 3065 = (153010875509:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3065+point split endpoint 4096 3066)/2 = (653248877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((653248877:ℝ)/168755200)*ClassicalSixthBranch.v ((653248877:ℝ)/168755200)/ClassicalSixthBranch.r = (92722147615097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3065
  · change upperPayment 3066 ≤ upperValue ((point split endpoint 4096 3066+point split endpoint 4096 3067)/2)
    have hp : upperPayment 3066 = (152881001288:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3066+point split endpoint 4096 3067)/2 = (653274027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((653274027:ℝ)/168755200)*ClassicalSixthBranch.v ((653274027:ℝ)/168755200)/ClassicalSixthBranch.r = (92702336102985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3066
  · change upperPayment 3067 ≤ upperValue ((point split endpoint 4096 3067+point split endpoint 4096 3068)/2)
    have hp : upperPayment 3067 = (152751093959:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3067+point split endpoint 4096 3068)/2 = (653299177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((653299177:ℝ)/168755200)*ClassicalSixthBranch.v ((653299177:ℝ)/168755200)/ClassicalSixthBranch.r = (92682526614945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3067
  · change upperPayment 3068 ≤ upperValue ((point split endpoint 4096 3068+point split endpoint 4096 3069)/2)
    have hp : upperPayment 3068 = (152621153512:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3068+point split endpoint 4096 3069)/2 = (653324327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((653324327:ℝ)/168755200)*ClassicalSixthBranch.v ((653324327:ℝ)/168755200)/ClassicalSixthBranch.r = (92662719150977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3068
  · change upperPayment 3069 ≤ upperValue ((point split endpoint 4096 3069+point split endpoint 4096 3070)/2)
    have hp : upperPayment 3069 = (152491179940:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3069+point split endpoint 4096 3070)/2 = (653349477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((653349477:ℝ)/168755200)*ClassicalSixthBranch.v ((653349477:ℝ)/168755200)/ClassicalSixthBranch.r = (92642913711081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3069
  · change upperPayment 3070 ≤ upperValue ((point split endpoint 4096 3070+point split endpoint 4096 3071)/2)
    have hp : upperPayment 3070 = (152361173236:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3070+point split endpoint 4096 3071)/2 = (653374627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((653374627:ℝ)/168755200)*ClassicalSixthBranch.v ((653374627:ℝ)/168755200)/ClassicalSixthBranch.r = (92623110295257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3070
  · change upperPayment 3071 ≤ upperValue ((point split endpoint 4096 3071+point split endpoint 4096 3072)/2)
    have hp : upperPayment 3071 = (152231133391:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3071+point split endpoint 4096 3072)/2 = (653399777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((653399777:ℝ)/168755200)*ClassicalSixthBranch.v ((653399777:ℝ)/168755200)/ClassicalSixthBranch.r = (92603308903505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3071
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_191
