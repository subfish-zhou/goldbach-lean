import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints178
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_178 (j : Fin 16) : upperPayment (16*178+j.val) ≤
    upperValue ((point split endpoint 4096 (16*178+j.val)+point split endpoint 4096 (16*178+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2848 ≤ upperValue ((point split endpoint 4096 2848+point split endpoint 4096 2849)/2)
    have hp : upperPayment 2848 = (180423885366:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2848+point split endpoint 4096 2849)/2 = (647791327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((647791327:ℝ)/168755200)*ClassicalSixthBranch.v ((647791327:ℝ)/168755200)/ClassicalSixthBranch.r = (97069121118417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2848
  · change upperPayment 2849 ≤ upperValue ((point split endpoint 4096 2849+point split endpoint 4096 2850)/2)
    have hp : upperPayment 2849 = (180301013145:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2849+point split endpoint 4096 2850)/2 = (647816477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((647816477:ℝ)/168755200)*ClassicalSixthBranch.v ((647816477:ℝ)/168755200)/ClassicalSixthBranch.r = (97048870382681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2849
  · change upperPayment 2850 ≤ upperValue ((point split endpoint 4096 2850+point split endpoint 4096 2851)/2)
    have hp : upperPayment 2850 = (180178109467:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2850+point split endpoint 4096 2851)/2 = (647841627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((647841627:ℝ)/168755200)*ClassicalSixthBranch.v ((647841627:ℝ)/168755200)/ClassicalSixthBranch.r = (97028621671017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2850
  · change upperPayment 2851 ≤ upperValue ((point split endpoint 4096 2851+point split endpoint 4096 2852)/2)
    have hp : upperPayment 2851 = (180055174324:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2851+point split endpoint 4096 2852)/2 = (647866777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((647866777:ℝ)/168755200)*ClassicalSixthBranch.v ((647866777:ℝ)/168755200)/ClassicalSixthBranch.r = (97008374983425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2851
  · change upperPayment 2852 ≤ upperValue ((point split endpoint 4096 2852+point split endpoint 4096 2853)/2)
    have hp : upperPayment 2852 = (179932207709:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2852+point split endpoint 4096 2853)/2 = (647891927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((647891927:ℝ)/168755200)*ClassicalSixthBranch.v ((647891927:ℝ)/168755200)/ClassicalSixthBranch.r = (96988130319905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2852
  · change upperPayment 2853 ≤ upperValue ((point split endpoint 4096 2853+point split endpoint 4096 2854)/2)
    have hp : upperPayment 2853 = (179809209615:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2853+point split endpoint 4096 2854)/2 = (647917077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((647917077:ℝ)/168755200)*ClassicalSixthBranch.v ((647917077:ℝ)/168755200)/ClassicalSixthBranch.r = (96967887680457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2853
  · change upperPayment 2854 ≤ upperValue ((point split endpoint 4096 2854+point split endpoint 4096 2855)/2)
    have hp : upperPayment 2854 = (179686180034:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2854+point split endpoint 4096 2855)/2 = (647942227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((647942227:ℝ)/168755200)*ClassicalSixthBranch.v ((647942227:ℝ)/168755200)/ClassicalSixthBranch.r = (96947647065081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2854
  · change upperPayment 2855 ≤ upperValue ((point split endpoint 4096 2855+point split endpoint 4096 2856)/2)
    have hp : upperPayment 2855 = (179563118959:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2855+point split endpoint 4096 2856)/2 = (647967377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((647967377:ℝ)/168755200)*ClassicalSixthBranch.v ((647967377:ℝ)/168755200)/ClassicalSixthBranch.r = (96927408473777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2855
  · change upperPayment 2856 ≤ upperValue ((point split endpoint 4096 2856+point split endpoint 4096 2857)/2)
    have hp : upperPayment 2856 = (179440026383:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2856+point split endpoint 4096 2857)/2 = (647992527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((647992527:ℝ)/168755200)*ClassicalSixthBranch.v ((647992527:ℝ)/168755200)/ClassicalSixthBranch.r = (96907171906545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2856
  · change upperPayment 2857 ≤ upperValue ((point split endpoint 4096 2857+point split endpoint 4096 2858)/2)
    have hp : upperPayment 2857 = (179316902299:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2857+point split endpoint 4096 2858)/2 = (648017677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((648017677:ℝ)/168755200)*ClassicalSixthBranch.v ((648017677:ℝ)/168755200)/ClassicalSixthBranch.r = (96886937363385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2857
  · change upperPayment 2858 ≤ upperValue ((point split endpoint 4096 2858+point split endpoint 4096 2859)/2)
    have hp : upperPayment 2858 = (179193746699:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2858+point split endpoint 4096 2859)/2 = (648042827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((648042827:ℝ)/168755200)*ClassicalSixthBranch.v ((648042827:ℝ)/168755200)/ClassicalSixthBranch.r = (96866704844297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2858
  · change upperPayment 2859 ≤ upperValue ((point split endpoint 4096 2859+point split endpoint 4096 2860)/2)
    have hp : upperPayment 2859 = (179070559575:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2859+point split endpoint 4096 2860)/2 = (648067977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((648067977:ℝ)/168755200)*ClassicalSixthBranch.v ((648067977:ℝ)/168755200)/ClassicalSixthBranch.r = (96846474349281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2859
  · change upperPayment 2860 ≤ upperValue ((point split endpoint 4096 2860+point split endpoint 4096 2861)/2)
    have hp : upperPayment 2860 = (178947340921:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2860+point split endpoint 4096 2861)/2 = (648093127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((648093127:ℝ)/168755200)*ClassicalSixthBranch.v ((648093127:ℝ)/168755200)/ClassicalSixthBranch.r = (96826245878337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2860
  · change upperPayment 2861 ≤ upperValue ((point split endpoint 4096 2861+point split endpoint 4096 2862)/2)
    have hp : upperPayment 2861 = (178824090730:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2861+point split endpoint 4096 2862)/2 = (648118277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((648118277:ℝ)/168755200)*ClassicalSixthBranch.v ((648118277:ℝ)/168755200)/ClassicalSixthBranch.r = (96806019431465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2861
  · change upperPayment 2862 ≤ upperValue ((point split endpoint 4096 2862+point split endpoint 4096 2863)/2)
    have hp : upperPayment 2862 = (178700808993:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2862+point split endpoint 4096 2863)/2 = (648143427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((648143427:ℝ)/168755200)*ClassicalSixthBranch.v ((648143427:ℝ)/168755200)/ClassicalSixthBranch.r = (96785795008665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2862
  · change upperPayment 2863 ≤ upperValue ((point split endpoint 4096 2863+point split endpoint 4096 2864)/2)
    have hp : upperPayment 2863 = (178577495704:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2863+point split endpoint 4096 2864)/2 = (648168577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((648168577:ℝ)/168755200)*ClassicalSixthBranch.v ((648168577:ℝ)/168755200)/ClassicalSixthBranch.r = (96765572609937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2863
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_178
