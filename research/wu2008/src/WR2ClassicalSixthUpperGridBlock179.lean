import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints179
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_179 (j : Fin 16) : upperPayment (16*179+j.val) ≤
    upperValue ((point split endpoint 4096 (16*179+j.val)+point split endpoint 4096 (16*179+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2864 ≤ upperValue ((point split endpoint 4096 2864+point split endpoint 4096 2865)/2)
    have hp : upperPayment 2864 = (178454150855:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2864+point split endpoint 4096 2865)/2 = (648193727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((648193727:ℝ)/168755200)*ClassicalSixthBranch.v ((648193727:ℝ)/168755200)/ClassicalSixthBranch.r = (96745352235281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2864
  · change upperPayment 2865 ≤ upperValue ((point split endpoint 4096 2865+point split endpoint 4096 2866)/2)
    have hp : upperPayment 2865 = (178330774440:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2865+point split endpoint 4096 2866)/2 = (648218877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((648218877:ℝ)/168755200)*ClassicalSixthBranch.v ((648218877:ℝ)/168755200)/ClassicalSixthBranch.r = (96725133884697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2865
  · change upperPayment 2866 ≤ upperValue ((point split endpoint 4096 2866+point split endpoint 4096 2867)/2)
    have hp : upperPayment 2866 = (178207366450:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2866+point split endpoint 4096 2867)/2 = (648244027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((648244027:ℝ)/168755200)*ClassicalSixthBranch.v ((648244027:ℝ)/168755200)/ClassicalSixthBranch.r = (96704917558185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2866
  · change upperPayment 2867 ≤ upperValue ((point split endpoint 4096 2867+point split endpoint 4096 2868)/2)
    have hp : upperPayment 2867 = (178083926878:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2867+point split endpoint 4096 2868)/2 = (648269177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((648269177:ℝ)/168755200)*ClassicalSixthBranch.v ((648269177:ℝ)/168755200)/ClassicalSixthBranch.r = (96684703255745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2867
  · change upperPayment 2868 ≤ upperValue ((point split endpoint 4096 2868+point split endpoint 4096 2869)/2)
    have hp : upperPayment 2868 = (177960455717:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2868+point split endpoint 4096 2869)/2 = (648294327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((648294327:ℝ)/168755200)*ClassicalSixthBranch.v ((648294327:ℝ)/168755200)/ClassicalSixthBranch.r = (96664490977377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2868
  · change upperPayment 2869 ≤ upperValue ((point split endpoint 4096 2869+point split endpoint 4096 2870)/2)
    have hp : upperPayment 2869 = (177836952960:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2869+point split endpoint 4096 2870)/2 = (648319477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((648319477:ℝ)/168755200)*ClassicalSixthBranch.v ((648319477:ℝ)/168755200)/ClassicalSixthBranch.r = (96644280723081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2869
  · change upperPayment 2870 ≤ upperValue ((point split endpoint 4096 2870+point split endpoint 4096 2871)/2)
    have hp : upperPayment 2870 = (177713418600:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2870+point split endpoint 4096 2871)/2 = (648344627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((648344627:ℝ)/168755200)*ClassicalSixthBranch.v ((648344627:ℝ)/168755200)/ClassicalSixthBranch.r = (96624072492857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2870
  · change upperPayment 2871 ≤ upperValue ((point split endpoint 4096 2871+point split endpoint 4096 2872)/2)
    have hp : upperPayment 2871 = (177589852628:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2871+point split endpoint 4096 2872)/2 = (648369777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((648369777:ℝ)/168755200)*ClassicalSixthBranch.v ((648369777:ℝ)/168755200)/ClassicalSixthBranch.r = (96603866286705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2871
  · change upperPayment 2872 ≤ upperValue ((point split endpoint 4096 2872+point split endpoint 4096 2873)/2)
    have hp : upperPayment 2872 = (177466255038:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2872+point split endpoint 4096 2873)/2 = (648394927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((648394927:ℝ)/168755200)*ClassicalSixthBranch.v ((648394927:ℝ)/168755200)/ClassicalSixthBranch.r = (96583662104625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2872
  · change upperPayment 2873 ≤ upperValue ((point split endpoint 4096 2873+point split endpoint 4096 2874)/2)
    have hp : upperPayment 2873 = (177342625822:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2873+point split endpoint 4096 2874)/2 = (648420077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((648420077:ℝ)/168755200)*ClassicalSixthBranch.v ((648420077:ℝ)/168755200)/ClassicalSixthBranch.r = (96563459946617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2873
  · change upperPayment 2874 ≤ upperValue ((point split endpoint 4096 2874+point split endpoint 4096 2875)/2)
    have hp : upperPayment 2874 = (177218964973:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2874+point split endpoint 4096 2875)/2 = (648445227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((648445227:ℝ)/168755200)*ClassicalSixthBranch.v ((648445227:ℝ)/168755200)/ClassicalSixthBranch.r = (96543259812681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2874
  · change upperPayment 2875 ≤ upperValue ((point split endpoint 4096 2875+point split endpoint 4096 2876)/2)
    have hp : upperPayment 2875 = (177095272484:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2875+point split endpoint 4096 2876)/2 = (648470377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((648470377:ℝ)/168755200)*ClassicalSixthBranch.v ((648470377:ℝ)/168755200)/ClassicalSixthBranch.r = (96523061702817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2875
  · change upperPayment 2876 ≤ upperValue ((point split endpoint 4096 2876+point split endpoint 4096 2877)/2)
    have hp : upperPayment 2876 = (176971548347:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2876+point split endpoint 4096 2877)/2 = (648495527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((648495527:ℝ)/168755200)*ClassicalSixthBranch.v ((648495527:ℝ)/168755200)/ClassicalSixthBranch.r = (96502865617025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2876
  · change upperPayment 2877 ≤ upperValue ((point split endpoint 4096 2877+point split endpoint 4096 2878)/2)
    have hp : upperPayment 2877 = (176847792555:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2877+point split endpoint 4096 2878)/2 = (648520677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((648520677:ℝ)/168755200)*ClassicalSixthBranch.v ((648520677:ℝ)/168755200)/ClassicalSixthBranch.r = (96482671555305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2877
  · change upperPayment 2878 ≤ upperValue ((point split endpoint 4096 2878+point split endpoint 4096 2879)/2)
    have hp : upperPayment 2878 = (176724005100:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2878+point split endpoint 4096 2879)/2 = (648545827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((648545827:ℝ)/168755200)*ClassicalSixthBranch.v ((648545827:ℝ)/168755200)/ClassicalSixthBranch.r = (96462479517657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2878
  · change upperPayment 2879 ≤ upperValue ((point split endpoint 4096 2879+point split endpoint 4096 2880)/2)
    have hp : upperPayment 2879 = (176600185975:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2879+point split endpoint 4096 2880)/2 = (648570977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((648570977:ℝ)/168755200)*ClassicalSixthBranch.v ((648570977:ℝ)/168755200)/ClassicalSixthBranch.r = (96442289504081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2879
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_179
