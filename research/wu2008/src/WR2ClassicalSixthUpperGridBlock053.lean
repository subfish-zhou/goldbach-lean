import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints053
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_053 (j : Fin 16) : upperPayment (16*53+j.val) ≤
    upperValue ((point split endpoint 4096 (16*53+j.val)+point split endpoint 4096 (16*53+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 848 ≤ upperValue ((point split endpoint 4096 848+point split endpoint 4096 849)/2)
    have hp : upperPayment 848 = (371263463547:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 848+point split endpoint 4096 849)/2 = (597491327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((597491327:ℝ)/168755200)*ClassicalSixthBranch.v ((597491327:ℝ)/168755200)/ClassicalSixthBranch.r = (141620760662417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_848
  · change upperPayment 849 ≤ upperValue ((point split endpoint 4096 849+point split endpoint 4096 850)/2)
    have hp : upperPayment 849 = (371192177241:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 849+point split endpoint 4096 850)/2 = (597516477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((597516477:ℝ)/168755200)*ClassicalSixthBranch.v ((597516477:ℝ)/168755200)/ClassicalSixthBranch.r = (141596461782681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_849
  · change upperPayment 850 ≤ upperValue ((point split endpoint 4096 850+point split endpoint 4096 851)/2)
    have hp : upperPayment 850 = (371120869457:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 850+point split endpoint 4096 851)/2 = (597541627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((597541627:ℝ)/168755200)*ClassicalSixthBranch.v ((597541627:ℝ)/168755200)/ClassicalSixthBranch.r = (141572164927017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_850
  · change upperPayment 851 ≤ upperValue ((point split endpoint 4096 851+point split endpoint 4096 852)/2)
    have hp : upperPayment 851 = (371049540191:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 851+point split endpoint 4096 852)/2 = (597566777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((597566777:ℝ)/168755200)*ClassicalSixthBranch.v ((597566777:ℝ)/168755200)/ClassicalSixthBranch.r = (1374251165975:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_851
  · change upperPayment 852 ≤ upperValue ((point split endpoint 4096 852+point split endpoint 4096 853)/2)
    have hp : upperPayment 852 = (370978189441:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 852+point split endpoint 4096 853)/2 = (597591927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((597591927:ℝ)/168755200)*ClassicalSixthBranch.v ((597591927:ℝ)/168755200)/ClassicalSixthBranch.r = (141523577287905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_852
  · change upperPayment 853 ≤ upperValue ((point split endpoint 4096 853+point split endpoint 4096 854)/2)
    have hp : upperPayment 853 = (370906817202:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 853+point split endpoint 4096 854)/2 = (597617077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((597617077:ℝ)/168755200)*ClassicalSixthBranch.v ((597617077:ℝ)/168755200)/ClassicalSixthBranch.r = (141499286504457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_853
  · change upperPayment 854 ≤ upperValue ((point split endpoint 4096 854+point split endpoint 4096 855)/2)
    have hp : upperPayment 854 = (370835423473:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 854+point split endpoint 4096 855)/2 = (597642227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((597642227:ℝ)/168755200)*ClassicalSixthBranch.v ((597642227:ℝ)/168755200)/ClassicalSixthBranch.r = (141474997745081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_854
  · change upperPayment 855 ≤ upperValue ((point split endpoint 4096 855+point split endpoint 4096 856)/2)
    have hp : upperPayment 855 = (370764008249:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 855+point split endpoint 4096 856)/2 = (597667377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((597667377:ℝ)/168755200)*ClassicalSixthBranch.v ((597667377:ℝ)/168755200)/ClassicalSixthBranch.r = (141450711009777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_855
  · change upperPayment 856 ≤ upperValue ((point split endpoint 4096 856+point split endpoint 4096 857)/2)
    have hp : upperPayment 856 = (370692571528:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 856+point split endpoint 4096 857)/2 = (597692527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((597692527:ℝ)/168755200)*ClassicalSixthBranch.v ((597692527:ℝ)/168755200)/ClassicalSixthBranch.r = (141426426298545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_856
  · change upperPayment 857 ≤ upperValue ((point split endpoint 4096 857+point split endpoint 4096 858)/2)
    have hp : upperPayment 857 = (370621113306:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 857+point split endpoint 4096 858)/2 = (597717677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((597717677:ℝ)/168755200)*ClassicalSixthBranch.v ((597717677:ℝ)/168755200)/ClassicalSixthBranch.r = (141402143611385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_857
  · change upperPayment 858 ≤ upperValue ((point split endpoint 4096 858+point split endpoint 4096 859)/2)
    have hp : upperPayment 858 = (370549633581:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 858+point split endpoint 4096 859)/2 = (597742827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((597742827:ℝ)/168755200)*ClassicalSixthBranch.v ((597742827:ℝ)/168755200)/ClassicalSixthBranch.r = (141377862948297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_858
  · change upperPayment 859 ≤ upperValue ((point split endpoint 4096 859+point split endpoint 4096 860)/2)
    have hp : upperPayment 859 = (370478132348:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 859+point split endpoint 4096 860)/2 = (597767977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((597767977:ℝ)/168755200)*ClassicalSixthBranch.v ((597767977:ℝ)/168755200)/ClassicalSixthBranch.r = (141353584309281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_859
  · change upperPayment 860 ≤ upperValue ((point split endpoint 4096 860+point split endpoint 4096 861)/2)
    have hp : upperPayment 860 = (370406609605:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 860+point split endpoint 4096 861)/2 = (597793127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((597793127:ℝ)/168755200)*ClassicalSixthBranch.v ((597793127:ℝ)/168755200)/ClassicalSixthBranch.r = (141329307694337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_860
  · change upperPayment 861 ≤ upperValue ((point split endpoint 4096 861+point split endpoint 4096 862)/2)
    have hp : upperPayment 861 = (370335065348:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 861+point split endpoint 4096 862)/2 = (597818277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((597818277:ℝ)/168755200)*ClassicalSixthBranch.v ((597818277:ℝ)/168755200)/ClassicalSixthBranch.r = (141305033103465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_861
  · change upperPayment 862 ≤ upperValue ((point split endpoint 4096 862+point split endpoint 4096 863)/2)
    have hp : upperPayment 862 = (370263499575:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 862+point split endpoint 4096 863)/2 = (597843427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((597843427:ℝ)/168755200)*ClassicalSixthBranch.v ((597843427:ℝ)/168755200)/ClassicalSixthBranch.r = (141280760536665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_862
  · change upperPayment 863 ≤ upperValue ((point split endpoint 4096 863+point split endpoint 4096 864)/2)
    have hp : upperPayment 863 = (370191912282:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 863+point split endpoint 4096 864)/2 = (597868577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((597868577:ℝ)/168755200)*ClassicalSixthBranch.v ((597868577:ℝ)/168755200)/ClassicalSixthBranch.r = (141256489993937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_863
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_053
