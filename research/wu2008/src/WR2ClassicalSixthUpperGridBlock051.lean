import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints051
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_051 (j : Fin 16) : upperPayment (16*51+j.val) ≤
    upperValue ((point split endpoint 4096 (16*51+j.val)+point split endpoint 4096 (16*51+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 816 ≤ upperValue ((point split endpoint 4096 816+point split endpoint 4096 817)/2)
    have hp : upperPayment 816 = (373533303811:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 816+point split endpoint 4096 817)/2 = (596686527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((596686527:ℝ)/168755200)*ClassicalSixthBranch.v ((596686527:ℝ)/168755200)/ClassicalSixthBranch.r = (142399393523985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_816
  · change upperPayment 817 ≤ upperValue ((point split endpoint 4096 817+point split endpoint 4096 818)/2)
    have hp : upperPayment 817 = (373462703134:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 817+point split endpoint 4096 818)/2 = (596711677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((596711677:ℝ)/168755200)*ClassicalSixthBranch.v ((596711677:ℝ)/168755200)/ClassicalSixthBranch.r = (142375029873945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_817
  · change upperPayment 818 ≤ upperValue ((point split endpoint 4096 818+point split endpoint 4096 819)/2)
    have hp : upperPayment 818 = (373392081080:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 818+point split endpoint 4096 819)/2 = (596736827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((596736827:ℝ)/168755200)*ClassicalSixthBranch.v ((596736827:ℝ)/168755200)/ClassicalSixthBranch.r = (142350668247977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_818
  · change upperPayment 819 ≤ upperValue ((point split endpoint 4096 819+point split endpoint 4096 820)/2)
    have hp : upperPayment 819 = (373321437647:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 819+point split endpoint 4096 820)/2 = (596761977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((596761977:ℝ)/168755200)*ClassicalSixthBranch.v ((596761977:ℝ)/168755200)/ClassicalSixthBranch.r = (142326308646081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_819
  · change upperPayment 820 ≤ upperValue ((point split endpoint 4096 820+point split endpoint 4096 821)/2)
    have hp : upperPayment 820 = (373250772830:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 820+point split endpoint 4096 821)/2 = (596787127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((596787127:ℝ)/168755200)*ClassicalSixthBranch.v ((596787127:ℝ)/168755200)/ClassicalSixthBranch.r = (142301951068257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_820
  · change upperPayment 821 ≤ upperValue ((point split endpoint 4096 821+point split endpoint 4096 822)/2)
    have hp : upperPayment 821 = (373180086627:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 821+point split endpoint 4096 822)/2 = (596812277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((596812277:ℝ)/168755200)*ClassicalSixthBranch.v ((596812277:ℝ)/168755200)/ClassicalSixthBranch.r = (142277595514505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_821
  · change upperPayment 822 ≤ upperValue ((point split endpoint 4096 822+point split endpoint 4096 823)/2)
    have hp : upperPayment 822 = (373109379034:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 822+point split endpoint 4096 823)/2 = (596837427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((596837427:ℝ)/168755200)*ClassicalSixthBranch.v ((596837427:ℝ)/168755200)/ClassicalSixthBranch.r = (142253241984825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_822
  · change upperPayment 823 ≤ upperValue ((point split endpoint 4096 823+point split endpoint 4096 824)/2)
    have hp : upperPayment 823 = (373038650049:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 823+point split endpoint 4096 824)/2 = (596862577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((596862577:ℝ)/168755200)*ClassicalSixthBranch.v ((596862577:ℝ)/168755200)/ClassicalSixthBranch.r = (142228890479217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_823
  · change upperPayment 824 ≤ upperValue ((point split endpoint 4096 824+point split endpoint 4096 825)/2)
    have hp : upperPayment 824 = (372967899667:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 824+point split endpoint 4096 825)/2 = (596887727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((596887727:ℝ)/168755200)*ClassicalSixthBranch.v ((596887727:ℝ)/168755200)/ClassicalSixthBranch.r = (142204540997681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_824
  · change upperPayment 825 ≤ upperValue ((point split endpoint 4096 825+point split endpoint 4096 826)/2)
    have hp : upperPayment 825 = (372897127887:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 825+point split endpoint 4096 826)/2 = (596912877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((596912877:ℝ)/168755200)*ClassicalSixthBranch.v ((596912877:ℝ)/168755200)/ClassicalSixthBranch.r = (142180193540217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_825
  · change upperPayment 826 ≤ upperValue ((point split endpoint 4096 826+point split endpoint 4096 827)/2)
    have hp : upperPayment 826 = (372826334705:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 826+point split endpoint 4096 827)/2 = (596938027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((596938027:ℝ)/168755200)*ClassicalSixthBranch.v ((596938027:ℝ)/168755200)/ClassicalSixthBranch.r = (142155848106825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_826
  · change upperPayment 827 ≤ upperValue ((point split endpoint 4096 827+point split endpoint 4096 828)/2)
    have hp : upperPayment 827 = (372755520117:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 827+point split endpoint 4096 828)/2 = (5795759:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((5795759:ℝ)/1638400)*ClassicalSixthBranch.v ((5795759:ℝ)/1638400)/ClassicalSixthBranch.r = (1379917521335:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_827
  · change upperPayment 828 ≤ upperValue ((point split endpoint 4096 828+point split endpoint 4096 829)/2)
    have hp : upperPayment 828 = (372684684121:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 828+point split endpoint 4096 829)/2 = (596988327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((596988327:ℝ)/168755200)*ClassicalSixthBranch.v ((596988327:ℝ)/168755200)/ClassicalSixthBranch.r = (142107163312257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_828
  · change upperPayment 829 ≤ upperValue ((point split endpoint 4096 829+point split endpoint 4096 830)/2)
    have hp : upperPayment 829 = (372613826713:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 829+point split endpoint 4096 830)/2 = (597013477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((597013477:ℝ)/168755200)*ClassicalSixthBranch.v ((597013477:ℝ)/168755200)/ClassicalSixthBranch.r = (142082823951081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_829
  · change upperPayment 830 ≤ upperValue ((point split endpoint 4096 830+point split endpoint 4096 831)/2)
    have hp : upperPayment 830 = (372542947891:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 830+point split endpoint 4096 831)/2 = (597038627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((597038627:ℝ)/168755200)*ClassicalSixthBranch.v ((597038627:ℝ)/168755200)/ClassicalSixthBranch.r = (142058486613977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_830
  · change upperPayment 831 ≤ upperValue ((point split endpoint 4096 831+point split endpoint 4096 832)/2)
    have hp : upperPayment 831 = (372472047650:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 831+point split endpoint 4096 832)/2 = (597063777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((597063777:ℝ)/168755200)*ClassicalSixthBranch.v ((597063777:ℝ)/168755200)/ClassicalSixthBranch.r = (142034151300945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_831
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_051
