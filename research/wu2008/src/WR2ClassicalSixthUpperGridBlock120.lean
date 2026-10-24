import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints120
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_120 (j : Fin 16) : upperPayment (16*120+j.val) ≤
    upperValue ((point split endpoint 4096 (16*120+j.val)+point split endpoint 4096 (16*120+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1920 ≤ upperValue ((point split endpoint 4096 1920+point split endpoint 4096 1921)/2)
    have hp : upperPayment 1920 = (281777764966:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1920+point split endpoint 4096 1921)/2 = (624452127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((624452127:ℝ)/168755200)*ClassicalSixthBranch.v ((624452127:ℝ)/168755200)/ClassicalSixthBranch.r = (116734292261457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1920
  · change upperPayment 1921 ≤ upperValue ((point split endpoint 4096 1921+point split endpoint 4096 1922)/2)
    have hp : upperPayment 1921 = (281681303640:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1921+point split endpoint 4096 1922)/2 = (624477277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((624477277:ℝ)/168755200)*ClassicalSixthBranch.v ((624477277:ℝ)/168755200)/ClassicalSixthBranch.r = (116712163186905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1921
  · change upperPayment 1922 ≤ upperValue ((point split endpoint 4096 1922+point split endpoint 4096 1923)/2)
    have hp : upperPayment 1922 = (281584816496:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1922+point split endpoint 4096 1923)/2 = (624502427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((624502427:ℝ)/168755200)*ClassicalSixthBranch.v ((624502427:ℝ)/168755200)/ClassicalSixthBranch.r = (116690036136425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1922
  · change upperPayment 1923 ≤ upperValue ((point split endpoint 4096 1923+point split endpoint 4096 1924)/2)
    have hp : upperPayment 1923 = (281488303529:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1923+point split endpoint 4096 1924)/2 = (624527577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((624527577:ℝ)/168755200)*ClassicalSixthBranch.v ((624527577:ℝ)/168755200)/ClassicalSixthBranch.r = (116667911110017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1923
  · change upperPayment 1924 ≤ upperValue ((point split endpoint 4096 1924+point split endpoint 4096 1925)/2)
    have hp : upperPayment 1924 = (281391764733:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1924+point split endpoint 4096 1925)/2 = (624552727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((624552727:ℝ)/168755200)*ClassicalSixthBranch.v ((624552727:ℝ)/168755200)/ClassicalSixthBranch.r = (116645788107681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1924
  · change upperPayment 1925 ≤ upperValue ((point split endpoint 4096 1925+point split endpoint 4096 1926)/2)
    have hp : upperPayment 1925 = (281295200104:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1925+point split endpoint 4096 1926)/2 = (624577877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((624577877:ℝ)/168755200)*ClassicalSixthBranch.v ((624577877:ℝ)/168755200)/ClassicalSixthBranch.r = (116623667129417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1925
  · change upperPayment 1926 ≤ upperValue ((point split endpoint 4096 1926+point split endpoint 4096 1927)/2)
    have hp : upperPayment 1926 = (281198609636:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1926+point split endpoint 4096 1927)/2 = (624603027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((624603027:ℝ)/168755200)*ClassicalSixthBranch.v ((624603027:ℝ)/168755200)/ClassicalSixthBranch.r = (116601548175225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1926
  · change upperPayment 1927 ≤ upperValue ((point split endpoint 4096 1927+point split endpoint 4096 1928)/2)
    have hp : upperPayment 1927 = (281101993325:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1927+point split endpoint 4096 1928)/2 = (624628177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((624628177:ℝ)/168755200)*ClassicalSixthBranch.v ((624628177:ℝ)/168755200)/ClassicalSixthBranch.r = (116579431245105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1927
  · change upperPayment 1928 ≤ upperValue ((point split endpoint 4096 1928+point split endpoint 4096 1929)/2)
    have hp : upperPayment 1928 = (281005351166:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1928+point split endpoint 4096 1929)/2 = (624653327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((624653327:ℝ)/168755200)*ClassicalSixthBranch.v ((624653327:ℝ)/168755200)/ClassicalSixthBranch.r = (116557316339057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1928
  · change upperPayment 1929 ≤ upperValue ((point split endpoint 4096 1929+point split endpoint 4096 1930)/2)
    have hp : upperPayment 1929 = (280908683153:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1929+point split endpoint 4096 1930)/2 = (624678477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((624678477:ℝ)/168755200)*ClassicalSixthBranch.v ((624678477:ℝ)/168755200)/ClassicalSixthBranch.r = (116535203457081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1929
  · change upperPayment 1930 ≤ upperValue ((point split endpoint 4096 1930+point split endpoint 4096 1931)/2)
    have hp : upperPayment 1930 = (280811989282:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1930+point split endpoint 4096 1931)/2 = (624703627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((624703627:ℝ)/168755200)*ClassicalSixthBranch.v ((624703627:ℝ)/168755200)/ClassicalSixthBranch.r = (116513092599177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1930
  · change upperPayment 1931 ≤ upperValue ((point split endpoint 4096 1931+point split endpoint 4096 1932)/2)
    have hp : upperPayment 1931 = (280715269547:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1931+point split endpoint 4096 1932)/2 = (624728777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((624728777:ℝ)/168755200)*ClassicalSixthBranch.v ((624728777:ℝ)/168755200)/ClassicalSixthBranch.r = (116490983765345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1931
  · change upperPayment 1932 ≤ upperValue ((point split endpoint 4096 1932+point split endpoint 4096 1933)/2)
    have hp : upperPayment 1932 = (280618523943:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1932+point split endpoint 4096 1933)/2 = (624753927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((624753927:ℝ)/168755200)*ClassicalSixthBranch.v ((624753927:ℝ)/168755200)/ClassicalSixthBranch.r = (116468876955585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1932
  · change upperPayment 1933 ≤ upperValue ((point split endpoint 4096 1933+point split endpoint 4096 1934)/2)
    have hp : upperPayment 1933 = (280521752466:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1933+point split endpoint 4096 1934)/2 = (624779077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((624779077:ℝ)/168755200)*ClassicalSixthBranch.v ((624779077:ℝ)/168755200)/ClassicalSixthBranch.r = (116446772169897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1933
  · change upperPayment 1934 ≤ upperValue ((point split endpoint 4096 1934+point split endpoint 4096 1935)/2)
    have hp : upperPayment 1934 = (280424955110:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1934+point split endpoint 4096 1935)/2 = (624804227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((624804227:ℝ)/168755200)*ClassicalSixthBranch.v ((624804227:ℝ)/168755200)/ClassicalSixthBranch.r = (116424669408281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1934
  · change upperPayment 1935 ≤ upperValue ((point split endpoint 4096 1935+point split endpoint 4096 1936)/2)
    have hp : upperPayment 1935 = (280328131871:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1935+point split endpoint 4096 1936)/2 = (624829377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((624829377:ℝ)/168755200)*ClassicalSixthBranch.v ((624829377:ℝ)/168755200)/ClassicalSixthBranch.r = (116402568670737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1935
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_120
