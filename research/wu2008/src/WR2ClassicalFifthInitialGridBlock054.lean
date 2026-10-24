import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints054
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_054 (j : Fin 16) : initialPayment (16*54+j.val) ≤
    initialValue ((point lo 4 1024 (16*54+j.val)+point lo 4 1024 (16*54+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 864 ≤ initialValue ((point lo 4 1024 864+point lo 4 1024 865)/2)
    have hp : initialPayment 864 = (487855992109:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 864+point lo 4 1024 865)/2 = (164905189:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((164905189:ℝ)/42188800) = (67942400:ℝ)/47075099 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_864
  · change initialPayment 865 ≤ initialValue ((point lo 4 1024 865+point lo 4 1024 866)/2)
    have hp : initialPayment 865 = (488658962063:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 865+point lo 4 1024 866)/2 = (164929327:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((164929327:ℝ)/42188800) = (67942400:ℝ)/47050961 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_865
  · change initialPayment 866 ≤ initialValue ((point lo 4 1024 866+point lo 4 1024 867)/2)
    have hp : initialPayment 866 = (489462647766:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 866+point lo 4 1024 867)/2 = (32990693:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((32990693:ℝ)/8437760) = (67942400:ℝ)/47026823 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_866
  · change initialPayment 867 ≤ initialValue ((point lo 4 1024 867+point lo 4 1024 868)/2)
    have hp : initialPayment 867 = (490267049988:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 867+point lo 4 1024 868)/2 = (164977603:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((164977603:ℝ)/42188800) = (13588480:ℝ)/9400537 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_867
  · change initialPayment 868 ≤ initialValue ((point lo 4 1024 868+point lo 4 1024 869)/2)
    have hp : initialPayment 868 = (491072169501:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 868+point lo 4 1024 869)/2 = (165001741:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((165001741:ℝ)/42188800) = (67942400:ℝ)/46978547 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_868
  · change initialPayment 869 ≤ initialValue ((point lo 4 1024 869+point lo 4 1024 870)/2)
    have hp : initialPayment 869 = (491878007077:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 869+point lo 4 1024 870)/2 = (1602193:ℝ)/409600 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((1602193:ℝ)/409600) = (67942400:ℝ)/46954409 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_869
  · change initialPayment 870 ≤ initialValue ((point lo 4 1024 870+point lo 4 1024 871)/2)
    have hp : initialPayment 870 = (492684563491:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 870+point lo 4 1024 871)/2 = (165050017:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((165050017:ℝ)/42188800) = (67942400:ℝ)/46930271 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_870
  · change initialPayment 871 ≤ initialValue ((point lo 4 1024 871+point lo 4 1024 872)/2)
    have hp : initialPayment 871 = (493491839519:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 871+point lo 4 1024 872)/2 = (33014831:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((33014831:ℝ)/8437760) = (67942400:ℝ)/46906133 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_871
  · change initialPayment 872 ≤ initialValue ((point lo 4 1024 872+point lo 4 1024 873)/2)
    have hp : initialPayment 872 = (494299835936:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 872+point lo 4 1024 873)/2 = (165098293:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((165098293:ℝ)/42188800) = (13588480:ℝ)/9376399 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_872
  · change initialPayment 873 ≤ initialValue ((point lo 4 1024 873+point lo 4 1024 874)/2)
    have hp : initialPayment 873 = (495108553522:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 873+point lo 4 1024 874)/2 = (165122431:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((165122431:ℝ)/42188800) = (67942400:ℝ)/46857857 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_873
  · change initialPayment 874 ≤ initialValue ((point lo 4 1024 874+point lo 4 1024 875)/2)
    have hp : initialPayment 874 = (495917993055:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 874+point lo 4 1024 875)/2 = (165146569:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((165146569:ℝ)/42188800) = (67942400:ℝ)/46833719 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_874
  · change initialPayment 875 ≤ initialValue ((point lo 4 1024 875+point lo 4 1024 876)/2)
    have hp : initialPayment 875 = (496728155315:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 875+point lo 4 1024 876)/2 = (165170707:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((165170707:ℝ)/42188800) = (67942400:ℝ)/46809581 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_875
  · change initialPayment 876 ≤ initialValue ((point lo 4 1024 876+point lo 4 1024 877)/2)
    have hp : initialPayment 876 = (497539041085:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 876+point lo 4 1024 877)/2 = (33038969:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((33038969:ℝ)/8437760) = (67942400:ℝ)/46785443 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_876
  · change initialPayment 877 ≤ initialValue ((point lo 4 1024 877+point lo 4 1024 878)/2)
    have hp : initialPayment 877 = (498350651148:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 877+point lo 4 1024 878)/2 = (165218983:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((165218983:ℝ)/42188800) = (13588480:ℝ)/9352261 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_877
  · change initialPayment 878 ≤ initialValue ((point lo 4 1024 878+point lo 4 1024 879)/2)
    have hp : initialPayment 878 = (499162986287:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 878+point lo 4 1024 879)/2 = (165243121:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((165243121:ℝ)/42188800) = (67942400:ℝ)/46737167 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_878
  · change initialPayment 879 ≤ initialValue ((point lo 4 1024 879+point lo 4 1024 880)/2)
    have hp : initialPayment 879 = (499976047288:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 879+point lo 4 1024 880)/2 = (165267259:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((165267259:ℝ)/42188800) = (67942400:ℝ)/46713029 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_879
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_054
