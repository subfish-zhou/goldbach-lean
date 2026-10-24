import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints053
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_053 (j : Fin 16) : initialPayment (16*53+j.val) ≤
    initialValue ((point lo 4 1024 (16*53+j.val)+point lo 4 1024 (16*53+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 848 ≤ initialValue ((point lo 4 1024 848+point lo 4 1024 849)/2)
    have hp : initialPayment 848 = (475105190655:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 848+point lo 4 1024 849)/2 = (164518981:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((164518981:ℝ)/42188800) = (67942400:ℝ)/47461307 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_848
  · change initialPayment 849 ≤ initialValue ((point lo 4 1024 849+point lo 4 1024 850)/2)
    have hp : initialPayment 849 = (475896812422:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 849+point lo 4 1024 850)/2 = (164543119:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((164543119:ℝ)/42188800) = (67942400:ℝ)/47437169 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_849
  · change initialPayment 850 ≤ initialValue ((point lo 4 1024 850+point lo 4 1024 851)/2)
    have hp : initialPayment 850 = (476689137775:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 850+point lo 4 1024 851)/2 = (164567257:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((164567257:ℝ)/42188800) = (67942400:ℝ)/47413031 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_850
  · change initialPayment 851 ≤ initialValue ((point lo 4 1024 851+point lo 4 1024 852)/2)
    have hp : initialPayment 851 = (477482167467:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 851+point lo 4 1024 852)/2 = (32918279:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((32918279:ℝ)/8437760) = (67942400:ℝ)/47388893 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_851
  · change initialPayment 852 ≤ initialValue ((point lo 4 1024 852+point lo 4 1024 853)/2)
    have hp : initialPayment 852 = (478275902249:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 852+point lo 4 1024 853)/2 = (164615533:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((164615533:ℝ)/42188800) = (13588480:ℝ)/9472951 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_852
  · change initialPayment 853 ≤ initialValue ((point lo 4 1024 853+point lo 4 1024 854)/2)
    have hp : initialPayment 853 = (479070342874:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 853+point lo 4 1024 854)/2 = (164639671:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((164639671:ℝ)/42188800) = (67942400:ℝ)/47340617 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_853
  · change initialPayment 854 ≤ initialValue ((point lo 4 1024 854+point lo 4 1024 855)/2)
    have hp : initialPayment 854 = (479865490097:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 854+point lo 4 1024 855)/2 = (164663809:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((164663809:ℝ)/42188800) = (67942400:ℝ)/47316479 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_854
  · change initialPayment 855 ≤ initialValue ((point lo 4 1024 855+point lo 4 1024 856)/2)
    have hp : initialPayment 855 = (480661344674:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 855+point lo 4 1024 856)/2 = (164687947:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((164687947:ℝ)/42188800) = (67942400:ℝ)/47292341 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_855
  · change initialPayment 856 ≤ initialValue ((point lo 4 1024 856+point lo 4 1024 857)/2)
    have hp : initialPayment 856 = (481457907362:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 856+point lo 4 1024 857)/2 = (32942417:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((32942417:ℝ)/8437760) = (67942400:ℝ)/47268203 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_856
  · change initialPayment 857 ≤ initialValue ((point lo 4 1024 857+point lo 4 1024 858)/2)
    have hp : initialPayment 857 = (482255178920:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 857+point lo 4 1024 858)/2 = (164736223:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((164736223:ℝ)/42188800) = (13588480:ℝ)/9448813 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_857
  · change initialPayment 858 ≤ initialValue ((point lo 4 1024 858+point lo 4 1024 859)/2)
    have hp : initialPayment 858 = (483053160106:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 858+point lo 4 1024 859)/2 = (164760361:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((164760361:ℝ)/42188800) = (67942400:ℝ)/47219927 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_858
  · change initialPayment 859 ≤ initialValue ((point lo 4 1024 859+point lo 4 1024 860)/2)
    have hp : initialPayment 859 = (483851851681:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 859+point lo 4 1024 860)/2 = (164784499:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((164784499:ℝ)/42188800) = (67942400:ℝ)/47195789 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_859
  · change initialPayment 860 ≤ initialValue ((point lo 4 1024 860+point lo 4 1024 861)/2)
    have hp : initialPayment 860 = (484651254408:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 860+point lo 4 1024 861)/2 = (164808637:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((164808637:ℝ)/42188800) = (67942400:ℝ)/47171651 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_860
  · change initialPayment 861 ≤ initialValue ((point lo 4 1024 861+point lo 4 1024 862)/2)
    have hp : initialPayment 861 = (485451369049:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 861+point lo 4 1024 862)/2 = (6593311:ℝ)/1687552 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((6593311:ℝ)/1687552) = (67942400:ℝ)/47147513 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_861
  · change initialPayment 862 ≤ initialValue ((point lo 4 1024 862+point lo 4 1024 863)/2)
    have hp : initialPayment 862 = (486252196369:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 862+point lo 4 1024 863)/2 = (164856913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((164856913:ℝ)/42188800) = (2717696:ℝ)/1884935 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_862
  · change initialPayment 863 ≤ initialValue ((point lo 4 1024 863+point lo 4 1024 864)/2)
    have hp : initialPayment 863 = (487053737133:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 863+point lo 4 1024 864)/2 = (164881051:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((164881051:ℝ)/42188800) = (67942400:ℝ)/47099237 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_863
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_053
