import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints058
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_058 (j : Fin 16) : initialPayment (16*58+j.val) ≤
    initialValue ((point lo 4 1024 (16*58+j.val)+point lo 4 1024 (16*58+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 928 ≤ initialValue ((point lo 4 1024 928+point lo 4 1024 929)/2)
    have hp : initialPayment 928 = (540721925644:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 928+point lo 4 1024 929)/2 = (166450021:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((166450021:ℝ)/42188800) = (67942400:ℝ)/45530267 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_928
  · change initialPayment 929 ≤ initialValue ((point lo 4 1024 929+point lo 4 1024 930)/2)
    have hp : initialPayment 929 = (541572309988:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 929+point lo 4 1024 930)/2 = (166474159:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((166474159:ℝ)/42188800) = (67942400:ℝ)/45506129 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_929
  · change initialPayment 930 ≤ initialValue ((point lo 4 1024 930+point lo 4 1024 931)/2)
    have hp : initialPayment 930 = (542423461992:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 930+point lo 4 1024 931)/2 = (166498297:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((166498297:ℝ)/42188800) = (67942400:ℝ)/45481991 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_930
  · change initialPayment 931 ≤ initialValue ((point lo 4 1024 931+point lo 4 1024 932)/2)
    have hp : initialPayment 931 = (543275382513:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 931+point lo 4 1024 932)/2 = (33304487:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((33304487:ℝ)/8437760) = (67942400:ℝ)/45457853 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_931
  · change initialPayment 932 ≤ initialValue ((point lo 4 1024 932+point lo 4 1024 933)/2)
    have hp : initialPayment 932 = (544128072405:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 932+point lo 4 1024 933)/2 = (166546573:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((166546573:ℝ)/42188800) = (13588480:ℝ)/9086743 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_932
  · change initialPayment 933 ≤ initialValue ((point lo 4 1024 933+point lo 4 1024 934)/2)
    have hp : initialPayment 933 = (544981532526:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 933+point lo 4 1024 934)/2 = (166570711:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((166570711:ℝ)/42188800) = (67942400:ℝ)/45409577 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_933
  · change initialPayment 934 ≤ initialValue ((point lo 4 1024 934+point lo 4 1024 935)/2)
    have hp : initialPayment 934 = (545835763737:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 934+point lo 4 1024 935)/2 = (166594849:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((166594849:ℝ)/42188800) = (67942400:ℝ)/45385439 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_934
  · change initialPayment 935 ≤ initialValue ((point lo 4 1024 935+point lo 4 1024 936)/2)
    have hp : initialPayment 935 = (546690766896:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 935+point lo 4 1024 936)/2 = (166618987:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((166618987:ℝ)/42188800) = (67942400:ℝ)/45361301 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_935
  · change initialPayment 936 ≤ initialValue ((point lo 4 1024 936+point lo 4 1024 937)/2)
    have hp : initialPayment 936 = (547546542867:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 936+point lo 4 1024 937)/2 = (6665725:ℝ)/1687552 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((6665725:ℝ)/1687552) = (67942400:ℝ)/45337163 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_936
  · change initialPayment 937 ≤ initialValue ((point lo 4 1024 937+point lo 4 1024 938)/2)
    have hp : initialPayment 937 = (548403092511:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 937+point lo 4 1024 938)/2 = (166667263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((166667263:ℝ)/42188800) = (2717696:ℝ)/1812521 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_937
  · change initialPayment 938 ≤ initialValue ((point lo 4 1024 938+point lo 4 1024 939)/2)
    have hp : initialPayment 938 = (549260416695:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 938+point lo 4 1024 939)/2 = (166691401:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((166691401:ℝ)/42188800) = (67942400:ℝ)/45288887 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_938
  · change initialPayment 939 ≤ initialValue ((point lo 4 1024 939+point lo 4 1024 940)/2)
    have hp : initialPayment 939 = (550118516285:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 939+point lo 4 1024 940)/2 = (166715539:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((166715539:ℝ)/42188800) = (67942400:ℝ)/45264749 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_939
  · change initialPayment 940 ≤ initialValue ((point lo 4 1024 940+point lo 4 1024 941)/2)
    have hp : initialPayment 940 = (550977392147:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 940+point lo 4 1024 941)/2 = (166739677:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((166739677:ℝ)/42188800) = (67942400:ℝ)/45240611 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_940
  · change initialPayment 941 ≤ initialValue ((point lo 4 1024 941+point lo 4 1024 942)/2)
    have hp : initialPayment 941 = (551837045151:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 941+point lo 4 1024 942)/2 = (33352763:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((33352763:ℝ)/8437760) = (67942400:ℝ)/45216473 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_941
  · change initialPayment 942 ≤ initialValue ((point lo 4 1024 942+point lo 4 1024 943)/2)
    have hp : initialPayment 942 = (552697476167:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 942+point lo 4 1024 943)/2 = (166787953:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((166787953:ℝ)/42188800) = (13588480:ℝ)/9038467 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_942
  · change initialPayment 943 ≤ initialValue ((point lo 4 1024 943+point lo 4 1024 944)/2)
    have hp : initialPayment 943 = (553558686068:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 943+point lo 4 1024 944)/2 = (166812091:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((166812091:ℝ)/42188800) = (67942400:ℝ)/45168197 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_943
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_058
