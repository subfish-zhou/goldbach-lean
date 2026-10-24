import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints061
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_061 (j : Fin 16) : initialPayment (16*61+j.val) ≤
    initialValue ((point lo 4 1024 (16*61+j.val)+point lo 4 1024 (16*61+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 976 ≤ initialValue ((point lo 4 1024 976+point lo 4 1024 977)/2)
    have hp : initialPayment 976 = (582421359492:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 976+point lo 4 1024 977)/2 = (33521729:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((33521729:ℝ)/8437760) = (67942400:ℝ)/44371643 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_976
  · change initialPayment 977 ≤ initialValue ((point lo 4 1024 977+point lo 4 1024 978)/2)
    have hp : initialPayment 977 = (583309580702:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 977+point lo 4 1024 978)/2 = (167632783:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((167632783:ℝ)/42188800) = (13588480:ℝ)/8869501 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_977
  · change initialPayment 978 ≤ initialValue ((point lo 4 1024 978+point lo 4 1024 979)/2)
    have hp : initialPayment 978 = (584198612243:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 978+point lo 4 1024 979)/2 = (167656921:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((167656921:ℝ)/42188800) = (67942400:ℝ)/44323367 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_978
  · change initialPayment 979 ≤ initialValue ((point lo 4 1024 979+point lo 4 1024 980)/2)
    have hp : initialPayment 979 = (585088455038:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 979+point lo 4 1024 980)/2 = (167681059:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((167681059:ℝ)/42188800) = (67942400:ℝ)/44299229 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_979
  · change initialPayment 980 ≤ initialValue ((point lo 4 1024 980+point lo 4 1024 981)/2)
    have hp : initialPayment 980 = (585979110016:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 980+point lo 4 1024 981)/2 = (167705197:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((167705197:ℝ)/42188800) = (67942400:ℝ)/44275091 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_980
  · change initialPayment 981 ≤ initialValue ((point lo 4 1024 981+point lo 4 1024 982)/2)
    have hp : initialPayment 981 = (586870578106:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 981+point lo 4 1024 982)/2 = (33545867:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((33545867:ℝ)/8437760) = (67942400:ℝ)/44250953 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_981
  · change initialPayment 982 ≤ initialValue ((point lo 4 1024 982+point lo 4 1024 983)/2)
    have hp : initialPayment 982 = (587762860236:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 982+point lo 4 1024 983)/2 = (167753473:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((167753473:ℝ)/42188800) = (13588480:ℝ)/8845363 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_982
  · change initialPayment 983 ≤ initialValue ((point lo 4 1024 983+point lo 4 1024 984)/2)
    have hp : initialPayment 983 = (588655957341:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 983+point lo 4 1024 984)/2 = (167777611:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((167777611:ℝ)/42188800) = (67942400:ℝ)/44202677 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_983
  · change initialPayment 984 ≤ initialValue ((point lo 4 1024 984+point lo 4 1024 985)/2)
    have hp : initialPayment 984 = (589549870352:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 984+point lo 4 1024 985)/2 = (167801749:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((167801749:ℝ)/42188800) = (67942400:ℝ)/44178539 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_984
  · change initialPayment 985 ≤ initialValue ((point lo 4 1024 985+point lo 4 1024 986)/2)
    have hp : initialPayment 985 = (590444600205:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 985+point lo 4 1024 986)/2 = (167825887:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((167825887:ℝ)/42188800) = (67942400:ℝ)/44154401 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_985
  · change initialPayment 986 ≤ initialValue ((point lo 4 1024 986+point lo 4 1024 987)/2)
    have hp : initialPayment 986 = (591340147836:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 986+point lo 4 1024 987)/2 = (6714001:ℝ)/1687552 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((6714001:ℝ)/1687552) = (67942400:ℝ)/44130263 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_986
  · change initialPayment 987 ≤ initialValue ((point lo 4 1024 987+point lo 4 1024 988)/2)
    have hp : initialPayment 987 = (592236514184:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 987+point lo 4 1024 988)/2 = (167874163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((167874163:ℝ)/42188800) = (2717696:ℝ)/1764245 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_987
  · change initialPayment 988 ≤ initialValue ((point lo 4 1024 988+point lo 4 1024 989)/2)
    have hp : initialPayment 988 = (593133700188:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 988+point lo 4 1024 989)/2 = (167898301:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((167898301:ℝ)/42188800) = (67942400:ℝ)/44081987 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_988
  · change initialPayment 989 ≤ initialValue ((point lo 4 1024 989+point lo 4 1024 990)/2)
    have hp : initialPayment 989 = (594031706790:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 989+point lo 4 1024 990)/2 = (167922439:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((167922439:ℝ)/42188800) = (67942400:ℝ)/44057849 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_989
  · change initialPayment 990 ≤ initialValue ((point lo 4 1024 990+point lo 4 1024 991)/2)
    have hp : initialPayment 990 = (594930534932:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 990+point lo 4 1024 991)/2 = (167946577:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((167946577:ℝ)/42188800) = (67942400:ℝ)/44033711 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_990
  · change initialPayment 991 ≤ initialValue ((point lo 4 1024 991+point lo 4 1024 992)/2)
    have hp : initialPayment 991 = (595830185559:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 991+point lo 4 1024 992)/2 = (33594143:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((33594143:ℝ)/8437760) = (67942400:ℝ)/44009573 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_991
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_061
