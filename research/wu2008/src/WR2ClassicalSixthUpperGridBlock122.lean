import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints122
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_122 (j : Fin 16) : upperPayment (16*122+j.val) ≤
    upperValue ((point split endpoint 4096 (16*122+j.val)+point split endpoint 4096 (16*122+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1952 ≤ upperValue ((point split endpoint 4096 1952+point split endpoint 4096 1953)/2)
    have hp : upperPayment 1952 = (278678171708:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1952+point split endpoint 4096 1953)/2 = (625256927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((625256927:ℝ)/168755200)*ClassicalSixthBranch.v ((625256927:ℝ)/168755200)/ClassicalSixthBranch.r = (116027165815505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1952
  · change upperPayment 1953 ≤ upperValue ((point split endpoint 4096 1953+point split endpoint 4096 1954)/2)
    have hp : upperPayment 1953 = (278580881698:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1953+point split endpoint 4096 1954)/2 = (625282077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((625282077:ℝ)/168755200)*ClassicalSixthBranch.v ((625282077:ℝ)/168755200)/ClassicalSixthBranch.r = (116005101511257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1953
  · change upperPayment 1954 ≤ upperValue ((point split endpoint 4096 1954+point split endpoint 4096 1955)/2)
    have hp : upperPayment 1954 = (278483565709:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1954+point split endpoint 4096 1955)/2 = (625307227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((625307227:ℝ)/168755200)*ClassicalSixthBranch.v ((625307227:ℝ)/168755200)/ClassicalSixthBranch.r = (115983039231081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1954
  · change upperPayment 1955 ≤ upperValue ((point split endpoint 4096 1955+point split endpoint 4096 1956)/2)
    have hp : upperPayment 1955 = (278386223735:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1955+point split endpoint 4096 1956)/2 = (625332377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((625332377:ℝ)/168755200)*ClassicalSixthBranch.v ((625332377:ℝ)/168755200)/ClassicalSixthBranch.r = (115960978974977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1955
  · change upperPayment 1956 ≤ upperValue ((point split endpoint 4096 1956+point split endpoint 4096 1957)/2)
    have hp : upperPayment 1956 = (278288855771:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1956+point split endpoint 4096 1957)/2 = (625357527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((625357527:ℝ)/168755200)*ClassicalSixthBranch.v ((625357527:ℝ)/168755200)/ClassicalSixthBranch.r = (115938920742945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1956
  · change upperPayment 1957 ≤ upperValue ((point split endpoint 4096 1957+point split endpoint 4096 1958)/2)
    have hp : upperPayment 1957 = (278191461812:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1957+point split endpoint 4096 1958)/2 = (625382677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((625382677:ℝ)/168755200)*ClassicalSixthBranch.v ((625382677:ℝ)/168755200)/ClassicalSixthBranch.r = (115916864534985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1957
  · change upperPayment 1958 ≤ upperValue ((point split endpoint 4096 1958+point split endpoint 4096 1959)/2)
    have hp : upperPayment 1958 = (278094041853:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1958+point split endpoint 4096 1959)/2 = (625407827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((625407827:ℝ)/168755200)*ClassicalSixthBranch.v ((625407827:ℝ)/168755200)/ClassicalSixthBranch.r = (115894810351097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1958
  · change upperPayment 1959 ≤ upperValue ((point split endpoint 4096 1959+point split endpoint 4096 1960)/2)
    have hp : upperPayment 1959 = (277996595889:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1959+point split endpoint 4096 1960)/2 = (625432977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((625432977:ℝ)/168755200)*ClassicalSixthBranch.v ((625432977:ℝ)/168755200)/ClassicalSixthBranch.r = (115872758191281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1959
  · change upperPayment 1960 ≤ upperValue ((point split endpoint 4096 1960+point split endpoint 4096 1961)/2)
    have hp : upperPayment 1960 = (277899123915:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1960+point split endpoint 4096 1961)/2 = (6072409:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((6072409:ℝ)/1638400)*ClassicalSixthBranch.v ((6072409:ℝ)/1638400)/ClassicalSixthBranch.r = (1124764155879:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1960
  · change upperPayment 1961 ≤ upperValue ((point split endpoint 4096 1961+point split endpoint 4096 1962)/2)
    have hp : upperPayment 1961 = (277801625925:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1961+point split endpoint 4096 1962)/2 = (625483277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((625483277:ℝ)/168755200)*ClassicalSixthBranch.v ((625483277:ℝ)/168755200)/ClassicalSixthBranch.r = (115828659943865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1961
  · change upperPayment 1962 ≤ upperValue ((point split endpoint 4096 1962+point split endpoint 4096 1963)/2)
    have hp : upperPayment 1962 = (277704101914:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1962+point split endpoint 4096 1963)/2 = (625508427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((625508427:ℝ)/168755200)*ClassicalSixthBranch.v ((625508427:ℝ)/168755200)/ClassicalSixthBranch.r = (115806613856265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1962
  · change upperPayment 1963 ≤ upperValue ((point split endpoint 4096 1963+point split endpoint 4096 1964)/2)
    have hp : upperPayment 1963 = (277606551878:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1963+point split endpoint 4096 1964)/2 = (625533577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((625533577:ℝ)/168755200)*ClassicalSixthBranch.v ((625533577:ℝ)/168755200)/ClassicalSixthBranch.r = (115784569792737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1963
  · change upperPayment 1964 ≤ upperValue ((point split endpoint 4096 1964+point split endpoint 4096 1965)/2)
    have hp : upperPayment 1964 = (277508975812:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1964+point split endpoint 4096 1965)/2 = (625558727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((625558727:ℝ)/168755200)*ClassicalSixthBranch.v ((625558727:ℝ)/168755200)/ClassicalSixthBranch.r = (115762527753281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1964
  · change upperPayment 1965 ≤ upperValue ((point split endpoint 4096 1965+point split endpoint 4096 1966)/2)
    have hp : upperPayment 1965 = (277411373709:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1965+point split endpoint 4096 1966)/2 = (625583877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((625583877:ℝ)/168755200)*ClassicalSixthBranch.v ((625583877:ℝ)/168755200)/ClassicalSixthBranch.r = (115740487737897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1965
  · change upperPayment 1966 ≤ upperValue ((point split endpoint 4096 1966+point split endpoint 4096 1967)/2)
    have hp : upperPayment 1966 = (277313745566:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1966+point split endpoint 4096 1967)/2 = (625609027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((625609027:ℝ)/168755200)*ClassicalSixthBranch.v ((625609027:ℝ)/168755200)/ClassicalSixthBranch.r = (115718449746585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1966
  · change upperPayment 1967 ≤ upperValue ((point split endpoint 4096 1967+point split endpoint 4096 1968)/2)
    have hp : upperPayment 1967 = (277216091377:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1967+point split endpoint 4096 1968)/2 = (625634177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((625634177:ℝ)/168755200)*ClassicalSixthBranch.v ((625634177:ℝ)/168755200)/ClassicalSixthBranch.r = (115696413779345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1967
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_122
