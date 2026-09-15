import Wu18938Campaign.M3.Confirmed.TableBounds

noncomputable section
namespace Wu18938Campaign.M3.Confirmed.TableRow05
open Real Set MeasureTheory QuarterTrim
open WuSource.SrcSixthGain Wu18938Campaign.M3.Confirmed.TableBounds

private theorem panel00 : (2606758699124622 / 18446744073709551616 : ℝ) ≤
    8 * (127132 / 10000000 : ℝ) * ∫ s in (5 / 2 : ℝ)..(801 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (5 / 2 : ℝ)) (b := (801 / 320 : ℝ))
    (l := (12784823261766654749 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (127132 / 10000000 : ℝ))
  have hp : (2606758699124622 / 18446744073709551616 : ℝ) ≤ 8 * (127132 / 10000000 : ℝ) *
      (((801 / 320 : ℝ) - (5 / 2 : ℝ)) * (12784823261766654749 / 18446744073709551616 : ℝ) / denomMax (5 / 2 : ℝ) (801 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel01 : (2606386060715001 / 18446744073709551616 : ℝ) ≤
    8 * (127132 / 10000000 : ℝ) * ∫ s in (801 / 320 : ℝ)..(401 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (801 / 320 : ℝ)) (b := (401 / 160 : ℝ))
    (l := (12789274412097506235 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (127132 / 10000000 : ℝ))
  have hp : (2606386060715001 / 18446744073709551616 : ℝ) ≤ 8 * (127132 / 10000000 : ℝ) *
      (((401 / 160 : ℝ) - (801 / 320 : ℝ)) * (12789274412097506235 / 18446744073709551616 : ℝ) / denomMax (801 / 320 : ℝ) (401 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel02 : (2606020735128090 / 18446744073709551616 : ℝ) ≤
    8 * (127132 / 10000000 : ℝ) * ∫ s in (401 / 160 : ℝ)..(803 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (401 / 160 : ℝ)) (b := (803 / 320 : ℝ))
    (l := (12793735531590600569 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (127132 / 10000000 : ℝ))
  have hp : (2606020735128090 / 18446744073709551616 : ℝ) ≤ 8 * (127132 / 10000000 : ℝ) *
      (((803 / 320 : ℝ) - (401 / 160 : ℝ)) * (12793735531590600569 / 18446744073709551616 : ℝ) / denomMax (401 / 160 : ℝ) (803 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel03 : (2605662716431730 / 18446744073709551616 : ℝ) ≤
    8 * (127132 / 10000000 : ℝ) * ∫ s in (803 / 320 : ℝ)..(201 / 80 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (803 / 320 : ℝ)) (b := (201 / 80 : ℝ))
    (l := (12798206653906013041 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (127132 / 10000000 : ℝ))
  have hp : (2605662716431730 / 18446744073709551616 : ℝ) ≤ 8 * (127132 / 10000000 : ℝ) *
      (((201 / 80 : ℝ) - (803 / 320 : ℝ)) * (12798206653906013041 / 18446744073709551616 : ℝ) / denomMax (803 / 320 : ℝ) (201 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel04 : (2605311998818947 / 18446744073709551616 : ℝ) ≤
    8 * (127132 / 10000000 : ℝ) * ∫ s in (201 / 80 : ℝ)..(161 / 64 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (201 / 80 : ℝ)) (b := (161 / 64 : ℝ))
    (l := (12802687812856110418 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (127132 / 10000000 : ℝ))
  have hp : (2605311998818947 / 18446744073709551616 : ℝ) ≤ 8 * (127132 / 10000000 : ℝ) *
      (((161 / 64 : ℝ) - (201 / 80 : ℝ)) * (12802687812856110418 / 18446744073709551616 : ℝ) / denomMax (201 / 80 : ℝ) (161 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel05 : (2604968576607716 / 18446744073709551616 : ℝ) ≤
    8 * (127132 / 10000000 : ℝ) * ∫ s in (161 / 64 : ℝ)..(403 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (161 / 64 : ℝ)) (b := (403 / 160 : ℝ))
    (l := (12807179042406416492 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (127132 / 10000000 : ℝ))
  have hp : (2604968576607716 / 18446744073709551616 : ℝ) ≤ 8 * (127132 / 10000000 : ℝ) *
      (((403 / 160 : ℝ) - (161 / 64 : ℝ)) * (12807179042406416492 / 18446744073709551616 : ℝ) / denomMax (161 / 64 : ℝ) (403 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel06 : (2604632444240729 / 18446744073709551616 : ℝ) ≤
    8 * (127132 / 10000000 : ℝ) * ∫ s in (403 / 160 : ℝ)..(807 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (403 / 160 : ℝ)) (b := (807 / 320 : ℝ))
    (l := (12811680376676483559 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (127132 / 10000000 : ℝ))
  have hp : (2604632444240729 / 18446744073709551616 : ℝ) ≤ 8 * (127132 / 10000000 : ℝ) *
      (((807 / 320 : ℝ) - (403 / 160 : ℝ)) * (12811680376676483559 / 18446744073709551616 : ℝ) / denomMax (403 / 160 : ℝ) (807 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel07 : (2604303596285166 / 18446744073709551616 : ℝ) ≤
    8 * (127132 / 10000000 : ℝ) * ∫ s in (807 / 320 : ℝ)..(101 / 40 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (807 / 320 : ℝ)) (b := (101 / 40 : ℝ))
    (l := (12816191849940769880 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (127132 / 10000000 : ℝ))
  have hp : (2604303596285166 / 18446744073709551616 : ℝ) ≤ 8 * (127132 / 10000000 : ℝ) *
      (((101 / 40 : ℝ) - (807 / 320 : ℝ)) * (12816191849940769880 / 18446744073709551616 : ℝ) / denomMax (807 / 320 : ℝ) (101 / 40 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel08 : (2603982027432474 / 18446744073709551616 : ℝ) ≤
    8 * (127132 / 10000000 : ℝ) * ∫ s in (101 / 40 : ℝ)..(809 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (101 / 40 : ℝ)) (b := (809 / 320 : ℝ))
    (l := (12820713496629523163 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (127132 / 10000000 : ℝ))
  have hp : (2603982027432474 / 18446744073709551616 : ℝ) ≤ 8 * (127132 / 10000000 : ℝ) *
      (((809 / 320 : ℝ) - (101 / 40 : ℝ)) * (12820713496629523163 / 18446744073709551616 : ℝ) / denomMax (101 / 40 : ℝ) (809 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel09 : (2603667732498154 / 18446744073709551616 : ℝ) ≤
    8 * (127132 / 10000000 : ℝ) * ∫ s in (809 / 320 : ℝ)..(81 / 32 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (809 / 320 : ℝ)) (b := (81 / 32 : ℝ))
    (l := (12825245351329670132 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (127132 / 10000000 : ℝ))
  have hp : (2603667732498154 / 18446744073709551616 : ℝ) ≤ 8 * (127132 / 10000000 : ℝ) *
      (((81 / 32 : ℝ) - (809 / 320 : ℝ)) * (12825245351329670132 / 18446744073709551616 : ℝ) / denomMax (809 / 320 : ℝ) (81 / 32 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel10 : (2603360706421544 / 18446744073709551616 : ℝ) ≤
    8 * (127132 / 10000000 : ℝ) * ∫ s in (81 / 32 : ℝ)..(811 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (81 / 32 : ℝ)) (b := (811 / 320 : ℝ))
    (l := (12829787448785712209 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (127132 / 10000000 : ℝ))
  have hp : (2603360706421544 / 18446744073709551616 : ℝ) ≤ 8 * (127132 / 10000000 : ℝ) *
      (((811 / 320 : ℝ) - (81 / 32 : ℝ)) * (12829787448785712209 / 18446744073709551616 : ℝ) / denomMax (81 / 32 : ℝ) (811 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel11 : (2603060944265622 / 18446744073709551616 : ℝ) ≤
    8 * (127132 / 10000000 : ℝ) * ∫ s in (811 / 320 : ℝ)..(203 / 80 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (811 / 320 : ℝ)) (b := (203 / 80 : ℝ))
    (l := (12834339823900627383 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (127132 / 10000000 : ℝ))
  have hp : (2603060944265622 / 18446744073709551616 : ℝ) ≤ 8 * (127132 / 10000000 : ℝ) *
      (((203 / 80 : ℝ) - (811 / 320 : ℝ)) * (12834339823900627383 / 18446744073709551616 : ℝ) / denomMax (811 / 320 : ℝ) (203 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel12 : (2602768441216798 / 18446744073709551616 : ℝ) ≤
    8 * (127132 / 10000000 : ℝ) * ∫ s in (203 / 80 : ℝ)..(813 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (203 / 80 : ℝ)) (b := (813 / 320 : ℝ))
    (l := (12838902511736778292 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (127132 / 10000000 : ℝ))
  have hp : (2602768441216798 / 18446744073709551616 : ℝ) ≤ 8 * (127132 / 10000000 : ℝ) *
      (((813 / 320 : ℝ) - (203 / 80 : ℝ)) * (12838902511736778292 / 18446744073709551616 : ℝ) / denomMax (203 / 80 : ℝ) (813 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel13 : (2602483192584724 / 18446744073709551616 : ℝ) ≤
    8 * (127132 / 10000000 : ℝ) * ∫ s in (813 / 320 : ℝ)..(407 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (813 / 320 : ℝ)) (b := (407 / 160 : ℝ))
    (l := (12843475547516826591 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (127132 / 10000000 : ℝ))
  have hp : (2602483192584724 / 18446744073709551616 : ℝ) ≤ 8 * (127132 / 10000000 : ℝ) *
      (((407 / 160 : ℝ) - (813 / 320 : ℝ)) * (12843475547516826591 / 18446744073709551616 : ℝ) / denomMax (813 / 320 : ℝ) (407 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel14 : (2602205193802103 / 18446744073709551616 : ℝ) ≤
    8 * (127132 / 10000000 : ℝ) * ∫ s in (407 / 160 : ℝ)..(163 / 64 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (407 / 160 : ℝ)) (b := (163 / 64 : ℝ))
    (l := (12848058966624653638 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (127132 / 10000000 : ℝ))
  have hp : (2602205193802103 / 18446744073709551616 : ℝ) ≤ 8 * (127132 / 10000000 : ℝ) *
      (((163 / 64 : ℝ) - (407 / 160 : ℝ)) * (12848058966624653638 / 18446744073709551616 : ℝ) / denomMax (407 / 160 : ℝ) (163 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel15 : (2601934440424507 / 18446744073709551616 : ℝ) ≤
    8 * (127132 / 10000000 : ℝ) * ∫ s in (163 / 64 : ℝ)..(51 / 20 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (163 / 64 : ℝ)) (b := (51 / 20 : ℝ))
    (l := (12852652804606287561 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (127132 / 10000000 : ℝ))
  have hp : (2601934440424507 / 18446744073709551616 : ℝ) ≤ 8 * (127132 / 10000000 : ℝ) *
      (((51 / 20 : ℝ) - (163 / 64 : ℝ)) * (12852652804606287561 / 18446744073709551616 : ℝ) / denomMax (163 / 64 : ℝ) (51 / 20 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel16 : (2601670928130193 / 18446744073709551616 : ℝ) ≤
    8 * (127132 / 10000000 : ℝ) * ∫ s in (51 / 20 : ℝ)..(817 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (51 / 20 : ℝ)) (b := (817 / 320 : ℝ))
    (l := (12857257097170836750 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (127132 / 10000000 : ℝ))
  have hp : (2601670928130193 / 18446744073709551616 : ℝ) ≤ 8 * (127132 / 10000000 : ℝ) *
      (((817 / 320 : ℝ) - (51 / 20 : ℝ)) * (12857257097170836750 / 18446744073709551616 : ℝ) / denomMax (51 / 20 : ℝ) (817 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel17 : (2601414652719934 / 18446744073709551616 : ℝ) ≤
    8 * (127132 / 10000000 : ℝ) * ∫ s in (817 / 320 : ℝ)..(409 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (817 / 320 : ℝ)) (b := (409 / 160 : ℝ))
    (l := (12861871880191429838 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (127132 / 10000000 : ℝ))
  have hp : (2601414652719934 / 18446744073709551616 : ℝ) ≤ 8 * (127132 / 10000000 : ℝ) *
      (((409 / 160 : ℝ) - (817 / 320 : ℝ)) * (12861871880191429838 / 18446744073709551616 : ℝ) / denomMax (817 / 320 : ℝ) (409 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel18 : (2601165610116850 / 18446744073709551616 : ℝ) ≤
    8 * (127132 / 10000000 : ℝ) * ∫ s in (409 / 160 : ℝ)..(819 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (409 / 160 : ℝ)) (b := (819 / 320 : ℝ))
    (l := (12866497189706162207 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (127132 / 10000000 : ℝ))
  have hp : (2601165610116850 / 18446744073709551616 : ℝ) ≤ 8 * (127132 / 10000000 : ℝ) *
      (((819 / 320 : ℝ) - (409 / 160 : ℝ)) * (12866497189706162207 / 18446744073709551616 : ℝ) / denomMax (409 / 160 : ℝ) (819 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel19 : (2600923796366244 / 18446744073709551616 : ℝ) ≤
    8 * (127132 / 10000000 : ℝ) * ∫ s in (819 / 320 : ℝ)..(41 / 16 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (819 / 320 : ℝ)) (b := (41 / 16 : ℝ))
    (l := (12871133061919049088 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (127132 / 10000000 : ℝ))
  have hp : (2600923796366244 / 18446744073709551616 : ℝ) ≤ 8 * (127132 / 10000000 : ℝ) *
      (((41 / 16 : ℝ) - (819 / 320 : ℝ)) * (12871133061919049088 / 18446744073709551616 : ℝ) / denomMax (819 / 320 : ℝ) (41 / 16 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel20 : (2600689207635441 / 18446744073709551616 : ℝ) ≤
    8 * (127132 / 10000000 : ℝ) * ∫ s in (41 / 16 : ℝ)..(821 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (41 / 16 : ℝ)) (b := (821 / 320 : ℝ))
    (l := (12875779533200985296 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (127132 / 10000000 : ℝ))
  have hp : (2600689207635441 / 18446744073709551616 : ℝ) ≤ 8 * (127132 / 10000000 : ℝ) *
      (((821 / 320 : ℝ) - (41 / 16 : ℝ)) * (12875779533200985296 / 18446744073709551616 : ℝ) / denomMax (41 / 16 : ℝ) (821 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel21 : (2600461840213642 / 18446744073709551616 : ℝ) ≤
    8 * (127132 / 10000000 : ℝ) * ∫ s in (821 / 320 : ℝ)..(411 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (821 / 320 : ℝ)) (b := (411 / 160 : ℝ))
    (l := (12880436640090711669 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (127132 / 10000000 : ℝ))
  have hp : (2600461840213642 / 18446744073709551616 : ℝ) ≤ 8 * (127132 / 10000000 : ℝ) *
      (((411 / 160 : ℝ) - (821 / 320 : ℝ)) * (12880436640090711669 / 18446744073709551616 : ℝ) / denomMax (821 / 320 : ℝ) (411 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel22 : (2600241690511770 / 18446744073709551616 : ℝ) ≤
    8 * (127132 / 10000000 : ℝ) * ∫ s in (411 / 160 : ℝ)..(823 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (411 / 160 : ℝ)) (b := (823 / 320 : ℝ))
    (l := (12885104419295788246 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (127132 / 10000000 : ℝ))
  have hp : (2600241690511770 / 18446744073709551616 : ℝ) ≤ 8 * (127132 / 10000000 : ℝ) *
      (((823 / 320 : ℝ) - (411 / 160 : ℝ)) * (12885104419295788246 / 18446744073709551616 : ℝ) / denomMax (411 / 160 : ℝ) (823 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel23 : (2600028755062333 / 18446744073709551616 : ℝ) ≤
    8 * (127132 / 10000000 : ℝ) * ∫ s in (823 / 320 : ℝ)..(103 / 40 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (823 / 320 : ℝ)) (b := (103 / 40 : ℝ))
    (l := (12889782907693574259 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (127132 / 10000000 : ℝ))
  have hp : (2600028755062333 / 18446744073709551616 : ℝ) ≤ 8 * (127132 / 10000000 : ℝ) *
      (((103 / 40 : ℝ) - (823 / 320 : ℝ)) * (12889782907693574259 / 18446744073709551616 : ℝ) / denomMax (823 / 320 : ℝ) (103 / 40 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel24 : (2599823030519283 / 18446744073709551616 : ℝ) ≤
    8 * (127132 / 10000000 : ℝ) * ∫ s in (103 / 40 : ℝ)..(165 / 64 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (103 / 40 : ℝ)) (b := (165 / 64 : ℝ))
    (l := (12894472142332214984 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (127132 / 10000000 : ℝ))
  have hp : (2599823030519283 / 18446744073709551616 : ℝ) ≤ 8 * (127132 / 10000000 : ℝ) *
      (((165 / 64 : ℝ) - (103 / 40 : ℝ)) * (12894472142332214984 / 18446744073709551616 : ℝ) / denomMax (103 / 40 : ℝ) (165 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel25 : (2599624513657883 / 18446744073709551616 : ℝ) ≤
    8 * (127132 / 10000000 : ℝ) * ∫ s in (165 / 64 : ℝ)..(413 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (165 / 64 : ℝ)) (b := (413 / 160 : ℝ))
    (l := (12899172160431635506 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (127132 / 10000000 : ℝ))
  have hp : (2599624513657883 / 18446744073709551616 : ℝ) ≤ 8 * (127132 / 10000000 : ℝ) *
      (((413 / 160 : ℝ) - (165 / 64 : ℝ)) * (12899172160431635506 / 18446744073709551616 : ℝ) / denomMax (165 / 64 : ℝ) (413 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel26 : (2599433201374584 / 18446744073709551616 : ℝ) ≤
    8 * (127132 / 10000000 : ℝ) * ∫ s in (413 / 160 : ℝ)..(827 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (413 / 160 : ℝ)) (b := (827 / 320 : ℝ))
    (l := (12903882999384541460 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (127132 / 10000000 : ℝ))
  have hp : (2599433201374584 / 18446744073709551616 : ℝ) ≤ 8 * (127132 / 10000000 : ℝ) *
      (((827 / 320 : ℝ) - (413 / 160 : ℝ)) * (12903882999384541460 / 18446744073709551616 : ℝ) / denomMax (413 / 160 : ℝ) (827 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel27 : (2599249090686903 / 18446744073709551616 : ℝ) ≤
    8 * (127132 / 10000000 : ℝ) * ∫ s in (827 / 320 : ℝ)..(207 / 80 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (827 / 320 : ℝ)) (b := (207 / 80 : ℝ))
    (l := (12908604696757426807 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (127132 / 10000000 : ℝ))
  have hp : (2599249090686903 / 18446744073709551616 : ℝ) ≤ 8 * (127132 / 10000000 : ℝ) *
      (((207 / 80 : ℝ) - (827 / 320 : ℝ)) * (12908604696757426807 / 18446744073709551616 : ℝ) / denomMax (827 / 320 : ℝ) (207 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel28 : (2599072178733302 / 18446744073709551616 : ℝ) ≤
    8 * (127132 / 10000000 : ℝ) * ∫ s in (207 / 80 : ℝ)..(829 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (207 / 80 : ℝ)) (b := (829 / 320 : ℝ))
    (l := (12913337290291588697 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (127132 / 10000000 : ℝ))
  have hp : (2599072178733302 / 18446744073709551616 : ℝ) ≤ 8 * (127132 / 10000000 : ℝ) *
      (((829 / 320 : ℝ) - (207 / 80 : ℝ)) * (12913337290291588697 / 18446744073709551616 : ℝ) / denomMax (207 / 80 : ℝ) (829 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel29 : (2598902462773081 / 18446744073709551616 : ℝ) ≤
    8 * (127132 / 10000000 : ℝ) * ∫ s in (829 / 320 : ℝ)..(83 / 32 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (829 / 320 : ℝ)) (b := (83 / 32 : ℝ))
    (l := (12918080817904149478 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (127132 / 10000000 : ℝ))
  have hp : (2598902462773081 / 18446744073709551616 : ℝ) ≤ 8 * (127132 / 10000000 : ℝ) *
      (((83 / 32 : ℝ) - (829 / 320 : ℝ)) * (12918080817904149478 / 18446744073709551616 : ℝ) / denomMax (829 / 320 : ℝ) (83 / 32 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel30 : (2598739940186268 / 18446744073709551616 : ℝ) ≤
    8 * (127132 / 10000000 : ℝ) * ∫ s in (83 / 32 : ℝ)..(831 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (83 / 32 : ℝ)) (b := (831 / 320 : ℝ))
    (l := (12922835317689085912 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (127132 / 10000000 : ℝ))
  have hp : (2598739940186268 / 18446744073709551616 : ℝ) ≤ 8 * (127132 / 10000000 : ℝ) *
      (((831 / 320 : ℝ) - (83 / 32 : ℝ)) * (12922835317689085912 / 18446744073709551616 : ℝ) / denomMax (83 / 32 : ℝ) (831 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel31 : (2598584608473523 / 18446744073709551616 : ℝ) ≤
    8 * (127132 / 10000000 : ℝ) * ∫ s in (831 / 320 : ℝ)..(13 / 5 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (831 / 320 : ℝ)) (b := (13 / 5 : ℝ))
    (l := (12927600827918265667 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (127132 / 10000000 : ℝ))
  have hp : (2598584608473523 / 18446744073709551616 : ℝ) ≤ 8 * (127132 / 10000000 : ℝ) *
      (((13 / 5 : ℝ) - (831 / 320 : ℝ)) * (12927600827918265667 / 18446744073709551616 : ℝ) / denomMax (831 / 320 : ℝ) (13 / 5 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

theorem lower : (83267533013159161 / 18446744073709551616 : ℝ) ≤
    8 * (127132 / 10000000 : ℝ) * ∫ s in (5 / 2 : ℝ)..(13 / 5 : ℝ), density s := by
  have he := integral_grid_sum (5 / 2 : ℝ) (13 / 5 : ℝ) 32 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [endpoint, alpha, beta])
  norm_num [Finset.sum_range_succ] at he
  linarith only [panel00, panel01, panel02, panel03, panel04, panel05, panel06, panel07, panel08, panel09, panel10, panel11, panel12, panel13, panel14, panel15, panel16, panel17, panel18, panel19, panel20, panel21, panel22, panel23, panel24, panel25, panel26, panel27, panel28, panel29, panel30, panel31, he]

end Wu18938Campaign.M3.Confirmed.TableRow05
