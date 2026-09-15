import Wu18938Campaign.M3.Confirmed.TableBounds

noncomputable section
namespace Wu18938Campaign.M3.Confirmed.TableRow21
open Real Set MeasureTheory QuarterTrim
open WuSource.SrcSixthGain Wu18938Campaign.M3.Confirmed.TableBounds

private theorem panel00 : (2205271596868 / 18446744073709551616 : ℝ) ≤
    8 * (8099 / 10000000 : ℝ) * ∫ s in (4 / 1 : ℝ)..(1318653 / 329600 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (4 / 1 : ℝ)) (b := (1318653 / 329600 : ℝ))
    (l := (704380076708814836 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (8099 / 10000000 : ℝ))
  have hp : (2205271596868 / 18446744073709551616 : ℝ) ≤ 8 * (8099 / 10000000 : ℝ) *
      (((1318653 / 329600 : ℝ) - (4 / 1 : ℝ)) * (704380076708814836 / 18446744073709551616 : ℝ) / denomMax (4 / 1 : ℝ) (1318653 / 329600 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel01 : (2135034121983 / 18446744073709551616 : ℝ) ≤
    8 * (8099 / 10000000 : ℝ) * ∫ s in (1318653 / 329600 : ℝ)..(659453 / 164800 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1318653 / 329600 : ℝ)) (b := (659453 / 164800 : ℝ))
    (l := (681877877556685454 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (8099 / 10000000 : ℝ))
  have hp : (2135034121983 / 18446744073709551616 : ℝ) ≤ 8 * (8099 / 10000000 : ℝ) *
      (((659453 / 164800 : ℝ) - (1318653 / 329600 : ℝ)) * (681877877556685454 / 18446744073709551616 : ℝ) / denomMax (1318653 / 329600 : ℝ) (659453 / 164800 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel02 : (2064737626896 / 18446744073709551616 : ℝ) ≤
    8 * (8099 / 10000000 : ℝ) * ∫ s in (659453 / 164800 : ℝ)..(1319159 / 329600 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (659453 / 164800 : ℝ)) (b := (1319159 / 329600 : ℝ))
    (l := (659361219792898385 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (8099 / 10000000 : ℝ))
  have hp : (2064737626896 / 18446744073709551616 : ℝ) ≤ 8 * (8099 / 10000000 : ℝ) *
      (((1319159 / 329600 : ℝ) - (659453 / 164800 : ℝ)) * (659361219792898385 / 18446744073709551616 : ℝ) / denomMax (659453 / 164800 : ℝ) (1319159 / 329600 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel03 : (1994382009527 / 18446744073709551616 : ℝ) ≤
    8 * (8099 / 10000000 : ℝ) * ∫ s in (1319159 / 329600 : ℝ)..(329853 / 82400 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1319159 / 329600 : ℝ)) (b := (329853 / 82400 : ℝ))
    (l := (636830083984462518 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (8099 / 10000000 : ℝ))
  have hp : (1994382009527 / 18446744073709551616 : ℝ) ≤ 8 * (8099 / 10000000 : ℝ) *
      (((329853 / 82400 : ℝ) - (1319159 / 329600 : ℝ)) * (636830083984462518 / 18446744073709551616 : ℝ) / denomMax (1319159 / 329600 : ℝ) (329853 / 82400 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel04 : (1923967167589 / 18446744073709551616 : ℝ) ≤
    8 * (8099 / 10000000 : ℝ) * ∫ s in (329853 / 82400 : ℝ)..(263933 / 65920 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (329853 / 82400 : ℝ)) (b := (263933 / 65920 : ℝ))
    (l := (614284450657794304 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (8099 / 10000000 : ℝ))
  have hp : (1923967167589 / 18446744073709551616 : ℝ) ≤ 8 * (8099 / 10000000 : ℝ) *
      (((263933 / 65920 : ℝ) - (329853 / 82400 : ℝ)) * (614284450657794304 / 18446744073709551616 : ℝ) / denomMax (329853 / 82400 : ℝ) (263933 / 65920 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel05 : (1853492998585 / 18446744073709551616 : ℝ) ≤
    8 * (8099 / 10000000 : ℝ) * ∫ s in (263933 / 65920 : ℝ)..(659959 / 164800 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (263933 / 65920 : ℝ)) (b := (659959 / 164800 : ℝ))
    (l := (591724300298601692 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (8099 / 10000000 : ℝ))
  have hp : (1853492998585 / 18446744073709551616 : ℝ) ≤ 8 * (8099 / 10000000 : ℝ) *
      (((659959 / 164800 : ℝ) - (263933 / 65920 : ℝ)) * (591724300298601692 / 18446744073709551616 : ℝ) / denomMax (263933 / 65920 : ℝ) (659959 / 164800 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel06 : (1782959399809 / 18446744073709551616 : ℝ) ≤
    8 * (8099 / 10000000 : ℝ) * ∫ s in (659959 / 164800 : ℝ)..(1320171 / 329600 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (659959 / 164800 : ℝ)) (b := (1320171 / 329600 : ℝ))
    (l := (569149613351767650 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (8099 / 10000000 : ℝ))
  have hp : (1782959399809 / 18446744073709551616 : ℝ) ≤ 8 * (8099 / 10000000 : ℝ) *
      (((1320171 / 329600 : ℝ) - (659959 / 164800 : ℝ)) * (569149613351767650 / 18446744073709551616 : ℝ) / denomMax (659959 / 164800 : ℝ) (1320171 / 329600 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel07 : (1712366268349 / 18446744073709551616 : ℝ) ≤
    8 * (8099 / 10000000 : ℝ) * ∫ s in (1320171 / 329600 : ℝ)..(165053 / 41200 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1320171 / 329600 : ℝ)) (b := (165053 / 41200 : ℝ))
    (l := (546560370221233262 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (8099 / 10000000 : ℝ))
  have hp : (1712366268349 / 18446744073709551616 : ℝ) ≤ 8 * (8099 / 10000000 : ℝ) *
      (((165053 / 41200 : ℝ) - (1320171 / 329600 : ℝ)) * (546560370221233262 / 18446744073709551616 : ℝ) / denomMax (1320171 / 329600 : ℝ) (165053 / 41200 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel08 : (1641713501080 / 18446744073709551616 : ℝ) ≤
    8 * (8099 / 10000000 : ℝ) * ∫ s in (165053 / 41200 : ℝ)..(1320677 / 329600 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (165053 / 41200 : ℝ)) (b := (1320677 / 329600 : ℝ))
    (l := (523956551269880390 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (8099 / 10000000 : ℝ))
  have hp : (1641713501080 / 18446744073709551616 : ℝ) ≤ 8 * (8099 / 10000000 : ℝ) *
      (((1320677 / 329600 : ℝ) - (165053 / 41200 : ℝ)) * (523956551269880390 / 18446744073709551616 : ℝ) / denomMax (165053 / 41200 : ℝ) (1320677 / 329600 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel09 : (1571000994667 / 18446744073709551616 : ℝ) ≤
    8 * (8099 / 10000000 : ℝ) * ∫ s in (1320677 / 329600 : ℝ)..(132093 / 32960 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1320677 / 329600 : ℝ)) (b := (132093 / 32960 : ℝ))
    (l := (501338136819413919 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (8099 / 10000000 : ℝ))
  have hp : (1571000994667 / 18446744073709551616 : ℝ) ≤ 8 * (8099 / 10000000 : ℝ) *
      (((132093 / 32960 : ℝ) - (1320677 / 329600 : ℝ)) * (501338136819413919 / 18446744073709551616 : ℝ) / denomMax (1320677 / 329600 : ℝ) (132093 / 32960 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel10 : (1500228645565 / 18446744073709551616 : ℝ) ≤
    8 * (8099 / 10000000 : ℝ) * ∫ s in (132093 / 32960 : ℝ)..(1321183 / 329600 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (132093 / 32960 : ℝ)) (b := (1321183 / 329600 : ℝ))
    (l := (478705107150243560 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (8099 / 10000000 : ℝ))
  have hp : (1500228645565 / 18446744073709551616 : ℝ) ≤ 8 * (8099 / 10000000 : ℝ) *
      (((1321183 / 329600 : ℝ) - (132093 / 32960 : ℝ)) * (478705107150243560 / 18446744073709551616 : ℝ) / denomMax (132093 / 32960 : ℝ) (1321183 / 329600 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel11 : (1429396350018 / 18446744073709551616 : ℝ) ≤
    8 * (8099 / 10000000 : ℝ) * ∫ s in (1321183 / 329600 : ℝ)..(330359 / 82400 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1321183 / 329600 : ℝ)) (b := (330359 / 82400 : ℝ))
    (l := (456057442501365237 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (8099 / 10000000 : ℝ))
  have hp : (1429396350018 / 18446744073709551616 : ℝ) ≤ 8 * (8099 / 10000000 : ℝ) *
      (((330359 / 82400 : ℝ) - (1321183 / 329600 : ℝ)) * (456057442501365237 / 18446744073709551616 : ℝ) / denomMax (1321183 / 329600 : ℝ) (330359 / 82400 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel12 : (1358504004055 / 18446744073709551616 : ℝ) ≤
    8 * (8099 / 10000000 : ℝ) * ∫ s in (330359 / 82400 : ℝ)..(1321689 / 329600 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (330359 / 82400 : ℝ)) (b := (1321689 / 329600 : ℝ))
    (l := (433395123070242019 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (8099 / 10000000 : ℝ))
  have hp : (1358504004055 / 18446744073709551616 : ℝ) ≤ 8 * (8099 / 10000000 : ℝ) *
      (((1321689 / 329600 : ℝ) - (330359 / 82400 : ℝ)) * (433395123070242019 / 18446744073709551616 : ℝ) / denomMax (330359 / 82400 : ℝ) (1321689 / 329600 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel13 : (1287551503495 / 18446744073709551616 : ℝ) ≤
    8 * (8099 / 10000000 : ℝ) * ∫ s in (1321689 / 329600 : ℝ)..(660971 / 164800 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1321689 / 329600 : ℝ)) (b := (660971 / 164800 : ℝ))
    (l := (410718129012684638 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (8099 / 10000000 : ℝ))
  have hp : (1287551503495 / 18446744073709551616 : ℝ) ≤ 8 * (8099 / 10000000 : ℝ) *
      (((660971 / 164800 : ℝ) - (1321689 / 329600 : ℝ)) * (410718129012684638 / 18446744073709551616 : ℝ) / denomMax (1321689 / 329600 : ℝ) (660971 / 164800 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel14 : (1216538743942 / 18446744073709551616 : ℝ) ≤
    8 * (8099 / 10000000 : ℝ) * ∫ s in (660971 / 164800 : ℝ)..(264439 / 65920 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (660971 / 164800 : ℝ)) (b := (264439 / 65920 : ℝ))
    (l := (388026440442731555 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (8099 / 10000000 : ℝ))
  have hp : (1216538743942 / 18446744073709551616 : ℝ) ≤ 8 * (8099 / 10000000 : ℝ) *
      (((264439 / 65920 : ℝ) - (660971 / 164800 : ℝ)) * (388026440442731555 / 18446744073709551616 : ℝ) / denomMax (660971 / 164800 : ℝ) (264439 / 65920 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel15 : (1145465620787 / 18446744073709551616 : ℝ) ≤
    8 * (8099 / 10000000 : ℝ) * ∫ s in (264439 / 65920 : ℝ)..(82653 / 20600 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (264439 / 65920 : ℝ)) (b := (82653 / 20600 : ℝ))
    (l := (365320037432528587 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (8099 / 10000000 : ℝ))
  have hp : (1145465620787 / 18446744073709551616 : ℝ) ≤ 8 * (8099 / 10000000 : ℝ) *
      (((82653 / 20600 : ℝ) - (264439 / 65920 : ℝ)) * (365320037432528587 / 18446744073709551616 : ℝ) / denomMax (264439 / 65920 : ℝ) (82653 / 20600 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel16 : (1074332029205 / 18446744073709551616 : ℝ) ≤
    8 * (8099 / 10000000 : ℝ) * ∫ s in (82653 / 20600 : ℝ)..(1322701 / 329600 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (82653 / 20600 : ℝ)) (b := (1322701 / 329600 : ℝ))
    (l := (342598900012208101 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (8099 / 10000000 : ℝ))
  have hp : (1074332029205 / 18446744073709551616 : ℝ) ≤ 8 * (8099 / 10000000 : ℝ) *
      (((1322701 / 329600 : ℝ) - (82653 / 20600 : ℝ)) * (342598900012208101 / 18446744073709551616 : ℝ) / denomMax (82653 / 20600 : ℝ) (1322701 / 329600 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel17 : (1003137864157 / 18446744073709551616 : ℝ) ≤
    8 * (8099 / 10000000 : ℝ) * ∫ s in (1322701 / 329600 : ℝ)..(661477 / 164800 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1322701 / 329600 : ℝ)) (b := (661477 / 164800 : ℝ))
    (l := (319863008169767757 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (8099 / 10000000 : ℝ))
  have hp : (1003137864157 / 18446744073709551616 : ℝ) ≤ 8 * (8099 / 10000000 : ℝ) *
      (((661477 / 164800 : ℝ) - (1322701 / 329600 : ℝ)) * (319863008169767757 / 18446744073709551616 : ℝ) / denomMax (1322701 / 329600 : ℝ) (661477 / 164800 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel18 : (931883020389 / 18446744073709551616 : ℝ) ≤
    8 * (8099 / 10000000 : ℝ) * ∫ s in (661477 / 164800 : ℝ)..(1323207 / 329600 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (661477 / 164800 : ℝ)) (b := (1323207 / 329600 : ℝ))
    (l := (297112341850948808 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (8099 / 10000000 : ℝ))
  have hp : (931883020389 / 18446744073709551616 : ℝ) ≤ 8 * (8099 / 10000000 : ℝ) *
      (((1323207 / 329600 : ℝ) - (661477 / 164800 : ℝ)) * (297112341850948808 / 18446744073709551616 : ℝ) / denomMax (661477 / 164800 : ℝ) (1323207 / 329600 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel19 : (860567392427 / 18446744073709551616 : ℝ) ≤
    8 * (8099 / 10000000 : ℝ) * ∫ s in (1323207 / 329600 : ℝ)..(66173 / 16480 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1323207 / 329600 : ℝ)) (b := (66173 / 16480 : ℝ))
    (l := (274346880959113948 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (8099 / 10000000 : ℝ))
  have hp : (860567392427 / 18446744073709551616 : ℝ) ≤ 8 * (8099 / 10000000 : ℝ) *
      (((66173 / 16480 : ℝ) - (1323207 / 329600 : ℝ)) * (274346880959113948 / 18446744073709551616 : ℝ) / denomMax (1323207 / 329600 : ℝ) (66173 / 16480 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel20 : (789190874583 / 18446744073709551616 : ℝ) ≤
    8 * (8099 / 10000000 : ℝ) * ∫ s in (66173 / 16480 : ℝ)..(1323713 / 329600 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (66173 / 16480 : ℝ)) (b := (1323713 / 329600 : ℝ))
    (l := (251566605355124721 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (8099 / 10000000 : ℝ))
  have hp : (789190874583 / 18446744073709551616 : ℝ) ≤ 8 * (8099 / 10000000 : ℝ) *
      (((1323713 / 329600 : ℝ) - (66173 / 16480 : ℝ)) * (251566605355124721 / 18446744073709551616 : ℝ) / denomMax (66173 / 16480 : ℝ) (1323713 / 329600 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel21 : (717753360952 / 18446744073709551616 : ℝ) ≤
    8 * (8099 / 10000000 : ℝ) * ∫ s in (1323713 / 329600 : ℝ)..(661983 / 164800 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1323713 / 329600 : ℝ)) (b := (661983 / 164800 : ℝ))
    (l := (228771494857218465 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (8099 / 10000000 : ℝ))
  have hp : (717753360952 / 18446744073709551616 : ℝ) ≤ 8 * (8099 / 10000000 : ℝ) *
      (((661983 / 164800 : ℝ) - (1323713 / 329600 : ℝ)) * (228771494857218465 / 18446744073709551616 : ℝ) / denomMax (1323713 / 329600 : ℝ) (661983 / 164800 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel22 : (646254745408 / 18446744073709551616 : ℝ) ≤
    8 * (8099 / 10000000 : ℝ) * ∫ s in (661983 / 164800 : ℝ)..(1324219 / 329600 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (661983 / 164800 : ℝ)) (b := (1324219 / 329600 : ℝ))
    (l := (205961529240884813 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (8099 / 10000000 : ℝ))
  have hp : (646254745408 / 18446744073709551616 : ℝ) ≤ 8 * (8099 / 10000000 : ℝ) *
      (((1324219 / 329600 : ℝ) - (661983 / 164800 : ℝ)) * (205961529240884813 / 18446744073709551616 : ℝ) / denomMax (661983 / 164800 : ℝ) (1324219 / 329600 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel23 : (574694921607 / 18446744073709551616 : ℝ) ≤
    8 * (8099 / 10000000 : ℝ) * ∫ s in (1324219 / 329600 : ℝ)..(165559 / 41200 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1324219 / 329600 : ℝ)) (b := (165559 / 41200 : ℝ))
    (l := (183136688238741732 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (8099 / 10000000 : ℝ))
  have hp : (574694921607 / 18446744073709551616 : ℝ) ≤ 8 * (8099 / 10000000 : ℝ) *
      (((165559 / 41200 : ℝ) - (1324219 / 329600 : ℝ)) * (183136688238741732 / 18446744073709551616 : ℝ) / denomMax (1324219 / 329600 : ℝ) (165559 / 41200 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel24 : (503073782987 / 18446744073709551616 : ℝ) ≤
    8 * (8099 / 10000000 : ℝ) * ∫ s in (165559 / 41200 : ℝ)..(52989 / 13184 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (165559 / 41200 : ℝ)) (b := (52989 / 13184 : ℝ))
    (l := (160296951540411109 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (8099 / 10000000 : ℝ))
  have hp : (503073782987 / 18446744073709551616 : ℝ) ≤ 8 * (8099 / 10000000 : ℝ) *
      (((52989 / 13184 : ℝ) - (165559 / 41200 : ℝ)) * (160296951540411109 / 18446744073709551616 : ℝ) / denomMax (165559 / 41200 : ℝ) (52989 / 13184 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel25 : (431391222764 / 18446744073709551616 : ℝ) ≤
    8 * (8099 / 10000000 : ℝ) * ∫ s in (52989 / 13184 : ℝ)..(662489 / 164800 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (52989 / 13184 : ℝ)) (b := (662489 / 164800 : ℝ))
    (l := (137442298792393872 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (8099 / 10000000 : ℝ))
  have hp : (431391222764 / 18446744073709551616 : ℝ) ≤ 8 * (8099 / 10000000 : ℝ) *
      (((662489 / 164800 : ℝ) - (52989 / 13184 : ℝ)) * (137442298792393872 / 18446744073709551616 : ℝ) / denomMax (52989 / 13184 : ℝ) (662489 / 164800 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel26 : (359647133934 / 18446744073709551616 : ℝ) ≤
    8 * (8099 / 10000000 : ℝ) * ∫ s in (662489 / 164800 : ℝ)..(1325231 / 329600 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (662489 / 164800 : ℝ)) (b := (1325231 / 329600 : ℝ))
    (l := (114572709597944654 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (8099 / 10000000 : ℝ))
  have hp : (359647133934 / 18446744073709551616 : ℝ) ≤ 8 * (8099 / 10000000 : ℝ) *
      (((1325231 / 329600 : ℝ) - (662489 / 164800 : ℝ)) * (114572709597944654 / 18446744073709551616 : ℝ) / denomMax (662489 / 164800 : ℝ) (1325231 / 329600 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel27 : (287841409271 / 18446744073709551616 : ℝ) ≤
    8 * (8099 / 10000000 : ℝ) * ∫ s in (1325231 / 329600 : ℝ)..(331371 / 82400 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1325231 / 329600 : ℝ)) (b := (331371 / 82400 : ℝ))
    (l := (91688163516945989 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (8099 / 10000000 : ℝ))
  have hp : (287841409271 / 18446744073709551616 : ℝ) ≤ 8 * (8099 / 10000000 : ℝ) *
      (((331371 / 82400 : ℝ) - (1325231 / 329600 : ℝ)) * (91688163516945989 / 18446744073709551616 : ℝ) / denomMax (1325231 / 329600 : ℝ) (331371 / 82400 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel28 : (215973941328 / 18446744073709551616 : ℝ) ≤
    8 * (8099 / 10000000 : ℝ) * ∫ s in (331371 / 82400 : ℝ)..(1325737 / 329600 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (331371 / 82400 : ℝ)) (b := (1325737 / 329600 : ℝ))
    (l := (68788640065782046 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (8099 / 10000000 : ℝ))
  have hp : (215973941328 / 18446744073709551616 : ℝ) ≤ 8 * (8099 / 10000000 : ℝ) *
      (((1325737 / 329600 : ℝ) - (331371 / 82400 : ℝ)) * (68788640065782046 / 18446744073709551616 : ℝ) / denomMax (331371 / 82400 : ℝ) (1325737 / 329600 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel29 : (144044622435 / 18446744073709551616 : ℝ) ≤
    8 * (8099 / 10000000 : ℝ) * ∫ s in (1325737 / 329600 : ℝ)..(132599 / 32960 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1325737 / 329600 : ℝ)) (b := (132599 / 32960 : ℝ))
    (l := (45874118717211893 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (8099 / 10000000 : ℝ))
  have hp : (144044622435 / 18446744073709551616 : ℝ) ≤ 8 * (8099 / 10000000 : ℝ) *
      (((132599 / 32960 : ℝ) - (1325737 / 329600 : ℝ)) * (45874118717211893 / 18446744073709551616 : ℝ) / denomMax (1325737 / 329600 : ℝ) (132599 / 32960 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel30 : (72053344698 / 18446744073709551616 : ℝ) ≤
    8 * (8099 / 10000000 : ℝ) * ∫ s in (132599 / 32960 : ℝ)..(1326243 / 329600 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (132599 / 32960 : ℝ)) (b := (1326243 / 329600 : ℝ))
    (l := (22944578900242286 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (8099 / 10000000 : ℝ))
  have hp : (72053344698 / 18446744073709551616 : ℝ) ≤ 8 * (8099 / 10000000 : ℝ) *
      (((1326243 / 329600 : ℝ) - (132599 / 32960 : ℝ)) * (22944578900242286 / 18446744073709551616 : ℝ) / denomMax (132599 / 32960 : ℝ) (1326243 / 329600 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel31 : (0 / 18446744073709551616 : ℝ) ≤
    8 * (8099 / 10000000 : ℝ) * ∫ s in (1326243 / 329600 : ℝ)..(41453 / 10300 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1326243 / 329600 : ℝ)) (b := (41453 / 10300 : ℝ))
    (l := (0 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (8099 / 10000000 : ℝ))
  have hp : (0 / 18446744073709551616 : ℝ) ≤ 8 * (8099 / 10000000 : ℝ) *
      (((41453 / 10300 : ℝ) - (1326243 / 329600 : ℝ)) * (0 / 18446744073709551616 : ℝ) / denomMax (1326243 / 329600 : ℝ) (41453 / 10300 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

theorem lower : (35434450219360 / 18446744073709551616 : ℝ) ≤
    8 * (8099 / 10000000 : ℝ) * ∫ s in (4 / 1 : ℝ)..(41453 / 10300 : ℝ), density s := by
  have he := integral_grid_sum (4 / 1 : ℝ) (41453 / 10300 : ℝ) 32 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [endpoint, alpha, beta])
  norm_num [Finset.sum_range_succ] at he
  linarith only [panel00, panel01, panel02, panel03, panel04, panel05, panel06, panel07, panel08, panel09, panel10, panel11, panel12, panel13, panel14, panel15, panel16, panel17, panel18, panel19, panel20, panel21, panel22, panel23, panel24, panel25, panel26, panel27, panel28, panel29, panel30, panel31, he]

end Wu18938Campaign.M3.Confirmed.TableRow21
