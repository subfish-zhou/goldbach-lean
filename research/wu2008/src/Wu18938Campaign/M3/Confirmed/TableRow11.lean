import Wu18938Campaign.M3.Confirmed.TableBounds

noncomputable section
namespace Wu18938Campaign.M3.Confirmed.TableRow11
open Real Set MeasureTheory QuarterTrim
open WuSource.SrcSixthGain Wu18938Campaign.M3.Confirmed.TableBounds

private theorem panel00 : (1171893825782743 / 18446744073709551616 : ℝ) ≤
    8 * (55818 / 10000000 : ℝ) * ∫ s in (31 / 10 : ℝ)..(993 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (31 / 10 : ℝ)) (b := (993 / 320 : ℝ))
    (l := (13871954439433785234 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (55818 / 10000000 : ℝ))
  have hp : (1171893825782743 / 18446744073709551616 : ℝ) ≤ 8 * (55818 / 10000000 : ℝ) *
      (((993 / 320 : ℝ) - (31 / 10 : ℝ)) * (13871954439433785234 / 18446744073709551616 : ℝ) / denomMax (31 / 10 : ℝ) (993 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel01 : (1172361748292613 / 18446744073709551616 : ℝ) ≤
    8 * (55818 / 10000000 : ℝ) * ∫ s in (993 / 320 : ℝ)..(497 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (993 / 320 : ℝ)) (b := (497 / 160 : ℝ))
    (l := (13879177497808761516 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (55818 / 10000000 : ℝ))
  have hp : (1172361748292613 / 18446744073709551616 : ℝ) ≤ 8 * (55818 / 10000000 : ℝ) *
      (((497 / 160 : ℝ) - (993 / 320 : ℝ)) * (13879177497808761516 / 18446744073709551616 : ℝ) / denomMax (993 / 320 : ℝ) (497 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel02 : (1172833394466392 / 18446744073709551616 : ℝ) ≤
    8 * (55818 / 10000000 : ℝ) * ∫ s in (497 / 160 : ℝ)..(199 / 64 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (497 / 160 : ℝ)) (b := (199 / 64 : ℝ))
    (l := (13886421248416500845 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (55818 / 10000000 : ℝ))
  have hp : (1172833394466392 / 18446744073709551616 : ℝ) ≤ 8 * (55818 / 10000000 : ℝ) *
      (((199 / 64 : ℝ) - (497 / 160 : ℝ)) * (13886421248416500845 / 18446744073709551616 : ℝ) / denomMax (497 / 160 : ℝ) (199 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel03 : (1173308773056480 / 18446744073709551616 : ℝ) ≤
    8 * (55818 / 10000000 : ℝ) * ∫ s in (199 / 64 : ℝ)..(249 / 80 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (199 / 64 : ℝ)) (b := (249 / 80 : ℝ))
    (l := (13893685780862462297 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (55818 / 10000000 : ℝ))
  have hp : (1173308773056480 / 18446744073709551616 : ℝ) ≤ 8 * (55818 / 10000000 : ℝ) *
      (((249 / 80 : ℝ) - (199 / 64 : ℝ)) * (13893685780862462297 / 18446744073709551616 : ℝ) / denomMax (199 / 64 : ℝ) (249 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel04 : (1173787892895036 / 18446744073709551616 : ℝ) ≤
    8 * (55818 / 10000000 : ℝ) * ∫ s in (249 / 80 : ℝ)..(997 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (249 / 80 : ℝ)) (b := (997 / 320 : ℝ))
    (l := (13900971185273433834 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (55818 / 10000000 : ℝ))
  have hp : (1173787892895036 / 18446744073709551616 : ℝ) ≤ 8 * (55818 / 10000000 : ℝ) *
      (((997 / 320 : ℝ) - (249 / 80 : ℝ)) * (13900971185273433834 / 18446744073709551616 : ℝ) / denomMax (249 / 80 : ℝ) (997 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel05 : (1174270762894407 / 18446744073709551616 : ℝ) ≤
    8 * (55818 / 10000000 : ℝ) * ∫ s in (997 / 320 : ℝ)..(499 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (997 / 320 : ℝ)) (b := (499 / 160 : ℝ))
    (l := (13908277552301352225 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (55818 / 10000000 : ℝ))
  have hp : (1174270762894407 / 18446744073709551616 : ℝ) ≤ 8 * (55818 / 10000000 : ℝ) *
      (((499 / 160 : ℝ) - (997 / 320 : ℝ)) * (13908277552301352225 / 18446744073709551616 : ℝ) / denomMax (997 / 320 : ℝ) (499 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel06 : (1174757392047569 / 18446744073709551616 : ℝ) ≤
    8 * (55818 / 10000000 : ℝ) * ∫ s in (499 / 160 : ℝ)..(999 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (499 / 160 : ℝ)) (b := (999 / 320 : ℝ))
    (l := (13915604973127156799 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (55818 / 10000000 : ℝ))
  have hp : (1174757392047569 / 18446744073709551616 : ℝ) ≤ 8 * (55818 / 10000000 : ℝ) *
      (((999 / 320 : ℝ) - (499 / 160 : ℝ)) * (13915604973127156799 / 18446744073709551616 : ℝ) / denomMax (499 / 160 : ℝ) (999 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel07 : (1175247789428568 / 18446744073709551616 : ℝ) ≤
    8 * (55818 / 10000000 : ℝ) * ∫ s in (999 / 320 : ℝ)..(25 / 8 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (999 / 320 : ℝ)) (b := (25 / 8 : ℝ))
    (l := (13922953539464677385 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (55818 / 10000000 : ℝ))
  have hp : (1175247789428568 / 18446744073709551616 : ℝ) ≤ 8 * (55818 / 10000000 : ℝ) *
      (((25 / 8 : ℝ) - (999 / 320 : ℝ)) * (13922953539464677385 / 18446744073709551616 : ℝ) / denomMax (999 / 320 : ℝ) (25 / 8 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel08 : (1175741964192965 / 18446744073709551616 : ℝ) ≤
    8 * (55818 / 10000000 : ℝ) * ∫ s in (25 / 8 : ℝ)..(1001 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (25 / 8 : ℝ)) (b := (1001 / 320 : ℝ))
    (l := (13930323343564556796 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (55818 / 10000000 : ℝ))
  have hp : (1175741964192965 / 18446744073709551616 : ℝ) ≤ 8 * (55818 / 10000000 : ℝ) *
      (((1001 / 320 : ℝ) - (25 / 8 : ℝ)) * (13930323343564556796 / 18446744073709551616 : ℝ) / denomMax (25 / 8 : ℝ) (1001 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel09 : (1176239925578293 / 18446744073709551616 : ℝ) ≤
    8 * (55818 / 10000000 : ℝ) * ∫ s in (1001 / 320 : ℝ)..(501 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (1001 / 320 : ℝ)) (b := (501 / 160 : ℝ))
    (l := (13937714478218208216 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (55818 / 10000000 : ℝ))
  have hp : (1176239925578293 / 18446744073709551616 : ℝ) ≤ 8 * (55818 / 10000000 : ℝ) *
      (((501 / 160 : ℝ) - (1001 / 320 : ℝ)) * (13937714478218208216 / 18446744073709551616 : ℝ) / denomMax (1001 / 320 : ℝ) (501 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel10 : (1176741682904508 / 18446744073709551616 : ℝ) ≤
    8 * (55818 / 10000000 : ℝ) * ∫ s in (501 / 160 : ℝ)..(1003 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (501 / 160 : ℝ)) (b := (1003 / 320 : ℝ))
    (l := (13945127036761807851 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (55818 / 10000000 : ℝ))
  have hp : (1176741682904508 / 18446744073709551616 : ℝ) ≤ 8 * (55818 / 10000000 : ℝ) *
      (((1003 / 320 : ℝ) - (501 / 160 : ℝ)) * (13945127036761807851 / 18446744073709551616 : ℝ) / denomMax (501 / 160 : ℝ) (1003 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel11 : (1177247245574454 / 18446744073709551616 : ℝ) ≤
    8 * (55818 / 10000000 : ℝ) * ∫ s in (1003 / 320 : ℝ)..(251 / 80 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (1003 / 320 : ℝ)) (b := (251 / 80 : ℝ))
    (l := (13952561113080323228 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (55818 / 10000000 : ℝ))
  have hp : (1177247245574454 / 18446744073709551616 : ℝ) ≤ 8 * (55818 / 10000000 : ℝ) *
      (((251 / 80 : ℝ) - (1003 / 320 : ℝ)) * (13952561113080323228 / 18446744073709551616 : ℝ) / denomMax (1003 / 320 : ℝ) (251 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel12 : (1177756623074330 / 18446744073709551616 : ℝ) ≤
    8 * (55818 / 10000000 : ℝ) * ∫ s in (251 / 80 : ℝ)..(201 / 64 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (251 / 80 : ℝ)) (b := (201 / 64 : ℝ))
    (l := (13960016801611577496 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (55818 / 10000000 : ℝ))
  have hp : (1177756623074330 / 18446744073709551616 : ℝ) ≤ 8 * (55818 / 10000000 : ℝ) *
      (((201 / 64 : ℝ) - (251 / 80 : ℝ)) * (13960016801611577496 / 18446744073709551616 : ℝ) / denomMax (251 / 80 : ℝ) (201 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel13 : (1178269824974159 / 18446744073709551616 : ℝ) ≤
    8 * (55818 / 10000000 : ℝ) * ∫ s in (201 / 64 : ℝ)..(503 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (201 / 64 : ℝ)) (b := (503 / 160 : ℝ))
    (l := (13967494197350350125 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (55818 / 10000000 : ℝ))
  have hp : (1178269824974159 / 18446744073709551616 : ℝ) ≤ 8 * (55818 / 10000000 : ℝ) *
      (((503 / 160 : ℝ) - (201 / 64 : ℝ)) * (13967494197350350125 / 18446744073709551616 : ℝ) / denomMax (201 / 64 : ℝ) (503 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel14 : (1178786860928268 / 18446744073709551616 : ℝ) ≤
    8 * (55818 / 10000000 : ℝ) * ∫ s in (503 / 160 : ℝ)..(1007 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (503 / 160 : ℝ)) (b := (1007 / 320 : ℝ))
    (l := (13974993395852514369 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (55818 / 10000000 : ℝ))
  have hp : (1178786860928268 / 18446744073709551616 : ℝ) ≤ 8 * (55818 / 10000000 : ℝ) *
      (((1007 / 320 : ℝ) - (503 / 160 : ℝ)) * (13974993395852514369 / 18446744073709551616 : ℝ) / denomMax (503 / 160 : ℝ) (1007 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel15 : (1179307740675767 / 18446744073709551616 : ℝ) ≤
    8 * (55818 / 10000000 : ℝ) * ∫ s in (1007 / 320 : ℝ)..(63 / 20 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (1007 / 320 : ℝ)) (b := (63 / 20 : ℝ))
    (l := (13982514493239211897 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (55818 / 10000000 : ℝ))
  have hp : (1179307740675767 / 18446744073709551616 : ℝ) ≤ 8 * (55818 / 10000000 : ℝ) *
      (((63 / 20 : ℝ) - (1007 / 320 : ℝ)) * (13982514493239211897 / 18446744073709551616 : ℝ) / denomMax (1007 / 320 : ℝ) (63 / 20 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel16 : (1179832474041036 / 18446744073709551616 : ℝ) ≤
    8 * (55818 / 10000000 : ℝ) * ∫ s in (63 / 20 : ℝ)..(1009 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (63 / 20 : ℝ)) (b := (1009 / 320 : ℝ))
    (l := (13990057586201064976 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (55818 / 10000000 : ℝ))
  have hp : (1179832474041036 / 18446744073709551616 : ℝ) ≤ 8 * (55818 / 10000000 : ℝ) *
      (((1009 / 320 : ℝ) - (63 / 20 : ℝ)) * (13990057586201064976 / 18446744073709551616 : ℝ) / denomMax (63 / 20 : ℝ) (1009 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel17 : (1180361070934221 / 18446744073709551616 : ℝ) ≤
    8 * (55818 / 10000000 : ℝ) * ∫ s in (1009 / 320 : ℝ)..(101 / 32 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (1009 / 320 : ℝ)) (b := (101 / 32 : ℝ))
    (l := (13997622772002426599 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (55818 / 10000000 : ℝ))
  have hp : (1180361070934221 / 18446744073709551616 : ℝ) ≤ 8 * (55818 / 10000000 : ℝ) *
      (((101 / 32 : ℝ) - (1009 / 320 : ℝ)) * (13997622772002426599 / 18446744073709551616 : ℝ) / denomMax (1009 / 320 : ℝ) (101 / 32 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel18 : (1180893541351726 / 18446744073709551616 : ℝ) ≤
    8 * (55818 / 10000000 : ℝ) * ∫ s in (101 / 32 : ℝ)..(1011 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (101 / 32 : ℝ)) (b := (1011 / 320 : ℝ))
    (l := (14005210148485668967 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (55818 / 10000000 : ℝ))
  have hp : (1180893541351726 / 18446744073709551616 : ℝ) ≤ 8 * (55818 / 10000000 : ℝ) *
      (((1011 / 320 : ℝ) - (101 / 32 : ℝ)) * (14005210148485668967 / 18446744073709551616 : ℝ) / denomMax (101 / 32 : ℝ) (1011 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel19 : (1181429895376720 / 18446744073709551616 : ℝ) ≤
    8 * (55818 / 10000000 : ℝ) * ∫ s in (1011 / 320 : ℝ)..(253 / 80 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (1011 / 320 : ℝ)) (b := (253 / 80 : ℝ))
    (l := (14012819814075510733 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (55818 / 10000000 : ℝ))
  have hp : (1181429895376720 / 18446744073709551616 : ℝ) ≤ 8 * (55818 / 10000000 : ℝ) *
      (((253 / 80 : ℝ) - (1011 / 320 : ℝ)) * (14012819814075510733 / 18446744073709551616 : ℝ) / denomMax (1011 / 320 : ℝ) (253 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel20 : (1181970143179642 / 18446744073709551616 : ℝ) ≤
    8 * (55818 / 10000000 : ℝ) * ∫ s in (253 / 80 : ℝ)..(1013 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (253 / 80 : ℝ)) (b := (1013 / 320 : ℝ))
    (l := (14020451867783383409 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (55818 / 10000000 : ℝ))
  have hp : (1181970143179642 / 18446744073709551616 : ℝ) ≤ 8 * (55818 / 10000000 : ℝ) *
      (((1013 / 320 : ℝ) - (253 / 80 : ℝ)) * (14020451867783383409 / 18446744073709551616 : ℝ) / denomMax (253 / 80 : ℝ) (1013 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel21 : (1182514295018715 / 18446744073709551616 : ℝ) ≤
    8 * (55818 / 10000000 : ℝ) * ∫ s in (1013 / 320 : ℝ)..(507 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (1013 / 320 : ℝ)) (b := (507 / 160 : ℝ))
    (l := (14028106409211837366 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (55818 / 10000000 : ℝ))
  have hp : (1182514295018715 / 18446744073709551616 : ℝ) ≤ 8 * (55818 / 10000000 : ℝ) *
      (((507 / 160 : ℝ) - (1013 / 320 : ℝ)) * (14028106409211837366 / 18446744073709551616 : ℝ) / denomMax (1013 / 320 : ℝ) (507 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel22 : (1183062361240467 / 18446744073709551616 : ℝ) ≤
    8 * (55818 / 10000000 : ℝ) * ∫ s in (507 / 160 : ℝ)..(203 / 64 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (507 / 160 : ℝ)) (b := (203 / 64 : ℝ))
    (l := (14035783538558987836 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (55818 / 10000000 : ℝ))
  have hp : (1183062361240467 / 18446744073709551616 : ℝ) ≤ 8 * (55818 / 10000000 : ℝ) *
      (((203 / 64 : ℝ) - (507 / 160 : ℝ)) * (14035783538558987836 / 18446744073709551616 : ℝ) / denomMax (507 / 160 : ℝ) (203 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel23 : (1183614352280252 / 18446744073709551616 : ℝ) ≤
    8 * (55818 / 10000000 : ℝ) * ∫ s in (203 / 64 : ℝ)..(127 / 40 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (203 / 64 : ℝ)) (b := (127 / 40 : ℝ))
    (l := (14043483356623001357 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (55818 / 10000000 : ℝ))
  have hp : (1183614352280252 / 18446744073709551616 : ℝ) ≤ 8 * (55818 / 10000000 : ℝ) *
      (((127 / 40 : ℝ) - (203 / 64 : ℝ)) * (14043483356623001357 / 18446744073709551616 : ℝ) / denomMax (203 / 64 : ℝ) (127 / 40 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel24 : (1184170278662783 / 18446744073709551616 : ℝ) ≤
    8 * (55818 / 10000000 : ℝ) * ∫ s in (127 / 40 : ℝ)..(1017 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (127 / 40 : ℝ)) (b := (1017 / 320 : ℝ))
    (l := (14051205964806623078 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (55818 / 10000000 : ℝ))
  have hp : (1184170278662783 / 18446744073709551616 : ℝ) ≤ 8 * (55818 / 10000000 : ℝ) *
      (((1017 / 320 : ℝ) - (127 / 40 : ℝ)) * (14051205964806623078 / 18446744073709551616 : ℝ) / denomMax (127 / 40 : ℝ) (1017 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel25 : (1184730151002666 / 18446744073709551616 : ℝ) ≤
    8 * (55818 / 10000000 : ℝ) * ∫ s in (1017 / 320 : ℝ)..(509 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (1017 / 320 : ℝ)) (b := (509 / 160 : ℝ))
    (l := (14058951465121745375 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (55818 / 10000000 : ℝ))
  have hp : (1184730151002666 / 18446744073709551616 : ℝ) ≤ 8 * (55818 / 10000000 : ℝ) *
      (((509 / 160 : ℝ) - (1017 / 320 : ℝ)) * (14058951465121745375 / 18446744073709551616 : ℝ) / denomMax (1017 / 320 : ℝ) (509 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel26 : (1185293980004941 / 18446744073709551616 : ℝ) ≤
    8 * (55818 / 10000000 : ℝ) * ∫ s in (509 / 160 : ℝ)..(1019 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (509 / 160 : ℝ)) (b := (1019 / 320 : ℝ))
    (l := (14066719960194018215 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (55818 / 10000000 : ℝ))
  have hp : (1185293980004941 / 18446744073709551616 : ℝ) ≤ 8 * (55818 / 10000000 : ℝ) *
      (((1019 / 320 : ℝ) - (509 / 160 : ℝ)) * (14066719960194018215 / 18446744073709551616 : ℝ) / denomMax (509 / 160 : ℝ) (1019 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel27 : (1185861776465627 / 18446744073709551616 : ℝ) ≤
    8 * (55818 / 10000000 : ℝ) * ∫ s in (1019 / 320 : ℝ)..(51 / 16 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (1019 / 320 : ℝ)) (b := (51 / 16 : ℝ))
    (l := (14074511553267501709 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (55818 / 10000000 : ℝ))
  have hp : (1185861776465627 / 18446744073709551616 : ℝ) ≤ 8 * (55818 / 10000000 : ℝ) *
      (((51 / 16 : ℝ) - (1019 / 320 : ℝ)) * (14074511553267501709 / 18446744073709551616 : ℝ) / denomMax (1019 / 320 : ℝ) (51 / 16 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel28 : (1186433551272279 / 18446744073709551616 : ℝ) ≤
    8 * (55818 / 10000000 : ℝ) * ∫ s in (51 / 16 : ℝ)..(1021 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (51 / 16 : ℝ)) (b := (1021 / 320 : ℝ))
    (l := (14082326348209361326 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (55818 / 10000000 : ℝ))
  have hp : (1186433551272279 / 18446744073709551616 : ℝ) ≤ 8 * (55818 / 10000000 : ℝ) *
      (((1021 / 320 : ℝ) - (51 / 16 : ℝ)) * (14082326348209361326 / 18446744073709551616 : ℝ) / denomMax (51 / 16 : ℝ) (1021 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel29 : (1187009315404544 / 18446744073709551616 : ℝ) ≤
    8 * (55818 / 10000000 : ℝ) * ∫ s in (1021 / 320 : ℝ)..(511 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (1021 / 320 : ℝ)) (b := (511 / 160 : ℝ))
    (l := (14090164449514606210 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (55818 / 10000000 : ℝ))
  have hp : (1187009315404544 / 18446744073709551616 : ℝ) ≤ 8 * (55818 / 10000000 : ℝ) *
      (((511 / 160 : ℝ) - (1021 / 320 : ℝ)) * (14090164449514606210 / 18446744073709551616 : ℝ) / denomMax (1021 / 320 : ℝ) (511 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel30 : (1187589079934723 / 18446744073709551616 : ℝ) ≤
    8 * (55818 / 10000000 : ℝ) * ∫ s in (511 / 160 : ℝ)..(1023 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (511 / 160 : ℝ)) (b := (1023 / 320 : ℝ))
    (l := (14098025962310871077 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (55818 / 10000000 : ℝ))
  have hp : (1187589079934723 / 18446744073709551616 : ℝ) ≤ 8 * (55818 / 10000000 : ℝ) *
      (((1023 / 320 : ℝ) - (511 / 160 : ℝ)) * (14098025962310871077 / 18446744073709551616 : ℝ) / denomMax (511 / 160 : ℝ) (1023 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel31 : (1188172856028347 / 18446744073709551616 : ℝ) ≤
    8 * (55818 / 10000000 : ℝ) * ∫ s in (1023 / 320 : ℝ)..(16 / 5 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (1023 / 320 : ℝ)) (b := (16 / 5 : ℝ))
    (l := (14105910992363242153 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (55818 / 10000000 : ℝ))
  have hp : (1188172856028347 / 18446744073709551616 : ℝ) ≤ 8 * (55818 / 10000000 : ℝ) *
      (((16 / 5 : ℝ) - (1023 / 320 : ℝ)) * (14105910992363242153 / 18446744073709551616 : ℝ) / denomMax (1023 / 320 : ℝ) (16 / 5 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

theorem lower : (37751492568965241 / 18446744073709551616 : ℝ) ≤
    8 * (55818 / 10000000 : ℝ) * ∫ s in (31 / 10 : ℝ)..(16 / 5 : ℝ), density s := by
  have he := integral_grid_sum (31 / 10 : ℝ) (16 / 5 : ℝ) 32 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [endpoint, alpha, beta])
  norm_num [Finset.sum_range_succ] at he
  linarith only [panel00, panel01, panel02, panel03, panel04, panel05, panel06, panel07, panel08, panel09, panel10, panel11, panel12, panel13, panel14, panel15, panel16, panel17, panel18, panel19, panel20, panel21, panel22, panel23, panel24, panel25, panel26, panel27, panel28, panel29, panel30, panel31, he]

end Wu18938Campaign.M3.Confirmed.TableRow11
