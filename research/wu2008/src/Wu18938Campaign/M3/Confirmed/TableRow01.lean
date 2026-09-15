import Wu18938Campaign.M3.Confirmed.TableBounds

noncomputable section
namespace Wu18938Campaign.M3.Confirmed.TableRow01
open Real Set MeasureTheory QuarterTrim
open WuSource.SrcSixthGain Wu18938Campaign.M3.Confirmed.TableBounds

private theorem panel00 : (4096148520442038 / 18446744073709551616 : ℝ) ≤
    8 * (191556 / 10000000 : ℝ) * ∫ s in (21 / 10 : ℝ)..(673 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (21 / 10 : ℝ)) (b := (673 / 320 : ℝ))
    (l := (12286891067824655916 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (191556 / 10000000 : ℝ))
  have hp : (4096148520442038 / 18446744073709551616 : ℝ) ≤ 8 * (191556 / 10000000 : ℝ) *
      (((673 / 320 : ℝ) - (21 / 10 : ℝ)) * (12286891067824655916 / 18446744073709551616 : ℝ) / denomMax (21 / 10 : ℝ) (673 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel01 : (4094028384157086 / 18446744073709551616 : ℝ) ≤
    8 * (191556 / 10000000 : ℝ) * ∫ s in (673 / 320 : ℝ)..(337 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (673 / 320 : ℝ)) (b := (337 / 160 : ℝ))
    (l := (12290298163286713909 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (191556 / 10000000 : ℝ))
  have hp : (4094028384157086 / 18446744073709551616 : ℝ) ≤ 8 * (191556 / 10000000 : ℝ) *
      (((337 / 160 : ℝ) - (673 / 320 : ℝ)) * (12290298163286713909 / 18446744073709551616 : ℝ) / denomMax (673 / 320 : ℝ) (337 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel02 : (4091922205326497 / 18446744073709551616 : ℝ) ≤
    8 * (191556 / 10000000 : ℝ) * ∫ s in (337 / 160 : ℝ)..(135 / 64 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (337 / 160 : ℝ)) (b := (135 / 64 : ℝ))
    (l := (12293711924355179675 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (191556 / 10000000 : ℝ))
  have hp : (4091922205326497 / 18446744073709551616 : ℝ) ≤ 8 * (191556 / 10000000 : ℝ) *
      (((135 / 64 : ℝ) - (337 / 160 : ℝ)) * (12293711924355179675 / 18446744073709551616 : ℝ) / denomMax (337 / 160 : ℝ) (135 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel03 : (4089829944428055 / 18446744073709551616 : ℝ) ≤
    8 * (191556 / 10000000 : ℝ) * ∫ s in (135 / 64 : ℝ)..(169 / 80 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (135 / 64 : ℝ)) (b := (169 / 80 : ℝ))
    (l := (12297132370668619658 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (191556 / 10000000 : ℝ))
  have hp : (4089829944428055 / 18446744073709551616 : ℝ) ≤ 8 * (191556 / 10000000 : ℝ) *
      (((169 / 80 : ℝ) - (135 / 64 : ℝ)) * (12297132370668619658 / 18446744073709551616 : ℝ) / denomMax (135 / 64 : ℝ) (169 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel04 : (4087751562260714 / 18446744073709551616 : ℝ) ≤
    8 * (191556 / 10000000 : ℝ) * ∫ s in (169 / 80 : ℝ)..(677 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (169 / 80 : ℝ)) (b := (677 / 320 : ℝ))
    (l := (12300559521943052685 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (191556 / 10000000 : ℝ))
  have hp : (4087751562260714 / 18446744073709551616 : ℝ) ≤ 8 * (191556 / 10000000 : ℝ) *
      (((677 / 320 : ℝ) - (169 / 80 : ℝ)) * (12300559521943052685 / 18446744073709551616 : ℝ) / denomMax (169 / 80 : ℝ) (677 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel05 : (4085687019942659 / 18446744073709551616 : ℝ) ≤
    8 * (191556 / 10000000 : ℝ) * ∫ s in (677 / 320 : ℝ)..(339 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (677 / 320 : ℝ)) (b := (339 / 160 : ℝ))
    (l := (12303993397972333299 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (191556 / 10000000 : ℝ))
  have hp : (4085687019942659 / 18446744073709551616 : ℝ) ≤ 8 * (191556 / 10000000 : ℝ) *
      (((339 / 160 : ℝ) - (677 / 320 : ℝ)) * (12303993397972333299 / 18446744073709551616 : ℝ) / denomMax (677 / 320 : ℝ) (339 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel06 : (4083636278909388 / 18446744073709551616 : ℝ) ≤
    8 * (191556 / 10000000 : ℝ) * ∫ s in (339 / 160 : ℝ)..(679 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (339 / 160 : ℝ)) (b := (679 / 320 : ℝ))
    (l := (12307434018628537370 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (191556 / 10000000 : ℝ))
  have hp : (4083636278909388 / 18446744073709551616 : ℝ) ≤ 8 * (191556 / 10000000 : ℝ) *
      (((679 / 320 : ℝ) - (339 / 160 : ℝ)) * (12307434018628537370 / 18446744073709551616 : ℝ) / denomMax (339 / 160 : ℝ) (679 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel07 : (4081599300911811 / 18446744073709551616 : ℝ) ≤
    8 * (191556 / 10000000 : ℝ) * ∫ s in (679 / 320 : ℝ)..(17 / 8 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (679 / 320 : ℝ)) (b := (17 / 8 : ℝ))
    (l := (12310881403862350020 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (191556 / 10000000 : ℝ))
  have hp : (4081599300911811 / 18446744073709551616 : ℝ) ≤ 8 * (191556 / 10000000 : ℝ) *
      (((17 / 8 : ℝ) - (679 / 320 : ℝ)) * (12310881403862350020 / 18446744073709551616 : ℝ) / denomMax (679 / 320 : ℝ) (17 / 8 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel08 : (4079576048014374 / 18446744073709551616 : ℝ) ≤
    8 * (191556 / 10000000 : ℝ) * ∫ s in (17 / 8 : ℝ)..(681 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (17 / 8 : ℝ)) (b := (681 / 320 : ℝ))
    (l := (12314335573703455853 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (191556 / 10000000 : ℝ))
  have hp : (4079576048014374 / 18446744073709551616 : ℝ) ≤ 8 * (191556 / 10000000 : ℝ) *
      (((681 / 320 : ℝ) - (17 / 8 : ℝ)) * (12314335573703455853 / 18446744073709551616 : ℝ) / denomMax (17 / 8 : ℝ) (681 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel09 : (4077566482593194 / 18446744073709551616 : ℝ) ≤
    8 * (191556 / 10000000 : ℝ) * ∫ s in (681 / 320 : ℝ)..(341 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (681 / 320 : ℝ)) (b := (341 / 160 : ℝ))
    (l := (12317796548260931529 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (191556 / 10000000 : ℝ))
  have hp : (4077566482593194 / 18446744073709551616 : ℝ) ≤ 8 * (191556 / 10000000 : ℝ) *
      (((341 / 160 : ℝ) - (681 / 320 : ℝ)) * (12317796548260931529 / 18446744073709551616 : ℝ) / denomMax (681 / 320 : ℝ) (341 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel10 : (4075570567334219 / 18446744073709551616 : ℝ) ≤
    8 * (191556 / 10000000 : ℝ) * ∫ s in (341 / 160 : ℝ)..(683 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (341 / 160 : ℝ)) (b := (683 / 320 : ℝ))
    (l := (12321264347723640679 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (191556 / 10000000 : ℝ))
  have hp : (4075570567334219 / 18446744073709551616 : ℝ) ≤ 8 * (191556 / 10000000 : ℝ) *
      (((683 / 320 : ℝ) - (341 / 160 : ℝ)) * (12321264347723640679 / 18446744073709551616 : ℝ) / denomMax (341 / 160 : ℝ) (683 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel11 : (4073588265231405 / 18446744073709551616 : ℝ) ≤
    8 * (191556 / 10000000 : ℝ) * ∫ s in (683 / 320 : ℝ)..(171 / 80 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (683 / 320 : ℝ)) (b := (171 / 80 : ℝ))
    (l := (12324738992360631195 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (191556 / 10000000 : ℝ))
  have hp : (4073588265231405 / 18446744073709551616 : ℝ) ≤ 8 * (191556 / 10000000 : ℝ) *
      (((171 / 80 : ℝ) - (683 / 320 : ℝ)) * (12324738992360631195 / 18446744073709551616 : ℝ) / denomMax (683 / 320 : ℝ) (171 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel12 : (4071619539584912 / 18446744073709551616 : ℝ) ≤
    8 * (191556 / 10000000 : ℝ) * ∫ s in (171 / 80 : ℝ)..(137 / 64 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (171 / 80 : ℝ)) (b := (137 / 64 : ℝ))
    (l := (12328220502521534899 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (191556 / 10000000 : ℝ))
  have hp : (4071619539584912 / 18446744073709551616 : ℝ) ≤ 8 * (191556 / 10000000 : ℝ) *
      (((137 / 64 : ℝ) - (171 / 80 : ℝ)) * (12328220502521534899 / 18446744073709551616 : ℝ) / denomMax (171 / 80 : ℝ) (137 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel13 : (4069664353999315 / 18446744073709551616 : ℝ) ≤
    8 * (191556 / 10000000 : ℝ) * ∫ s in (137 / 64 : ℝ)..(343 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (137 / 64 : ℝ)) (b := (343 / 160 : ℝ))
    (l := (12331708898636969612 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (191556 / 10000000 : ℝ))
  have hp : (4069664353999315 / 18446744073709551616 : ℝ) ≤ 8 * (191556 / 10000000 : ℝ) *
      (((343 / 160 : ℝ) - (137 / 64 : ℝ)) * (12331708898636969612 / 18446744073709551616 : ℝ) / denomMax (137 / 64 : ℝ) (343 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel14 : (4067722672381841 / 18446744073709551616 : ℝ) ≤
    8 * (191556 / 10000000 : ℝ) * ∫ s in (343 / 160 : ℝ)..(687 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (343 / 160 : ℝ)) (b := (687 / 320 : ℝ))
    (l := (12335204201218943637 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (191556 / 10000000 : ℝ))
  have hp : (4067722672381841 / 18446744073709551616 : ℝ) ≤ 8 * (191556 / 10000000 : ℝ) *
      (((687 / 320 : ℝ) - (343 / 160 : ℝ)) * (12335204201218943637 / 18446744073709551616 : ℝ) / denomMax (343 / 160 : ℝ) (687 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel15 : (4065794458940615 / 18446744073709551616 : ℝ) ≤
    8 * (191556 / 10000000 : ℝ) * ∫ s in (687 / 320 : ℝ)..(43 / 20 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (687 / 320 : ℝ)) (b := (43 / 20 : ℝ))
    (l := (12338706430861262683 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (191556 / 10000000 : ℝ))
  have hp : (4065794458940615 / 18446744073709551616 : ℝ) ≤ 8 * (191556 / 10000000 : ℝ) *
      (((43 / 20 : ℝ) - (687 / 320 : ℝ)) * (12338706430861262683 / 18446744073709551616 : ℝ) / denomMax (687 / 320 : ℝ) (43 / 20 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel16 : (4063879678182930 / 18446744073709551616 : ℝ) ≤
    8 * (191556 / 10000000 : ℝ) * ∫ s in (43 / 20 : ℝ)..(689 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (43 / 20 : ℝ)) (b := (689 / 320 : ℝ))
    (l := (12342215608239939237 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (191556 / 10000000 : ℝ))
  have hp : (4063879678182930 / 18446744073709551616 : ℝ) ≤ 8 * (191556 / 10000000 : ℝ) *
      (((689 / 320 : ℝ) - (43 / 20 : ℝ)) * (12342215608239939237 / 18446744073709551616 : ℝ) / denomMax (43 / 20 : ℝ) (689 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel17 : (4061978294913533 / 18446744073709551616 : ℝ) ≤
    8 * (191556 / 10000000 : ℝ) * ∫ s in (689 / 320 : ℝ)..(69 / 32 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (689 / 320 : ℝ)) (b := (69 / 32 : ℝ))
    (l := (12345731754113604399 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (191556 / 10000000 : ℝ))
  have hp : (4061978294913533 / 18446744073709551616 : ℝ) ≤ 8 * (191556 / 10000000 : ℝ) *
      (((69 / 32 : ℝ) - (689 / 320 : ℝ)) * (12345731754113604399 / 18446744073709551616 : ℝ) / denomMax (689 / 320 : ℝ) (69 / 32 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel18 : (4060090274232928 / 18446744073709551616 : ℝ) ≤
    8 * (191556 / 10000000 : ℝ) * ∫ s in (69 / 32 : ℝ)..(691 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (69 / 32 : ℝ)) (b := (691 / 320 : ℝ))
    (l := (12349254889323922209 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (191556 / 10000000 : ℝ))
  have hp : (4060090274232928 / 18446744073709551616 : ℝ) ≤ 8 * (191556 / 10000000 : ℝ) *
      (((691 / 320 : ℝ) - (69 / 32 : ℝ)) * (12349254889323922209 / 18446744073709551616 : ℝ) / denomMax (69 / 32 : ℝ) (691 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel19 : (4058215581535697 / 18446744073709551616 : ℝ) ≤
    8 * (191556 / 10000000 : ℝ) * ∫ s in (691 / 320 : ℝ)..(173 / 80 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (691 / 320 : ℝ)) (b := (173 / 80 : ℝ))
    (l := (12352785034796006477 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (191556 / 10000000 : ℝ))
  have hp : (4058215581535697 / 18446744073709551616 : ℝ) ≤ 8 * (191556 / 10000000 : ℝ) *
      (((173 / 80 : ℝ) - (691 / 320 : ℝ)) * (12352785034796006477 / 18446744073709551616 : ℝ) / denomMax (691 / 320 : ℝ) (173 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel20 : (4056354182508839 / 18446744073709551616 : ℝ) ≤
    8 * (191556 / 10000000 : ℝ) * ∫ s in (173 / 80 : ℝ)..(693 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (173 / 80 : ℝ)) (b := (693 / 320 : ℝ))
    (l := (12356322211538840130 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (191556 / 10000000 : ℝ))
  have hp : (4056354182508839 / 18446744073709551616 : ℝ) ≤ 8 * (191556 / 10000000 : ℝ) *
      (((693 / 320 : ℝ) - (173 / 80 : ℝ)) * (12356322211538840130 / 18446744073709551616 : ℝ) / denomMax (173 / 80 : ℝ) (693 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel21 : (4054506043130126 / 18446744073709551616 : ℝ) ≤
    8 * (191556 / 10000000 : ℝ) * ∫ s in (693 / 320 : ℝ)..(347 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (693 / 320 : ℝ)) (b := (347 / 160 : ℝ))
    (l := (12359866440645697100 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (191556 / 10000000 : ℝ))
  have hp : (4054506043130126 / 18446744073709551616 : ℝ) ≤ 8 * (191556 / 10000000 : ℝ) *
      (((347 / 160 : ℝ) - (693 / 320 : ℝ)) * (12359866440645697100 / 18446744073709551616 : ℝ) / denomMax (693 / 320 : ℝ) (347 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel22 : (4052671129666471 / 18446744073709551616 : ℝ) ≤
    8 * (191556 / 10000000 : ℝ) * ∫ s in (347 / 160 : ℝ)..(139 / 64 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (347 / 160 : ℝ)) (b := (139 / 64 : ℝ))
    (l := (12363417743294566772 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (191556 / 10000000 : ℝ))
  have hp : (4052671129666471 / 18446744073709551616 : ℝ) ≤ 8 * (191556 / 10000000 : ℝ) *
      (((139 / 64 : ℝ) - (347 / 160 : ℝ)) * (12363417743294566772 / 18446744073709551616 : ℝ) / denomMax (347 / 160 : ℝ) (139 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel23 : (4050849408672324 / 18446744073709551616 : ℝ) ≤
    8 * (191556 / 10000000 : ℝ) * ∫ s in (139 / 64 : ℝ)..(87 / 40 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (139 / 64 : ℝ)) (b := (87 / 40 : ℝ))
    (l := (12366976140748581002 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (191556 / 10000000 : ℝ))
  have hp : (4050849408672324 / 18446744073709551616 : ℝ) ≤ 8 * (191556 / 10000000 : ℝ) *
      (((87 / 40 : ℝ) - (139 / 64 : ℝ)) * (12366976140748581002 / 18446744073709551616 : ℝ) / denomMax (139 / 64 : ℝ) (87 / 40 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel24 : (4049040846988074 / 18446744073709551616 : ℝ) ≤
    8 * (191556 / 10000000 : ℝ) * ∫ s in (87 / 40 : ℝ)..(697 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (87 / 40 : ℝ)) (b := (697 / 320 : ℝ))
    (l := (12370541654356443730 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (191556 / 10000000 : ℝ))
  have hp : (4049040846988074 / 18446744073709551616 : ℝ) ≤ 8 * (191556 / 10000000 : ℝ) *
      (((697 / 320 : ℝ) - (87 / 40 : ℝ)) * (12370541654356443730 / 18446744073709551616 : ℝ) / denomMax (87 / 40 : ℝ) (697 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel25 : (4047245411738468 / 18446744073709551616 : ℝ) ≤
    8 * (191556 / 10000000 : ℝ) * ∫ s in (697 / 320 : ℝ)..(349 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (697 / 320 : ℝ)) (b := (349 / 160 : ℝ))
    (l := (12374114305552863206 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (191556 / 10000000 : ℝ))
  have hp : (4047245411738468 / 18446744073709551616 : ℝ) ≤ 8 * (191556 / 10000000 : ℝ) *
      (((349 / 160 : ℝ) - (697 / 320 : ℝ)) * (12374114305552863206 / 18446744073709551616 : ℝ) / denomMax (697 / 320 : ℝ) (349 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel26 : (4045463070331058 / 18446744073709551616 : ℝ) ≤
    8 * (191556 / 10000000 : ℝ) * ∫ s in (349 / 160 : ℝ)..(699 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (349 / 160 : ℝ)) (b := (699 / 320 : ℝ))
    (l := (12377694115858986844 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (191556 / 10000000 : ℝ))
  have hp : (4045463070331058 / 18446744073709551616 : ℝ) ≤ 8 * (191556 / 10000000 : ℝ) *
      (((699 / 320 : ℝ) - (349 / 160 : ℝ)) * (12377694115858986844 / 18446744073709551616 : ℝ) / denomMax (349 / 160 : ℝ) (699 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel27 : (4043693790454650 / 18446744073709551616 : ℝ) ≤
    8 * (191556 / 10000000 : ℝ) * ∫ s in (699 / 320 : ℝ)..(35 / 16 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (699 / 320 : ℝ)) (b := (35 / 16 : ℝ))
    (l := (12381281106882838731 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (191556 / 10000000 : ℝ))
  have hp : (4043693790454650 / 18446744073709551616 : ℝ) ≤ 8 * (191556 / 10000000 : ℝ) *
      (((35 / 16 : ℝ) - (699 / 320 : ℝ)) * (12381281106882838731 / 18446744073709551616 : ℝ) / denomMax (699 / 320 : ℝ) (35 / 16 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel28 : (4041937540077776 / 18446744073709551616 : ℝ) ≤
    8 * (191556 / 10000000 : ℝ) * ∫ s in (35 / 16 : ℝ)..(701 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (35 / 16 : ℝ)) (b := (701 / 320 : ℝ))
    (l := (12384875300319759792 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (191556 / 10000000 : ℝ))
  have hp : (4041937540077776 / 18446744073709551616 : ℝ) ≤ 8 * (191556 / 10000000 : ℝ) *
      (((701 / 320 : ℝ) - (35 / 16 : ℝ)) * (12384875300319759792 / 18446744073709551616 : ℝ) / denomMax (35 / 16 : ℝ) (701 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel29 : (4040194287447182 / 18446744073709551616 : ℝ) ≤
    8 * (191556 / 10000000 : ℝ) * ∫ s in (701 / 320 : ℝ)..(351 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (701 / 320 : ℝ)) (b := (351 / 160 : ℝ))
    (l := (12388476717952850659 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (191556 / 10000000 : ℝ))
  have hp : (4040194287447182 / 18446744073709551616 : ℝ) ≤ 8 * (191556 / 10000000 : ℝ) *
      (((351 / 160 : ℝ) - (701 / 320 : ℝ)) * (12388476717952850659 / 18446744073709551616 : ℝ) / denomMax (701 / 320 : ℝ) (351 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel30 : (4038464001086330 / 18446744073709551616 : ℝ) ≤
    8 * (191556 / 10000000 : ℝ) * ∫ s in (351 / 160 : ℝ)..(703 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (351 / 160 : ℝ)) (b := (703 / 320 : ℝ))
    (l := (12392085381653417229 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (191556 / 10000000 : ℝ))
  have hp : (4038464001086330 / 18446744073709551616 : ℝ) ≤ 8 * (191556 / 10000000 : ℝ) *
      (((703 / 320 : ℝ) - (351 / 160 : ℝ)) * (12392085381653417229 / 18446744073709551616 : ℝ) / denomMax (351 / 160 : ℝ) (703 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel31 : (4036746649793920 / 18446744073709551616 : ℝ) ≤
    8 * (191556 / 10000000 : ℝ) * ∫ s in (703 / 320 : ℝ)..(11 / 5 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (703 / 320 : ℝ)) (b := (11 / 5 : ℝ))
    (l := (12395701313381418960 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (191556 / 10000000 : ℝ))
  have hp : (4036746649793920 / 18446744073709551616 : ℝ) ≤ 8 * (191556 / 10000000 : ℝ) *
      (((11 / 5 : ℝ) - (703 / 320 : ℝ)) * (12395701313381418960 / 18446744073709551616 : ℝ) / denomMax (703 / 320 : ℝ) (11 / 5 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

theorem lower : (130093035795218429 / 18446744073709551616 : ℝ) ≤
    8 * (191556 / 10000000 : ℝ) * ∫ s in (21 / 10 : ℝ)..(11 / 5 : ℝ), density s := by
  have he := integral_grid_sum (21 / 10 : ℝ) (11 / 5 : ℝ) 32 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [endpoint, alpha, beta])
  norm_num [Finset.sum_range_succ] at he
  linarith only [panel00, panel01, panel02, panel03, panel04, panel05, panel06, panel07, panel08, panel09, panel10, panel11, panel12, panel13, panel14, panel15, panel16, panel17, panel18, panel19, panel20, panel21, panel22, panel23, panel24, panel25, panel26, panel27, panel28, panel29, panel30, panel31, he]

end Wu18938Campaign.M3.Confirmed.TableRow01
