import Wu18938Campaign.M3.Confirmed.TableBounds

noncomputable section
namespace Wu18938Campaign.M3.Confirmed.TableRow17
open Real Set MeasureTheory QuarterTrim
open WuSource.SrcSixthGain Wu18938Campaign.M3.Confirmed.TableBounds

private theorem panel00 : (310762429444675 / 18446744073709551616 : ℝ) ≤
    8 * (18997 / 10000000 : ℝ) * ∫ s in (18 / 5 : ℝ)..(1153 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (18 / 5 : ℝ)) (b := (1153 / 320 : ℝ))
    (l := (10775160442736848566 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (18997 / 10000000 : ℝ))
  have hp : (310762429444675 / 18446744073709551616 : ℝ) ≤ 8 * (18997 / 10000000 : ℝ) *
      (((1153 / 320 : ℝ) - (18 / 5 : ℝ)) * (10775160442736848566 / 18446744073709551616 : ℝ) / denomMax (18 / 5 : ℝ) (1153 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel01 : (308822834568987 / 18446744073709551616 : ℝ) ≤
    8 * (18997 / 10000000 : ℝ) * ∫ s in (1153 / 320 : ℝ)..(577 / 160 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1153 / 320 : ℝ)) (b := (577 / 160 : ℝ))
    (l := (10706168325980397674 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (18997 / 10000000 : ℝ))
  have hp : (308822834568987 / 18446744073709551616 : ℝ) ≤ 8 * (18997 / 10000000 : ℝ) *
      (((577 / 160 : ℝ) - (1153 / 320 : ℝ)) * (10706168325980397674 / 18446744073709551616 : ℝ) / denomMax (1153 / 320 : ℝ) (577 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel02 : (306879311594293 / 18446744073709551616 : ℝ) ≤
    8 * (18997 / 10000000 : ℝ) * ∫ s in (577 / 160 : ℝ)..(231 / 64 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (577 / 160 : ℝ)) (b := (231 / 64 : ℝ))
    (l := (10637042888299869548 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (18997 / 10000000 : ℝ))
  have hp : (306879311594293 / 18446744073709551616 : ℝ) ≤ 8 * (18997 / 10000000 : ℝ) *
      (((231 / 64 : ℝ) - (577 / 160 : ℝ)) * (10637042888299869548 / 18446744073709551616 : ℝ) / denomMax (577 / 160 : ℝ) (231 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel03 : (304931832831509 / 18446744073709551616 : ℝ) ≤
    8 * (18997 / 10000000 : ℝ) * ∫ s in (231 / 64 : ℝ)..(289 / 80 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (231 / 64 : ℝ)) (b := (289 / 80 : ℝ))
    (l := (10567783598610228971 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (18997 / 10000000 : ℝ))
  have hp : (304931832831509 / 18446744073709551616 : ℝ) ≤ 8 * (18997 / 10000000 : ℝ) *
      (((289 / 80 : ℝ) - (231 / 64 : ℝ)) * (10567783598610228971 / 18446744073709551616 : ℝ) / denomMax (231 / 64 : ℝ) (289 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel04 : (302980370436744 / 18446744073709551616 : ℝ) ≤
    8 * (18997 / 10000000 : ℝ) * ∫ s in (289 / 80 : ℝ)..(1157 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (289 / 80 : ℝ)) (b := (1157 / 320 : ℝ))
    (l := (10498389922567873456 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (18997 / 10000000 : ℝ))
  have hp : (302980370436744 / 18446744073709551616 : ℝ) ≤ 8 * (18997 / 10000000 : ℝ) *
      (((1157 / 320 : ℝ) - (289 / 80 : ℝ)) * (10498389922567873456 / 18446744073709551616 : ℝ) / denomMax (289 / 80 : ℝ) (1157 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel05 : (301024896409892 / 18446744073709551616 : ℝ) ≤
    8 * (18997 / 10000000 : ℝ) * ∫ s in (1157 / 320 : ℝ)..(579 / 160 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1157 / 320 : ℝ)) (b := (579 / 160 : ℝ))
    (l := (10428861322543375930 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (18997 / 10000000 : ℝ))
  have hp : (301024896409892 / 18446744073709551616 : ℝ) ≤ 8 * (18997 / 10000000 : ℝ) *
      (((579 / 160 : ℝ) - (1157 / 320 : ℝ)) * (10428861322543375930 / 18446744073709551616 : ℝ) / denomMax (1157 / 320 : ℝ) (579 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel06 : (299065382593202 / 18446744073709551616 : ℝ) ≤
    8 * (18997 / 10000000 : ℝ) * ∫ s in (579 / 160 : ℝ)..(1159 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (579 / 160 : ℝ)) (b := (1159 / 320 : ℝ))
    (l := (10359197257593937212 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (18997 / 10000000 : ℝ))
  have hp : (299065382593202 / 18446744073709551616 : ℝ) ≤ 8 * (18997 / 10000000 : ℝ) *
      (((1159 / 320 : ℝ) - (579 / 160 : ℝ)) * (10359197257593937212 / 18446744073709551616 : ℝ) / denomMax (579 / 160 : ℝ) (1159 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel07 : (297101800669838 / 18446744073709551616 : ℝ) ≤
    8 * (18997 / 10000000 : ℝ) * ∫ s in (1159 / 320 : ℝ)..(29 / 8 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1159 / 320 : ℝ)) (b := (29 / 8 : ℝ))
    (l := (10289397183435544539 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (18997 / 10000000 : ℝ))
  have hp : (297101800669838 / 18446744073709551616 : ℝ) ≤ 8 * (18997 / 10000000 : ℝ) *
      (((29 / 8 : ℝ) - (1159 / 320 : ℝ)) * (10289397183435544539 / 18446744073709551616 : ℝ) / denomMax (1159 / 320 : ℝ) (29 / 8 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel08 : (295134122162419 / 18446744073709551616 : ℝ) ≤
    8 * (18997 / 10000000 : ℝ) * ∫ s in (29 / 8 : ℝ)..(1161 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (29 / 8 : ℝ)) (b := (1161 / 320 : ℝ))
    (l := (10219460552414832313 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (18997 / 10000000 : ℝ))
  have hp : (295134122162419 / 18446744073709551616 : ℝ) ≤ 8 * (18997 / 10000000 : ℝ) *
      (((1161 / 320 : ℝ) - (29 / 8 : ℝ)) * (10219460552414832313 / 18446744073709551616 : ℝ) / denomMax (29 / 8 : ℝ) (1161 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel09 : (293162318431553 / 18446744073709551616 : ℝ) ≤
    8 * (18997 / 10000000 : ℝ) * ∫ s in (1161 / 320 : ℝ)..(581 / 160 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1161 / 320 : ℝ)) (b := (581 / 160 : ℝ))
    (l := (10149386813480641191 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (18997 / 10000000 : ℝ))
  have hp : (293162318431553 / 18446744073709551616 : ℝ) ≤ 8 * (18997 / 10000000 : ℝ) *
      (((581 / 160 : ℝ) - (1161 / 320 : ℝ)) * (10149386813480641191 / 18446744073709551616 : ℝ) / denomMax (1161 / 320 : ℝ) (581 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel10 : (291186360674349 / 18446744073709551616 : ℝ) ≤
    8 * (18997 / 10000000 : ℝ) * ∫ s in (581 / 160 : ℝ)..(1163 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (581 / 160 : ℝ)) (b := (1163 / 320 : ℝ))
    (l := (10079175412155271591 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (18997 / 10000000 : ℝ))
  have hp : (291186360674349 / 18446744073709551616 : ℝ) ≤ 8 * (18997 / 10000000 : ℝ) *
      (((1163 / 320 : ℝ) - (581 / 160 : ℝ)) * (10079175412155271591 / 18446744073709551616 : ℝ) / denomMax (581 / 160 : ℝ) (1163 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel11 : (289206219922917 / 18446744073709551616 : ℝ) ≤
    8 * (18997 / 10000000 : ℝ) * ∫ s in (1163 / 320 : ℝ)..(291 / 80 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1163 / 320 : ℝ)) (b := (291 / 80 : ℝ))
    (l := (10008825790505427604 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (18997 / 10000000 : ℝ))
  have hp : (289206219922917 / 18446744073709551616 : ℝ) ≤ 8 * (18997 / 10000000 : ℝ) *
      (((291 / 80 : ℝ) - (1163 / 320 : ℝ)) * (10008825790505427604 / 18446744073709551616 : ℝ) / denomMax (1163 / 320 : ℝ) (291 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel12 : (287221867042854 / 18446744073709551616 : ℝ) ≤
    8 * (18997 / 10000000 : ℝ) * ∫ s in (291 / 80 : ℝ)..(233 / 64 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (291 / 80 : ℝ)) (b := (233 / 64 : ℝ))
    (l := (9938337387112847262 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (18997 / 10000000 : ℝ))
  have hp : (287221867042854 / 18446744073709551616 : ℝ) ≤ 8 * (18997 / 10000000 : ℝ) *
      (((233 / 64 : ℝ) - (291 / 80 : ℝ)) * (9938337387112847262 / 18446744073709551616 : ℝ) / denomMax (291 / 80 : ℝ) (233 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel13 : (285233272731711 / 18446744073709551616 : ℝ) ≤
    8 * (18997 / 10000000 : ℝ) * ∫ s in (233 / 64 : ℝ)..(583 / 160 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (233 / 64 : ℝ)) (b := (583 / 160 : ℝ))
    (l := (9867709637044615036 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (18997 / 10000000 : ℝ))
  have hp : (285233272731711 / 18446744073709551616 : ℝ) ≤ 8 * (18997 / 10000000 : ℝ) *
      (((583 / 160 : ℝ) - (233 / 64 : ℝ)) * (9867709637044615036 / 18446744073709551616 : ℝ) / denomMax (233 / 64 : ℝ) (583 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel14 : (283240407517451 / 18446744073709551616 : ℝ) ≤
    8 * (18997 / 10000000 : ℝ) * ∫ s in (583 / 160 : ℝ)..(1167 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (583 / 160 : ℝ)) (b := (1167 / 320 : ℝ))
    (l := (9796941971823152381 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (18997 / 10000000 : ℝ))
  have hp : (283240407517451 / 18446744073709551616 : ℝ) ≤ 8 * (18997 / 10000000 : ℝ) *
      (((1167 / 320 : ℝ) - (583 / 160 : ℝ)) * (9796941971823152381 / 18446744073709551616 : ℝ) / denomMax (583 / 160 : ℝ) (1167 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel15 : (281243241756882 / 18446744073709551616 : ℝ) ≤
    8 * (18997 / 10000000 : ℝ) * ∫ s in (1167 / 320 : ℝ)..(73 / 20 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1167 / 320 : ℝ)) (b := (73 / 20 : ℝ))
    (l := (9726033819395882070 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (18997 / 10000000 : ℝ))
  have hp : (281243241756882 / 18446744073709551616 : ℝ) ≤ 8 * (18997 / 10000000 : ℝ) *
      (((73 / 20 : ℝ) - (1167 / 320 : ℝ)) * (9726033819395882070 / 18446744073709551616 : ℝ) / denomMax (1167 / 320 : ℝ) (73 / 20 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel16 : (279241745634082 / 18446744073709551616 : ℝ) ≤
    8 * (18997 / 10000000 : ℝ) * ∫ s in (73 / 20 : ℝ)..(1169 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (73 / 20 : ℝ)) (b := (1169 / 320 : ℝ))
    (l := (9654984604104562015 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (18997 / 10000000 : ℝ))
  have hp : (279241745634082 / 18446744073709551616 : ℝ) ≤ 8 * (18997 / 10000000 : ℝ) *
      (((1169 / 320 : ℝ) - (73 / 20 : ℝ)) * (9654984604104562015 / 18446744073709551616 : ℝ) / denomMax (73 / 20 : ℝ) (1169 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel17 : (277235889158807 / 18446744073709551616 : ℝ) ≤
    8 * (18997 / 10000000 : ℝ) * ∫ s in (1169 / 320 : ℝ)..(117 / 32 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1169 / 320 : ℝ)) (b := (117 / 32 : ℝ))
    (l := (9583793746654284172 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (18997 / 10000000 : ℝ))
  have hp : (277235889158807 / 18446744073709551616 : ℝ) ≤ 8 * (18997 / 10000000 : ℝ) *
      (((117 / 32 : ℝ) - (1169 / 320 : ℝ)) * (9583793746654284172 / 18446744073709551616 : ℝ) / denomMax (1169 / 320 : ℝ) (117 / 32 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel18 : (275225642164877 / 18446744073709551616 : ℝ) ≤
    8 * (18997 / 10000000 : ℝ) * ∫ s in (117 / 32 : ℝ)..(1171 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (117 / 32 : ℝ)) (b := (1171 / 320 : ℝ))
    (l := (9512460664082134089 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (18997 / 10000000 : ℝ))
  have hp : (275225642164877 / 18446744073709551616 : ℝ) ≤ 8 * (18997 / 10000000 : ℝ) *
      (((1171 / 320 : ℝ) - (117 / 32 : ℝ)) * (9512460664082134089 / 18446744073709551616 : ℝ) / denomMax (117 / 32 : ℝ) (1171 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel19 : (273210974308552 / 18446744073709551616 : ℝ) ≤
    8 * (18997 / 10000000 : ℝ) * ∫ s in (1171 / 320 : ℝ)..(293 / 80 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1171 / 320 : ℝ)) (b := (293 / 80 : ℝ))
    (l := (9440984769725506574 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (18997 / 10000000 : ℝ))
  have hp : (273210974308552 / 18446744073709551616 : ℝ) ≤ 8 * (18997 / 10000000 : ℝ) *
      (((293 / 80 : ℝ) - (1171 / 320 : ℝ)) * (9440984769725506574 / 18446744073709551616 : ℝ) / denomMax (1171 / 320 : ℝ) (293 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel20 : (271191855066887 / 18446744073709551616 : ℝ) ≤
    8 * (18997 / 10000000 : ℝ) * ∫ s in (293 / 80 : ℝ)..(1173 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (293 / 80 : ℝ)) (b := (1173 / 320 : ℝ))
    (l := (9369365473190072880 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (18997 / 10000000 : ℝ))
  have hp : (271191855066887 / 18446744073709551616 : ℝ) ≤ 8 * (18997 / 10000000 : ℝ) *
      (((1173 / 320 : ℝ) - (293 / 80 : ℝ)) * (9369365473190072880 / 18446744073709551616 : ℝ) / denomMax (293 / 80 : ℝ) (1173 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel21 : (269168253736073 / 18446744073709551616 : ℝ) ≤
    8 * (18997 / 10000000 : ℝ) * ∫ s in (1173 / 320 : ℝ)..(587 / 160 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1173 / 320 : ℝ)) (b := (587 / 160 : ℝ))
    (l := (9297602180317394752 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (18997 / 10000000 : ℝ))
  have hp : (269168253736073 / 18446744073709551616 : ℝ) ≤ 8 * (18997 / 10000000 : ℝ) *
      (((587 / 160 : ℝ) - (1173 / 320 : ℝ)) * (9297602180317394752 / 18446744073709551616 : ℝ) / denomMax (1173 / 320 : ℝ) (587 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel22 : (267140139429760 / 18446744073709551616 : ℝ) ≤
    8 * (18997 / 10000000 : ℝ) * ∫ s in (587 / 160 : ℝ)..(235 / 64 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (587 / 160 : ℝ)) (b := (235 / 64 : ℝ))
    (l := (9225694293152180587 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (18997 / 10000000 : ℝ))
  have hp : (267140139429760 / 18446744073709551616 : ℝ) ≤ 8 * (18997 / 10000000 : ℝ) *
      (((235 / 64 : ℝ) - (587 / 160 : ℝ)) * (9225694293152180587 / 18446744073709551616 : ℝ) / denomMax (587 / 160 : ℝ) (235 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel23 : (265107481077358 / 18446744073709551616 : ℝ) ≤
    8 * (18997 / 10000000 : ℝ) * ∫ s in (235 / 64 : ℝ)..(147 / 40 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (235 / 64 : ℝ)) (b := (147 / 40 : ℝ))
    (l := (9153641209909178895 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (18997 / 10000000 : ℝ))
  have hp : (265107481077358 / 18446744073709551616 : ℝ) ≤ 8 * (18997 / 10000000 : ℝ) *
      (((147 / 40 : ℝ) - (235 / 64 : ℝ)) * (9153641209909178895 / 18446744073709551616 : ℝ) / denomMax (235 / 64 : ℝ) (147 / 40 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel24 : (263070247422330 / 18446744073709551616 : ℝ) ≤
    8 * (18997 / 10000000 : ℝ) * ∫ s in (147 / 40 : ℝ)..(1177 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (147 / 40 : ℝ)) (b := (1177 / 320 : ℝ))
    (l := (9081442324939704170 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (18997 / 10000000 : ℝ))
  have hp : (263070247422330 / 18446744073709551616 : ℝ) ≤ 8 * (18997 / 10000000 : ℝ) *
      (((1177 / 320 : ℝ) - (147 / 40 : ℝ)) * (9081442324939704170 / 18446744073709551616 : ℝ) / denomMax (147 / 40 : ℝ) (1177 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel25 : (261028407020458 / 18446744073709551616 : ℝ) ≤
    8 * (18997 / 10000000 : ℝ) * ∫ s in (1177 / 320 : ℝ)..(589 / 160 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1177 / 320 : ℝ)) (b := (589 / 160 : ℝ))
    (l := (9009097028697790199 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (18997 / 10000000 : ℝ))
  have hp : (261028407020458 / 18446744073709551616 : ℝ) ≤ 8 * (18997 / 10000000 : ℝ) *
      (((589 / 160 : ℝ) - (1177 / 320 : ℝ)) * (9009097028697790199 / 18446744073709551616 : ℝ) / denomMax (1177 / 320 : ℝ) (589 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel26 : (258981928238095 / 18446744073709551616 : ℝ) ≤
    8 * (18997 / 10000000 : ℝ) * ∫ s in (589 / 160 : ℝ)..(1179 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (589 / 160 : ℝ)) (b := (1179 / 320 : ℝ))
    (l := (8936604707705965764 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (18997 / 10000000 : ℝ))
  have hp : (258981928238095 / 18446744073709551616 : ℝ) ≤ 8 * (18997 / 10000000 : ℝ) *
      (((1179 / 320 : ℝ) - (589 / 160 : ℝ)) * (8936604707705965764 / 18446744073709551616 : ℝ) / denomMax (589 / 160 : ℝ) (1179 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel27 : (256930779250397 / 18446744073709551616 : ℝ) ≤
    8 * (18997 / 10000000 : ℝ) * ∫ s in (1179 / 320 : ℝ)..(59 / 16 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1179 / 320 : ℝ)) (b := (59 / 16 : ℝ))
    (l := (8863964744520647603 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (18997 / 10000000 : ℝ))
  have hp : (256930779250397 / 18446744073709551616 : ℝ) ≤ 8 * (18997 / 10000000 : ℝ) *
      (((59 / 16 : ℝ) - (1179 / 320 : ℝ)) * (8863964744520647603 / 18446744073709551616 : ℝ) / denomMax (1179 / 320 : ℝ) (59 / 16 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel28 : (254874928039540 / 18446744073709551616 : ℝ) ≤
    8 * (18997 / 10000000 : ℝ) * ∫ s in (59 / 16 : ℝ)..(1181 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (59 / 16 : ℝ)) (b := (1181 / 320 : ℝ))
    (l := (8791176517697145420 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (18997 / 10000000 : ℝ))
  have hp : (254874928039540 / 18446744073709551616 : ℝ) ≤ 8 * (18997 / 10000000 : ℝ) *
      (((1181 / 320 : ℝ) - (59 / 16 : ℝ)) * (8791176517697145420 / 18446744073709551616 : ℝ) / denomMax (59 / 16 : ℝ) (1181 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel29 : (252814342392915 / 18446744073709551616 : ℝ) ≤
    8 * (18997 / 10000000 : ℝ) * ∫ s in (1181 / 320 : ℝ)..(591 / 160 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1181 / 320 : ℝ)) (b := (591 / 160 : ℝ))
    (l := (8718239401754273650 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (18997 / 10000000 : ℝ))
  have hp : (252814342392915 / 18446744073709551616 : ℝ) ≤ 8 * (18997 / 10000000 : ℝ) *
      (((591 / 160 : ℝ) - (1181 / 320 : ℝ)) * (8718239401754273650 / 18446744073709551616 : ℝ) / denomMax (1181 / 320 : ℝ) (591 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel30 : (250748989901301 / 18446744073709551616 : ℝ) ≤
    8 * (18997 / 10000000 : ℝ) * ∫ s in (591 / 160 : ℝ)..(1183 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (591 / 160 : ℝ)) (b := (1183 / 320 : ℝ))
    (l := (8645152767138564592 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (18997 / 10000000 : ℝ))
  have hp : (250748989901301 / 18446744073709551616 : ℝ) ≤ 8 * (18997 / 10000000 : ℝ) *
      (((1183 / 320 : ℝ) - (591 / 160 : ℝ)) * (8645152767138564592 / 18446744073709551616 : ℝ) / denomMax (591 / 160 : ℝ) (1183 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel31 : (248678837957028 / 18446744073709551616 : ℝ) ≤
    8 * (18997 / 10000000 : ℝ) * ∫ s in (1183 / 320 : ℝ)..(37 / 10 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1183 / 320 : ℝ)) (b := (37 / 10 : ℝ))
    (l := (8571915980188077456 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (18997 / 10000000 : ℝ))
  have hp : (248678837957028 / 18446744073709551616 : ℝ) ≤ 8 * (18997 / 10000000 : ℝ) *
      (((37 / 10 : ℝ) - (1183 / 320 : ℝ)) * (8571915980188077456 / 18446744073709551616 : ℝ) / denomMax (1183 / 320 : ℝ) (37 / 10 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

theorem lower : (8961847109587736 / 18446744073709551616 : ℝ) ≤
    8 * (18997 / 10000000 : ℝ) * ∫ s in (18 / 5 : ℝ)..(37 / 10 : ℝ), density s := by
  have he := integral_grid_sum (18 / 5 : ℝ) (37 / 10 : ℝ) 32 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [endpoint, alpha, beta])
  norm_num [Finset.sum_range_succ] at he
  linarith only [panel00, panel01, panel02, panel03, panel04, panel05, panel06, panel07, panel08, panel09, panel10, panel11, panel12, panel13, panel14, panel15, panel16, panel17, panel18, panel19, panel20, panel21, panel22, panel23, panel24, panel25, panel26, panel27, panel28, panel29, panel30, panel31, he]

end Wu18938Campaign.M3.Confirmed.TableRow17
