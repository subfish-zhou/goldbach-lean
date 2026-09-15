import Wu18938Campaign.M3.Confirmed.TableBounds

noncomputable section
namespace Wu18938Campaign.M3.Confirmed.TableRow16
open Real Set MeasureTheory QuarterTrim
open WuSource.SrcSixthGain Wu18938Campaign.M3.Confirmed.TableBounds

private theorem panel00 : (466663367140250 / 18446744073709551616 : ℝ) ≤
    8 * (23901 / 10000000 : ℝ) * ∫ s in (7 / 2 : ℝ)..(1121 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (7 / 2 : ℝ)) (b := (1121 / 320 : ℝ))
    (l := (12915531770629710843 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (23901 / 10000000 : ℝ))
  have hp : (466663367140250 / 18446744073709551616 : ℝ) ≤ 8 * (23901 / 10000000 : ℝ) *
      (((1121 / 320 : ℝ) - (7 / 2 : ℝ)) * (12915531770629710843 / 18446744073709551616 : ℝ) / denomMax (7 / 2 : ℝ) (1121 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel01 : (464363906085239 / 18446744073709551616 : ℝ) ≤
    8 * (23901 / 10000000 : ℝ) * ∫ s in (1121 / 320 : ℝ)..(561 / 160 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1121 / 320 : ℝ)) (b := (561 / 160 : ℝ))
    (l := (12850543683945064584 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (23901 / 10000000 : ℝ))
  have hp : (464363906085239 / 18446744073709551616 : ℝ) ≤ 8 * (23901 / 10000000 : ℝ) *
      (((561 / 160 : ℝ) - (1121 / 320 : ℝ)) * (12850543683945064584 / 18446744073709551616 : ℝ) / denomMax (1121 / 320 : ℝ) (561 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel02 : (462060524651825 / 18446744073709551616 : ℝ) ≤
    8 * (23901 / 10000000 : ℝ) * ∫ s in (561 / 160 : ℝ)..(1123 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (561 / 160 : ℝ)) (b := (1123 / 320 : ℝ))
    (l := (12785437699742904708 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (23901 / 10000000 : ℝ))
  have hp : (462060524651825 / 18446744073709551616 : ℝ) ≤ 8 * (23901 / 10000000 : ℝ) *
      (((1123 / 320 : ℝ) - (561 / 160 : ℝ)) * (12785437699742904708 / 18446744073709551616 : ℝ) / denomMax (561 / 160 : ℝ) (1123 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel03 : (459753193391215 / 18446744073709551616 : ℝ) ≤
    8 * (23901 / 10000000 : ℝ) * ∫ s in (1123 / 320 : ℝ)..(281 / 80 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1123 / 320 : ℝ)) (b := (281 / 80 : ℝ))
    (l := (12720213378379646477 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (23901 / 10000000 : ℝ))
  have hp : (459753193391215 / 18446744073709551616 : ℝ) ≤ 8 * (23901 / 10000000 : ℝ) *
      (((281 / 80 : ℝ) - (1123 / 320 : ℝ)) * (12720213378379646477 / 18446744073709551616 : ℝ) / denomMax (1123 / 320 : ℝ) (281 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel04 : (457441882708664 / 18446744073709551616 : ℝ) ≤
    8 * (23901 / 10000000 : ℝ) * ∫ s in (281 / 80 : ℝ)..(225 / 64 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (281 / 80 : ℝ)) (b := (225 / 64 : ℝ))
    (l := (12654870277691983348 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (23901 / 10000000 : ℝ))
  have hp : (457441882708664 / 18446744073709551616 : ℝ) ≤ 8 * (23901 / 10000000 : ℝ) *
      (((225 / 64 : ℝ) - (281 / 80 : ℝ)) * (12654870277691983348 / 18446744073709551616 : ℝ) / denomMax (281 / 80 : ℝ) (225 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel05 : (455126562862154 / 18446744073709551616 : ℝ) ≤
    8 * (23901 / 10000000 : ℝ) * ∫ s in (225 / 64 : ℝ)..(563 / 160 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (225 / 64 : ℝ)) (b := (563 / 160 : ℝ))
    (l := (12589407952977227889 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (23901 / 10000000 : ℝ))
  have hp : (455126562862154 / 18446744073709551616 : ℝ) ≤ 8 * (23901 / 10000000 : ℝ) *
      (((563 / 160 : ℝ) - (225 / 64 : ℝ)) * (12589407952977227889 / 18446744073709551616 : ℝ) / denomMax (225 / 64 : ℝ) (563 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel06 : (452807203961067 / 18446744073709551616 : ℝ) ≤
    8 * (23901 / 10000000 : ℝ) * ∫ s in (563 / 160 : ℝ)..(1127 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (563 / 160 : ℝ)) (b := (1127 / 320 : ℝ))
    (l := (12523825956973457632 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (23901 / 10000000 : ℝ))
  have hp : (452807203961067 / 18446744073709551616 : ℝ) ≤ 8 * (23901 / 10000000 : ℝ) *
      (((1127 / 320 : ℝ) - (563 / 160 : ℝ)) * (12523825956973457632 / 18446744073709551616 : ℝ) / denomMax (563 / 160 : ℝ) (1127 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel07 : (450483775964846 / 18446744073709551616 : ℝ) ≤
    8 * (23901 / 10000000 : ℝ) * ∫ s in (1127 / 320 : ℝ)..(141 / 40 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1127 / 320 : ℝ)) (b := (141 / 40 : ℝ))
    (l := (12458123839839463519 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (23901 / 10000000 : ℝ))
  have hp : (450483775964846 / 18446744073709551616 : ℝ) ≤ 8 * (23901 / 10000000 : ℝ) *
      (((141 / 40 : ℝ) - (1127 / 320 : ℝ)) * (12458123839839463519 / 18446744073709551616 : ℝ) / denomMax (1127 / 320 : ℝ) (141 / 40 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel08 : (448156248681638 / 18446744073709551616 : ℝ) ≤
    8 * (23901 / 10000000 : ℝ) * ∫ s in (141 / 40 : ℝ)..(1129 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (141 / 40 : ℝ)) (b := (1129 / 320 : ℝ))
    (l := (12392301149134498551 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (23901 / 10000000 : ℝ))
  have hp : (448156248681638 / 18446744073709551616 : ℝ) ≤ 8 * (23901 / 10000000 : ℝ) *
      (((1129 / 320 : ℝ) - (141 / 40 : ℝ)) * (12392301149134498551 / 18446744073709551616 : ℝ) / denomMax (141 / 40 : ℝ) (1129 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel09 : (445824591766931 / 18446744073709551616 : ℝ) ≤
    8 * (23901 / 10000000 : ℝ) * ∫ s in (1129 / 320 : ℝ)..(113 / 32 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1129 / 320 : ℝ)) (b := (113 / 32 : ℝ))
    (l := (12326357429797824214 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (23901 / 10000000 : ℝ))
  have hp : (445824591766931 / 18446744073709551616 : ℝ) ≤ 8 * (23901 / 10000000 : ℝ) *
      (((113 / 32 : ℝ) - (1129 / 320 : ℝ)) * (12326357429797824214 / 18446744073709551616 : ℝ) / denomMax (1129 / 320 : ℝ) (113 / 32 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel10 : (443488774722179 / 18446744073709551616 : ℝ) ≤
    8 * (23901 / 10000000 : ℝ) * ∫ s in (113 / 32 : ℝ)..(1131 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (113 / 32 : ℝ)) (b := (1131 / 320 : ℝ))
    (l := (12260292224128052230 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (23901 / 10000000 : ℝ))
  have hp : (443488774722179 / 18446744073709551616 : ℝ) ≤ 8 * (23901 / 10000000 : ℝ) *
      (((1131 / 320 : ℝ) - (113 / 32 : ℝ)) * (12260292224128052230 / 18446744073709551616 : ℝ) / denomMax (113 / 32 : ℝ) (1131 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel11 : (441148766893406 / 18446744073709551616 : ℝ) ≤
    8 * (23901 / 10000000 : ℝ) * ∫ s in (1131 / 320 : ℝ)..(283 / 80 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1131 / 320 : ℝ)) (b := (283 / 80 : ℝ))
    (l := (12194105071762279132 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (23901 / 10000000 : ℝ))
  have hp : (441148766893406 / 18446744073709551616 : ℝ) ≤ 8 * (23901 / 10000000 : ℝ) *
      (((283 / 80 : ℝ) - (1131 / 320 : ℝ)) * (12194105071762279132 / 18446744073709551616 : ℝ) / denomMax (1131 / 320 : ℝ) (283 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel12 : (438804537469808 / 18446744073709551616 : ℝ) ≤
    8 * (23901 / 10000000 : ℝ) * ∫ s in (283 / 80 : ℝ)..(1133 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (283 / 80 : ℝ)) (b := (1133 / 320 : ℝ))
    (l := (12127795509655011147 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (23901 / 10000000 : ℝ))
  have hp : (438804537469808 / 18446744073709551616 : ℝ) ≤ 8 * (23901 / 10000000 : ℝ) *
      (((1133 / 320 : ℝ) - (283 / 80 : ℝ)) * (12127795509655011147 / 18446744073709551616 : ℝ) / denomMax (283 / 80 : ℝ) (1133 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel13 : (436456055482334 / 18446744073709551616 : ℝ) ≤
    8 * (23901 / 10000000 : ℝ) * ∫ s in (1133 / 320 : ℝ)..(567 / 160 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1133 / 320 : ℝ)) (b := (567 / 160 : ℝ))
    (l := (12061363072056876809 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (23901 / 10000000 : ℝ))
  have hp : (436456055482334 / 18446744073709551616 : ℝ) ≤ 8 * (23901 / 10000000 : ℝ) *
      (((567 / 160 : ℝ) - (1133 / 320 : ℝ)) * (12061363072056876809 / 18446744073709551616 : ℝ) / denomMax (1133 / 320 : ℝ) (567 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel14 : (434103289802260 / 18446744073709551616 : ℝ) ≤
    8 * (23901 / 10000000 : ℝ) * ∫ s in (567 / 160 : ℝ)..(227 / 64 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (567 / 160 : ℝ)) (b := (227 / 64 : ℝ))
    (l := (11994807290493124717 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (23901 / 10000000 : ℝ))
  have hp : (434103289802260 / 18446744073709551616 : ℝ) ≤ 8 * (23901 / 10000000 : ℝ) *
      (((227 / 64 : ℝ) - (567 / 160 : ℝ)) * (11994807290493124717 / 18446744073709551616 : ℝ) / denomMax (567 / 160 : ℝ) (227 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel15 : (431746209139744 / 18446744073709551616 : ℝ) ≤
    8 * (23901 / 10000000 : ℝ) * ∫ s in (227 / 64 : ℝ)..(71 / 20 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (227 / 64 : ℝ)) (b := (71 / 20 : ℝ))
    (l := (11928127693741903779 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (23901 / 10000000 : ℝ))
  have hp : (431746209139744 / 18446744073709551616 : ℝ) ≤ 8 * (23901 / 10000000 : ℝ) *
      (((71 / 20 : ℝ) - (227 / 64 : ℝ)) * (11928127693741903779 / 18446744073709551616 : ℝ) / denomMax (227 / 64 : ℝ) (71 / 20 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel16 : (429384782042371 / 18446744073709551616 : ℝ) ≤
    8 * (23901 / 10000000 : ℝ) * ∫ s in (71 / 20 : ℝ)..(1137 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (71 / 20 : ℝ)) (b := (1137 / 320 : ℝ))
    (l := (11861323807812323279 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (23901 / 10000000 : ℝ))
  have hp : (429384782042371 / 18446744073709551616 : ℝ) ≤ 8 * (23901 / 10000000 : ℝ) *
      (((1137 / 320 : ℝ) - (71 / 20 : ℝ)) * (11861323807812323279 / 18446744073709551616 : ℝ) / denomMax (71 / 20 : ℝ) (1137 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel17 : (427018976893685 / 18446744073709551616 : ℝ) ≤
    8 * (23901 / 10000000 : ℝ) * ∫ s in (1137 / 320 : ℝ)..(569 / 160 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1137 / 320 : ℝ)) (b := (569 / 160 : ℝ))
    (l := (11794395155922290049 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (23901 / 10000000 : ℝ))
  have hp : (427018976893685 / 18446744073709551616 : ℝ) ≤ 8 * (23901 / 10000000 : ℝ) *
      (((569 / 160 : ℝ) - (1137 / 320 : ℝ)) * (11794395155922290049 / 18446744073709551616 : ℝ) / denomMax (1137 / 320 : ℝ) (569 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel18 : (424648761911707 / 18446744073709551616 : ℝ) ≤
    8 * (23901 / 10000000 : ℝ) * ∫ s in (569 / 160 : ℝ)..(1139 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (569 / 160 : ℝ)) (b := (1139 / 320 : ℝ))
    (l := (11727341258476119981 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (23901 / 10000000 : ℝ))
  have hp : (424648761911707 / 18446744073709551616 : ℝ) ≤ 8 * (23901 / 10000000 : ℝ) *
      (((1139 / 320 : ℝ) - (569 / 160 : ℝ)) * (11727341258476119981 / 18446744073709551616 : ℝ) / denomMax (569 / 160 : ℝ) (1139 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel19 : (422274105147434 / 18446744073709551616 : ℝ) ≤
    8 * (23901 / 10000000 : ℝ) * ∫ s in (1139 / 320 : ℝ)..(57 / 16 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1139 / 320 : ℝ)) (b := (57 / 16 : ℝ))
    (l := (11660161633041921095 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (23901 / 10000000 : ℝ))
  have hp : (422274105147434 / 18446744073709551616 : ℝ) ≤ 8 * (23901 / 10000000 : ℝ) *
      (((57 / 16 : ℝ) - (1139 / 320 : ℝ)) * (11660161633041921095 / 18446744073709551616 : ℝ) / denomMax (1139 / 320 : ℝ) (57 / 16 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel20 : (419894974483335 / 18446744073709551616 : ℝ) ≤
    8 * (23901 / 10000000 : ℝ) * ∫ s in (57 / 16 : ℝ)..(1141 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (57 / 16 : ℝ)) (b := (1141 / 320 : ℝ))
    (l := (11592855794328745320 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (23901 / 10000000 : ℝ))
  have hp : (419894974483335 / 18446744073709551616 : ℝ) ≤ 8 * (23901 / 10000000 : ℝ) *
      (((1141 / 320 : ℝ) - (57 / 16 : ℝ)) * (11592855794328745320 / 18446744073709551616 : ℝ) / denomMax (57 / 16 : ℝ) (1141 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel21 : (417511337631818 / 18446744073709551616 : ℝ) ≤
    8 * (23901 / 10000000 : ℝ) * ∫ s in (1141 / 320 : ℝ)..(571 / 160 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1141 / 320 : ℝ)) (b := (571 / 160 : ℝ))
    (l := (11525423254163506105 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (23901 / 10000000 : ℝ))
  have hp : (417511337631818 / 18446744073709551616 : ℝ) ≤ 8 * (23901 / 10000000 : ℝ) *
      (((571 / 160 : ℝ) - (1141 / 320 : ℝ)) * (11525423254163506105 / 18446744073709551616 : ℝ) / denomMax (1141 / 320 : ℝ) (571 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel22 : (415123162133699 / 18446744073709551616 : ℝ) ≤
    8 * (23901 / 10000000 : ℝ) * ∫ s in (571 / 160 : ℝ)..(1143 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (571 / 160 : ℝ)) (b := (1143 / 320 : ℝ))
    (l := (11457863521467658946 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (23901 / 10000000 : ℝ))
  have hp : (415123162133699 / 18446744073709551616 : ℝ) ≤ 8 * (23901 / 10000000 : ℝ) *
      (((1143 / 320 : ℝ) - (571 / 160 : ℝ)) * (11457863521467658946 / 18446744073709551616 : ℝ) / denomMax (571 / 160 : ℝ) (1143 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel23 : (412730415356641 / 18446744073709551616 : ℝ) ≤
    8 * (23901 / 10000000 : ℝ) * ∫ s in (1143 / 320 : ℝ)..(143 / 40 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1143 / 320 : ℝ)) (b := (143 / 40 : ℝ))
    (l := (11390176102233641867 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (23901 / 10000000 : ℝ))
  have hp : (412730415356641 / 18446744073709551616 : ℝ) ≤ 8 * (23901 / 10000000 : ℝ) *
      (((143 / 40 : ℝ) - (1143 / 320 : ℝ)) * (11390176102233641867 / 18446744073709551616 : ℝ) / denomMax (1143 / 320 : ℝ) (143 / 40 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel24 : (410333064493588 / 18446744073709551616 : ℝ) ≤
    8 * (23901 / 10000000 : ℝ) * ∫ s in (143 / 40 : ℝ)..(229 / 64 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (143 / 40 : ℝ)) (b := (229 / 64 : ℝ))
    (l := (11322360499501072842 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (23901 / 10000000 : ℝ))
  have hp : (410333064493588 / 18446744073709551616 : ℝ) ≤ 8 * (23901 / 10000000 : ℝ) *
      (((229 / 64 : ℝ) - (143 / 40 : ℝ)) * (11322360499501072842 / 18446744073709551616 : ℝ) / denomMax (143 / 40 : ℝ) (229 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel25 : (407931076561184 / 18446744073709551616 : ℝ) ≤
    8 * (23901 / 10000000 : ℝ) * ∫ s in (229 / 64 : ℝ)..(573 / 160 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (229 / 64 : ℝ)) (b := (573 / 160 : ℝ))
    (l := (11254416213332701099 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (23901 / 10000000 : ℝ))
  have hp : (407931076561184 / 18446744073709551616 : ℝ) ≤ 8 * (23901 / 10000000 : ℝ) *
      (((573 / 160 : ℝ) - (229 / 64 : ℝ)) * (11254416213332701099 / 18446744073709551616 : ℝ) / denomMax (229 / 64 : ℝ) (573 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel26 : (405524418398170 / 18446744073709551616 : ℝ) ≤
    8 * (23901 / 10000000 : ℝ) * ∫ s in (573 / 160 : ℝ)..(1147 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (573 / 160 : ℝ)) (b := (1147 / 320 : ℝ))
    (l := (11186342740790109234 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (23901 / 10000000 : ℝ))
  have hp : (405524418398170 / 18446744073709551616 : ℝ) ≤ 8 * (23901 / 10000000 : ℝ) *
      (((1147 / 320 : ℝ) - (573 / 160 : ℝ)) * (11186342740790109234 / 18446744073709551616 : ℝ) / denomMax (573 / 160 : ℝ) (1147 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel27 : (403113056663770 / 18446744073709551616 : ℝ) ≤
    8 * (23901 / 10000000 : ℝ) * ∫ s in (1147 / 320 : ℝ)..(287 / 80 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1147 / 320 : ℝ)) (b := (287 / 80 : ℝ))
    (l := (11118139575909162956 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (23901 / 10000000 : ℝ))
  have hp : (403113056663770 / 18446744073709551616 : ℝ) ≤ 8 * (23901 / 10000000 : ℝ) *
      (((287 / 80 : ℝ) - (1147 / 320 : ℝ)) * (11118139575909162956 / 18446744073709551616 : ℝ) / denomMax (1147 / 320 : ℝ) (287 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel28 : (400696957836065 / 18446744073709551616 : ℝ) ≤
    8 * (23901 / 10000000 : ℝ) * ∫ s in (287 / 80 : ℝ)..(1149 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (287 / 80 : ℝ)) (b := (1149 / 320 : ℝ))
    (l := (11049806209675205310 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (23901 / 10000000 : ℝ))
  have hp : (400696957836065 / 18446744073709551616 : ℝ) ≤ 8 * (23901 / 10000000 : ℝ) *
      (((1149 / 320 : ℝ) - (287 / 80 : ℝ)) * (11049806209675205310 / 18446744073709551616 : ℝ) / denomMax (287 / 80 : ℝ) (1149 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel29 : (398276088210344 / 18446744073709551616 : ℝ) ≤
    8 * (23901 / 10000000 : ℝ) * ∫ s in (1149 / 320 : ℝ)..(115 / 32 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1149 / 320 : ℝ)) (b := (115 / 32 : ℝ))
    (l := (10981342129997992111 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (23901 / 10000000 : ℝ))
  have hp : (398276088210344 / 18446744073709551616 : ℝ) ≤ 8 * (23901 / 10000000 : ℝ) *
      (((115 / 32 : ℝ) - (1149 / 320 : ℝ)) * (10981342129997992111 / 18446744073709551616 : ℝ) / denomMax (1149 / 320 : ℝ) (115 / 32 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel30 : (395850413897445 / 18446744073709551616 : ℝ) ≤
    8 * (23901 / 10000000 : ℝ) * ∫ s in (115 / 32 : ℝ)..(1151 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (115 / 32 : ℝ)) (b := (1151 / 320 : ℝ))
    (l := (10912746821686365316 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (23901 / 10000000 : ℝ))
  have hp : (395850413897445 / 18446744073709551616 : ℝ) ≤ 8 * (23901 / 10000000 : ℝ) *
      (((1151 / 320 : ℝ) - (115 / 32 : ℝ)) * (10912746821686365316 / 18446744073709551616 : ℝ) / denomMax (115 / 32 : ℝ) (1151 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel31 : (393419900822076 / 18446744073709551616 : ℝ) ≤
    8 * (23901 / 10000000 : ℝ) * ∫ s in (1151 / 320 : ℝ)..(18 / 5 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1151 / 320 : ℝ)) (b := (18 / 5 : ℝ))
    (l := (10844019766422661004 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (23901 / 10000000 : ℝ))
  have hp : (393419900822076 / 18446744073709551616 : ℝ) ≤ 8 * (23901 / 10000000 : ℝ) *
      (((18 / 5 : ℝ) - (1151 / 320 : ℝ)) * (10844019766422661004 / 18446744073709551616 : ℝ) / denomMax (1151 / 320 : ℝ) (18 / 5 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

theorem lower : (13772160383206892 / 18446744073709551616 : ℝ) ≤
    8 * (23901 / 10000000 : ℝ) * ∫ s in (7 / 2 : ℝ)..(18 / 5 : ℝ), density s := by
  have he := integral_grid_sum (7 / 2 : ℝ) (18 / 5 : ℝ) 32 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [endpoint, alpha, beta])
  norm_num [Finset.sum_range_succ] at he
  linarith only [panel00, panel01, panel02, panel03, panel04, panel05, panel06, panel07, panel08, panel09, panel10, panel11, panel12, panel13, panel14, panel15, panel16, panel17, panel18, panel19, panel20, panel21, panel22, panel23, panel24, panel25, panel26, panel27, panel28, panel29, panel30, panel31, he]

end Wu18938Campaign.M3.Confirmed.TableRow16
