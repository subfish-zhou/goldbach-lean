import Wu18938Campaign.M3.Confirmed.TableBounds

noncomputable section
namespace Wu18938Campaign.M3.Confirmed.TableRow06
open Real Set MeasureTheory QuarterTrim
open WuSource.SrcSixthGain Wu18938Campaign.M3.Confirmed.TableBounds

private theorem panel00 : (2320958147819702 / 18446744073709551616 : ℝ) ≤
    8 * (113556 / 10000000 : ℝ) * ∫ s in (13 / 5 : ℝ)..(833 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (13 / 5 : ℝ)) (b := (833 / 320 : ℝ))
    (l := (12932377387042491121 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (113556 / 10000000 : ℝ))
  have hp : (2320958147819702 / 18446744073709551616 : ℝ) ≤ 8 * (113556 / 10000000 : ℝ) *
      (((833 / 320 : ℝ) - (13 / 5 : ℝ)) * (12932377387042491121 / 18446744073709551616 : ℝ) / denomMax (13 / 5 : ℝ) (833 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel01 : (2320832243162426 / 18446744073709551616 : ℝ) ≤
    8 * (113556 / 10000000 : ℝ) * ∫ s in (833 / 320 : ℝ)..(417 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (833 / 320 : ℝ)) (b := (417 / 160 : ℝ))
    (l := (12937165033692550565 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (113556 / 10000000 : ℝ))
  have hp : (2320832243162426 / 18446744073709551616 : ℝ) ≤ 8 * (113556 / 10000000 : ℝ) *
      (((417 / 160 : ℝ) - (833 / 320 : ℝ)) * (12937165033692550565 / 18446744073709551616 : ℝ) / denomMax (833 / 320 : ℝ) (417 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel02 : (2320712755438196 / 18446744073709551616 : ℝ) ≤
    8 * (113556 / 10000000 : ℝ) * ∫ s in (417 / 160 : ℝ)..(167 / 64 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (417 / 160 : ℝ)) (b := (167 / 64 : ℝ))
    (l := (12941963806680276849 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (113556 / 10000000 : ℝ))
  have hp : (2320712755438196 / 18446744073709551616 : ℝ) ≤ 8 * (113556 / 10000000 : ℝ) *
      (((167 / 64 : ℝ) - (417 / 160 : ℝ)) * (12941963806680276849 / 18446744073709551616 : ℝ) / denomMax (417 / 160 : ℝ) (167 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel03 : (2320599682844743 / 18446744073709551616 : ℝ) ≤
    8 * (113556 / 10000000 : ℝ) * ∫ s in (167 / 64 : ℝ)..(209 / 80 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (167 / 64 : ℝ)) (b := (209 / 80 : ℝ))
    (l := (12946773744999613542 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (113556 / 10000000 : ℝ))
  have hp : (2320599682844743 / 18446744073709551616 : ℝ) ≤ 8 * (113556 / 10000000 : ℝ) *
      (((209 / 80 : ℝ) - (167 / 64 : ℝ)) * (12946773744999613542 / 18446744073709551616 : ℝ) / denomMax (167 / 64 : ℝ) (209 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel04 : (2320493023687157 / 18446744073709551616 : ℝ) ≤
    8 * (113556 / 10000000 : ℝ) * ∫ s in (209 / 80 : ℝ)..(837 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (209 / 80 : ℝ)) (b := (837 / 320 : ℝ))
    (l := (12951594887827688666 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (113556 / 10000000 : ℝ))
  have hp : (2320493023687157 / 18446744073709551616 : ℝ) ≤ 8 * (113556 / 10000000 : ℝ) *
      (((837 / 320 : ℝ) - (209 / 80 : ℝ)) * (12951594887827688666 / 18446744073709551616 : ℝ) / denomMax (209 / 80 : ℝ) (837 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel05 : (2320392776377832 / 18446744073709551616 : ℝ) ≤
    8 * (113556 / 10000000 : ℝ) * ∫ s in (837 / 320 : ℝ)..(419 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (837 / 320 : ℝ)) (b := (419 / 160 : ℝ))
    (l := (12956427274525896060 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (113556 / 10000000 : ℝ))
  have hp : (2320392776377832 / 18446744073709551616 : ℝ) ≤ 8 * (113556 / 10000000 : ℝ) *
      (((419 / 160 : ℝ) - (837 / 320 : ℝ)) * (12956427274525896060 / 18446744073709551616 : ℝ) / denomMax (837 / 320 : ℝ) (419 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel06 : (2320298939436401 / 18446744073709551616 : ℝ) ≤
    8 * (113556 / 10000000 : ℝ) * ∫ s in (419 / 160 : ℝ)..(839 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (419 / 160 : ℝ)) (b := (839 / 320 : ℝ))
    (l := (12961270944640984449 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (113556 / 10000000 : ℝ))
  have hp : (2320298939436401 / 18446744073709551616 : ℝ) ≤ 8 * (113556 / 10000000 : ℝ) *
      (((839 / 320 : ℝ) - (419 / 160 : ℝ)) * (12961270944640984449 / 18446744073709551616 : ℝ) / denomMax (419 / 160 : ℝ) (839 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel07 : (2320211511489685 / 18446744073709551616 : ℝ) ≤
    8 * (113556 / 10000000 : ℝ) * ∫ s in (839 / 320 : ℝ)..(21 / 8 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (839 / 320 : ℝ)) (b := (21 / 8 : ℝ))
    (l := (12966125937906154281 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (113556 / 10000000 : ℝ))
  have hp : (2320211511489685 / 18446744073709551616 : ℝ) ≤ 8 * (113556 / 10000000 : ℝ) *
      (((21 / 8 : ℝ) - (839 / 320 : ℝ)) * (12966125937906154281 / 18446744073709551616 : ℝ) / denomMax (839 / 320 : ℝ) (21 / 8 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel08 : (2320130491271641 / 18446744073709551616 : ℝ) ≤
    8 * (113556 / 10000000 : ℝ) * ∫ s in (21 / 8 : ℝ)..(841 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (21 / 8 : ℝ)) (b := (841 / 320 : ℝ))
    (l := (12970992294242162384 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (113556 / 10000000 : ℝ))
  have hp : (2320130491271641 / 18446744073709551616 : ℝ) ≤ 8 * (113556 / 10000000 : ℝ) *
      (((841 / 320 : ℝ) - (21 / 8 : ℝ)) * (12970992294242162384 / 18446744073709551616 : ℝ) / denomMax (21 / 8 : ℝ) (841 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel09 : (2320055877623320 / 18446744073709551616 : ℝ) ≤
    8 * (113556 / 10000000 : ℝ) * ∫ s in (841 / 320 : ℝ)..(421 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (841 / 320 : ℝ)) (b := (421 / 160 : ℝ))
    (l := (12975870053758434525 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (113556 / 10000000 : ℝ))
  have hp : (2320055877623320 / 18446744073709551616 : ℝ) ≤ 8 * (113556 / 10000000 : ℝ) *
      (((421 / 160 : ℝ) - (841 / 320 : ℝ)) * (12975870053758434525 / 18446744073709551616 : ℝ) / denomMax (841 / 320 : ℝ) (421 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel10 : (2319987669492823 / 18446744073709551616 : ℝ) ≤
    8 * (113556 / 10000000 : ℝ) * ∫ s in (421 / 160 : ℝ)..(843 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (421 / 160 : ℝ)) (b := (843 / 320 : ℝ))
    (l := (12980759256754185927 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (113556 / 10000000 : ℝ))
  have hp : (2319987669492823 / 18446744073709551616 : ℝ) ≤ 8 * (113556 / 10000000 : ℝ) *
      (((843 / 320 : ℝ) - (421 / 160 : ℝ)) * (12980759256754185927 / 18446744073709551616 : ℝ) / denomMax (421 / 160 : ℝ) (843 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel11 : (2319925865935268 / 18446744073709551616 : ℝ) ≤
    8 * (113556 / 10000000 : ℝ) * ∫ s in (843 / 320 : ℝ)..(211 / 80 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (843 / 320 : ℝ)) (b := (211 / 80 : ℝ))
    (l := (12985659943719549814 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (113556 / 10000000 : ℝ))
  have hp : (2319925865935268 / 18446744073709551616 : ℝ) ≤ 8 * (113556 / 10000000 : ℝ) *
      (((211 / 80 : ℝ) - (843 / 320 : ℝ)) * (12985659943719549814 / 18446744073709551616 : ℝ) / denomMax (843 / 320 : ℝ) (211 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel12 : (2319870466112756 / 18446744073709551616 : ℝ) ≤
    8 * (113556 / 10000000 : ℝ) * ∫ s in (211 / 80 : ℝ)..(169 / 64 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (211 / 80 : ℝ)) (b := (169 / 64 : ℝ))
    (l := (12990572155336714051 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (113556 / 10000000 : ℝ))
  have hp : (2319870466112756 / 18446744073709551616 : ℝ) ≤ 8 * (113556 / 10000000 : ℝ) *
      (((169 / 64 : ℝ) - (211 / 80 : ℝ)) * (12990572155336714051 / 18446744073709551616 : ℝ) / denomMax (211 / 80 : ℝ) (169 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel13 : (2319821469294346 / 18446744073709551616 : ℝ) ≤
    8 * (113556 / 10000000 : ℝ) * ∫ s in (169 / 64 : ℝ)..(423 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (169 / 64 : ℝ)) (b := (423 / 160 : ℝ))
    (l := (12995495932481065950 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (113556 / 10000000 : ℝ))
  have hp : (2319821469294346 / 18446744073709551616 : ℝ) ≤ 8 * (113556 / 10000000 : ℝ) *
      (((423 / 160 : ℝ) - (169 / 64 : ℝ)) * (12995495932481065950 / 18446744073709551616 : ℝ) / denomMax (169 / 64 : ℝ) (423 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel14 : (2319778874856029 / 18446744073709551616 : ℝ) ≤
    8 * (113556 / 10000000 : ℝ) * ∫ s in (423 / 160 : ℝ)..(847 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (423 / 160 : ℝ)) (b := (847 / 320 : ℝ))
    (l := (13000431316222345301 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (113556 / 10000000 : ℝ))
  have hp : (2319778874856029 / 18446744073709551616 : ℝ) ≤ 8 * (113556 / 10000000 : ℝ) *
      (((847 / 320 : ℝ) - (423 / 160 : ℝ)) * (13000431316222345301 / 18446744073709551616 : ℝ) / denomMax (423 / 160 : ℝ) (847 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel15 : (2319742682280714 / 18446744073709551616 : ℝ) ≤
    8 * (113556 / 10000000 : ℝ) * ∫ s in (847 / 320 : ℝ)..(53 / 20 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (847 / 320 : ℝ)) (b := (53 / 20 : ℝ))
    (l := (13005378347825805713 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (113556 / 10000000 : ℝ))
  have hp : (2319742682280714 / 18446744073709551616 : ℝ) ≤ 8 * (113556 / 10000000 : ℝ) *
      (((53 / 20 : ℝ) - (847 / 320 : ℝ)) * (13005378347825805713 / 18446744073709551616 : ℝ) / denomMax (847 / 320 : ℝ) (53 / 20 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel16 : (2319712891158213 / 18446744073709551616 : ℝ) ≤
    8 * (113556 / 10000000 : ℝ) * ∫ s in (53 / 20 : ℝ)..(849 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (53 / 20 : ℝ)) (b := (849 / 320 : ℝ))
    (l := (13010337068753384324 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (113556 / 10000000 : ℝ))
  have hp : (2319712891158213 / 18446744073709551616 : ℝ) ≤ 8 * (113556 / 10000000 : ℝ) *
      (((849 / 320 : ℝ) - (53 / 20 : ℝ)) * (13010337068753384324 / 18446744073709551616 : ℝ) / denomMax (53 / 20 : ℝ) (849 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel17 : (2319689501185230 / 18446744073709551616 : ℝ) ≤
    8 * (113556 / 10000000 : ℝ) * ∫ s in (849 / 320 : ℝ)..(85 / 32 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (849 / 320 : ℝ)) (b := (85 / 32 : ℝ))
    (l := (13015307520664879945 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (113556 / 10000000 : ℝ))
  have hp : (2319689501185230 / 18446744073709551616 : ℝ) ≤ 8 * (113556 / 10000000 : ℝ) *
      (((85 / 32 : ℝ) - (849 / 320 : ℝ)) * (13015307520664879945 / 18446744073709551616 : ℝ) / denomMax (849 / 320 : ℝ) (85 / 32 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel18 : (2319672512165358 / 18446744073709551616 : ℝ) ≤
    8 * (113556 / 10000000 : ℝ) * ∫ s in (85 / 32 : ℝ)..(851 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (85 / 32 : ℝ)) (b := (851 / 320 : ℝ))
    (l := (13020289745419139731 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (113556 / 10000000 : ℝ))
  have hp : (2319672512165358 / 18446744073709551616 : ℝ) ≤ 8 * (113556 / 10000000 : ℝ) *
      (((851 / 320 : ℝ) - (85 / 32 : ℝ)) * (13020289745419139731 / 18446744073709551616 : ℝ) / denomMax (85 / 32 : ℝ) (851 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel19 : (2319661924009080 / 18446744073709551616 : ℝ) ≤
    8 * (113556 / 10000000 : ℝ) * ∫ s in (851 / 320 : ℝ)..(213 / 80 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (851 / 320 : ℝ)) (b := (213 / 80 : ℝ))
    (l := (13025283785075254431 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (113556 / 10000000 : ℝ))
  have hp : (2319661924009080 / 18446744073709551616 : ℝ) ≤ 8 * (113556 / 10000000 : ℝ) *
      (((213 / 80 : ℝ) - (851 / 320 : ℝ)) * (13025283785075254431 / 18446744073709551616 : ℝ) / denomMax (851 / 320 : ℝ) (213 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel20 : (2319657736733771 / 18446744073709551616 : ℝ) ≤
    8 * (113556 / 10000000 : ℝ) * ∫ s in (213 / 80 : ℝ)..(853 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (213 / 80 : ℝ)) (b := (853 / 320 : ℝ))
    (l := (13030289681893762292 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (113556 / 10000000 : ℝ))
  have hp : (2319657736733771 / 18446744073709551616 : ℝ) ≤ 8 * (113556 / 10000000 : ℝ) *
      (((853 / 320 : ℝ) - (213 / 80 : ℝ)) * (13030289681893762292 / 18446744073709551616 : ℝ) / denomMax (213 / 80 : ℝ) (853 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel21 : (2319659950463709 / 18446744073709551616 : ℝ) ≤
    8 * (113556 / 10000000 : ℝ) * ∫ s in (853 / 320 : ℝ)..(427 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (853 / 320 : ℝ)) (b := (427 / 160 : ℝ))
    (l := (13035307478337861708 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (113556 / 10000000 : ℝ))
  have hp : (2319659950463709 / 18446744073709551616 : ℝ) ≤ 8 * (113556 / 10000000 : ℝ) *
      (((427 / 160 : ℝ) - (853 / 320 : ℝ)) * (13035307478337861708 / 18446744073709551616 : ℝ) / denomMax (853 / 320 : ℝ) (427 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel22 : (2319668565430087 / 18446744073709551616 : ℝ) ≤
    8 * (113556 / 10000000 : ℝ) * ∫ s in (427 / 160 : ℝ)..(171 / 64 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (427 / 160 : ℝ)) (b := (171 / 64 : ℝ))
    (l := (13040337217074632661 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (113556 / 10000000 : ℝ))
  have hp : (2319668565430087 / 18446744073709551616 : ℝ) ≤ 8 * (113556 / 10000000 : ℝ) *
      (((171 / 64 : ℝ) - (427 / 160 : ℝ)) * (13040337217074632661 / 18446744073709551616 : ℝ) / denomMax (427 / 160 : ℝ) (171 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel23 : (2319683581971032 / 18446744073709551616 : ℝ) ≤
    8 * (113556 / 10000000 : ℝ) * ∫ s in (171 / 64 : ℝ)..(107 / 40 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (171 / 64 : ℝ)) (b := (107 / 40 : ℝ))
    (l := (13045378940976267056 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (113556 / 10000000 : ℝ))
  have hp : (2319683581971032 / 18446744073709551616 : ℝ) ≤ 8 * (113556 / 10000000 : ℝ) *
      (((107 / 40 : ℝ) - (171 / 64 : ℝ)) * (13045378940976267056 / 18446744073709551616 : ℝ) / denomMax (171 / 64 : ℝ) (107 / 40 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel24 : (2319705000531626 / 18446744073709551616 : ℝ) ≤
    8 * (113556 / 10000000 : ℝ) * ∫ s in (107 / 40 : ℝ)..(857 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (107 / 40 : ℝ)) (b := (857 / 320 : ℝ))
    (l := (13050432693121308007 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (113556 / 10000000 : ℝ))
  have hp : (2319705000531626 / 18446744073709551616 : ℝ) ≤ 8 * (113556 / 10000000 : ℝ) *
      (((857 / 320 : ℝ) - (107 / 40 : ℝ)) * (13050432693121308007 / 18446744073709551616 : ℝ) / denomMax (107 / 40 : ℝ) (857 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel25 : (2319732821663934 / 18446744073709551616 : ℝ) ≤
    8 * (113556 / 10000000 : ℝ) * ∫ s in (857 / 320 : ℝ)..(429 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (857 / 320 : ℝ)) (b := (429 / 160 : ℝ))
    (l := (13055498516795898155 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (113556 / 10000000 : ℝ))
  have hp : (2319732821663934 / 18446744073709551616 : ℝ) ≤ 8 * (113556 / 10000000 : ℝ) *
      (((429 / 160 : ℝ) - (857 / 320 : ℝ)) * (13055498516795898155 / 18446744073709551616 : ℝ) / denomMax (857 / 320 : ℝ) (429 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel26 : (2319767046027036 / 18446744073709551616 : ℝ) ≤
    8 * (113556 / 10000000 : ℝ) * ∫ s in (429 / 160 : ℝ)..(859 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (429 / 160 : ℝ)) (b := (859 / 320 : ℝ))
    (l := (13060576455495037104 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (113556 / 10000000 : ℝ))
  have hp : (2319767046027036 / 18446744073709551616 : ℝ) ≤ 8 * (113556 / 10000000 : ℝ) *
      (((859 / 320 : ℝ) - (429 / 160 : ℝ)) * (13060576455495037104 / 18446744073709551616 : ℝ) / denomMax (429 / 160 : ℝ) (859 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel27 : (2319807674387062 / 18446744073709551616 : ℝ) ≤
    8 * (113556 / 10000000 : ℝ) * ∫ s in (859 / 320 : ℝ)..(43 / 16 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (859 / 320 : ℝ)) (b := (43 / 16 : ℝ))
    (l := (13065666552923848039 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (113556 / 10000000 : ℝ))
  have hp : (2319807674387062 / 18446744073709551616 : ℝ) ≤ 8 * (113556 / 10000000 : ℝ) *
      (((43 / 16 : ℝ) - (859 / 320 : ℝ)) * (13065666552923848039 / 18446744073709551616 : ℝ) / denomMax (859 / 320 : ℝ) (43 / 16 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel28 : (2319854707617232 / 18446744073709551616 : ℝ) ≤
    8 * (113556 / 10000000 : ℝ) * ∫ s in (43 / 16 : ℝ)..(861 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (43 / 16 : ℝ)) (b := (861 / 320 : ℝ))
    (l := (13070768852998853618 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (113556 / 10000000 : ℝ))
  have hp : (2319854707617232 / 18446744073709551616 : ℝ) ≤ 8 * (113556 / 10000000 : ℝ) *
      (((861 / 320 : ℝ) - (43 / 16 : ℝ)) * (13070768852998853618 / 18446744073709551616 : ℝ) / denomMax (43 / 16 : ℝ) (861 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel29 : (2319908146697904 / 18446744073709551616 : ℝ) ≤
    8 * (113556 / 10000000 : ℝ) * ∫ s in (861 / 320 : ℝ)..(431 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (861 / 320 : ℝ)) (b := (431 / 160 : ℝ))
    (l := (13075883399849261205 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (113556 / 10000000 : ℝ))
  have hp : (2319908146697904 / 18446744073709551616 : ℝ) ≤ 8 * (113556 / 10000000 : ℝ) *
      (((431 / 160 : ℝ) - (861 / 320 : ℝ)) * (13075883399849261205 / 18446744073709551616 : ℝ) / denomMax (861 / 320 : ℝ) (431 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel30 : (2319967992716617 / 18446744073709551616 : ℝ) ≤
    8 * (113556 / 10000000 : ℝ) * ∫ s in (431 / 160 : ℝ)..(863 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (431 / 160 : ℝ)) (b := (863 / 320 : ℝ))
    (l := (13081010237818257535 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (113556 / 10000000 : ℝ))
  have hp : (2319967992716617 / 18446744073709551616 : ℝ) ≤ 8 * (113556 / 10000000 : ℝ) *
      (((863 / 320 : ℝ) - (431 / 160 : ℝ)) * (13081010237818257535 / 18446744073709551616 : ℝ) / denomMax (431 / 160 : ℝ) (863 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel31 : (2320034246868154 / 18446744073709551616 : ℝ) ≤
    8 * (113556 / 10000000 : ℝ) * ∫ s in (863 / 320 : ℝ)..(27 / 10 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (863 / 320 : ℝ)) (b := (27 / 10 : ℝ))
    (l := (13086149411464312889 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (113556 / 10000000 : ℝ))
  have hp : (2320034246868154 / 18446744073709551616 : ℝ) ≤ 8 * (113556 / 10000000 : ℝ) *
      (((27 / 10 : ℝ) - (863 / 320 : ℝ)) * (13086149411464312889 / 18446744073709551616 : ℝ) / denomMax (863 / 320 : ℝ) (27 / 10 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

theorem lower : (74239996776749084 / 18446744073709551616 : ℝ) ≤
    8 * (113556 / 10000000 : ℝ) * ∫ s in (13 / 5 : ℝ)..(27 / 10 : ℝ), density s := by
  have he := integral_grid_sum (13 / 5 : ℝ) (27 / 10 : ℝ) 32 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [endpoint, alpha, beta])
  norm_num [Finset.sum_range_succ] at he
  linarith only [panel00, panel01, panel02, panel03, panel04, panel05, panel06, panel07, panel08, panel09, panel10, panel11, panel12, panel13, panel14, panel15, panel16, panel17, panel18, panel19, panel20, panel21, panel22, panel23, panel24, panel25, panel26, panel27, panel28, panel29, panel30, panel31, he]

end Wu18938Campaign.M3.Confirmed.TableRow06
