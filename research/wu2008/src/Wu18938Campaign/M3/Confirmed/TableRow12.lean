import Wu18938Campaign.M3.Confirmed.TableBounds

noncomputable section
namespace Wu18938Campaign.M3.Confirmed.TableRow12
open Real Set MeasureTheory QuarterTrim
open WuSource.SrcSixthGain Wu18938Campaign.M3.Confirmed.TableBounds

private theorem panel00 : (983158602509392 / 18446744073709551616 : ℝ) ≤
    8 * (46164 / 10000000 : ℝ) * ∫ s in (16 / 5 : ℝ)..(205 / 64 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (16 / 5 : ℝ)) (b := (205 / 64 : ℝ))
    (l := (14113819646079127640 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (46164 / 10000000 : ℝ))
  have hp : (983158602509392 / 18446744073709551616 : ℝ) ≤ 8 * (46164 / 10000000 : ℝ) *
      (((205 / 64 : ℝ) - (16 / 5 : ℝ)) * (14113819646079127640 / 18446744073709551616 : ℝ) / denomMax (16 / 5 : ℝ) (205 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel01 : (983648075132924 / 18446744073709551616 : ℝ) ≤
    8 * (46164 / 10000000 : ℝ) * ∫ s in (205 / 64 : ℝ)..(513 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (205 / 64 : ℝ)) (b := (513 / 160 : ℝ))
    (l := (14121752030513173189 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (46164 / 10000000 : ℝ))
  have hp : (983648075132924 / 18446744073709551616 : ℝ) ≤ 8 * (46164 / 10000000 : ℝ) *
      (((513 / 160 : ℝ) - (205 / 64 : ℝ)) * (14121752030513173189 / 18446744073709551616 : ℝ) / denomMax (205 / 64 : ℝ) (513 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel02 : (984140893670693 / 18446744073709551616 : ℝ) ≤
    8 * (46164 / 10000000 : ℝ) * ∫ s in (513 / 160 : ℝ)..(1027 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (513 / 160 : ℝ)) (b := (1027 / 320 : ℝ))
    (l := (14129708253372222864 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (46164 / 10000000 : ℝ))
  have hp : (984140893670693 / 18446744073709551616 : ℝ) ≤ 8 * (46164 / 10000000 : ℝ) *
      (((1027 / 320 : ℝ) - (513 / 160 : ℝ)) * (14129708253372222864 / 18446744073709551616 : ℝ) / denomMax (513 / 160 : ℝ) (1027 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel03 : (984637067670322 / 18446744073709551616 : ℝ) ≤
    8 * (46164 / 10000000 : ℝ) * ∫ s in (1027 / 320 : ℝ)..(257 / 80 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (1027 / 320 : ℝ)) (b := (257 / 80 : ℝ))
    (l := (14137688423020326096 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (46164 / 10000000 : ℝ))
  have hp : (984637067670322 / 18446744073709551616 : ℝ) ≤ 8 * (46164 / 10000000 : ℝ) *
      (((257 / 80 : ℝ) - (1027 / 320 : ℝ)) * (14137688423020326096 / 18446744073709551616 : ℝ) / denomMax (1027 / 320 : ℝ) (257 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel04 : (985136606758969 / 18446744073709551616 : ℝ) ≤
    8 * (46164 / 10000000 : ℝ) * ∫ s in (257 / 80 : ℝ)..(1029 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (257 / 80 : ℝ)) (b := (1029 / 320 : ℝ))
    (l := (14145692648483791134 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (46164 / 10000000 : ℝ))
  have hp : (985136606758969 / 18446744073709551616 : ℝ) ≤ 8 * (46164 / 10000000 : ℝ) *
      (((1029 / 320 : ℝ) - (257 / 80 : ℝ)) * (14145692648483791134 / 18446744073709551616 : ℝ) / denomMax (257 / 80 : ℝ) (1029 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel05 : (985639520643827 / 18446744073709551616 : ℝ) ≤
    8 * (46164 / 10000000 : ℝ) * ∫ s in (1029 / 320 : ℝ)..(103 / 32 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (1029 / 320 : ℝ)) (b := (103 / 32 : ℝ))
    (l := (14153721039456285493 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (46164 / 10000000 : ℝ))
  have hp : (985639520643827 / 18446744073709551616 : ℝ) ≤ 8 * (46164 / 10000000 : ℝ) *
      (((103 / 32 : ℝ) - (1029 / 320 : ℝ)) * (14153721039456285493 / 18446744073709551616 : ℝ) / denomMax (1029 / 320 : ℝ) (103 / 32 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel06 : (986145819112640 / 18446744073709551616 : ℝ) ≤
    8 * (46164 / 10000000 : ℝ) * ∫ s in (103 / 32 : ℝ)..(1031 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (103 / 32 : ℝ)) (b := (1031 / 320 : ℝ))
    (l := (14161773706303983908 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (46164 / 10000000 : ℝ))
  have hp : (986145819112640 / 18446744073709551616 : ℝ) ≤ 8 * (46164 / 10000000 : ℝ) *
      (((1031 / 320 : ℝ) - (103 / 32 : ℝ)) * (14161773706303983908 / 18446744073709551616 : ℝ) / denomMax (103 / 32 : ℝ) (1031 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel07 : (986655512034204 / 18446744073709551616 : ℝ) ≤
    8 * (46164 / 10000000 : ℝ) * ∫ s in (1031 / 320 : ℝ)..(129 / 40 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (1031 / 320 : ℝ)) (b := (129 / 40 : ℝ))
    (l := (14169850760070764331 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (46164 / 10000000 : ℝ))
  have hp : (986655512034204 / 18446744073709551616 : ℝ) ≤ 8 * (46164 / 10000000 : ℝ) *
      (((129 / 40 : ℝ) - (1031 / 320 : ℝ)) * (14169850760070764331 / 18446744073709551616 : ℝ) / denomMax (1031 / 320 : ℝ) (129 / 40 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel08 : (987168609358895 / 18446744073709551616 : ℝ) ≤
    8 * (46164 / 10000000 : ℝ) * ∫ s in (129 / 40 : ℝ)..(1033 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (129 / 40 : ℝ)) (b := (1033 / 320 : ℝ))
    (l := (14177952312483452480 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (46164 / 10000000 : ℝ))
  have hp : (987168609358895 / 18446744073709551616 : ℝ) ≤ 8 * (46164 / 10000000 : ℝ) *
      (((1033 / 320 : ℝ) - (129 / 40 : ℝ)) * (14177952312483452480 / 18446744073709551616 : ℝ) / denomMax (129 / 40 : ℝ) (1033 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel09 : (987685121119188 / 18446744073709551616 : ℝ) ≤
    8 * (46164 / 10000000 : ℝ) * ∫ s in (1033 / 320 : ℝ)..(517 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (1033 / 320 : ℝ)) (b := (517 / 160 : ℝ))
    (l := (14186078475957115490 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (46164 / 10000000 : ℝ))
  have hp : (987685121119188 / 18446744073709551616 : ℝ) ≤ 8 * (46164 / 10000000 : ℝ) *
      (((517 / 160 : ℝ) - (1033 / 320 : ℝ)) * (14186078475957115490 / 18446744073709551616 : ℝ) / denomMax (1033 / 320 : ℝ) (517 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel10 : (988205057430186 / 18446744073709551616 : ℝ) ≤
    8 * (46164 / 10000000 : ℝ) * ∫ s in (517 / 160 : ℝ)..(207 / 64 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (517 / 160 : ℝ)) (b := (207 / 64 : ℝ))
    (l := (14194229363600405187 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (46164 / 10000000 : ℝ))
  have hp : (988205057430186 / 18446744073709551616 : ℝ) ≤ 8 * (46164 / 10000000 : ℝ) *
      (((207 / 64 : ℝ) - (517 / 160 : ℝ)) * (14194229363600405187 / 18446744073709551616 : ℝ) / denomMax (517 / 160 : ℝ) (207 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel11 : (988728428490154 / 18446744073709551616 : ℝ) ≤
    8 * (46164 / 10000000 : ℝ) * ∫ s in (207 / 64 : ℝ)..(259 / 80 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (207 / 64 : ℝ)) (b := (259 / 80 : ℝ))
    (l := (14202405089220951555 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (46164 / 10000000 : ℝ))
  have hp : (988728428490154 / 18446744073709551616 : ℝ) ≤ 8 * (46164 / 10000000 : ℝ) *
      (((259 / 80 : ℝ) - (207 / 64 : ℝ)) * (14202405089220951555 / 18446744073709551616 : ℝ) / denomMax (207 / 64 : ℝ) (259 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel12 : (989255244581061 / 18446744073709551616 : ℝ) ≤
    8 * (46164 / 10000000 : ℝ) * ∫ s in (259 / 80 : ℝ)..(1037 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (259 / 80 : ℝ)) (b := (1037 / 320 : ℝ))
    (l := (14210605767330806928 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (46164 / 10000000 : ℝ))
  have hp : (989255244581061 / 18446744073709551616 : ℝ) ≤ 8 * (46164 / 10000000 : ℝ) *
      (((1037 / 320 : ℝ) - (259 / 80 : ℝ)) * (14210605767330806928 / 18446744073709551616 : ℝ) / denomMax (259 / 80 : ℝ) (1037 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel13 : (989785516069125 / 18446744073709551616 : ℝ) ≤
    8 * (46164 / 10000000 : ℝ) * ∫ s in (1037 / 320 : ℝ)..(519 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (1037 / 320 : ℝ)) (b := (519 / 160 : ℝ))
    (l := (14218831513151941485 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (46164 / 10000000 : ℝ))
  have hp : (989785516069125 / 18446744073709551616 : ℝ) ≤ 8 * (46164 / 10000000 : ℝ) *
      (((519 / 160 : ℝ) - (1037 / 320 : ℝ)) * (14218831513151941485 / 18446744073709551616 : ℝ) / denomMax (1037 / 320 : ℝ) (519 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel14 : (990319253405364 / 18446744073709551616 : ℝ) ≤
    8 * (46164 / 10000000 : ℝ) * ∫ s in (519 / 160 : ℝ)..(1039 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (519 / 160 : ℝ)) (b := (1039 / 320 : ℝ))
    (l := (14227082442621790608 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (46164 / 10000000 : ℝ))
  have hp : (990319253405364 / 18446744073709551616 : ℝ) ≤ 8 * (46164 / 10000000 : ℝ) *
      (((1039 / 320 : ℝ) - (519 / 160 : ℝ)) * (14227082442621790608 / 18446744073709551616 : ℝ) / denomMax (519 / 160 : ℝ) (1039 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel15 : (990856467126153 / 18446744073709551616 : ℝ) ≤
    8 * (46164 / 10000000 : ℝ) * ∫ s in (1039 / 320 : ℝ)..(13 / 4 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (1039 / 320 : ℝ)) (b := (13 / 4 : ℝ))
    (l := (14235358672398854677 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (46164 / 10000000 : ℝ))
  have hp : (990856467126153 / 18446744073709551616 : ℝ) ≤ 8 * (46164 / 10000000 : ℝ) *
      (((13 / 4 : ℝ) - (1039 / 320 : ℝ)) * (14235358672398854677 / 18446744073709551616 : ℝ) / denomMax (1039 / 320 : ℝ) (13 / 4 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel16 : (991397167853787 / 18446744073709551616 : ℝ) ≤
    8 * (46164 / 10000000 : ℝ) * ∫ s in (13 / 4 : ℝ)..(1041 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (13 / 4 : ℝ)) (b := (1041 / 320 : ℝ))
    (l := (14243660319868351895 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (46164 / 10000000 : ℝ))
  have hp : (991397167853787 / 18446744073709551616 : ℝ) ≤ 8 * (46164 / 10000000 : ℝ) *
      (((1041 / 320 : ℝ) - (13 / 4 : ℝ)) * (14243660319868351895 / 18446744073709551616 : ℝ) / denomMax (13 / 4 : ℝ) (1041 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel17 : (991941366297051 / 18446744073709551616 : ℝ) ≤
    8 * (46164 / 10000000 : ℝ) * ∫ s in (1041 / 320 : ℝ)..(521 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (1041 / 320 : ℝ)) (b := (521 / 160 : ℝ))
    (l := (14251987503147924717 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (46164 / 10000000 : ℝ))
  have hp : (991941366297051 / 18446744073709551616 : ℝ) ≤ 8 * (46164 / 10000000 : ℝ) *
      (((521 / 160 : ℝ) - (1041 / 320 : ℝ)) * (14251987503147924717 / 18446744073709551616 : ℝ) / denomMax (1041 / 320 : ℝ) (521 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel18 : (992489073251794 / 18446744073709551616 : ℝ) ≤
    8 * (46164 / 10000000 : ℝ) * ∫ s in (521 / 160 : ℝ)..(1043 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (521 / 160 : ℝ)) (b := (1043 / 320 : ℝ))
    (l := (14260340341093400503 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (46164 / 10000000 : ℝ))
  have hp : (992489073251794 / 18446744073709551616 : ℝ) ≤ 8 * (46164 / 10000000 : ℝ) *
      (((1043 / 320 : ℝ) - (521 / 160 : ℝ)) * (14260340341093400503 / 18446744073709551616 : ℝ) / denomMax (521 / 160 : ℝ) (1043 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel19 : (993040299601509 / 18446744073709551616 : ℝ) ≤
    8 * (46164 / 10000000 : ℝ) * ∫ s in (1043 / 320 : ℝ)..(261 / 80 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (1043 / 320 : ℝ)) (b := (261 / 80 : ℝ))
    (l := (14268718953304606972 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (46164 / 10000000 : ℝ))
  have hp : (993040299601509 / 18446744073709551616 : ℝ) ≤ 8 * (46164 / 10000000 : ℝ) *
      (((261 / 80 : ℝ) - (1043 / 320 : ℝ)) * (14268718953304606972 / 18446744073709551616 : ℝ) / denomMax (1043 / 320 : ℝ) (261 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel20 : (993595056317921 / 18446744073709551616 : ℝ) ≤
    8 * (46164 / 10000000 : ℝ) * ∫ s in (261 / 80 : ℝ)..(209 / 64 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (261 / 80 : ℝ)) (b := (209 / 64 : ℝ))
    (l := (14277123460131243105 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (46164 / 10000000 : ℝ))
  have hp : (993595056317921 / 18446744073709551616 : ℝ) ≤ 8 * (46164 / 10000000 : ℝ) *
      (((209 / 64 : ℝ) - (261 / 80 : ℝ)) * (14277123460131243105 / 18446744073709551616 : ℝ) / denomMax (261 / 80 : ℝ) (209 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel21 : (994153354461581 / 18446744073709551616 : ℝ) ≤
    8 * (46164 / 10000000 : ℝ) * ∫ s in (209 / 64 : ℝ)..(523 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (209 / 64 : ℝ)) (b := (523 / 160 : ℝ))
    (l := (14285553982678806080 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (46164 / 10000000 : ℝ))
  have hp : (994153354461581 / 18446744073709551616 : ℝ) ≤ 8 * (46164 / 10000000 : ℝ) *
      (((523 / 160 : ℝ) - (209 / 64 : ℝ)) * (14285553982678806080 / 18446744073709551616 : ℝ) / denomMax (209 / 64 : ℝ) (523 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel22 : (994715205182463 / 18446744073709551616 : ℝ) ≤
    8 * (46164 / 10000000 : ℝ) * ∫ s in (523 / 160 : ℝ)..(1047 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (523 / 160 : ℝ)) (b := (1047 / 320 : ℝ))
    (l := (14294010642814574909 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (46164 / 10000000 : ℝ))
  have hp : (994715205182463 / 18446744073709551616 : ℝ) ≤ 8 * (46164 / 10000000 : ℝ) *
      (((1047 / 320 : ℝ) - (523 / 160 : ℝ)) * (14294010642814574909 / 18446744073709551616 : ℝ) / denomMax (523 / 160 : ℝ) (1047 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel23 : (995280619720570 / 18446744073709551616 : ℝ) ≤
    8 * (46164 / 10000000 : ℝ) * ∫ s in (1047 / 320 : ℝ)..(131 / 40 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (1047 / 320 : ℝ)) (b := (131 / 40 : ℝ))
    (l := (14302493563173651373 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (46164 / 10000000 : ℝ))
  have hp : (995280619720570 / 18446744073709551616 : ℝ) ≤ 8 * (46164 / 10000000 : ℝ) *
      (((131 / 40 : ℝ) - (1047 / 320 : ℝ)) * (14302493563173651373 / 18446744073709551616 : ℝ) / denomMax (1047 / 320 : ℝ) (131 / 40 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel24 : (995849609406548 / 18446744073709551616 : ℝ) ≤
    8 * (46164 / 10000000 : ℝ) * ∫ s in (131 / 40 : ℝ)..(1049 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (131 / 40 : ℝ)) (b := (1049 / 320 : ℝ))
    (l := (14311002867165058940 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (46164 / 10000000 : ℝ))
  have hp : (995849609406548 / 18446744073709551616 : ℝ) ≤ 8 * (46164 / 10000000 : ℝ) *
      (((1049 / 320 : ℝ) - (131 / 40 : ℝ)) * (14311002867165058940 / 18446744073709551616 : ℝ) / denomMax (131 / 40 : ℝ) (1049 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel25 : (996422185662301 / 18446744073709551616 : ℝ) ≤
    8 * (46164 / 10000000 : ℝ) * ∫ s in (1049 / 320 : ℝ)..(105 / 32 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (1049 / 320 : ℝ)) (b := (105 / 32 : ℝ))
    (l := (14319538678977900285 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (46164 / 10000000 : ℝ))
  have hp : (996422185662301 / 18446744073709551616 : ℝ) ≤ 8 * (46164 / 10000000 : ℝ) *
      (((105 / 32 : ℝ) - (1049 / 320 : ℝ)) * (14319538678977900285 / 18446744073709551616 : ℝ) / denomMax (1049 / 320 : ℝ) (105 / 32 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel26 : (996998360001619 / 18446744073709551616 : ℝ) ≤
    8 * (46164 / 10000000 : ℝ) * ∫ s in (105 / 32 : ℝ)..(1051 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (105 / 32 : ℝ)) (b := (1051 / 320 : ℝ))
    (l := (14328101123587574104 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (46164 / 10000000 : ℝ))
  have hp : (996998360001619 / 18446744073709551616 : ℝ) ≤ 8 * (46164 / 10000000 : ℝ) *
      (((1051 / 320 : ℝ) - (105 / 32 : ℝ)) * (14328101123587574104 / 18446744073709551616 : ℝ) / denomMax (105 / 32 : ℝ) (1051 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel27 : (997578144030806 / 18446744073709551616 : ℝ) ≤
    8 * (46164 / 10000000 : ℝ) * ∫ s in (1051 / 320 : ℝ)..(263 / 80 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (1051 / 320 : ℝ)) (b := (263 / 80 : ℝ))
    (l := (14336690326762051874 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (46164 / 10000000 : ℝ))
  have hp : (997578144030806 / 18446744073709551616 : ℝ) ≤ 8 * (46164 / 10000000 : ℝ) *
      (((263 / 80 : ℝ) - (1051 / 320 : ℝ)) * (14336690326762051874 / 18446744073709551616 : ℝ) / denomMax (1051 / 320 : ℝ) (263 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel28 : (998161549449320 / 18446744073709551616 : ℝ) ≤
    8 * (46164 / 10000000 : ℝ) * ∫ s in (263 / 80 : ℝ)..(1053 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (263 / 80 : ℝ)) (b := (1053 / 320 : ℝ))
    (l := (14345306415068215244 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (46164 / 10000000 : ℝ))
  have hp : (998161549449320 / 18446744073709551616 : ℝ) ≤ 8 * (46164 / 10000000 : ℝ) *
      (((1053 / 320 : ℝ) - (263 / 80 : ℝ)) * (14345306415068215244 / 18446744073709551616 : ℝ) / denomMax (263 / 80 : ℝ) (1053 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel29 : (998748588050418 / 18446744073709551616 : ℝ) ≤
    8 * (46164 / 10000000 : ℝ) * ∫ s in (1053 / 320 : ℝ)..(527 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (1053 / 320 : ℝ)) (b := (527 / 160 : ℝ))
    (l := (14353949515878254752 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (46164 / 10000000 : ℝ))
  have hp : (998748588050418 / 18446744073709551616 : ℝ) ≤ 8 * (46164 / 10000000 : ℝ) *
      (((527 / 160 : ℝ) - (1053 / 320 : ℝ)) * (14353949515878254752 / 18446744073709551616 : ℝ) / denomMax (1053 / 320 : ℝ) (527 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel30 : (999339271721804 / 18446744073709551616 : ℝ) ≤
    8 * (46164 / 10000000 : ℝ) * ∫ s in (527 / 160 : ℝ)..(211 / 64 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (527 / 160 : ℝ)) (b := (211 / 64 : ℝ))
    (l := (14362619757376130559 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (46164 / 10000000 : ℝ))
  have hp : (999339271721804 / 18446744073709551616 : ℝ) ≤ 8 * (46164 / 10000000 : ℝ) *
      (((211 / 64 : ℝ) - (527 / 160 : ℝ)) * (14362619757376130559 / 18446744073709551616 : ℝ) / denomMax (527 / 160 : ℝ) (211 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel31 : (999933612446291 / 18446744073709551616 : ℝ) ≤
    8 * (46164 / 10000000 : ℝ) * ∫ s in (211 / 64 : ℝ)..(33 / 10 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (211 / 64 : ℝ)) (b := (33 / 10 : ℝ))
    (l := (14371317268564095906 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (46164 / 10000000 : ℝ))
  have hp : (999933612446291 / 18446744073709551616 : ℝ) ≤ 8 * (46164 / 10000000 : ℝ) *
      (((33 / 10 : ℝ) - (211 / 64 : ℝ)) * (14371317268564095906 / 18446744073709551616 : ℝ) / denomMax (211 / 64 : ℝ) (33 / 10 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

theorem lower : (31720809258568880 / 18446744073709551616 : ℝ) ≤
    8 * (46164 / 10000000 : ℝ) * ∫ s in (16 / 5 : ℝ)..(33 / 10 : ℝ), density s := by
  have he := integral_grid_sum (16 / 5 : ℝ) (33 / 10 : ℝ) 32 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [endpoint, alpha, beta])
  norm_num [Finset.sum_range_succ] at he
  linarith only [panel00, panel01, panel02, panel03, panel04, panel05, panel06, panel07, panel08, panel09, panel10, panel11, panel12, panel13, panel14, panel15, panel16, panel17, panel18, panel19, panel20, panel21, panel22, panel23, panel24, panel25, panel26, panel27, panel28, panel29, panel30, panel31, he]

end Wu18938Campaign.M3.Confirmed.TableRow12
