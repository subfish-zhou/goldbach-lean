import Wu18938Campaign.M3.Confirmed.TableBounds

noncomputable section
namespace Wu18938Campaign.M3.Confirmed.TableRow10
open Real Set MeasureTheory QuarterTrim
open WuSource.SrcSixthGain Wu18938Campaign.M3.Confirmed.TableBounds

private theorem panel00 : (1375126249783808 / 18446744073709551616 : ℝ) ≤
    8 * (66236 / 10000000 : ℝ) * ∫ s in (3 / 1 : ℝ)..(961 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (3 / 1 : ℝ)) (b := (961 / 320 : ℝ))
    (l := (13651231802426706479 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (66236 / 10000000 : ℝ))
  have hp : (1375126249783808 / 18446744073709551616 : ℝ) ≤ 8 * (66236 / 10000000 : ℝ) *
      (((961 / 320 : ℝ) - (3 / 1 : ℝ)) * (13651231802426706479 / 18446744073709551616 : ℝ) / denomMax (3 / 1 : ℝ) (961 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel01 : (1375545051751033 / 18446744073709551616 : ℝ) ≤
    8 * (66236 / 10000000 : ℝ) * ∫ s in (961 / 320 : ℝ)..(481 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (961 / 320 : ℝ)) (b := (481 / 160 : ℝ))
    (l := (13657837089427910135 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (66236 / 10000000 : ℝ))
  have hp : (1375545051751033 / 18446744073709551616 : ℝ) ≤ 8 * (66236 / 10000000 : ℝ) *
      (((481 / 160 : ℝ) - (961 / 320 : ℝ)) * (13657837089427910135 / 18446744073709551616 : ℝ) / denomMax (961 / 320 : ℝ) (481 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel02 : (1375967987196440 / 18446744073709551616 : ℝ) ≤
    8 * (66236 / 10000000 : ℝ) * ∫ s in (481 / 160 : ℝ)..(963 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (481 / 160 : ℝ)) (b := (963 / 320 : ℝ))
    (l := (13664460455338400583 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (66236 / 10000000 : ℝ))
  have hp : (1375967987196440 / 18446744073709551616 : ℝ) ≤ 8 * (66236 / 10000000 : ℝ) *
      (((963 / 320 : ℝ) - (481 / 160 : ℝ)) * (13664460455338400583 / 18446744073709551616 : ℝ) / denomMax (481 / 160 : ℝ) (963 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel03 : (1376395063717689 / 18446744073709551616 : ℝ) ≤
    8 * (66236 / 10000000 : ℝ) * ∫ s in (963 / 320 : ℝ)..(241 / 80 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (963 / 320 : ℝ)) (b := (241 / 80 : ℝ))
    (l := (13671101974912534579 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (66236 / 10000000 : ℝ))
  have hp : (1376395063717689 / 18446744073709551616 : ℝ) ≤ 8 * (66236 / 10000000 : ℝ) *
      (((241 / 80 : ℝ) - (963 / 320 : ℝ)) * (13671101974912534579 / 18446744073709551616 : ℝ) / denomMax (963 / 320 : ℝ) (241 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel04 : (1376826288993319 / 18446744073709551616 : ℝ) ≤
    8 * (66236 / 10000000 : ℝ) * ∫ s in (241 / 80 : ℝ)..(193 / 64 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (241 / 80 : ℝ)) (b := (193 / 64 : ℝ))
    (l := (13677761723319718922 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (66236 / 10000000 : ℝ))
  have hp : (1376826288993319 / 18446744073709551616 : ℝ) ≤ 8 * (66236 / 10000000 : ℝ) *
      (((193 / 64 : ℝ) - (241 / 80 : ℝ)) * (13677761723319718922 / 18446744073709551616 : ℝ) / denomMax (241 / 80 : ℝ) (193 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel05 : (1377261670783103 / 18446744073709551616 : ℝ) ≤
    8 * (66236 / 10000000 : ℝ) * ∫ s in (193 / 64 : ℝ)..(483 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (193 / 64 : ℝ)) (b := (483 / 160 : ℝ))
    (l := (13684439776147311062 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (66236 / 10000000 : ℝ))
  have hp : (1377261670783103 / 18446744073709551616 : ℝ) ≤ 8 * (66236 / 10000000 : ℝ) *
      (((483 / 160 : ℝ) - (193 / 64 : ℝ)) * (13684439776147311062 / 18446744073709551616 : ℝ) / denomMax (193 / 64 : ℝ) (483 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel06 : (1377701216928417 / 18446744073709551616 : ℝ) ≤
    8 * (66236 / 10000000 : ℝ) * ∫ s in (483 / 160 : ℝ)..(967 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (483 / 160 : ℝ)) (b := (967 / 320 : ℝ))
    (l := (13691136209403544187 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (66236 / 10000000 : ℝ))
  have hp : (1377701216928417 / 18446744073709551616 : ℝ) ≤ 8 * (66236 / 10000000 : ℝ) *
      (((967 / 320 : ℝ) - (483 / 160 : ℝ)) * (13691136209403544187 / 18446744073709551616 : ℝ) / denomMax (483 / 160 : ℝ) (967 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel07 : (1378144935352603 / 18446744073709551616 : ℝ) ≤
    8 * (66236 / 10000000 : ℝ) * ∫ s in (967 / 320 : ℝ)..(121 / 40 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (967 / 320 : ℝ)) (b := (121 / 40 : ℝ))
    (l := (13697851099520477061 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (66236 / 10000000 : ℝ))
  have hp : (1378144935352603 / 18446744073709551616 : ℝ) ≤ 8 * (66236 / 10000000 : ℝ) *
      (((121 / 40 : ℝ) - (967 / 320 : ℝ)) * (13697851099520477061 / 18446744073709551616 : ℝ) / denomMax (967 / 320 : ℝ) (121 / 40 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel08 : (1378592834061341 / 18446744073709551616 : ℝ) ≤
    8 * (66236 / 10000000 : ℝ) * ∫ s in (121 / 40 : ℝ)..(969 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (121 / 40 : ℝ)) (b := (969 / 320 : ℝ))
    (l := (13704584523356968823 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (66236 / 10000000 : ℝ))
  have hp : (1378592834061341 / 18446744073709551616 : ℝ) ≤ 8 * (66236 / 10000000 : ℝ) *
      (((969 / 320 : ℝ) - (121 / 40 : ℝ)) * (13704584523356968823 / 18446744073709551616 : ℝ) / denomMax (121 / 40 : ℝ) (969 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel09 : (1379044921143024 / 18446744073709551616 : ℝ) ≤
    8 * (66236 / 10000000 : ℝ) * ∫ s in (969 / 320 : ℝ)..(97 / 32 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (969 / 320 : ℝ)) (b := (97 / 32 : ℝ))
    (l := (13711336558201679028 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (66236 / 10000000 : ℝ))
  have hp : (1379044921143024 / 18446744073709551616 : ℝ) ≤ 8 * (66236 / 10000000 : ℝ) *
      (((97 / 32 : ℝ) - (969 / 320 : ℝ)) * (13711336558201679028 / 18446744073709551616 : ℝ) / denomMax (969 / 320 : ℝ) (97 / 32 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel10 : (1379501204769139 / 18446744073709551616 : ℝ) ≤
    8 * (66236 / 10000000 : ℝ) * ∫ s in (97 / 32 : ℝ)..(971 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (97 / 32 : ℝ)) (b := (971 / 320 : ℝ))
    (l := (13718107281776093161 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (66236 / 10000000 : ℝ))
  have hp : (1379501204769139 / 18446744073709551616 : ℝ) ≤ 8 * (66236 / 10000000 : ℝ) *
      (((971 / 320 : ℝ) - (97 / 32 : ℝ)) * (13718107281776093161 / 18446744073709551616 : ℝ) / denomMax (97 / 32 : ℝ) (971 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel11 : (1379961693194652 / 18446744073709551616 : ℝ) ≤
    8 * (66236 / 10000000 : ℝ) * ∫ s in (971 / 320 : ℝ)..(243 / 80 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (971 / 320 : ℝ)) (b := (243 / 80 : ℝ))
    (l := (13724896772237573887 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (66236 / 10000000 : ℝ))
  have hp : (1379961693194652 / 18446744073709551616 : ℝ) ≤ 8 * (66236 / 10000000 : ℝ) *
      (((243 / 80 : ℝ) - (971 / 320 : ℝ)) * (13724896772237573887 / 18446744073709551616 : ℝ) / denomMax (971 / 320 : ℝ) (243 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel12 : (1380426394758395 / 18446744073709551616 : ℝ) ≤
    8 * (66236 / 10000000 : ℝ) * ∫ s in (243 / 80 : ℝ)..(973 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (243 / 80 : ℝ)) (b := (973 / 320 : ℝ))
    (l := (13731705108182438290 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (66236 / 10000000 : ℝ))
  have hp : (1380426394758395 / 18446744073709551616 : ℝ) ≤ 8 * (66236 / 10000000 : ℝ) *
      (((973 / 320 : ℝ) - (243 / 80 : ℝ)) * (13731705108182438290 / 18446744073709551616 : ℝ) / denomMax (243 / 80 : ℝ) (973 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel13 : (1380895317883461 / 18446744073709551616 : ℝ) ≤
    8 * (66236 / 10000000 : ℝ) * ∫ s in (973 / 320 : ℝ)..(487 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (973 / 320 : ℝ)) (b := (487 / 160 : ℝ))
    (l := (13738532368649061365 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (66236 / 10000000 : ℝ))
  have hp : (1380895317883461 / 18446744073709551616 : ℝ) ≤ 8 * (66236 / 10000000 : ℝ) *
      (((487 / 160 : ℝ) - (973 / 320 : ℝ)) * (13738532368649061365 / 18446744073709551616 : ℝ) / denomMax (973 / 320 : ℝ) (487 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel14 : (1381368471077600 / 18446744073709551616 : ℝ) ≤
    8 * (66236 / 10000000 : ℝ) * ∫ s in (487 / 160 : ℝ)..(195 / 64 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (487 / 160 : ℝ)) (b := (195 / 64 : ℝ))
    (l := (13745378633121006020 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (66236 / 10000000 : ℝ))
  have hp : (1381368471077600 / 18446744073709551616 : ℝ) ≤ 8 * (66236 / 10000000 : ℝ) *
      (((195 / 64 : ℝ) - (487 / 160 : ℝ)) * (13745378633121006020 / 18446744073709551616 : ℝ) / denomMax (487 / 160 : ℝ) (195 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel15 : (1381845862933625 / 18446744073709551616 : ℝ) ≤
    8 * (66236 / 10000000 : ℝ) * ∫ s in (195 / 64 : ℝ)..(61 / 20 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (195 / 64 : ℝ)) (b := (61 / 20 : ℝ))
    (l := (13752243981530179861 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (66236 / 10000000 : ℝ))
  have hp : (1381845862933625 / 18446744073709551616 : ℝ) ≤ 8 * (66236 / 10000000 : ℝ) *
      (((61 / 20 : ℝ) - (195 / 64 : ℝ)) * (13752243981530179861 / 18446744073709551616 : ℝ) / denomMax (195 / 64 : ℝ) (61 / 20 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel16 : (1382327502129817 / 18446744073709551616 : ℝ) ≤
    8 * (66236 / 10000000 : ℝ) * ∫ s in (61 / 20 : ℝ)..(977 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (61 / 20 : ℝ)) (b := (977 / 320 : ℝ))
    (l := (13759128494260019025 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (66236 / 10000000 : ℝ))
  have hp : (1382327502129817 / 18446744073709551616 : ℝ) ≤ 8 * (66236 / 10000000 : ℝ) *
      (((977 / 320 : ℝ) - (61 / 20 : ℝ)) * (13759128494260019025 / 18446744073709551616 : ℝ) / denomMax (61 / 20 : ℝ) (977 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel17 : (1382813397430335 / 18446744073709551616 : ℝ) ≤
    8 * (66236 / 10000000 : ℝ) * ∫ s in (977 / 320 : ℝ)..(489 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (977 / 320 : ℝ)) (b := (489 / 160 : ℝ))
    (l := (13766032252148699335 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (66236 / 10000000 : ℝ))
  have hp : (1382813397430335 / 18446744073709551616 : ℝ) ≤ 8 * (66236 / 10000000 : ℝ) *
      (((489 / 160 : ℝ) - (977 / 320 : ℝ)) * (13766032252148699335 / 18446744073709551616 : ℝ) / denomMax (977 / 320 : ℝ) (489 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel18 : (1383303557685636 / 18446744073709551616 : ℝ) ≤
    8 * (66236 / 10000000 : ℝ) * ∫ s in (489 / 160 : ℝ)..(979 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (489 / 160 : ℝ)) (b := (979 / 320 : ℝ))
    (l := (13772955336492375048 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (66236 / 10000000 : ℝ))
  have hp : (1383303557685636 / 18446744073709551616 : ℝ) ≤ 8 * (66236 / 10000000 : ℝ) *
      (((979 / 320 : ℝ) - (489 / 160 : ℝ)) * (13772955336492375048 / 18446744073709551616 : ℝ) / denomMax (489 / 160 : ℝ) (979 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel19 : (1383797991832895 / 18446744073709551616 : ℝ) ≤
    8 * (66236 / 10000000 : ℝ) * ∫ s in (979 / 320 : ℝ)..(49 / 16 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (979 / 320 : ℝ)) (b := (49 / 16 : ℝ))
    (l := (13779897829048445482 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (66236 / 10000000 : ℝ))
  have hp : (1383797991832895 / 18446744073709551616 : ℝ) ≤ 8 * (66236 / 10000000 : ℝ) *
      (((49 / 16 : ℝ) - (979 / 320 : ℝ)) * (13779897829048445482 / 18446744073709551616 : ℝ) / denomMax (979 / 320 : ℝ) (49 / 16 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel20 : (1384296708896430 / 18446744073709551616 : ℝ) ≤
    8 * (66236 / 10000000 : ℝ) * ∫ s in (49 / 16 : ℝ)..(981 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (49 / 16 : ℝ)) (b := (981 / 320 : ℝ))
    (l := (13786859812038849799 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (66236 / 10000000 : ℝ))
  have hp : (1384296708896430 / 18446744073709551616 : ℝ) ≤ 8 * (66236 / 10000000 : ℝ) *
      (((981 / 320 : ℝ) - (49 / 16 : ℝ)) * (13786859812038849799 / 18446744073709551616 : ℝ) / denomMax (49 / 16 : ℝ) (981 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel21 : (1384799717988134 / 18446744073709551616 : ℝ) ≤
    8 * (66236 / 10000000 : ℝ) * ∫ s in (981 / 320 : ℝ)..(491 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (981 / 320 : ℝ)) (b := (491 / 160 : ℝ))
    (l := (13793841368153390229 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (66236 / 10000000 : ℝ))
  have hp : (1384799717988134 / 18446744073709551616 : ℝ) ≤ 8 * (66236 / 10000000 : ℝ) *
      (((491 / 160 : ℝ) - (981 / 320 : ℝ)) * (13793841368153390229 / 18446744073709551616 : ℝ) / denomMax (981 / 320 : ℝ) (491 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel22 : (1385307028307910 / 18446744073709551616 : ℝ) ≤
    8 * (66236 / 10000000 : ℝ) * ∫ s in (491 / 160 : ℝ)..(983 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (491 / 160 : ℝ)) (b := (983 / 320 : ℝ))
    (l := (13800842580553084022 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (66236 / 10000000 : ℝ))
  have hp : (1385307028307910 / 18446744073709551616 : ℝ) ≤ 8 * (66236 / 10000000 : ℝ) *
      (((983 / 320 : ℝ) - (491 / 160 : ℝ)) * (13800842580553084022 / 18446744073709551616 : ℝ) / denomMax (491 / 160 : ℝ) (983 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel23 : (1385818649144112 / 18446744073709551616 : ℝ) ≤
    8 * (66236 / 10000000 : ℝ) * ∫ s in (983 / 320 : ℝ)..(123 / 40 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (983 / 320 : ℝ)) (b := (123 / 40 : ℝ))
    (l := (13807863532873544431 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (66236 / 10000000 : ℝ))
  have hp : (1385818649144112 / 18446744073709551616 : ℝ) ≤ 8 * (66236 / 10000000 : ℝ) *
      (((123 / 40 : ℝ) - (983 / 320 : ℝ)) * (13807863532873544431 / 18446744073709551616 : ℝ) / denomMax (983 / 320 : ℝ) (123 / 40 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel24 : (1386334589873991 / 18446744073709551616 : ℝ) ≤
    8 * (66236 / 10000000 : ℝ) * ∫ s in (123 / 40 : ℝ)..(197 / 64 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (123 / 40 : ℝ)) (b := (197 / 64 : ℝ))
    (l := (13814904309228391001 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (66236 / 10000000 : ℝ))
  have hp : (1386334589873991 / 18446744073709551616 : ℝ) ≤ 8 * (66236 / 10000000 : ℝ) *
      (((197 / 64 : ℝ) - (123 / 40 : ℝ)) * (13814904309228391001 / 18446744073709551616 : ℝ) / denomMax (123 / 40 : ℝ) (197 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel25 : (1386854859964144 / 18446744073709551616 : ℝ) ≤
    8 * (66236 / 10000000 : ℝ) * ∫ s in (197 / 64 : ℝ)..(493 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (197 / 64 : ℝ)) (b := (493 / 160 : ℝ))
    (l := (13821964994212689482 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (66236 / 10000000 : ℝ))
  have hp : (1386854859964144 / 18446744073709551616 : ℝ) ≤ 8 * (66236 / 10000000 : ℝ) *
      (((493 / 160 : ℝ) - (197 / 64 : ℝ)) * (13821964994212689482 / 18446744073709551616 : ℝ) / denomMax (197 / 64 : ℝ) (493 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel26 : (1387379468970972 / 18446744073709551616 : ℝ) ≤
    8 * (66236 / 10000000 : ℝ) * ∫ s in (493 / 160 : ℝ)..(987 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (493 / 160 : ℝ)) (b := (987 / 320 : ℝ))
    (l := (13829045672906421658 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (66236 / 10000000 : ℝ))
  have hp : (1387379468970972 / 18446744073709551616 : ℝ) ≤ 8 * (66236 / 10000000 : ℝ) *
      (((987 / 320 : ℝ) - (493 / 160 : ℝ)) * (13829045672906421658 / 18446744073709551616 : ℝ) / denomMax (493 / 160 : ℝ) (987 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel27 : (1387908426541136 / 18446744073709551616 : ℝ) ≤
    8 * (66236 / 10000000 : ℝ) * ∫ s in (987 / 320 : ℝ)..(247 / 80 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (987 / 320 : ℝ)) (b := (247 / 80 : ℝ))
    (l := (13836146430877985397 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (66236 / 10000000 : ℝ))
  have hp : (1387908426541136 / 18446744073709551616 : ℝ) ≤ 8 * (66236 / 10000000 : ℝ) *
      (((247 / 80 : ℝ) - (987 / 320 : ℝ)) * (13836146430877985397 / 18446744073709551616 : ℝ) / denomMax (987 / 320 : ℝ) (247 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel28 : (1388441742412029 / 18446744073709551616 : ℝ) ≤
    8 * (66236 / 10000000 : ℝ) * ∫ s in (247 / 80 : ℝ)..(989 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (247 / 80 : ℝ)) (b := (989 / 320 : ℝ))
    (l := (13843267354187725240 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (66236 / 10000000 : ℝ))
  have hp : (1388441742412029 / 18446744073709551616 : ℝ) ≤ 8 * (66236 / 10000000 : ℝ) *
      (((989 / 320 : ℝ) - (247 / 80 : ℝ)) * (13843267354187725240 / 18446744073709551616 : ℝ) / denomMax (247 / 80 : ℝ) (989 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel29 : (1388979426412242 / 18446744073709551616 : ℝ) ≤
    8 * (66236 / 10000000 : ℝ) * ∫ s in (989 / 320 : ℝ)..(99 / 32 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (989 / 320 : ℝ)) (b := (99 / 32 : ℝ))
    (l := (13850408529391493829 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (66236 / 10000000 : ℝ))
  have hp : (1388979426412242 / 18446744073709551616 : ℝ) ≤ 8 * (66236 / 10000000 : ℝ) *
      (((99 / 32 : ℝ) - (989 / 320 : ℝ)) * (13850408529391493829 / 18446744073709551616 : ℝ) / denomMax (989 / 320 : ℝ) (99 / 32 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel30 : (1389521488462040 / 18446744073709551616 : ℝ) ≤
    8 * (66236 / 10000000 : ℝ) * ∫ s in (99 / 32 : ℝ)..(991 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (99 / 32 : ℝ)) (b := (991 / 320 : ℝ))
    (l := (13857570043544244504 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (66236 / 10000000 : ℝ))
  have hp : (1389521488462040 / 18446744073709551616 : ℝ) ≤ 8 * (66236 / 10000000 : ℝ) *
      (((991 / 320 : ℝ) - (99 / 32 : ℝ)) * (13857570043544244504 / 18446744073709551616 : ℝ) / denomMax (99 / 32 : ℝ) (991 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel31 : (1390067938573848 / 18446744073709551616 : ℝ) ≤
    8 * (66236 / 10000000 : ℝ) * ∫ s in (991 / 320 : ℝ)..(31 / 10 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (991 / 320 : ℝ)) (b := (31 / 10 : ℝ))
    (l := (13864751984203655381 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (66236 / 10000000 : ℝ))
  have hp : (1390067938573848 / 18446744073709551616 : ℝ) ≤ 8 * (66236 / 10000000 : ℝ) *
      (((31 / 10 : ℝ) - (991 / 320 : ℝ)) * (13864751984203655381 / 18446744073709551616 : ℝ) / denomMax (991 / 320 : ℝ) (31 / 10 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

theorem lower : (44232557658953320 / 18446744073709551616 : ℝ) ≤
    8 * (66236 / 10000000 : ℝ) * ∫ s in (3 / 1 : ℝ)..(31 / 10 : ℝ), density s := by
  have he := integral_grid_sum (3 / 1 : ℝ) (31 / 10 : ℝ) 32 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [endpoint, alpha, beta])
  norm_num [Finset.sum_range_succ] at he
  linarith only [panel00, panel01, panel02, panel03, panel04, panel05, panel06, panel07, panel08, panel09, panel10, panel11, panel12, panel13, panel14, panel15, panel16, panel17, panel18, panel19, panel20, panel21, panel22, panel23, panel24, panel25, panel26, panel27, panel28, panel29, panel30, panel31, he]

end Wu18938Campaign.M3.Confirmed.TableRow10
