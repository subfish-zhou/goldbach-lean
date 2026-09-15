import Wu18938Campaign.M3.Confirmed.TableBounds

noncomputable section
namespace Wu18938Campaign.M3.Confirmed.TableRow19
open Real Set MeasureTheory QuarterTrim
open WuSource.SrcSixthGain Wu18938Campaign.M3.Confirmed.TableBounds

private theorem panel00 : (117627491391473 / 18446744073709551616 : ℝ) ≤
    8 * (12593 / 10000000 : ℝ) * ∫ s in (19 / 5 : ℝ)..(1217 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (19 / 5 : ℝ)) (b := (1217 / 320 : ℝ))
    (l := (6066460241504942152 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (12593 / 10000000 : ℝ))
  have hp : (117627491391473 / 18446744073709551616 : ℝ) ≤ 8 * (12593 / 10000000 : ℝ) *
      (((1217 / 320 : ℝ) - (19 / 5 : ℝ)) * (6066460241504942152 / 18446744073709551616 : ℝ) / denomMax (19 / 5 : ℝ) (1217 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel01 : (116133139608927 / 18446744073709551616 : ℝ) ≤
    8 * (12593 / 10000000 : ℝ) * ∫ s in (1217 / 320 : ℝ)..(609 / 160 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1217 / 320 : ℝ)) (b := (609 / 160 : ℝ))
    (l := (5987709299128681511 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (12593 / 10000000 : ℝ))
  have hp : (116133139608927 / 18446744073709551616 : ℝ) ≤ 8 * (12593 / 10000000 : ℝ) *
      (((609 / 160 : ℝ) - (1217 / 320 : ℝ)) * (5987709299128681511 / 18446744073709551616 : ℝ) / denomMax (1217 / 320 : ℝ) (609 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel02 : (114634756330969 / 18446744073709551616 : ℝ) ≤
    8 * (12593 / 10000000 : ℝ) * ∫ s in (609 / 160 : ℝ)..(1219 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (609 / 160 : ℝ)) (b := (1219 / 320 : ℝ))
    (l := (5908783123358123463 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (12593 / 10000000 : ℝ))
  have hp : (114634756330969 / 18446744073709551616 : ℝ) ≤ 8 * (12593 / 10000000 : ℝ) *
      (((1219 / 320 : ℝ) - (609 / 160 : ℝ)) * (5908783123358123463 / 18446744073709551616 : ℝ) / denomMax (609 / 160 : ℝ) (1219 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel03 : (113132314268532 / 18446744073709551616 : ℝ) ≤
    8 * (12593 / 10000000 : ℝ) * ∫ s in (1219 / 320 : ℝ)..(61 / 16 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1219 / 320 : ℝ)) (b := (61 / 16 : ℝ))
    (l := (5829680904599149862 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (12593 / 10000000 : ℝ))
  have hp : (113132314268532 / 18446744073709551616 : ℝ) ≤ 8 * (12593 / 10000000 : ℝ) *
      (((61 / 16 : ℝ) - (1219 / 320 : ℝ)) * (5829680904599149862 / 18446744073709551616 : ℝ) / denomMax (1219 / 320 : ℝ) (61 / 16 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel04 : (111625785944949 / 18446744073709551616 : ℝ) ≤
    8 * (12593 / 10000000 : ℝ) * ∫ s in (61 / 16 : ℝ)..(1221 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (61 / 16 : ℝ)) (b := (1221 / 320 : ℝ))
    (l := (5750401827466729551 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (12593 / 10000000 : ℝ))
  have hp : (111625785944949 / 18446744073709551616 : ℝ) ≤ 8 * (12593 / 10000000 : ℝ) *
      (((1221 / 320 : ℝ) - (61 / 16 : ℝ)) * (5750401827466729551 / 18446744073709551616 : ℝ) / denomMax (61 / 16 : ℝ) (1221 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel05 : (110115143694084 / 18446744073709551616 : ℝ) ≤
    8 * (12593 / 10000000 : ℝ) * ∫ s in (1221 / 320 : ℝ)..(611 / 160 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1221 / 320 : ℝ)) (b := (611 / 160 : ℝ))
    (l := (5670945070728268305 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (12593 / 10000000 : ℝ))
  have hp : (110115143694084 / 18446744073709551616 : ℝ) ≤ 8 * (12593 / 10000000 : ℝ) *
      (((611 / 160 : ℝ) - (1221 / 320 : ℝ)) * (5670945070728268305 / 18446744073709551616 : ℝ) / denomMax (1221 / 320 : ℝ) (611 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel06 : (108600359658452 / 18446744073709551616 : ℝ) ≤
    8 * (12593 / 10000000 : ℝ) * ∫ s in (611 / 160 : ℝ)..(1223 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (611 / 160 : ℝ)) (b := (1223 / 320 : ℝ))
    (l := (5591309807246252263 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (12593 / 10000000 : ℝ))
  have hp : (108600359658452 / 18446744073709551616 : ℝ) ≤ 8 * (12593 / 10000000 : ℝ) *
      (((1223 / 320 : ℝ) - (611 / 160 : ℝ)) * (5591309807246252263 / 18446744073709551616 : ℝ) / denomMax (611 / 160 : ℝ) (1223 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel07 : (107081405787298 / 18446744073709551616 : ℝ) ≤
    8 * (12593 / 10000000 : ℝ) * ∫ s in (1223 / 320 : ℝ)..(153 / 40 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1223 / 320 : ℝ)) (b := (153 / 40 : ℝ))
    (l := (5511495203920174120 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (12593 / 10000000 : ℝ))
  have hp : (107081405787298 / 18446744073709551616 : ℝ) ≤ 8 * (12593 / 10000000 : ℝ) *
      (((153 / 40 : ℝ) - (1223 / 320 : ℝ)) * (5511495203920174120 / 18446744073709551616 : ℝ) / denomMax (1223 / 320 : ℝ) (153 / 40 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel08 : (105558253834674 / 18446744073709551616 : ℝ) ≤
    8 * (12593 / 10000000 : ℝ) * ∫ s in (153 / 40 : ℝ)..(245 / 64 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (153 / 40 : ℝ)) (b := (245 / 64 : ℝ))
    (l := (5431500421627731141 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (12593 / 10000000 : ℝ))
  have hp : (105558253834674 / 18446744073709551616 : ℝ) ≤ 8 * (12593 / 10000000 : ℝ) *
      (((245 / 64 : ℝ) - (153 / 40 : ℝ)) * (5431500421627731141 / 18446744073709551616 : ℝ) / denomMax (153 / 40 : ℝ) (245 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel09 : (104030875357476 / 18446744073709551616 : ℝ) ≤
    8 * (12593 / 10000000 : ℝ) * ∫ s in (245 / 64 : ℝ)..(613 / 160 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (245 / 64 : ℝ)) (b := (613 / 160 : ℝ))
    (l := (5351324615165283896 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (12593 / 10000000 : ℝ))
  have hp : (104030875357476 / 18446744073709551616 : ℝ) ≤ 8 * (12593 / 10000000 : ℝ) *
      (((613 / 160 : ℝ) - (245 / 64 : ℝ)) * (5351324615165283896 / 18446744073709551616 : ℝ) / denomMax (245 / 64 : ℝ) (613 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel10 : (102499241713465 / 18446744073709551616 : ℝ) ≤
    8 * (12593 / 10000000 : ℝ) * ∫ s in (613 / 160 : ℝ)..(1227 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (613 / 160 : ℝ)) (b := (1227 / 320 : ℝ))
    (l := (5270966933187564373 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (12593 / 10000000 : ℝ))
  have hp : (102499241713465 / 18446744073709551616 : ℝ) ≤ 8 * (12593 / 10000000 : ℝ) *
      (((1227 / 320 : ℝ) - (613 / 160 : ℝ)) * (5270966933187564373 / 18446744073709551616 : ℝ) / denomMax (613 / 160 : ℝ) (1227 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel11 : (100963324059266 / 18446744073709551616 : ℝ) ≤
    8 * (12593 / 10000000 : ℝ) * ∫ s in (1227 / 320 : ℝ)..(307 / 80 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1227 / 320 : ℝ)) (b := (307 / 80 : ℝ))
    (l := (5190426518146621954 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (12593 / 10000000 : ℝ))
  have hp : (100963324059266 / 18446744073709551616 : ℝ) ≤ 8 * (12593 / 10000000 : ℝ) *
      (((307 / 80 : ℝ) - (1227 / 320 : ℝ)) * (5190426518146621954 / 18446744073709551616 : ℝ) / denomMax (1227 / 320 : ℝ) (307 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel12 : (99423093348337 / 18446744073709551616 : ℝ) ≤
    8 * (12593 / 10000000 : ℝ) * ∫ s in (307 / 80 : ℝ)..(1229 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (307 / 80 : ℝ)) (b := (1229 / 320 : ℝ))
    (l := (5109702506229995519 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (12593 / 10000000 : ℝ))
  have hp : (99423093348337 / 18446744073709551616 : ℝ) ≤ 8 * (12593 / 10000000 : ℝ) *
      (((1229 / 320 : ℝ) - (307 / 80 : ℝ)) * (5109702506229995519 / 18446744073709551616 : ℝ) / denomMax (307 / 80 : ℝ) (1229 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel13 : (97878520328922 / 18446744073709551616 : ℝ) ≤
    8 * (12593 / 10000000 : ℝ) * ∫ s in (1229 / 320 : ℝ)..(123 / 32 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1229 / 320 : ℝ)) (b := (123 / 32 : ℝ))
    (l := (5028794027298099717 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (12593 / 10000000 : ℝ))
  have hp : (97878520328922 / 18446744073709551616 : ℝ) ≤ 8 * (12593 / 10000000 : ℝ) *
      (((123 / 32 : ℝ) - (1229 / 320 : ℝ)) * (5028794027298099717 / 18446744073709551616 : ℝ) / denomMax (1229 / 320 : ℝ) (123 / 32 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel14 : (96329575541968 / 18446744073709551616 : ℝ) ≤
    8 * (12593 / 10000000 : ℝ) * ∫ s in (123 / 32 : ℝ)..(1231 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (123 / 32 : ℝ)) (b := (1231 / 320 : ℝ))
    (l := (4947700204820813258 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (12593 / 10000000 : ℝ))
  have hp : (96329575541968 / 18446744073709551616 : ℝ) ≤ 8 * (12593 / 10000000 : ℝ) *
      (((1231 / 320 : ℝ) - (123 / 32 : ℝ)) * (4947700204820813258 / 18446744073709551616 : ℝ) / denomMax (123 / 32 : ℝ) (1231 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel15 : (94776229319026 / 18446744073709551616 : ℝ) ≤
    8 * (12593 / 10000000 : ℝ) * ∫ s in (1231 / 320 : ℝ)..(77 / 20 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1231 / 320 : ℝ)) (b := (77 / 20 : ℝ))
    (l := (4866420155813256815 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (12593 / 10000000 : ℝ))
  have hp : (94776229319026 / 18446744073709551616 : ℝ) ≤ 8 * (12593 / 10000000 : ℝ) *
      (((77 / 20 : ℝ) - (1231 / 320 : ℝ)) * (4866420155813256815 / 18446744073709551616 : ℝ) / denomMax (1231 / 320 : ℝ) (77 / 20 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel16 : (93218451780122 / 18446744073709551616 : ℝ) ≤
    8 * (12593 / 10000000 : ℝ) * ∫ s in (77 / 20 : ℝ)..(1233 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (77 / 20 : ℝ)) (b := (1233 / 320 : ℝ))
    (l := (4784952990770747935 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (12593 / 10000000 : ℝ))
  have hp : (93218451780122 / 18446744073709551616 : ℝ) ≤ 8 * (12593 / 10000000 : ℝ) *
      (((1233 / 320 : ℝ) - (77 / 20 : ℝ)) * (4784952990770747935 / 18446744073709551616 : ℝ) / denomMax (77 / 20 : ℝ) (1233 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel17 : (91656212831606 / 18446744073709551616 : ℝ) ≤
    8 * (12593 / 10000000 : ℝ) * ∫ s in (1233 / 320 : ℝ)..(617 / 160 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1233 / 320 : ℝ)) (b := (617 / 160 : ℝ))
    (l := (4703297813602920110 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (12593 / 10000000 : ℝ))
  have hp : (91656212831606 / 18446744073709551616 : ℝ) ≤ 8 * (12593 / 10000000 : ℝ) *
      (((617 / 160 : ℝ) - (1233 / 320 : ℝ)) * (4703297813602920110 / 18446744073709551616 : ℝ) / denomMax (1233 / 320 : ℝ) (617 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel18 : (90089482163968 / 18446744073709551616 : ℝ) ≤
    8 * (12593 / 10000000 : ℝ) * ∫ s in (617 / 160 : ℝ)..(247 / 64 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (617 / 160 : ℝ)) (b := (247 / 64 : ℝ))
    (l := (4621453721566992915 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (12593 / 10000000 : ℝ))
  have hp : (90089482163968 / 18446744073709551616 : ℝ) ≤ 8 * (12593 / 10000000 : ℝ) *
      (((247 / 64 : ℝ) - (617 / 160 : ℝ)) * (4621453721566992915 / 18446744073709551616 : ℝ) / denomMax (617 / 160 : ℝ) (247 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel19 : (88518229249632 / 18446744073709551616 : ℝ) ≤
    8 * (12593 / 10000000 : ℝ) * ∫ s in (247 / 64 : ℝ)..(309 / 80 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (247 / 64 : ℝ)) (b := (309 / 80 : ℝ))
    (l := (4539419805200179894 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (12593 / 10000000 : ℝ))
  have hp : (88518229249632 / 18446744073709551616 : ℝ) ≤ 8 * (12593 / 10000000 : ℝ) *
      (((309 / 80 : ℝ) - (247 / 64 : ℝ)) * (4539419805200179894 / 18446744073709551616 : ℝ) / denomMax (247 / 64 : ℝ) (309 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel20 : (86942423340725 / 18446744073709551616 : ℝ) ≤
    8 * (12593 / 10000000 : ℝ) * ∫ s in (309 / 80 : ℝ)..(1237 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (309 / 80 : ℝ)) (b := (1237 / 320 : ℝ))
    (l := (4457195148251220629 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (12593 / 10000000 : ℝ))
  have hp : (86942423340725 / 18446744073709551616 : ℝ) ≤ 8 * (12593 / 10000000 : ℝ) *
      (((1237 / 320 : ℝ) - (309 / 80 : ℝ)) * (4457195148251220629 / 18446744073709551616 : ℝ) / denomMax (309 / 80 : ℝ) (1237 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel21 : (85362033466810 / 18446744073709551616 : ℝ) ≤
    8 * (12593 / 10000000 : ℝ) * ∫ s in (1237 / 320 : ℝ)..(619 / 160 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1237 / 320 : ℝ)) (b := (619 / 160 : ℝ))
    (l := (4374778827611023147 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (12593 / 10000000 : ℝ))
  have hp : (85362033466810 / 18446744073709551616 : ℝ) ≤ 8 * (12593 / 10000000 : ℝ) *
      (((619 / 160 : ℝ) - (1237 / 320 : ℝ)) * (4374778827611023147 / 18446744073709551616 : ℝ) / denomMax (1237 / 320 : ℝ) (619 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel22 : (83777028432601 / 18446744073709551616 : ℝ) ≤
    8 * (12593 / 10000000 : ℝ) * ∫ s in (619 / 160 : ℝ)..(1239 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (619 / 160 : ℝ)) (b := (1239 / 320 : ℝ))
    (l := (4292169913242402602 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (12593 / 10000000 : ℝ))
  have hp : (83777028432601 / 18446744073709551616 : ℝ) ≤ 8 * (12593 / 10000000 : ℝ) *
      (((1239 / 320 : ℝ) - (619 / 160 : ℝ)) * (4292169913242402602 / 18446744073709551616 : ℝ) / denomMax (619 / 160 : ℝ) (1239 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel23 : (82187376815642 / 18446744073709551616 : ℝ) ≤
    8 * (12593 / 10000000 : ℝ) * ∫ s in (1239 / 320 : ℝ)..(31 / 8 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1239 / 320 : ℝ)) (b := (31 / 8 : ℝ))
    (l := (4209367468108901876 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (12593 / 10000000 : ℝ))
  have hp : (82187376815642 / 18446744073709551616 : ℝ) ≤ 8 * (12593 / 10000000 : ℝ) *
      (((31 / 8 : ℝ) - (1239 / 320 : ℝ)) * (4209367468108901876 / 18446744073709551616 : ℝ) / denomMax (1239 / 320 : ℝ) (31 / 8 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel24 : (80593046963961 / 18446744073709551616 : ℝ) ≤
    8 * (12593 / 10000000 : ℝ) * ∫ s in (31 / 8 : ℝ)..(1241 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (31 / 8 : ℝ)) (b := (1241 / 320 : ℝ))
    (l := (4126370548102679496 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (12593 / 10000000 : ℝ))
  have hp : (80593046963961 / 18446744073709551616 : ℝ) ≤ 8 * (12593 / 10000000 : ℝ) *
      (((1241 / 320 : ℝ) - (31 / 8 : ℝ)) * (4126370548102679496 / 18446744073709551616 : ℝ) / denomMax (31 / 8 : ℝ) (1241 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel25 : (78994006993691 / 18446744073709551616 : ℝ) ≤
    8 * (12593 / 10000000 : ℝ) * ∫ s in (1241 / 320 : ℝ)..(621 / 160 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1241 / 320 : ℝ)) (b := (621 / 160 : ℝ))
    (l := (4043178201971449960 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (12593 / 10000000 : ℝ))
  have hp : (78994006993691 / 18446744073709551616 : ℝ) ≤ 8 * (12593 / 10000000 : ℝ) *
      (((621 / 160 : ℝ) - (1241 / 320 : ℝ)) * (4043178201971449960 / 18446744073709551616 : ℝ) / denomMax (1241 / 320 : ℝ) (621 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel26 : (77390224786669 / 18446744073709551616 : ℝ) ≤
    8 * (12593 / 10000000 : ℝ) * ∫ s in (621 / 160 : ℝ)..(1243 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (621 / 160 : ℝ)) (b := (1243 / 320 : ℝ))
    (l := (3959789471244461321 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (12593 / 10000000 : ℝ))
  have hp : (77390224786669 / 18446744073709551616 : ℝ) ≤ 8 * (12593 / 10000000 : ℝ) *
      (((1243 / 320 : ℝ) - (621 / 160 : ℝ)) * (3959789471244461321 / 18446744073709551616 : ℝ) / denomMax (621 / 160 : ℝ) (1243 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel27 : (75781667987994 / 18446744073709551616 : ℝ) ≤
    8 * (12593 / 10000000 : ℝ) * ∫ s in (1243 / 320 : ℝ)..(311 / 80 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1243 / 320 : ℝ)) (b := (311 / 80 : ℝ))
    (l := (3876203390157494572 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (12593 / 10000000 : ℝ))
  have hp : (75781667987994 / 18446744073709551616 : ℝ) ≤ 8 * (12593 / 10000000 : ℝ) *
      (((311 / 80 : ℝ) - (1243 / 320 : ℝ)) * (3876203390157494572 / 18446744073709551616 : ℝ) / denomMax (1243 / 320 : ℝ) (311 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel28 : (74168304003564 / 18446744073709551616 : ℝ) ≤
    8 * (12593 / 10000000 : ℝ) * ∫ s in (311 / 80 : ℝ)..(249 / 64 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (311 / 80 : ℝ)) (b := (249 / 64 : ℝ))
    (l := (3792418985576869070 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (12593 / 10000000 : ℝ))
  have hp : (74168304003564 / 18446744073709551616 : ℝ) ≤ 8 * (12593 / 10000000 : ℝ) *
      (((249 / 64 : ℝ) - (311 / 80 : ℝ)) * (3792418985576869070 / 18446744073709551616 : ℝ) / denomMax (311 / 80 : ℝ) (249 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel29 : (72550099997572 / 18446744073709551616 : ℝ) ≤
    8 * (12593 / 10000000 : ℝ) * ∫ s in (249 / 64 : ℝ)..(623 / 160 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (249 / 64 : ℝ)) (b := (623 / 160 : ℝ))
    (l := (3708435276922437969 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (12593 / 10000000 : ℝ))
  have hp : (72550099997572 / 18446744073709551616 : ℝ) ≤ 8 * (12593 / 10000000 : ℝ) *
      (((623 / 160 : ℝ) - (249 / 64 : ℝ)) * (3708435276922437969 / 18446744073709551616 : ℝ) / denomMax (249 / 64 : ℝ) (623 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel30 : (70927022889985 / 18446744073709551616 : ℝ) ≤
    8 * (12593 / 10000000 : ℝ) * ∫ s in (623 / 160 : ℝ)..(1247 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (623 / 160 : ℝ)) (b := (1247 / 320 : ℝ))
    (l := (3624251276089557295 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (12593 / 10000000 : ℝ))
  have hp : (70927022889985 / 18446744073709551616 : ℝ) ≤ 8 * (12593 / 10000000 : ℝ) *
      (((1247 / 320 : ℝ) - (623 / 160 : ℝ)) * (3624251276089557295 / 18446744073709551616 : ℝ) / denomMax (623 / 160 : ℝ) (1247 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel31 : (69299039353970 / 18446744073709551616 : ℝ) ≤
    8 * (12593 / 10000000 : ℝ) * ∫ s in (1247 / 320 : ℝ)..(39 / 10 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1247 / 320 : ℝ)) (b := (39 / 10 : ℝ))
    (l := (3539865987370012016 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (12593 / 10000000 : ℝ))
  have hp : (69299039353970 / 18446744073709551616 : ℝ) ≤ 8 * (12593 / 10000000 : ℝ) *
      (((39 / 10 : ℝ) - (1247 / 320 : ℝ)) * (3539865987370012016 / 18446744073709551616 : ℝ) / denomMax (1247 / 320 : ℝ) (39 / 10 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

theorem lower : (3001864161246330 / 18446744073709551616 : ℝ) ≤
    8 * (12593 / 10000000 : ℝ) * ∫ s in (19 / 5 : ℝ)..(39 / 10 : ℝ), density s := by
  have he := integral_grid_sum (19 / 5 : ℝ) (39 / 10 : ℝ) 32 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [endpoint, alpha, beta])
  norm_num [Finset.sum_range_succ] at he
  linarith only [panel00, panel01, panel02, panel03, panel04, panel05, panel06, panel07, panel08, panel09, panel10, panel11, panel12, panel13, panel14, panel15, panel16, panel17, panel18, panel19, panel20, panel21, panel22, panel23, panel24, panel25, panel26, panel27, panel28, panel29, panel30, panel31, he]

end Wu18938Campaign.M3.Confirmed.TableRow19
