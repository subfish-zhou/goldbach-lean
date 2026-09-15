import Wu18938Campaign.M3.Confirmed.TableBounds

noncomputable section
namespace Wu18938Campaign.M3.Confirmed.TableRow20
open Real Set MeasureTheory QuarterTrim
open WuSource.SrcSixthGain Wu18938Campaign.M3.Confirmed.TableBounds

private theorem panel00 : (54377915669871 / 18446744073709551616 : ℝ) ≤
    8 * (10120 / 10000000 : ℝ) * ∫ s in (39 / 10 : ℝ)..(1249 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (39 / 10 : ℝ)) (b := (1249 / 320 : ℝ))
    (l := (3455278407371882096 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (10120 / 10000000 : ℝ))
  have hp : (54377915669871 / 18446744073709551616 : ℝ) ≤ 8 * (10120 / 10000000 : ℝ) *
      (((1249 / 320 : ℝ) - (39 / 10 : ℝ)) * (3455278407371882096 / 18446744073709551616 : ℝ) / denomMax (39 / 10 : ℝ) (1249 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel01 : (53061666847489 / 18446744073709551616 : ℝ) ≤
    8 * (10120 / 10000000 : ℝ) * ∫ s in (1249 / 320 : ℝ)..(125 / 32 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1249 / 320 : ℝ)) (b := (125 / 32 : ℝ))
    (l := (3370487524938331252 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (10120 / 10000000 : ℝ))
  have hp : (53061666847489 / 18446744073709551616 : ℝ) ≤ 8 * (10120 / 10000000 : ℝ) *
      (((125 / 32 : ℝ) - (1249 / 320 : ℝ)) * (3370487524938331252 / 18446744073709551616 : ℝ) / denomMax (1249 / 320 : ℝ) (125 / 32 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel02 : (51741393558507 / 18446744073709551616 : ℝ) ≤
    8 * (10120 / 10000000 : ℝ) * ∫ s in (125 / 32 : ℝ)..(1251 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (125 / 32 : ℝ)) (b := (1251 / 320 : ℝ))
    (l := (3285492321065300745 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (10120 / 10000000 : ℝ))
  have hp : (51741393558507 / 18446744073709551616 : ℝ) ≤ 8 * (10120 / 10000000 : ℝ) *
      (((1251 / 320 : ℝ) - (125 / 32 : ℝ)) * (3285492321065300745 / 18446744073709551616 : ℝ) / denomMax (125 / 32 : ℝ) (1251 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel03 : (50417068206345 / 18446744073709551616 : ℝ) ≤
    8 * (10120 / 10000000 : ℝ) * ∫ s in (1251 / 320 : ℝ)..(313 / 80 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1251 / 320 : ℝ)) (b := (313 / 80 : ℝ))
    (l := (3200291768818090238 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (10120 / 10000000 : ℝ))
  have hp : (50417068206345 / 18446744073709551616 : ℝ) ≤ 8 * (10120 / 10000000 : ℝ) *
      (((313 / 80 : ℝ) - (1251 / 320 : ℝ)) * (3200291768818090238 / 18446744073709551616 : ℝ) / denomMax (1251 / 320 : ℝ) (313 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel04 : (49088662985394 / 18446744073709551616 : ℝ) ≤
    8 * (10120 / 10000000 : ℝ) * ∫ s in (313 / 80 : ℝ)..(1253 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (313 / 80 : ℝ)) (b := (1253 / 320 : ℝ))
    (l := (3114884833246807371 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (10120 / 10000000 : ℝ))
  have hp : (49088662985394 / 18446744073709551616 : ℝ) ≤ 8 * (10120 / 10000000 : ℝ) *
      (((1253 / 320 : ℝ) - (313 / 80 : ℝ)) * (3114884833246807371 / 18446744073709551616 : ℝ) / denomMax (313 / 80 : ℝ) (1253 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel05 : (47756149878794 / 18446744073709551616 : ℝ) ≤
    8 * (10120 / 10000000 : ℝ) * ∫ s in (1253 / 320 : ℝ)..(627 / 160 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1253 / 320 : ℝ)) (b := (627 / 160 : ℝ))
    (l := (3029270471300667382 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (10120 / 10000000 : ℝ))
  have hp : (47756149878794 / 18446744073709551616 : ℝ) ≤ 8 * (10120 / 10000000 : ℝ) *
      (((627 / 160 : ℝ) - (1253 / 320 : ℝ)) * (3029270471300667382 / 18446744073709551616 : ℝ) / denomMax (1253 / 320 : ℝ) (627 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel06 : (46419500656185 / 18446744073709551616 : ℝ) ≤
    8 * (10120 / 10000000 : ℝ) * ∫ s in (627 / 160 : ℝ)..(251 / 64 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (627 / 160 : ℝ)) (b := (251 / 64 : ℝ))
    (l := (2943447631741123700 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (10120 / 10000000 : ℝ))
  have hp : (46419500656185 / 18446744073709551616 : ℝ) ≤ 8 * (10120 / 10000000 : ℝ) *
      (((251 / 64 : ℝ) - (627 / 160 : ℝ)) * (2943447631741123700 / 18446744073709551616 : ℝ) / denomMax (627 / 160 : ℝ) (251 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel07 : (45078686871419 / 18446744073709551616 : ℝ) ≤
    8 * (10120 / 10000000 : ℝ) * ∫ s in (251 / 64 : ℝ)..(157 / 40 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (251 / 64 : ℝ)) (b := (157 / 40 : ℝ))
    (l := (2857415255053810100 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (10120 / 10000000 : ℝ))
  have hp : (45078686871419 / 18446744073709551616 : ℝ) ≤ 8 * (10120 / 10000000 : ℝ) *
      (((157 / 40 : ℝ) - (251 / 64 : ℝ)) * (2857415255053810100 / 18446744073709551616 : ℝ) / denomMax (251 / 64 : ℝ) (157 / 40 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel08 : (43733679860257 / 18446744073709551616 : ℝ) ≤
    8 * (10120 / 10000000 : ℝ) * ∫ s in (157 / 40 : ℝ)..(1257 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (157 / 40 : ℝ)) (b := (1257 / 320 : ℝ))
    (l := (2771172273359274595 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (10120 / 10000000 : ℝ))
  have hp : (43733679860257 / 18446744073709551616 : ℝ) ≤ 8 * (10120 / 10000000 : ℝ) *
      (((1257 / 320 : ℝ) - (157 / 40 : ℝ)) * (2771172273359274595 / 18446744073709551616 : ℝ) / denomMax (157 / 40 : ℝ) (1257 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel09 : (42384450738020 / 18446744073709551616 : ℝ) ≤
    8 * (10120 / 10000000 : ℝ) * ∫ s in (1257 / 320 : ℝ)..(629 / 160 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1257 / 320 : ℝ)) (b := (629 / 160 : ℝ))
    (l := (2684717610322484890 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (10120 / 10000000 : ℝ))
  have hp : (42384450738020 / 18446744073709551616 : ℝ) ≤ 8 * (10120 / 10000000 : ℝ) *
      (((629 / 160 : ℝ) - (1257 / 320 : ℝ)) * (2684717610322484890 / 18446744073709551616 : ℝ) / denomMax (1257 / 320 : ℝ) (629 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel10 : (41030970397221 / 18446744073709551616 : ℝ) ≤
    8 * (10120 / 10000000 : ℝ) * ∫ s in (629 / 160 : ℝ)..(1259 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (629 / 160 : ℝ)) (b := (1259 / 320 : ℝ))
    (l := (2598050181061084780 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (10120 / 10000000 : ℝ))
  have hp : (41030970397221 / 18446744073709551616 : ℝ) ≤ 8 * (10120 / 10000000 : ℝ) *
      (((1259 / 320 : ℝ) - (629 / 160 : ℝ)) * (2598050181061084780 / 18446744073709551616 : ℝ) / denomMax (629 / 160 : ℝ) (1259 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel11 : (39673209505160 / 18446744073709551616 : ℝ) ≤
    8 * (10120 / 10000000 : ℝ) * ∫ s in (1259 / 320 : ℝ)..(63 / 16 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1259 / 320 : ℝ)) (b := (63 / 16 : ℝ))
    (l := (2511168892052380505 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (10120 / 10000000 : ℝ))
  have hp : (39673209505160 / 18446744073709551616 : ℝ) ≤ 8 * (10120 / 10000000 : ℝ) *
      (((63 / 16 : ℝ) - (1259 / 320 : ℝ)) * (2511168892052380505 / 18446744073709551616 : ℝ) / denomMax (1259 / 320 : ℝ) (63 / 16 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel12 : (38311138501489 / 18446744073709551616 : ℝ) ≤
    8 * (10120 / 10000000 : ℝ) * ∫ s in (63 / 16 : ℝ)..(1261 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (63 / 16 : ℝ)) (b := (1261 / 320 : ℝ))
    (l := (2424072641039035631 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (10120 / 10000000 : ℝ))
  have hp : (38311138501489 / 18446744073709551616 : ℝ) ≤ 8 * (10120 / 10000000 : ℝ) *
      (((1261 / 320 : ℝ) - (63 / 16 : ℝ)) * (2424072641039035631 / 18446744073709551616 : ℝ) / denomMax (63 / 16 : ℝ) (1261 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel13 : (36944727595743 / 18446744073709551616 : ℝ) ≤
    8 * (10120 / 10000000 : ℝ) * ∫ s in (1261 / 320 : ℝ)..(631 / 160 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1261 / 320 : ℝ)) (b := (631 / 160 : ℝ))
    (l := (2336760316933452627 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (10120 / 10000000 : ℝ))
  have hp : (36944727595743 / 18446744073709551616 : ℝ) ≤ 8 * (10120 / 10000000 : ℝ) *
      (((631 / 160 : ℝ) - (1261 / 320 : ℝ)) * (2336760316933452627 / 18446744073709551616 : ℝ) / denomMax (1261 / 320 : ℝ) (631 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel14 : (35573946764841 / 18446744073709551616 : ℝ) ≤
    8 * (10120 / 10000000 : ℝ) * ∫ s in (631 / 160 : ℝ)..(1263 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (631 / 160 : ℝ)) (b := (1263 / 320 : ℝ))
    (l := (2249230799720818834 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (10120 / 10000000 : ℝ))
  have hp : (35573946764841 / 18446744073709551616 : ℝ) ≤ 8 * (10120 / 10000000 : ℝ) *
      (((1263 / 320 : ℝ) - (631 / 160 : ℝ)) * (2249230799720818834 / 18446744073709551616 : ℝ) / denomMax (631 / 160 : ℝ) (1263 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel15 : (34198765750551 / 18446744073709551616 : ℝ) ≤
    8 * (10120 / 10000000 : ℝ) * ∫ s in (1263 / 320 : ℝ)..(79 / 20 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1263 / 320 : ℝ)) (b := (79 / 20 : ℝ))
    (l := (2161482960360794124 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (10120 / 10000000 : ℝ))
  have hp : (34198765750551 / 18446744073709551616 : ℝ) ≤ 8 * (10120 / 10000000 : ℝ) *
      (((79 / 20 : ℝ) - (1263 / 320 : ℝ)) * (2161482960360794124 / 18446744073709551616 : ℝ) / denomMax (1263 / 320 : ℝ) (79 / 20 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel16 : (32819154056921 / 18446744073709551616 : ℝ) ≤
    8 * (10120 / 10000000 : ℝ) * ∫ s in (79 / 20 : ℝ)..(253 / 64 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (79 / 20 : ℝ)) (b := (253 / 64 : ℝ))
    (l := (2073515660687817039 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (10120 / 10000000 : ℝ))
  have hp : (32819154056921 / 18446744073709551616 : ℝ) ≤ 8 * (10120 / 10000000 : ℝ) *
      (((253 / 64 : ℝ) - (79 / 20 : ℝ)) * (2073515660687817039 / 18446744073709551616 : ℝ) / denomMax (79 / 20 : ℝ) (253 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel17 : (31435080947678 / 18446744073709551616 : ℝ) ≤
    8 * (10120 / 10000000 : ℝ) * ∫ s in (253 / 64 : ℝ)..(633 / 160 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (253 / 64 : ℝ)) (b := (633 / 160 : ℝ))
    (l := (1985327753310005782 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (10120 / 10000000 : ℝ))
  have hp : (31435080947678 / 18446744073709551616 : ℝ) ≤ 8 * (10120 / 10000000 : ℝ) *
      (((633 / 160 : ℝ) - (253 / 64 : ℝ)) * (1985327753310005782 / 18446744073709551616 : ℝ) / denomMax (253 / 64 : ℝ) (633 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel18 : (30046515443593 / 18446744073709551616 : ℝ) ≤
    8 * (10120 / 10000000 : ℝ) * ∫ s in (633 / 160 : ℝ)..(1267 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (633 / 160 : ℝ)) (b := (1267 / 320 : ℝ))
    (l := (1896918081506629918 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (10120 / 10000000 : ℝ))
  have hp : (30046515443593 / 18446744073709551616 : ℝ) ≤ 8 * (10120 / 10000000 : ℝ) *
      (((1267 / 320 : ℝ) - (633 / 160 : ℝ)) * (1896918081506629918 / 18446744073709551616 : ℝ) / denomMax (633 / 160 : ℝ) (1267 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel19 : (28653426319800 / 18446744073709551616 : ℝ) ≤
    8 * (10120 / 10000000 : ℝ) * ∫ s in (1267 / 320 : ℝ)..(317 / 80 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1267 / 320 : ℝ)) (b := (317 / 80 : ℝ))
    (l := (1808285479124128175 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (10120 / 10000000 : ℝ))
  have hp : (28653426319800 / 18446744073709551616 : ℝ) ≤ 8 * (10120 / 10000000 : ℝ) *
      (((317 / 80 : ℝ) - (1267 / 320 : ℝ)) * (1808285479124128175 / 18446744073709551616 : ℝ) / denomMax (1267 / 320 : ℝ) (317 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel20 : (27255782103094 / 18446744073709551616 : ℝ) ≤
    8 * (10120 / 10000000 : ℝ) * ∫ s in (317 / 80 : ℝ)..(1269 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (317 / 80 : ℝ)) (b := (1269 / 320 : ℝ))
    (l := (1719428770470647220 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (10120 / 10000000 : ℝ))
  have hp : (27255782103094 / 18446744073709551616 : ℝ) ≤ 8 * (10120 / 10000000 : ℝ) *
      (((1269 / 320 : ℝ) - (317 / 80 : ℝ)) * (1719428770470647220 / 18446744073709551616 : ℝ) / denomMax (317 / 80 : ℝ) (1269 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel21 : (25853551069184 / 18446744073709551616 : ℝ) ≤
    8 * (10120 / 10000000 : ℝ) * ∫ s in (1269 / 320 : ℝ)..(127 / 32 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1269 / 320 : ℝ)) (b := (127 / 32 : ℝ))
    (l := (1630346770209075785 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (10120 / 10000000 : ℝ))
  have hp : (25853551069184 / 18446744073709551616 : ℝ) ≤ 8 * (10120 / 10000000 : ℝ) *
      (((127 / 32 : ℝ) - (1269 / 320 : ℝ)) * (1630346770209075785 / 18446744073709551616 : ℝ) / denomMax (1269 / 320 : ℝ) (127 / 32 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel22 : (24446701239902 / 18446744073709551616 : ℝ) ≤
    8 * (10120 / 10000000 : ℝ) * ∫ s in (127 / 32 : ℝ)..(1271 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (127 / 32 : ℝ)) (b := (1271 / 320 : ℝ))
    (l := (1541038283248548002 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (10120 / 10000000 : ℝ))
  have hp : (24446701239902 / 18446744073709551616 : ℝ) ≤ 8 * (10120 / 10000000 : ℝ) *
      (((1271 / 320 : ℝ) - (127 / 32 : ℝ)) * (1541038283248548002 / 18446744073709551616 : ℝ) / denomMax (127 / 32 : ℝ) (1271 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel23 : (23035200380391 / 18446744073709551616 : ℝ) ≤
    8 * (10120 / 10000000 : ℝ) * ∫ s in (1271 / 320 : ℝ)..(159 / 40 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1271 / 320 : ℝ)) (b := (159 / 40 : ℝ))
    (l := (1451502104634389230 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (10120 / 10000000 : ℝ))
  have hp : (23035200380391 / 18446744073709551616 : ℝ) ≤ 8 * (10120 / 10000000 : ℝ) *
      (((159 / 40 : ℝ) - (1271 / 320 : ℝ)) * (1451502104634389230 / 18446744073709551616 : ℝ) / denomMax (1271 / 320 : ℝ) (159 / 40 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel24 : (21619015996237 / 18446744073709551616 : ℝ) ≤
    8 * (10120 / 10000000 : ℝ) * ∫ s in (159 / 40 : ℝ)..(1273 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (159 / 40 : ℝ)) (b := (1273 / 320 : ℝ))
    (l := (1361737019436477160 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (10120 / 10000000 : ℝ))
  have hp : (21619015996237 / 18446744073709551616 : ℝ) ≤ 8 * (10120 / 10000000 : ℝ) *
      (((1273 / 320 : ℝ) - (159 / 40 : ℝ)) * (1361737019436477160 / 18446744073709551616 : ℝ) / denomMax (159 / 40 : ℝ) (1273 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel25 : (20198115330571 / 18446744073709551616 : ℝ) ≤
    8 * (10120 / 10000000 : ℝ) * ∫ s in (1273 / 320 : ℝ)..(637 / 160 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1273 / 320 : ℝ)) (b := (637 / 160 : ℝ))
    (l := (1271741802635990396 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (10120 / 10000000 : ℝ))
  have hp : (20198115330571 / 18446744073709551616 : ℝ) ≤ 8 * (10120 / 10000000 : ℝ) *
      (((637 / 160 : ℝ) - (1273 / 320 : ℝ)) * (1271741802635990396 / 18446744073709551616 : ℝ) / denomMax (1273 / 320 : ℝ) (637 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel26 : (18772465361131 / 18446744073709551616 : ℝ) ≤
    8 * (10120 / 10000000 : ℝ) * ∫ s in (637 / 160 : ℝ)..(255 / 64 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (637 / 160 : ℝ)) (b := (255 / 64 : ℝ))
    (l := (1181515219010516112 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (10120 / 10000000 : ℝ))
  have hp : (18772465361131 / 18446744073709551616 : ℝ) ≤ 8 * (10120 / 10000000 : ℝ) *
      (((255 / 64 : ℝ) - (637 / 160 : ℝ)) * (1181515219010516112 / 18446744073709551616 : ℝ) / denomMax (637 / 160 : ℝ) (255 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel27 : (17342032797278 / 18446744073709551616 : ℝ) ≤
    8 * (10120 / 10000000 : ℝ) * ∫ s in (255 / 64 : ℝ)..(319 / 80 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (255 / 64 : ℝ)) (b := (319 / 80 : ℝ))
    (l := (1091056023017487861 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (10120 / 10000000 : ℝ))
  have hp : (17342032797278 / 18446744073709551616 : ℝ) ≤ 8 * (10120 / 10000000 : ℝ) *
      (((319 / 80 : ℝ) - (255 / 64 : ℝ)) * (1091056023017487861 / 18446744073709551616 : ℝ) / denomMax (255 / 64 : ℝ) (319 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel28 : (15906784076974 / 18446744073709551616 : ℝ) ≤
    8 * (10120 / 10000000 : ℝ) * ∫ s in (319 / 80 : ℝ)..(1277 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (319 / 80 : ℝ)) (b := (1277 / 320 : ℝ))
    (l := (1000362958675923929 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (10120 / 10000000 : ℝ))
  have hp : (15906784076974 / 18446744073709551616 : ℝ) ≤ 8 * (10120 / 10000000 : ℝ) *
      (((1277 / 320 : ℝ) - (319 / 80 : ℝ)) * (1000362958675923929 / 18446744073709551616 : ℝ) / denomMax (319 / 80 : ℝ) (1277 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel29 : (14466685363720 / 18446744073709551616 : ℝ) ≤
    8 * (10120 / 10000000 : ℝ) * ∫ s in (1277 / 320 : ℝ)..(639 / 160 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1277 / 320 : ℝ)) (b := (639 / 160 : ℝ))
    (l := (909434759446436072 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (10120 / 10000000 : ℝ))
  have hp : (14466685363720 / 18446744073709551616 : ℝ) ≤ 8 * (10120 / 10000000 : ℝ) *
      (((639 / 160 : ℝ) - (1277 / 320 : ℝ)) * (909434759446436072 / 18446744073709551616 : ℝ) / denomMax (1277 / 320 : ℝ) (639 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel30 : (13021702543444 / 18446744073709551616 : ℝ) ≤
    8 * (10120 / 10000000 : ℝ) * ∫ s in (639 / 160 : ℝ)..(1279 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (639 / 160 : ℝ)) (b := (1279 / 320 : ℝ))
    (l := (818270148109477815 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (10120 / 10000000 : ℝ))
  have hp : (13021702543444 / 18446744073709551616 : ℝ) ≤ 8 * (10120 / 10000000 : ℝ) *
      (((1279 / 320 : ℝ) - (639 / 160 : ℝ)) * (818270148109477815 / 18446744073709551616 : ℝ) / denomMax (639 / 160 : ℝ) (1279 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel31 : (11571801221354 / 18446744073709551616 : ℝ) ≤
    8 * (10120 / 10000000 : ℝ) * ∫ s in (1279 / 320 : ℝ)..(4 / 1 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1279 / 320 : ℝ)) (b := (4 / 1 : ℝ))
    (l := (726867836641800842 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (10120 / 10000000 : ℝ))
  have hp : (11571801221354 / 18446744073709551616 : ℝ) ≤ 8 * (10120 / 10000000 : ℝ) *
      (((4 / 1 : ℝ) - (1279 / 320 : ℝ)) * (726867836641800842 / 18446744073709551616 : ℝ) / denomMax (1279 / 320 : ℝ) (4 / 1 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

theorem lower : (1066235948038558 / 18446744073709551616 : ℝ) ≤
    8 * (10120 / 10000000 : ℝ) * ∫ s in (39 / 10 : ℝ)..(4 / 1 : ℝ), density s := by
  have he := integral_grid_sum (39 / 10 : ℝ) (4 / 1 : ℝ) 32 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [endpoint, alpha, beta])
  norm_num [Finset.sum_range_succ] at he
  linarith only [panel00, panel01, panel02, panel03, panel04, panel05, panel06, panel07, panel08, panel09, panel10, panel11, panel12, panel13, panel14, panel15, panel16, panel17, panel18, panel19, panel20, panel21, panel22, panel23, panel24, panel25, panel26, panel27, panel28, panel29, panel30, panel31, he]

end Wu18938Campaign.M3.Confirmed.TableRow20
