import Wu18938Campaign.M3.Confirmed.TableBounds

noncomputable section
namespace Wu18938Campaign.M3.Confirmed.TableRow07
open Real Set MeasureTheory QuarterTrim
open WuSource.SrcSixthGain Wu18938Campaign.M3.Confirmed.TableBounds

private theorem panel00 : (2058585119850672 / 18446744073709551616 : ℝ) ≤
    8 * (100756 / 10000000 : ℝ) * ∫ s in (27 / 10 : ℝ)..(173 / 64 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (27 / 10 : ℝ)) (b := (173 / 64 : ℝ))
    (l := (13091300965562494855 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (100756 / 10000000 : ℝ))
  have hp : (2058585119850672 / 18446744073709551616 : ℝ) ≤ 8 * (100756 / 10000000 : ℝ) *
      (((173 / 64 : ℝ) - (27 / 10 : ℝ)) * (13091300965562494855 / 18446744073709551616 : ℝ) / denomMax (27 / 10 : ℝ) (173 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel01 : (2058655281034122 / 18446744073709551616 : ℝ) ≤
    8 * (100756 / 10000000 : ℝ) * ∫ s in (173 / 64 : ℝ)..(433 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (173 / 64 : ℝ)) (b := (433 / 160 : ℝ))
    (l := (13096464945105791765 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (100756 / 10000000 : ℝ))
  have hp : (2058655281034122 / 18446744073709551616 : ℝ) ≤ 8 * (100756 / 10000000 : ℝ) *
      (((433 / 160 : ℝ) - (173 / 64 : ℝ)) * (13096464945105791765 / 18446744073709551616 : ℝ) / denomMax (173 / 64 : ℝ) (433 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel02 : (2058731131779252 / 18446744073709551616 : ℝ) ≤
    8 * (100756 / 10000000 : ℝ) * ∫ s in (433 / 160 : ℝ)..(867 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (433 / 160 : ℝ)) (b := (867 / 320 : ℝ))
    (l := (13101641395306445890 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (100756 / 10000000 : ℝ))
  have hp : (2058731131779252 / 18446744073709551616 : ℝ) ≤ 8 * (100756 / 10000000 : ℝ) *
      (((867 / 320 : ℝ) - (433 / 160 : ℝ)) * (13101641395306445890 / 18446744073709551616 : ℝ) / denomMax (433 / 160 : ℝ) (867 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel03 : (2058812673527334 / 18446744073709551616 : ℝ) ≤
    8 * (100756 / 10000000 : ℝ) * ∫ s in (867 / 320 : ℝ)..(217 / 80 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (867 / 320 : ℝ)) (b := (217 / 80 : ℝ))
    (l := (13106830361597296474 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (100756 / 10000000 : ℝ))
  have hp : (2058812673527334 / 18446744073709551616 : ℝ) ≤ 8 * (100756 / 10000000 : ℝ) *
      (((217 / 80 : ℝ) - (867 / 320 : ℝ)) * (13106830361597296474 / 18446744073709551616 : ℝ) / denomMax (867 / 320 : ℝ) (217 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel04 : (2058899907815090 / 18446744073709551616 : ℝ) ≤
    8 * (100756 / 10000000 : ℝ) * ∫ s in (217 / 80 : ℝ)..(869 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (217 / 80 : ℝ)) (b := (869 / 320 : ℝ))
    (l := (13112031889633132696 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (100756 / 10000000 : ℝ))
  have hp : (2058899907815090 / 18446744073709551616 : ℝ) ≤ 8 * (100756 / 10000000 : ℝ) *
      (((869 / 320 : ℝ) - (217 / 80 : ℝ)) * (13112031889633132696 / 18446744073709551616 : ℝ) / denomMax (217 / 80 : ℝ) (869 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel05 : (2058992836274768 / 18446744073709551616 : ℝ) ≤
    8 * (100756 / 10000000 : ℝ) * ∫ s in (869 / 320 : ℝ)..(87 / 32 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (869 / 320 : ℝ)) (b := (87 / 32 : ℝ))
    (l := (13117246025292056647 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (100756 / 10000000 : ℝ))
  have hp : (2058992836274768 / 18446744073709551616 : ℝ) ≤ 8 * (100756 / 10000000 : ℝ) *
      (((87 / 32 : ℝ) - (869 / 320 : ℝ)) * (13117246025292056647 / 18446744073709551616 : ℝ) / denomMax (869 / 320 : ℝ) (87 / 32 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel06 : (2059091460634215 / 18446744073709551616 : ℝ) ≤
    8 * (100756 / 10000000 : ℝ) * ∫ s in (87 / 32 : ℝ)..(871 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (87 / 32 : ℝ)) (b := (871 / 320 : ℝ))
    (l := (13122472814676856399 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (100756 / 10000000 : ℝ))
  have hp : (2059091460634215 / 18446744073709551616 : ℝ) ≤ 8 * (100756 / 10000000 : ℝ) *
      (((871 / 320 : ℝ) - (87 / 32 : ℝ)) * (13122472814676856399 / 18446744073709551616 : ℝ) / denomMax (87 / 32 : ℝ) (871 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel07 : (2059195782716959 / 18446744073709551616 : ℝ) ≤
    8 * (100756 / 10000000 : ℝ) * ∫ s in (871 / 320 : ℝ)..(109 / 40 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (871 / 320 : ℝ)) (b := (109 / 40 : ℝ))
    (l := (13127712304116389271 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (100756 / 10000000 : ℝ))
  have hp : (2059195782716959 / 18446744073709551616 : ℝ) ≤ 8 * (100756 / 10000000 : ℝ) *
      (((109 / 40 : ℝ) - (871 / 320 : ℝ)) * (13127712304116389271 / 18446744073709551616 : ℝ) / denomMax (871 / 320 : ℝ) (109 / 40 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel08 : (2059305804442292 / 18446744073709551616 : ℝ) ≤
    8 * (100756 / 10000000 : ℝ) * ∫ s in (109 / 40 : ℝ)..(873 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (109 / 40 : ℝ)) (b := (873 / 320 : ℝ))
    (l := (13132964540166975364 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (100756 / 10000000 : ℝ))
  have hp : (2059305804442292 / 18446744073709551616 : ℝ) ≤ 8 * (100756 / 10000000 : ℝ) *
      (((873 / 320 : ℝ) - (109 / 40 : ℝ)) * (13132964540166975364 / 18446744073709551616 : ℝ) / denomMax (109 / 40 : ℝ) (873 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel09 : (2059421527825360 / 18446744073709551616 : ℝ) ≤
    8 * (100756 / 10000000 : ℝ) * ∫ s in (873 / 320 : ℝ)..(437 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (873 / 320 : ℝ)) (b := (437 / 160 : ℝ))
    (l := (13138229569613801464 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (100756 / 10000000 : ℝ))
  have hp : (2059421527825360 / 18446744073709551616 : ℝ) ≤ 8 * (100756 / 10000000 : ℝ) *
      (((437 / 160 : ℝ) - (873 / 320 : ℝ)) * (13138229569613801464 / 18446744073709551616 : ℝ) / denomMax (873 / 320 : ℝ) (437 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel10 : (2059542954977255 / 18446744073709551616 : ℝ) ≤
    8 * (100756 / 10000000 : ℝ) * ∫ s in (437 / 160 : ℝ)..(175 / 64 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (437 / 160 : ℝ)) (b := (175 / 64 : ℝ))
    (l := (13143507439472335400 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (100756 / 10000000 : ℝ))
  have hp : (2059542954977255 / 18446744073709551616 : ℝ) ≤ 8 * (100756 / 10000000 : ℝ) *
      (((175 / 64 : ℝ) - (437 / 160 : ℝ)) * (13143507439472335400 / 18446744073709551616 : ℝ) / denomMax (437 / 160 : ℝ) (175 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel11 : (2059670088105111 / 18446744073709551616 : ℝ) ≤
    8 * (100756 / 10000000 : ℝ) * ∫ s in (175 / 64 : ℝ)..(219 / 80 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (175 / 64 : ℝ)) (b := (219 / 80 : ℝ))
    (l := (13148798196989750953 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (100756 / 10000000 : ℝ))
  have hp : (2059670088105111 / 18446744073709551616 : ℝ) ≤ 8 * (100756 / 10000000 : ℝ) *
      (((219 / 80 : ℝ) - (175 / 64 : ℝ)) * (13148798196989750953 / 18446744073709551616 : ℝ) / denomMax (175 / 64 : ℝ) (219 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel12 : (2059802929512207 / 18446744073709551616 : ℝ) ≤
    8 * (100756 / 10000000 : ℝ) * ∫ s in (219 / 80 : ℝ)..(877 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (219 / 80 : ℝ)) (b := (877 / 320 : ℝ))
    (l := (13154101889646363397 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (100756 / 10000000 : ℝ))
  have hp : (2059802929512207 / 18446744073709551616 : ℝ) ≤ 8 * (100756 / 10000000 : ℝ) *
      (((877 / 320 : ℝ) - (219 / 80 : ℝ)) * (13154101889646363397 / 18446744073709551616 : ℝ) / denomMax (219 / 80 : ℝ) (877 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel13 : (2059941481598068 / 18446744073709551616 : ℝ) ≤
    8 * (100756 / 10000000 : ℝ) * ∫ s in (877 / 320 : ℝ)..(439 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (877 / 320 : ℝ)) (b := (439 / 160 : ℝ))
    (l := (13159418565157075784 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (100756 / 10000000 : ℝ))
  have hp : (2059941481598068 / 18446744073709551616 : ℝ) ≤ 8 * (100756 / 10000000 : ℝ) *
      (((439 / 160 : ℝ) - (877 / 320 : ℝ)) * (13159418565157075784 / 18446744073709551616 : ℝ) / denomMax (877 / 320 : ℝ) (439 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel14 : (2060085746858578 / 18446744073709551616 : ℝ) ≤
    8 * (100756 / 10000000 : ℝ) * ∫ s in (439 / 160 : ℝ)..(879 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (439 / 160 : ℝ)) (b := (879 / 320 : ℝ))
    (l := (13164748271472836041 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (100756 / 10000000 : ℝ))
  have hp : (2060085746858578 / 18446744073709551616 : ℝ) ≤ 8 * (100756 / 10000000 : ℝ) *
      (((879 / 320 : ℝ) - (439 / 160 : ℝ)) * (13164748271472836041 / 18446744073709551616 : ℝ) / denomMax (439 / 160 : ℝ) (879 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel15 : (2060235727886090 / 18446744073709551616 : ℝ) ≤
    8 * (100756 / 10000000 : ℝ) * ∫ s in (879 / 320 : ℝ)..(11 / 4 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (879 / 320 : ℝ)) (b := (11 / 4 : ℝ))
    (l := (13170091056782105008 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (100756 / 10000000 : ℝ))
  have hp : (2060235727886090 / 18446744073709551616 : ℝ) ≤ 8 * (100756 / 10000000 : ℝ) *
      (((11 / 4 : ℝ) - (879 / 320 : ℝ)) * (13170091056782105008 / 18446744073709551616 : ℝ) / denomMax (879 / 320 : ℝ) (11 / 4 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel16 : (2060391427369547 / 18446744073709551616 : ℝ) ≤
    8 * (100756 / 10000000 : ℝ) * ∫ s in (11 / 4 : ℝ)..(881 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (11 / 4 : ℝ)) (b := (881 / 320 : ℝ))
    (l := (13175446969512335472 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (100756 / 10000000 : ℝ))
  have hp : (2060391427369547 / 18446744073709551616 : ℝ) ≤ 8 * (100756 / 10000000 : ℝ) *
      (((881 / 320 : ℝ) - (11 / 4 : ℝ)) * (13175446969512335472 / 18446744073709551616 : ℝ) / denomMax (11 / 4 : ℝ) (881 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel17 : (2060552848094597 / 18446744073709551616 : ℝ) ≤
    8 * (100756 / 10000000 : ℝ) * ∫ s in (881 / 320 : ℝ)..(441 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (881 / 320 : ℝ)) (b := (441 / 160 : ℝ))
    (l := (13180816058331462338 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (100756 / 10000000 : ℝ))
  have hp : (2060552848094597 / 18446744073709551616 : ℝ) ≤ 8 * (100756 / 10000000 : ℝ) *
      (((441 / 160 : ℝ) - (881 / 320 : ℝ)) * (13180816058331462338 / 18446744073709551616 : ℝ) / denomMax (881 / 320 : ℝ) (441 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel18 : (2060719992943727 / 18446744073709551616 : ℝ) ≤
    8 * (100756 / 10000000 : ℝ) * ∫ s in (441 / 160 : ℝ)..(883 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (441 / 160 : ℝ)) (b := (883 / 320 : ℝ))
    (l := (13186198372149403995 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (100756 / 10000000 : ℝ))
  have hp : (2060719992943727 / 18446744073709551616 : ℝ) ≤ 8 * (100756 / 10000000 : ℝ) *
      (((883 / 320 : ℝ) - (441 / 160 : ℝ)) * (13186198372149403995 / 18446744073709551616 : ℝ) / denomMax (441 / 160 : ℝ) (883 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel19 : (2060892864896385 / 18446744073709551616 : ℝ) ≤
    8 * (100756 / 10000000 : ℝ) * ∫ s in (883 / 320 : ℝ)..(221 / 80 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (883 / 320 : ℝ)) (b := (221 / 80 : ℝ))
    (l := (13191593960119575004 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (100756 / 10000000 : ℝ))
  have hp : (2060892864896385 / 18446744073709551616 : ℝ) ≤ 8 * (100756 / 10000000 : ℝ) *
      (((221 / 80 : ℝ) - (883 / 320 : ℝ)) * (13191593960119575004 / 18446744073709551616 : ℝ) / denomMax (883 / 320 : ℝ) (221 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel20 : (2061071467029120 / 18446744073709551616 : ℝ) ≤
    8 * (100756 / 10000000 : ℝ) * ∫ s in (221 / 80 : ℝ)..(177 / 64 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (221 / 80 : ℝ)) (b := (177 / 64 : ℝ))
    (l := (13197002871640410200 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (100756 / 10000000 : ℝ))
  have hp : (2061071467029120 / 18446744073709551616 : ℝ) ≤ 8 * (100756 / 10000000 : ℝ) *
      (((177 / 64 : ℝ) - (221 / 80 : ℝ)) * (13197002871640410200 / 18446744073709551616 : ℝ) / denomMax (221 / 80 : ℝ) (177 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel21 : (2061255802515716 / 18446744073709551616 : ℝ) ≤
    8 * (100756 / 10000000 : ℝ) * ∫ s in (177 / 64 : ℝ)..(443 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (177 / 64 : ℝ)) (b := (443 / 160 : ℝ))
    (l := (13202425156356900295 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (100756 / 10000000 : ℝ))
  have hp : (2061255802515716 / 18446744073709551616 : ℝ) ≤ 8 * (100756 / 10000000 : ℝ) *
      (((443 / 160 : ℝ) - (177 / 64 : ℝ)) * (13202425156356900295 / 18446744073709551616 : ℝ) / denomMax (177 / 64 : ℝ) (443 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel22 : (2061445874627334 / 18446744073709551616 : ℝ) ≤
    8 * (100756 / 10000000 : ℝ) * ∫ s in (443 / 160 : ℝ)..(887 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (443 / 160 : ℝ)) (b := (887 / 320 : ℝ))
    (l := (13207860864162139111 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (100756 / 10000000 : ℝ))
  have hp : (2061445874627334 / 18446744073709551616 : ℝ) ≤ 8 * (100756 / 10000000 : ℝ) *
      (((887 / 320 : ℝ) - (443 / 160 : ℝ)) * (13207860864162139111 / 18446744073709551616 : ℝ) / denomMax (443 / 160 : ℝ) (887 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel23 : (2061641686732665 / 18446744073709551616 : ℝ) ≤
    8 * (100756 / 10000000 : ℝ) * ∫ s in (887 / 320 : ℝ)..(111 / 40 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (887 / 320 : ℝ)) (b := (111 / 40 : ℝ))
    (l := (13213310045198882518 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (100756 / 10000000 : ℝ))
  have hp : (2061641686732665 / 18446744073709551616 : ℝ) ≤ 8 * (100756 / 10000000 : ℝ) *
      (((111 / 40 : ℝ) - (887 / 320 : ℝ)) * (13213310045198882518 / 18446744073709551616 : ℝ) / denomMax (887 / 320 : ℝ) (111 / 40 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel24 : (2061843242298072 / 18446744073709551616 : ℝ) ≤
    8 * (100756 / 10000000 : ℝ) * ∫ s in (111 / 40 : ℝ)..(889 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (111 / 40 : ℝ)) (b := (889 / 320 : ℝ))
    (l := (13218772749861119206 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (100756 / 10000000 : ℝ))
  have hp : (2061843242298072 / 18446744073709551616 : ℝ) ≤ 8 * (100756 / 10000000 : ℝ) *
      (((889 / 320 : ℝ) - (111 / 40 : ℝ)) * (13218772749861119206 / 18446744073709551616 : ℝ) / denomMax (111 / 40 : ℝ) (889 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel25 : (2062050544887749 / 18446744073709551616 : ℝ) ≤
    8 * (100756 / 10000000 : ℝ) * ∫ s in (889 / 320 : ℝ)..(89 / 32 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (889 / 320 : ℝ)) (b := (89 / 32 : ℝ))
    (l := (13224249028795653372 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (100756 / 10000000 : ℝ))
  have hp : (2062050544887749 / 18446744073709551616 : ℝ) ≤ 8 * (100756 / 10000000 : ℝ) *
      (((89 / 32 : ℝ) - (889 / 320 : ℝ)) * (13224249028795653372 / 18446744073709551616 : ℝ) / denomMax (889 / 320 : ℝ) (89 / 32 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel26 : (2062263598163884 / 18446744073709551616 : ℝ) ≤
    8 * (100756 / 10000000 : ℝ) * ∫ s in (89 / 32 : ℝ)..(891 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (89 / 32 : ℝ)) (b := (891 / 320 : ℝ))
    (l := (13229738932903699455 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (100756 / 10000000 : ℝ))
  have hp : (2062263598163884 / 18446744073709551616 : ℝ) ≤ 8 * (100756 / 10000000 : ℝ) *
      (((891 / 320 : ℝ) - (89 / 32 : ℝ)) * (13229738932903699455 / 18446744073709551616 : ℝ) / denomMax (89 / 32 : ℝ) (891 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel27 : (2062482405886815 / 18446744073709551616 : ℝ) ≤
    8 * (100756 / 10000000 : ℝ) * ∫ s in (891 / 320 : ℝ)..(223 / 80 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (891 / 320 : ℝ)) (b := (223 / 80 : ℝ))
    (l := (13235242513342488999 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (100756 / 10000000 : ℝ))
  have hp : (2062482405886815 / 18446744073709551616 : ℝ) ≤ 8 * (100756 / 10000000 : ℝ) *
      (((223 / 80 : ℝ) - (891 / 320 : ℝ)) * (13235242513342488999 / 18446744073709551616 : ℝ) / denomMax (891 / 320 : ℝ) (223 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel28 : (2062706971915204 / 18446744073709551616 : ℝ) ≤
    8 * (100756 / 10000000 : ℝ) * ∫ s in (223 / 80 : ℝ)..(893 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (223 / 80 : ℝ)) (b := (893 / 320 : ℝ))
    (l := (13240759821526889770 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (100756 / 10000000 : ℝ))
  have hp : (2062706971915204 / 18446744073709551616 : ℝ) ≤ 8 * (100756 / 10000000 : ℝ) *
      (((893 / 320 : ℝ) - (223 / 80 : ℝ)) * (13240759821526889770 / 18446744073709551616 : ℝ) / denomMax (223 / 80 : ℝ) (893 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel29 : (2062937300206206 / 18446744073709551616 : ℝ) ≤
    8 * (100756 / 10000000 : ℝ) * ∫ s in (893 / 320 : ℝ)..(447 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (893 / 320 : ℝ)) (b := (447 / 160 : ℝ))
    (l := (13246290909131037240 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (100756 / 10000000 : ℝ))
  have hp : (2062937300206206 / 18446744073709551616 : ℝ) ≤ 8 * (100756 / 10000000 : ℝ) *
      (((447 / 160 : ℝ) - (893 / 320 : ℝ)) * (13246290909131037240 / 18446744073709551616 : ℝ) / denomMax (893 / 320 : ℝ) (447 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel30 : (2063173394815646 / 18446744073709551616 : ℝ) ≤
    8 * (100756 / 10000000 : ℝ) * ∫ s in (447 / 160 : ℝ)..(179 / 64 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (447 / 160 : ℝ)) (b := (179 / 64 : ℝ))
    (l := (13251835828089978527 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (100756 / 10000000 : ℝ))
  have hp : (2063173394815646 / 18446744073709551616 : ℝ) ≤ 8 * (100756 / 10000000 : ℝ) *
      (((179 / 64 : ℝ) - (447 / 160 : ℝ)) * (13251835828089978527 / 18446744073709551616 : ℝ) / denomMax (447 / 160 : ℝ) (179 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel31 : (2063415259898201 / 18446744073709551616 : ℝ) ≤
    8 * (100756 / 10000000 : ℝ) * ∫ s in (179 / 64 : ℝ)..(14 / 5 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (179 / 64 : ℝ)) (b := (14 / 5 : ℝ))
    (l := (13257394630601328925 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (100756 / 10000000 : ℝ))
  have hp : (2063415259898201 / 18446744073709551616 : ℝ) ≤ 8 * (100756 / 10000000 : ℝ) *
      (((14 / 5 : ℝ) - (179 / 64 : ℝ)) * (13257394630601328925 / 18446744073709551616 : ℝ) / denomMax (179 / 64 : ℝ) (14 / 5 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

theorem lower : (65937815137118241 / 18446744073709551616 : ℝ) ≤
    8 * (100756 / 10000000 : ℝ) * ∫ s in (27 / 10 : ℝ)..(14 / 5 : ℝ), density s := by
  have he := integral_grid_sum (27 / 10 : ℝ) (14 / 5 : ℝ) 32 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [endpoint, alpha, beta])
  norm_num [Finset.sum_range_succ] at he
  linarith only [panel00, panel01, panel02, panel03, panel04, panel05, panel06, panel07, panel08, panel09, panel10, panel11, panel12, panel13, panel14, panel15, panel16, panel17, panel18, panel19, panel20, panel21, panel22, panel23, panel24, panel25, panel26, panel27, panel28, panel29, panel30, panel31, he]

end Wu18938Campaign.M3.Confirmed.TableRow07
