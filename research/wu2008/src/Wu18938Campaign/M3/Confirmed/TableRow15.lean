import Wu18938Campaign.M3.Confirmed.TableBounds

noncomputable section
namespace Wu18938Campaign.M3.Confirmed.TableRow15
open Real Set MeasureTheory QuarterTrim
open WuSource.SrcSixthGain Wu18938Campaign.M3.Confirmed.TableBounds

private theorem panel00 : (572250793445503 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (70331 / 20600 : ℝ)..(2252361 / 659200 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (70331 / 20600 : ℝ)) (b := (2252361 / 659200 : ℝ))
    (l := (14665602588844915138 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (572250793445503 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((2252361 / 659200 : ℝ) - (70331 / 20600 : ℝ)) * (14665602588844915138 / 18446744073709551616 : ℝ) / denomMax (70331 / 20600 : ℝ) (2252361 / 659200 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel01 : (570204300881404 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (2252361 / 659200 : ℝ)..(225413 / 65920 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (2252361 / 659200 : ℝ)) (b := (225413 / 65920 : ℝ))
    (l := (14612456483211967954 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (570204300881404 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((225413 / 65920 : ℝ) - (2252361 / 659200 : ℝ)) * (14612456483211967954 / 18446744073709551616 : ℝ) / denomMax (2252361 / 659200 : ℝ) (225413 / 65920 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel02 : (568155288424646 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (225413 / 65920 : ℝ)..(2255899 / 659200 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (225413 / 65920 : ℝ)) (b := (2255899 / 659200 : ℝ))
    (l := (14559231748529103770 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (568155288424646 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((2255899 / 659200 : ℝ) - (225413 / 65920 : ℝ)) * (14559231748529103770 / 18446744073709551616 : ℝ) / denomMax (225413 / 65920 : ℝ) (2255899 / 659200 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel03 : (566103738342105 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (2255899 / 659200 : ℝ)..(564417 / 164800 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (2255899 / 659200 : ℝ)) (b := (564417 / 164800 : ℝ))
    (l := (14505928146254659216 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (566103738342105 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((564417 / 164800 : ℝ) - (2255899 / 659200 : ℝ)) * (14505928146254659216 / 18446744073709551616 : ℝ) / denomMax (2255899 / 659200 : ℝ) (564417 / 164800 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel04 : (564049632833851 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (564417 / 164800 : ℝ)..(2259437 / 659200 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (564417 / 164800 : ℝ)) (b := (2259437 / 659200 : ℝ))
    (l := (14452545436736906807 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (564049632833851 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((2259437 / 659200 : ℝ) - (564417 / 164800 : ℝ)) * (14452545436736906807 / 18446744073709551616 : ℝ) / denomMax (564417 / 164800 : ℝ) (2259437 / 659200 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel05 : (561992954032632 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (2259437 / 659200 : ℝ)..(1130603 / 329600 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (2259437 / 659200 : ℝ)) (b := (1130603 / 329600 : ℝ))
    (l := (14399083379207033163 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (561992954032632 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((1130603 / 329600 : ℝ) - (2259437 / 659200 : ℝ)) * (14399083379207033163 / 18446744073709551616 : ℝ) / denomMax (2259437 / 659200 : ℝ) (1130603 / 329600 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel06 : (559933684003343 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (1130603 / 329600 : ℝ)..(90519 / 26368 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1130603 / 329600 : ℝ)) (b := (90519 / 26368 : ℝ))
    (l := (14345541731772060797 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (559933684003343 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((90519 / 26368 : ℝ) - (1130603 / 329600 : ℝ)) * (14345541731772060797 / 18446744073709551616 : ℝ) / denomMax (1130603 / 329600 : ℝ) (90519 / 26368 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel07 : (557871804742492 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (90519 / 26368 : ℝ)..(283093 / 82400 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (90519 / 26368 : ℝ)) (b := (283093 / 82400 : ℝ))
    (l := (14291920251407712925 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (557871804742492 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((283093 / 82400 : ℝ) - (90519 / 26368 : ℝ)) * (14291920251407712925 / 18446744073709551616 : ℝ) / denomMax (90519 / 26368 : ℝ) (283093 / 82400 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel08 : (555807298177669 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (283093 / 82400 : ℝ)..(2266513 / 659200 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (283093 / 82400 : ℝ)) (b := (2266513 / 659200 : ℝ))
    (l := (14238218693951220734 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (555807298177669 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((2266513 / 659200 : ℝ) - (283093 / 82400 : ℝ)) * (14238218693951220734 / 18446744073709551616 : ℝ) / denomMax (283093 / 82400 : ℝ) (2266513 / 659200 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel09 : (553740146167003 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (2266513 / 659200 : ℝ)..(1134141 / 329600 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (2266513 / 659200 : ℝ)) (b := (1134141 / 329600 : ℝ))
    (l := (14184436814094072545 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (553740146167003 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((1134141 / 329600 : ℝ) - (2266513 / 659200 : ℝ)) * (14184436814094072545 / 18446744073709551616 : ℝ) / denomMax (2266513 / 659200 : ℝ) (1134141 / 329600 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel10 : (551670330498622 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (1134141 / 329600 : ℝ)..(2270051 / 659200 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1134141 / 329600 : ℝ)) (b := (2270051 / 659200 : ℝ))
    (l := (14130574365374704309 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (551670330498622 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((2270051 / 659200 : ℝ) - (1134141 / 329600 : ℝ)) * (14130574365374704309 / 18446744073709551616 : ℝ) / denomMax (1134141 / 329600 : ℝ) (2270051 / 659200 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel11 : (549597832890106 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (2270051 / 659200 : ℝ)..(113591 / 32960 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (2270051 / 659200 : ℝ)) (b := (113591 / 32960 : ℝ))
    (l := (14076631100171130842 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (549597832890106 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((113591 / 32960 : ℝ) - (2270051 / 659200 : ℝ)) * (14076631100171130842 / 18446744073709551616 : ℝ) / denomMax (2270051 / 659200 : ℝ) (113591 / 32960 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel12 : (547522634987935 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (113591 / 32960 : ℝ)..(2273589 / 659200 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (113591 / 32960 : ℝ)) (b := (2273589 / 659200 : ℝ))
    (l := (14022606769693517237 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (547522634987935 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((2273589 / 659200 : ℝ) - (113591 / 32960 : ℝ)) * (14022606769693517237 / 18446744073709551616 : ℝ) / denomMax (113591 / 32960 : ℝ) (2273589 / 659200 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel13 : (545444718366932 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (2273589 / 659200 : ℝ)..(1137679 / 329600 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (2273589 / 659200 : ℝ)) (b := (1137679 / 329600 : ℝ))
    (l := (13968501123976689838 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (545444718366932 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((1137679 / 329600 : ℝ) - (2273589 / 659200 : ℝ)) * (13968501123976689838 / 18446744073709551616 : ℝ) / denomMax (2273589 / 659200 : ℝ) (1137679 / 329600 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel14 : (543364064529712 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (1137679 / 329600 : ℝ)..(2277127 / 659200 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1137679 / 329600 : ℝ)) (b := (2277127 / 659200 : ℝ))
    (l := (13914313911872586201 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (543364064529712 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((2277127 / 659200 : ℝ) - (1137679 / 329600 : ℝ)) * (13914313911872586201 / 18446744073709551616 : ℝ) / denomMax (1137679 / 329600 : ℝ) (2277127 / 659200 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel15 : (541280654906111 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (2277127 / 659200 : ℝ)..(142431 / 41200 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (2277127 / 659200 : ℝ)) (b := (142431 / 41200 : ℝ))
    (l := (13860044881042643420 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (541280654906111 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((142431 / 41200 : ℝ) - (2277127 / 659200 : ℝ)) * (13860044881042643420 / 18446744073709551616 : ℝ) / denomMax (2277127 / 659200 : ℝ) (142431 / 41200 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel16 : (539194470852622 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (142431 / 41200 : ℝ)..(456133 / 131840 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (142431 / 41200 : ℝ)) (b := (456133 / 131840 : ℝ))
    (l := (13805693777950124222 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (539194470852622 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((456133 / 131840 : ℝ) - (142431 / 41200 : ℝ)) * (13805693777950124222 / 18446744073709551616 : ℝ) / denomMax (142431 / 41200 : ℝ) (456133 / 131840 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel17 : (537105493651829 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (456133 / 131840 : ℝ)..(1141217 / 329600 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (456133 / 131840 : ℝ)) (b := (1141217 / 329600 : ℝ))
    (l := (13751260347852380192 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (537105493651829 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((1141217 / 329600 : ℝ) - (456133 / 131840 : ℝ)) * (13751260347852380192 / 18446744073709551616 : ℝ) / denomMax (456133 / 131840 : ℝ) (1141217 / 329600 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel18 : (535013704511823 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (1141217 / 329600 : ℝ)..(2284203 / 659200 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1141217 / 329600 : ℝ)) (b := (2284203 / 659200 : ℝ))
    (l := (13696744334793051530 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (535013704511823 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((2284203 / 659200 : ℝ) - (1141217 / 329600 : ℝ)) * (13696744334793051530 / 18446744073709551616 : ℝ) / denomMax (1141217 / 329600 : ℝ) (2284203 / 659200 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel19 : (532919084565629 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (2284203 / 659200 : ℝ)..(571493 / 164800 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (2284203 / 659200 : ℝ)) (b := (571493 / 164800 : ℝ))
    (l := (13642145481594202673 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (532919084565629 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((571493 / 164800 : ℝ) - (2284203 / 659200 : ℝ)) * (13642145481594202673 / 18446744073709551616 : ℝ) / denomMax (2284203 / 659200 : ℝ) (571493 / 164800 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel20 : (530821614870623 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (571493 / 164800 : ℝ)..(2287741 / 659200 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (571493 / 164800 : ℝ)) (b := (2287741 / 659200 : ℝ))
    (l := (13587463529848393172 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (530821614870623 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((2287741 / 659200 : ℝ) - (571493 / 164800 : ℝ)) * (13587463529848393172 / 18446744073709551616 : ℝ) / denomMax (571493 / 164800 : ℝ) (2287741 / 659200 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel21 : (528721276407939 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (2287741 / 659200 : ℝ)..(228951 / 65920 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (2287741 / 659200 : ℝ)) (b := (228951 / 65920 : ℝ))
    (l := (13532698219910683158 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (528721276407939 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((228951 / 65920 : ℝ) - (2287741 / 659200 : ℝ)) * (13532698219910683158 / 18446744073709551616 : ℝ) / denomMax (2287741 / 659200 : ℝ) (228951 / 65920 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel22 : (526618050081881 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (228951 / 65920 : ℝ)..(2291279 / 659200 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (228951 / 65920 : ℝ)) (b := (2291279 / 659200 : ℝ))
    (l := (13477849290890572742 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (526618050081881 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((2291279 / 659200 : ℝ) - (228951 / 65920 : ℝ)) * (13477849290890572742 / 18446744073709551616 : ℝ) / denomMax (228951 / 65920 : ℝ) (2291279 / 659200 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel23 : (524511916719327 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (2291279 / 659200 : ℝ)..(286631 / 82400 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (2291279 / 659200 : ℝ)) (b := (286631 / 82400 : ℝ))
    (l := (13422916480643874695 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (524511916719327 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((286631 / 82400 : ℝ) - (2291279 / 659200 : ℝ)) * (13422916480643874695 / 18446744073709551616 : ℝ) / denomMax (2291279 / 659200 : ℝ) (286631 / 82400 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel24 : (522402857069123 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (286631 / 82400 : ℝ)..(2294817 / 659200 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (286631 / 82400 : ℝ)) (b := (2294817 / 659200 : ℝ))
    (l := (13367899525764519725 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (522402857069123 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((2294817 / 659200 : ℝ) - (286631 / 82400 : ℝ)) * (13367899525764519725 / 18446744073709551616 : ℝ) / denomMax (286631 / 82400 : ℝ) (2294817 / 659200 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel25 : (520290851801485 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (2294817 / 659200 : ℝ)..(1148293 / 329600 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (2294817 / 659200 : ℝ)) (b := (1148293 / 329600 : ℝ))
    (l := (13312798161576293673 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (520290851801485 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((1148293 / 329600 : ℝ) - (2294817 / 659200 : ℝ)) * (13312798161576293673 / 18446744073709551616 : ℝ) / denomMax (2294817 / 659200 : ℝ) (1148293 / 329600 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel26 : (518175881507383 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (1148293 / 329600 : ℝ)..(459671 / 131840 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1148293 / 329600 : ℝ)) (b := (459671 / 131840 : ℝ))
    (l := (13257612122124505956 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (518175881507383 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((459671 / 131840 : ℝ) - (1148293 / 329600 : ℝ)) * (13257612122124505956 / 18446744073709551616 : ℝ) / denomMax (1148293 / 329600 : ℝ) (459671 / 131840 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel27 : (516057926697927 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (459671 / 131840 : ℝ)..(575031 / 164800 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (459671 / 131840 : ℝ)) (b := (575031 / 164800 : ℝ))
    (l := (13202341140167588531 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (516057926697927 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((575031 / 164800 : ℝ) - (459671 / 131840 : ℝ)) * (13202341140167588531 / 18446744073709551616 : ℝ) / denomMax (459671 / 131840 : ℝ) (575031 / 164800 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel28 : (513936967803753 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (575031 / 164800 : ℝ)..(2301893 / 659200 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (575031 / 164800 : ℝ)) (b := (2301893 / 659200 : ℝ))
    (l := (13146984947168624709 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (513936967803753 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((2301893 / 659200 : ℝ) - (575031 / 164800 : ℝ)) * (13146984947168624709 / 18446744073709551616 : ℝ) / denomMax (575031 / 164800 : ℝ) (2301893 / 659200 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel29 : (511812985174393 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (2301893 / 659200 : ℝ)..(1151831 / 329600 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (2301893 / 659200 : ℝ)) (b := (1151831 / 329600 : ℝ))
    (l := (13091543273286807078 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (511812985174393 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((1151831 / 329600 : ℝ) - (2301893 / 659200 : ℝ)) * (13091543273286807078 / 18446744073709551616 : ℝ) / denomMax (2301893 / 659200 : ℝ) (1151831 / 329600 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel30 : (509685959077652 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (1151831 / 329600 : ℝ)..(2305431 / 659200 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1151831 / 329600 : ℝ)) (b := (2305431 / 659200 : ℝ))
    (l := (13036015847368823833 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (509685959077652 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((2305431 / 659200 : ℝ) - (1151831 / 329600 : ℝ)) * (13036015847368823833 / 18446744073709551616 : ℝ) / denomMax (1151831 / 329600 : ℝ) (2305431 / 659200 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel31 : (507555869698968 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (2305431 / 659200 : ℝ)..(7 / 2 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (2305431 / 659200 : ℝ)) (b := (7 / 2 : ℝ))
    (l := (12980402396940172775 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (507555869698968 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((7 / 2 : ℝ) - (2305431 / 659200 : ℝ)) * (12980402396940172775 / 18446744073709551616 : ℝ) / denomMax (2305431 / 659200 : ℝ) (7 / 2 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

theorem lower : (17283814787722423 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (70331 / 20600 : ℝ)..(7 / 2 : ℝ), density s := by
  have he := integral_grid_sum (70331 / 20600 : ℝ) (7 / 2 : ℝ) 32 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [endpoint, alpha, beta])
  norm_num [Finset.sum_range_succ] at he
  linarith only [panel00, panel01, panel02, panel03, panel04, panel05, panel06, panel07, panel08, panel09, panel10, panel11, panel12, panel13, panel14, panel15, panel16, panel17, panel18, panel19, panel20, panel21, panel22, panel23, panel24, panel25, panel26, panel27, panel28, panel29, panel30, panel31, he]

end Wu18938Campaign.M3.Confirmed.TableRow15
