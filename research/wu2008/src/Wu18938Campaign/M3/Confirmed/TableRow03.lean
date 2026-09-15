import Wu18938Campaign.M3.Confirmed.TableBounds

noncomputable section
namespace Wu18938Campaign.M3.Confirmed.TableRow03
open Real Set MeasureTheory QuarterTrim
open WuSource.SrcSixthGain Wu18938Campaign.M3.Confirmed.TableBounds

private theorem panel00 : (3268604732303435 / 18446744073709551616 : ℝ) ≤
    8 * (157035 / 10000000 : ℝ) * ∫ s in (23 / 10 : ℝ)..(737 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (23 / 10 : ℝ)) (b := (737 / 320 : ℝ))
    (l := (12519253577113434807 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (157035 / 10000000 : ℝ))
  have hp : (3268604732303435 / 18446744073709551616 : ℝ) ≤ 8 * (157035 / 10000000 : ℝ) *
      (((737 / 320 : ℝ) - (23 / 10 : ℝ)) * (12519253577113434807 / 18446744073709551616 : ℝ) / denomMax (23 / 10 : ℝ) (737 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel01 : (3267543724643110 / 18446744073709551616 : ℝ) ≤
    8 * (157035 / 10000000 : ℝ) * ∫ s in (737 / 320 : ℝ)..(369 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (737 / 320 : ℝ)) (b := (369 / 160 : ℝ))
    (l := (12523130351978353050 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (157035 / 10000000 : ℝ))
  have hp : (3267543724643110 / 18446744073709551616 : ℝ) ≤ 8 * (157035 / 10000000 : ℝ) *
      (((369 / 160 : ℝ) - (737 / 320 : ℝ)) * (12523130351978353050 / 18446744073709551616 : ℝ) / denomMax (737 / 320 : ℝ) (369 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel02 : (3266492559334218 / 18446744073709551616 : ℝ) ≤
    8 * (157035 / 10000000 : ℝ) * ∫ s in (369 / 160 : ℝ)..(739 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (369 / 160 : ℝ)) (b := (739 / 320 : ℝ))
    (l := (12527015223017242917 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (157035 / 10000000 : ℝ))
  have hp : (3266492559334218 / 18446744073709551616 : ℝ) ≤ 8 * (157035 / 10000000 : ℝ) *
      (((739 / 320 : ℝ) - (369 / 160 : ℝ)) * (12527015223017242917 / 18446744073709551616 : ℝ) / denomMax (369 / 160 : ℝ) (739 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel03 : (3265451218212447 / 18446744073709551616 : ℝ) ≤
    8 * (157035 / 10000000 : ℝ) * ∫ s in (739 / 320 : ℝ)..(37 / 16 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (739 / 320 : ℝ)) (b := (37 / 16 : ℝ))
    (l := (12530908215704851829 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (157035 / 10000000 : ℝ))
  have hp : (3265451218212447 / 18446744073709551616 : ℝ) ≤ 8 * (157035 / 10000000 : ℝ) *
      (((37 / 16 : ℝ) - (739 / 320 : ℝ)) * (12530908215704851829 / 18446744073709551616 : ℝ) / denomMax (739 / 320 : ℝ) (37 / 16 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel04 : (3264419683302315 / 18446744073709551616 : ℝ) ≤
    8 * (157035 / 10000000 : ℝ) * ∫ s in (37 / 16 : ℝ)..(741 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (37 / 16 : ℝ)) (b := (741 / 320 : ℝ))
    (l := (12534809355623276302 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (157035 / 10000000 : ℝ))
  have hp : (3264419683302315 / 18446744073709551616 : ℝ) ≤ 8 * (157035 / 10000000 : ℝ) *
      (((741 / 320 : ℝ) - (37 / 16 : ℝ)) * (12534809355623276302 / 18446744073709551616 : ℝ) / denomMax (37 / 16 : ℝ) (741 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel05 : (3263397936816374 / 18446744073709551616 : ℝ) ≤
    8 * (157035 / 10000000 : ℝ) * ∫ s in (741 / 320 : ℝ)..(371 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (741 / 320 : ℝ)) (b := (371 / 160 : ℝ))
    (l := (12538718668462529880 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (157035 / 10000000 : ℝ))
  have hp : (3263397936816374 / 18446744073709551616 : ℝ) ≤ 8 * (157035 / 10000000 : ℝ) *
      (((371 / 160 : ℝ) - (741 / 320 : ℝ)) * (12538718668462529880 / 18446744073709551616 : ℝ) / denomMax (741 / 320 : ℝ) (371 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel06 : (3262385961154423 / 18446744073709551616 : ℝ) ≤
    8 * (157035 / 10000000 : ℝ) * ∫ s in (371 / 160 : ℝ)..(743 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (371 / 160 : ℝ)) (b := (743 / 320 : ℝ))
    (l := (12542636180021114701 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (157035 / 10000000 : ℝ))
  have hp : (3262385961154423 / 18446744073709551616 : ℝ) ≤ 8 * (157035 / 10000000 : ℝ) *
      (((743 / 320 : ℝ) - (371 / 160 : ℝ)) * (12542636180021114701 / 18446744073709551616 : ℝ) / denomMax (371 / 160 : ℝ) (743 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel07 : (3261383738902732 / 18446744073709551616 : ℝ) ≤
    8 * (157035 / 10000000 : ℝ) * ∫ s in (743 / 320 : ℝ)..(93 / 40 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (743 / 320 : ℝ)) (b := (93 / 40 : ℝ))
    (l := (12546561916206596699 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (157035 / 10000000 : ℝ))
  have hp : (3261383738902732 / 18446744073709551616 : ℝ) ≤ 8 * (157035 / 10000000 : ℝ) *
      (((93 / 40 : ℝ) - (743 / 320 : ℝ)) * (12546561916206596699 / 18446744073709551616 : ℝ) / denomMax (743 / 320 : ℝ) (93 / 40 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel08 : (3260391252833270 / 18446744073709551616 : ℝ) ≤
    8 * (157035 / 10000000 : ℝ) * ∫ s in (93 / 40 : ℝ)..(149 / 64 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (93 / 40 : ℝ)) (b := (149 / 64 : ℝ))
    (l := (12550495903036184493 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (157035 / 10000000 : ℝ))
  have hp : (3260391252833270 / 18446744073709551616 : ℝ) ≤ 8 * (157035 / 10000000 : ℝ) *
      (((149 / 64 : ℝ) - (93 / 40 : ℝ)) * (12550495903036184493 / 18446744073709551616 : ℝ) / denomMax (93 / 40 : ℝ) (149 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel09 : (3259408485902951 / 18446744073709551616 : ℝ) ≤
    8 * (157035 / 10000000 : ℝ) * ∫ s in (149 / 64 : ℝ)..(373 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (149 / 64 : ℝ)) (b := (373 / 160 : ℝ))
    (l := (12554438166637311967 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (157035 / 10000000 : ℝ))
  have hp : (3259408485902951 / 18446744073709551616 : ℝ) ≤ 8 * (157035 / 10000000 : ℝ) *
      (((373 / 160 : ℝ) - (149 / 64 : ℝ)) * (12554438166637311967 / 18446744073709551616 : ℝ) / denomMax (149 / 64 : ℝ) (373 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel10 : (3258435421252879 / 18446744073709551616 : ℝ) ≤
    8 * (157035 / 10000000 : ℝ) * ∫ s in (373 / 160 : ℝ)..(747 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (373 / 160 : ℝ)) (b := (747 / 320 : ℝ))
    (l := (12558388733248224596 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (157035 / 10000000 : ℝ))
  have hp : (3258435421252879 / 18446744073709551616 : ℝ) ≤ 8 * (157035 / 10000000 : ℝ) *
      (((747 / 320 : ℝ) - (373 / 160 : ℝ)) * (12558388733248224596 / 18446744073709551616 : ℝ) / denomMax (373 / 160 : ℝ) (747 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel11 : (3257472042207609 / 18446744073709551616 : ℝ) ≤
    8 * (157035 / 10000000 : ℝ) * ∫ s in (747 / 320 : ℝ)..(187 / 80 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (747 / 320 : ℝ)) (b := (187 / 80 : ℝ))
    (l := (12562347629218569514 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (157035 / 10000000 : ℝ))
  have hp : (3257472042207609 / 18446744073709551616 : ℝ) ≤ 8 * (157035 / 10000000 : ℝ) *
      (((187 / 80 : ℝ) - (747 / 320 : ℝ)) * (12562347629218569514 / 18446744073709551616 : ℝ) / denomMax (747 / 320 : ℝ) (187 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel12 : (3256518332274418 / 18446744073709551616 : ℝ) ≤
    8 * (157035 / 10000000 : ℝ) * ∫ s in (187 / 80 : ℝ)..(749 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (187 / 80 : ℝ)) (b := (749 / 320 : ℝ))
    (l := (12566314881009989387 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (157035 / 10000000 : ℝ))
  have hp : (3256518332274418 / 18446744073709551616 : ℝ) ≤ 8 * (157035 / 10000000 : ℝ) *
      (((749 / 320 : ℝ) - (187 / 80 : ℝ)) * (12566314881009989387 / 18446744073709551616 : ℝ) / denomMax (187 / 80 : ℝ) (749 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel13 : (3255574275142578 / 18446744073709551616 : ℝ) ≤
    8 * (157035 / 10000000 : ℝ) * ∫ s in (749 / 320 : ℝ)..(75 / 32 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (749 / 320 : ℝ)) (b := (75 / 32 : ℝ))
    (l := (12570290515196720083 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (157035 / 10000000 : ℝ))
  have hp : (3255574275142578 / 18446744073709551616 : ℝ) ≤ 8 * (157035 / 10000000 : ℝ) *
      (((75 / 32 : ℝ) - (749 / 320 : ℝ)) * (12570290515196720083 / 18446744073709551616 : ℝ) / denomMax (749 / 320 : ℝ) (75 / 32 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel14 : (3254639854682645 / 18446744073709551616 : ℝ) ≤
    8 * (157035 / 10000000 : ℝ) * ∫ s in (75 / 32 : ℝ)..(751 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (75 / 32 : ℝ)) (b := (751 / 320 : ℝ))
    (l := (12574274558466192205 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (157035 / 10000000 : ℝ))
  have hp : (3254639854682645 / 18446744073709551616 : ℝ) ≤ 8 * (157035 / 10000000 : ℝ) *
      (((751 / 320 : ℝ) - (75 / 32 : ℝ)) * (12574274558466192205 / 18446744073709551616 : ℝ) / denomMax (75 / 32 : ℝ) (751 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel15 : (3253715054945752 / 18446744073709551616 : ℝ) ≤
    8 * (157035 / 10000000 : ℝ) * ∫ s in (751 / 320 : ℝ)..(47 / 20 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (751 / 320 : ℝ)) (b := (47 / 20 : ℝ))
    (l := (12578267037619636479 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (157035 / 10000000 : ℝ))
  have hp : (3253715054945752 / 18446744073709551616 : ℝ) ≤ 8 * (157035 / 10000000 : ℝ) *
      (((47 / 20 : ℝ) - (751 / 320 : ℝ)) * (12578267037619636479 / 18446744073709551616 : ℝ) / denomMax (751 / 320 : ℝ) (47 / 20 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel16 : (3252799860162918 / 18446744073709551616 : ℝ) ≤
    8 * (157035 / 10000000 : ℝ) * ∫ s in (47 / 20 : ℝ)..(753 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (47 / 20 : ℝ)) (b := (753 / 320 : ℝ))
    (l := (12582267979572693063 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (157035 / 10000000 : ℝ))
  have hp : (3252799860162918 / 18446744073709551616 : ℝ) ≤ 8 * (157035 / 10000000 : ℝ) *
      (((753 / 320 : ℝ) - (47 / 20 : ℝ)) * (12582267979572693063 / 18446744073709551616 : ℝ) / denomMax (47 / 20 : ℝ) (753 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel17 : (3251894254744350 / 18446744073709551616 : ℝ) ≤
    8 * (157035 / 10000000 : ℝ) * ∫ s in (753 / 320 : ℝ)..(377 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (753 / 320 : ℝ)) (b := (377 / 160 : ℝ))
    (l := (12586277411356024772 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (157035 / 10000000 : ℝ))
  have hp : (3251894254744350 / 18446744073709551616 : ℝ) ≤ 8 * (157035 / 10000000 : ℝ) *
      (((377 / 160 : ℝ) - (753 / 320 : ℝ)) * (12586277411356024772 / 18446744073709551616 : ℝ) / denomMax (753 / 320 : ℝ) (377 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel18 : (3250998223278778 / 18446744073709551616 : ℝ) ≤
    8 * (157035 / 10000000 : ℝ) * ∫ s in (377 / 160 : ℝ)..(151 / 64 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (377 / 160 : ℝ)) (b := (151 / 64 : ℝ))
    (l := (12590295360115934275 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (157035 / 10000000 : ℝ))
  have hp : (3250998223278778 / 18446744073709551616 : ℝ) ≤ 8 * (157035 / 10000000 : ℝ) *
      (((151 / 64 : ℝ) - (377 / 160 : ℝ)) * (12590295360115934275 / 18446744073709551616 : ℝ) / denomMax (377 / 160 : ℝ) (151 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel19 : (3250111750532773 / 18446744073709551616 : ℝ) ≤
    8 * (157035 / 10000000 : ℝ) * ∫ s in (151 / 64 : ℝ)..(189 / 80 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (151 / 64 : ℝ)) (b := (189 / 80 : ℝ))
    (l := (12594321853114985282 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (157035 / 10000000 : ℝ))
  have hp : (3250111750532773 / 18446744073709551616 : ℝ) ≤ 8 * (157035 / 10000000 : ℝ) *
      (((189 / 80 : ℝ) - (151 / 64 : ℝ)) * (12594321853114985282 / 18446744073709551616 : ℝ) / denomMax (151 / 64 : ℝ) (189 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel20 : (3249234821450093 / 18446744073709551616 : ℝ) ≤
    8 * (157035 / 10000000 : ℝ) * ∫ s in (189 / 80 : ℝ)..(757 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (189 / 80 : ℝ)) (b := (757 / 320 : ℝ))
    (l := (12598356917732627746 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (157035 / 10000000 : ℝ))
  have hp : (3249234821450093 / 18446744073709551616 : ℝ) ≤ 8 * (157035 / 10000000 : ℝ) *
      (((757 / 320 : ℝ) - (189 / 80 : ℝ)) * (12598356917732627746 / 18446744073709551616 : ℝ) / denomMax (189 / 80 : ℝ) (757 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel21 : (3248367421151026 / 18446744073709551616 : ℝ) ≤
    8 * (157035 / 10000000 : ℝ) * ∫ s in (757 / 320 : ℝ)..(379 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (757 / 320 : ℝ)) (b := (379 / 160 : ℝ))
    (l := (12602400581465827128 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (157035 / 10000000 : ℝ))
  have hp : (3248367421151026 / 18446744073709551616 : ℝ) ≤ 8 * (157035 / 10000000 : ℝ) *
      (((379 / 160 : ℝ) - (757 / 320 : ℝ)) * (12602400581465827128 / 18446744073709551616 : ℝ) / denomMax (757 / 320 : ℝ) (379 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel22 : (3247509534931750 / 18446744073709551616 : ℝ) ≤
    8 * (157035 / 10000000 : ℝ) * ∫ s in (379 / 160 : ℝ)..(759 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (379 / 160 : ℝ)) (b := (759 / 320 : ℝ))
    (l := (12606452871929697740 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (157035 / 10000000 : ℝ))
  have hp : (3247509534931750 / 18446744073709551616 : ℝ) ≤ 8 * (157035 / 10000000 : ℝ) *
      (((759 / 320 : ℝ) - (379 / 160 : ℝ)) * (12606452871929697740 / 18446744073709551616 : ℝ) / denomMax (379 / 160 : ℝ) (759 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel23 : (3246661148263691 / 18446744073709551616 : ℝ) ≤
    8 * (157035 / 10000000 : ℝ) * ∫ s in (759 / 320 : ℝ)..(19 / 8 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (759 / 320 : ℝ)) (b := (19 / 8 : ℝ))
    (l := (12610513816858140201 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (157035 / 10000000 : ℝ))
  have hp : (3246661148263691 / 18446744073709551616 : ℝ) ≤ 8 * (157035 / 10000000 : ℝ) *
      (((19 / 8 : ℝ) - (759 / 320 : ℝ)) * (12610513816858140201 / 18446744073709551616 : ℝ) / denomMax (759 / 320 : ℝ) (19 / 8 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel24 : (3245822246792901 / 18446744073709551616 : ℝ) ≤
    8 * (157035 / 10000000 : ℝ) * ∫ s in (19 / 8 : ℝ)..(761 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (19 / 8 : ℝ)) (b := (761 / 320 : ℝ))
    (l := (12614583444104483042 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (157035 / 10000000 : ℝ))
  have hp : (3245822246792901 / 18446744073709551616 : ℝ) ≤ 8 * (157035 / 10000000 : ℝ) *
      (((761 / 320 : ℝ) - (19 / 8 : ℝ)) * (12614583444104483042 / 18446744073709551616 : ℝ) / denomMax (19 / 8 : ℝ) (761 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel25 : (3244992816339435 / 18446744073709551616 : ℝ) ≤
    8 * (157035 / 10000000 : ℝ) * ∫ s in (761 / 320 : ℝ)..(381 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (761 / 320 : ℝ)) (b := (381 / 160 : ℝ))
    (l := (12618661781642128485 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (157035 / 10000000 : ℝ))
  have hp : (3244992816339435 / 18446744073709551616 : ℝ) ≤ 8 * (157035 / 10000000 : ℝ) *
      (((381 / 160 : ℝ) - (761 / 320 : ℝ)) * (12618661781642128485 / 18446744073709551616 : ℝ) / denomMax (761 / 320 : ℝ) (381 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel26 : (3244172842896741 / 18446744073709551616 : ℝ) ≤
    8 * (157035 / 10000000 : ℝ) * ∫ s in (381 / 160 : ℝ)..(763 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (381 / 160 : ℝ)) (b := (763 / 320 : ℝ))
    (l := (12622748857565202436 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (157035 / 10000000 : ℝ))
  have hp : (3244172842896741 / 18446744073709551616 : ℝ) ≤ 8 * (157035 / 10000000 : ℝ) *
      (((763 / 320 : ℝ) - (381 / 160 : ℝ)) * (12622748857565202436 / 18446744073709551616 : ℝ) / denomMax (381 / 160 : ℝ) (763 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel27 : (3243362312631059 / 18446744073709551616 : ℝ) ≤
    8 * (157035 / 10000000 : ℝ) * ∫ s in (763 / 320 : ℝ)..(191 / 80 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (763 / 320 : ℝ)) (b := (191 / 80 : ℝ))
    (l := (12626844700089208715 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (157035 / 10000000 : ℝ))
  have hp : (3243362312631059 / 18446744073709551616 : ℝ) ≤ 8 * (157035 / 10000000 : ℝ) *
      (((191 / 80 : ℝ) - (763 / 320 : ℝ)) * (12626844700089208715 / 18446744073709551616 : ℝ) / denomMax (763 / 320 : ℝ) (191 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel28 : (3242561211880824 / 18446744073709551616 : ℝ) ≤
    8 * (157035 / 10000000 : ℝ) * ∫ s in (191 / 80 : ℝ)..(153 / 64 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (191 / 80 : ℝ)) (b := (153 / 64 : ℝ))
    (l := (12630949337551687561 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (157035 / 10000000 : ℝ))
  have hp : (3242561211880824 / 18446744073709551616 : ℝ) ≤ 8 * (157035 / 10000000 : ℝ) *
      (((153 / 64 : ℝ) - (191 / 80 : ℝ)) * (12630949337551687561 / 18446744073709551616 : ℝ) / denomMax (191 / 80 : ℝ) (153 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel29 : (3241769527156079 / 18446744073709551616 : ℝ) ≤
    8 * (157035 / 10000000 : ℝ) * ∫ s in (153 / 64 : ℝ)..(383 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (153 / 64 : ℝ)) (b := (383 / 160 : ℝ))
    (l := (12635062798412878441 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (157035 / 10000000 : ℝ))
  have hp : (3241769527156079 / 18446744073709551616 : ℝ) ≤ 8 * (157035 / 10000000 : ℝ) *
      (((383 / 160 : ℝ) - (153 / 64 : ℝ)) * (12635062798412878441 / 18446744073709551616 : ℝ) / denomMax (153 / 64 : ℝ) (383 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel30 : (3240987245137899 / 18446744073709551616 : ℝ) ≤
    8 * (157035 / 10000000 : ℝ) * ∫ s in (383 / 160 : ℝ)..(767 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (383 / 160 : ℝ)) (b := (767 / 320 : ℝ))
    (l := (12639185111256387208 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (157035 / 10000000 : ℝ))
  have hp : (3240987245137899 / 18446744073709551616 : ℝ) ≤ 8 * (157035 / 10000000 : ℝ) *
      (((767 / 320 : ℝ) - (383 / 160 : ℝ)) * (12639185111256387208 / 18446744073709551616 : ℝ) / denomMax (383 / 160 : ℝ) (767 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel31 : (3240214352677821 / 18446744073709551616 : ℝ) ≤
    8 * (157035 / 10000000 : ℝ) * ∫ s in (767 / 320 : ℝ)..(12 / 5 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (767 / 320 : ℝ)) (b := (12 / 5 : ℝ))
    (l := (12643316304789857618 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (157035 / 10000000 : ℝ))
  have hp : (3240214352677821 / 18446744073709551616 : ℝ) ≤ 8 * (157035 / 10000000 : ℝ) *
      (((12 / 5 : ℝ) - (767 / 320 : ℝ)) * (12643316304789857618 / 18446744073709551616 : ℝ) / denomMax (767 / 320 : ℝ) (12 / 5 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

theorem lower : (104117293843939294 / 18446744073709551616 : ℝ) ≤
    8 * (157035 / 10000000 : ℝ) * ∫ s in (23 / 10 : ℝ)..(12 / 5 : ℝ), density s := by
  have he := integral_grid_sum (23 / 10 : ℝ) (12 / 5 : ℝ) 32 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [endpoint, alpha, beta])
  norm_num [Finset.sum_range_succ] at he
  linarith only [panel00, panel01, panel02, panel03, panel04, panel05, panel06, panel07, panel08, panel09, panel10, panel11, panel12, panel13, panel14, panel15, panel16, panel17, panel18, panel19, panel20, panel21, panel22, panel23, panel24, panel25, panel26, panel27, panel28, panel29, panel30, panel31, he]

end Wu18938Campaign.M3.Confirmed.TableRow03
