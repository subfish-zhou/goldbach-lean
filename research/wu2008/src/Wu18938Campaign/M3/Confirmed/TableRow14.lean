import Wu18938Campaign.M3.Confirmed.TableBounds

noncomputable section
namespace Wu18938Campaign.M3.Confirmed.TableRow14
open Real Set MeasureTheory QuarterTrim
open WuSource.SrcSixthGain Wu18938Campaign.M3.Confirmed.TableBounds

private theorem panel00 : (94170720798125 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (17 / 5 : ℝ)..(2241571 / 659200 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (17 / 5 : ℝ)) (b := (2241571 / 659200 : ℝ))
    (l := (14674528983560565572 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (94170720798125 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((2241571 / 659200 : ℝ) - (17 / 5 : ℝ)) * (14674528983560565572 / 18446744073709551616 : ℝ) / denomMax (17 / 5 : ℝ) (2241571 / 659200 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel01 : (94180133864287 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (2241571 / 659200 : ℝ)..(1120931 / 329600 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (2241571 / 659200 : ℝ)) (b := (1120931 / 329600 : ℝ))
    (l := (14675898363873074925 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (94180133864287 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((1120931 / 329600 : ℝ) - (2241571 / 659200 : ℝ)) * (14675898363873074925 / 18446744073709551616 : ℝ) / denomMax (2241571 / 659200 : ℝ) (1120931 / 329600 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel02 : (94189554518683 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (1120931 / 329600 : ℝ)..(2242153 / 659200 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (1120931 / 329600 : ℝ)) (b := (2242153 / 659200 : ℝ))
    (l := (14677268387066142266 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (94189554518683 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((2242153 / 659200 : ℝ) - (1120931 / 329600 : ℝ)) * (14677268387066142266 / 18446744073709551616 : ℝ) / denomMax (1120931 / 329600 : ℝ) (2242153 / 659200 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel03 : (94198982765395 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (2242153 / 659200 : ℝ)..(560611 / 164800 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (2242153 / 659200 : ℝ)) (b := (560611 / 164800 : ℝ))
    (l := (14678639053596373007 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (94198982765395 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((560611 / 164800 : ℝ) - (2242153 / 659200 : ℝ)) * (14678639053596373007 / 18446744073709551616 : ℝ) / denomMax (2242153 / 659200 : ℝ) (560611 / 164800 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel04 : (94208418608512 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (560611 / 164800 : ℝ)..(448547 / 131840 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (560611 / 164800 : ℝ)) (b := (448547 / 131840 : ℝ))
    (l := (14680010363920808590 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (94208418608512 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((448547 / 131840 : ℝ) - (560611 / 164800 : ℝ)) * (14680010363920808590 / 18446744073709551616 : ℝ) / denomMax (560611 / 164800 : ℝ) (448547 / 131840 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel05 : (94217862052127 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (448547 / 131840 : ℝ)..(1121513 / 329600 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (448547 / 131840 : ℝ)) (b := (1121513 / 329600 : ℝ))
    (l := (14681382318496927014 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (94217862052127 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((1121513 / 329600 : ℝ) - (448547 / 131840 : ℝ)) * (14681382318496927014 / 18446744073709551616 : ℝ) / denomMax (448547 / 131840 : ℝ) (1121513 / 329600 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel06 : (94227313100337 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (1121513 / 329600 : ℝ)..(2243317 / 659200 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (1121513 / 329600 : ℝ)) (b := (2243317 / 659200 : ℝ))
    (l := (14682754917782643361 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (94227313100337 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((2243317 / 659200 : ℝ) - (1121513 / 329600 : ℝ)) * (14682754917782643361 / 18446744073709551616 : ℝ) / denomMax (1121513 / 329600 : ℝ) (2243317 / 659200 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel07 : (94236771757243 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (2243317 / 659200 : ℝ)..(280451 / 82400 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (2243317 / 659200 : ℝ)) (b := (280451 / 82400 : ℝ))
    (l := (14684128162236310316 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (94236771757243 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((280451 / 82400 : ℝ) - (2243317 / 659200 : ℝ)) * (14684128162236310316 / 18446744073709551616 : ℝ) / denomMax (2243317 / 659200 : ℝ) (280451 / 82400 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel08 : (94246238026953 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (280451 / 82400 : ℝ)..(2243899 / 659200 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (280451 / 82400 : ℝ)) (b := (2243899 / 659200 : ℝ))
    (l := (14685502052316718704 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (94246238026953 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((2243899 / 659200 : ℝ) - (280451 / 82400 : ℝ)) * (14685502052316718704 / 18446744073709551616 : ℝ) / denomMax (280451 / 82400 : ℝ) (2243899 / 659200 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel09 : (94255711913576 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (2243899 / 659200 : ℝ)..(224419 / 65920 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (2243899 / 659200 : ℝ)) (b := (224419 / 65920 : ℝ))
    (l := (14686876588483098009 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (94255711913576 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((224419 / 65920 : ℝ) - (2243899 / 659200 : ℝ)) * (14686876588483098009 / 18446744073709551616 : ℝ) / denomMax (2243899 / 659200 : ℝ) (224419 / 65920 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel10 : (94265193421229 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (224419 / 65920 : ℝ)..(2244481 / 659200 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (224419 / 65920 : ℝ)) (b := (2244481 / 659200 : ℝ))
    (l := (14688251771195116907 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (94265193421229 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((2244481 / 659200 : ℝ) - (224419 / 65920 : ℝ)) * (14688251771195116907 / 18446744073709551616 : ℝ) / denomMax (224419 / 65920 : ℝ) (2244481 / 659200 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel11 : (94274682554031 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (2244481 / 659200 : ℝ)..(561193 / 164800 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (2244481 / 659200 : ℝ)) (b := (561193 / 164800 : ℝ))
    (l := (14689627600912883793 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (94274682554031 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((561193 / 164800 : ℝ) - (2244481 / 659200 : ℝ)) * (14689627600912883793 / 18446744073709551616 : ℝ) / denomMax (2244481 / 659200 : ℝ) (561193 / 164800 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel12 : (94284179316107 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (561193 / 164800 : ℝ)..(2245063 / 659200 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (561193 / 164800 : ℝ)) (b := (2245063 / 659200 : ℝ))
    (l := (14691004078096947314 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (94284179316107 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((2245063 / 659200 : ℝ) - (561193 / 164800 : ℝ)) * (14691004078096947314 / 18446744073709551616 : ℝ) / denomMax (561193 / 164800 : ℝ) (2245063 / 659200 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel13 : (94293683711586 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (2245063 / 659200 : ℝ)..(1122677 / 329600 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (2245063 / 659200 : ℝ)) (b := (1122677 / 329600 : ℝ))
    (l := (14692381203208296897 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (94293683711586 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((1122677 / 329600 : ℝ) - (2245063 / 659200 : ℝ)) * (14692381203208296897 / 18446744073709551616 : ℝ) / denomMax (2245063 / 659200 : ℝ) (1122677 / 329600 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel14 : (94303195744602 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (1122677 / 329600 : ℝ)..(449129 / 131840 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (1122677 / 329600 : ℝ)) (b := (449129 / 131840 : ℝ))
    (l := (14693758976708363283 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (94303195744602 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((449129 / 131840 : ℝ) - (1122677 / 329600 : ℝ)) * (14693758976708363283 / 18446744073709551616 : ℝ) / denomMax (1122677 / 329600 : ℝ) (449129 / 131840 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel15 : (94312715419293 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (449129 / 131840 : ℝ)..(140371 / 41200 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (449129 / 131840 : ℝ)) (b := (140371 / 41200 : ℝ))
    (l := (14695137399059019056 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (94312715419293 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((140371 / 41200 : ℝ) - (449129 / 131840 : ℝ)) * (14695137399059019056 / 18446744073709551616 : ℝ) / denomMax (449129 / 131840 : ℝ) (140371 / 41200 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel16 : (94322242739801 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (140371 / 41200 : ℝ)..(2246227 / 659200 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (140371 / 41200 : ℝ)) (b := (2246227 / 659200 : ℝ))
    (l := (14696516470722579181 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (94322242739801 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((2246227 / 659200 : ℝ) - (140371 / 41200 : ℝ)) * (14696516470722579181 / 18446744073709551616 : ℝ) / denomMax (140371 / 41200 : ℝ) (2246227 / 659200 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel17 : (94331777710275 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (2246227 / 659200 : ℝ)..(1123259 / 329600 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (2246227 / 659200 : ℝ)) (b := (1123259 / 329600 : ℝ))
    (l := (14697896192161801532 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (94331777710275 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((1123259 / 329600 : ℝ) - (2246227 / 659200 : ℝ)) * (14697896192161801532 / 18446744073709551616 : ℝ) / denomMax (2246227 / 659200 : ℝ) (1123259 / 329600 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel18 : (94341320334866 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (1123259 / 329600 : ℝ)..(2246809 / 659200 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (1123259 / 329600 : ℝ)) (b := (2246809 / 659200 : ℝ))
    (l := (14699276563839887435 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (94341320334866 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((2246809 / 659200 : ℝ) - (1123259 / 329600 : ℝ)) * (14699276563839887435 / 18446744073709551616 : ℝ) / denomMax (1123259 / 329600 : ℝ) (2246809 / 659200 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel19 : (94350870617731 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (2246809 / 659200 : ℝ)..(22471 / 6592 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (2246809 / 659200 : ℝ)) (b := (22471 / 6592 : ℝ))
    (l := (14700657586220482192 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (94350870617731 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((22471 / 6592 : ℝ) - (2246809 / 659200 : ℝ)) * (14700657586220482192 / 18446744073709551616 : ℝ) / denomMax (2246809 / 659200 : ℝ) (22471 / 6592 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel20 : (94360428563031 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (22471 / 6592 : ℝ)..(2247391 / 659200 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (22471 / 6592 : ℝ)) (b := (2247391 / 659200 : ℝ))
    (l := (14702039259767675630 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (94360428563031 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((2247391 / 659200 : ℝ) - (22471 / 6592 : ℝ)) * (14702039259767675630 / 18446744073709551616 : ℝ) / denomMax (22471 / 6592 : ℝ) (2247391 / 659200 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel21 : (94369994174932 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (2247391 / 659200 : ℝ)..(1123841 / 329600 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (2247391 / 659200 : ℝ)) (b := (1123841 / 329600 : ℝ))
    (l := (14703421584946002628 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (94369994174932 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((1123841 / 329600 : ℝ) - (2247391 / 659200 : ℝ)) * (14703421584946002628 / 18446744073709551616 : ℝ) / denomMax (2247391 / 659200 : ℝ) (1123841 / 329600 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel22 : (94379567457604 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (1123841 / 329600 : ℝ)..(2247973 / 659200 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (1123841 / 329600 : ℝ)) (b := (2247973 / 659200 : ℝ))
    (l := (14704804562220443661 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (94379567457604 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((2247973 / 659200 : ℝ) - (1123841 / 329600 : ℝ)) * (14704804562220443661 / 18446744073709551616 : ℝ) / denomMax (1123841 / 329600 : ℝ) (2247973 / 659200 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel23 : (94389148415222 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (2247973 / 659200 : ℝ)..(281033 / 82400 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (2247973 / 659200 : ℝ)) (b := (281033 / 82400 : ℝ))
    (l := (14706188192056425335 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (94389148415222 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((281033 / 82400 : ℝ) - (2247973 / 659200 : ℝ)) * (14706188192056425335 / 18446744073709551616 : ℝ) / denomMax (2247973 / 659200 : ℝ) (281033 / 82400 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel24 : (94398737051967 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (281033 / 82400 : ℝ)..(449711 / 131840 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (281033 / 82400 : ℝ)) (b := (449711 / 131840 : ℝ))
    (l := (14707572474919820927 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (94398737051967 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((449711 / 131840 : ℝ) - (281033 / 82400 : ℝ)) * (14707572474919820927 / 18446744073709551616 : ℝ) / denomMax (281033 / 82400 : ℝ) (449711 / 131840 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel25 : (94408333372022 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (449711 / 131840 : ℝ)..(1124423 / 329600 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (449711 / 131840 : ℝ)) (b := (1124423 / 329600 : ℝ))
    (l := (14708957411276950930 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (94408333372022 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((1124423 / 329600 : ℝ) - (449711 / 131840 : ℝ)) * (14708957411276950930 / 18446744073709551616 : ℝ) / denomMax (449711 / 131840 : ℝ) (1124423 / 329600 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel26 : (94417937379576 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (1124423 / 329600 : ℝ)..(2249137 / 659200 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (1124423 / 329600 : ℝ)) (b := (2249137 / 659200 : ℝ))
    (l := (14710343001594583585 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (94417937379576 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((2249137 / 659200 : ℝ) - (1124423 / 329600 : ℝ)) * (14710343001594583585 / 18446744073709551616 : ℝ) / denomMax (1124423 / 329600 : ℝ) (2249137 / 659200 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel27 : (94427549078823 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (2249137 / 659200 : ℝ)..(562357 / 164800 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (2249137 / 659200 : ℝ)) (b := (562357 / 164800 : ℝ))
    (l := (14711729246339935432 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (94427549078823 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((562357 / 164800 : ℝ) - (2249137 / 659200 : ℝ)) * (14711729246339935432 / 18446744073709551616 : ℝ) / denomMax (2249137 / 659200 : ℝ) (562357 / 164800 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel28 : (94437168473961 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (562357 / 164800 : ℝ)..(2249719 / 659200 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (562357 / 164800 : ℝ)) (b := (2249719 / 659200 : ℝ))
    (l := (14713116145980671847 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (94437168473961 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((2249719 / 659200 : ℝ) - (562357 / 164800 : ℝ)) * (14713116145980671847 / 18446744073709551616 : ℝ) / denomMax (562357 / 164800 : ℝ) (2249719 / 659200 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel29 : (94446795569194 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (2249719 / 659200 : ℝ)..(225001 / 65920 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (2249719 / 659200 : ℝ)) (b := (225001 / 65920 : ℝ))
    (l := (14714503700984907587 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (94446795569194 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((225001 / 65920 : ℝ) - (2249719 / 659200 : ℝ)) * (14714503700984907587 / 18446744073709551616 : ℝ) / denomMax (2249719 / 659200 : ℝ) (225001 / 65920 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel30 : (94456430368727 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (225001 / 65920 : ℝ)..(2250301 / 659200 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (225001 / 65920 : ℝ)) (b := (2250301 / 659200 : ℝ))
    (l := (14715891911821207334 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (94456430368727 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((2250301 / 659200 : ℝ) - (225001 / 65920 : ℝ)) * (14715891911821207334 / 18446744073709551616 : ℝ) / denomMax (225001 / 65920 : ℝ) (2250301 / 659200 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel31 : (94466072876775 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (2250301 / 659200 : ℝ)..(70331 / 20600 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (2250301 / 659200 : ℝ)) (b := (70331 / 20600 : ℝ))
    (l := (14717280778958586239 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (30123 / 10000000 : ℝ))
  have hp : (94466072876775 / 18446744073709551616 : ℝ) ≤ 8 * (30123 / 10000000 : ℝ) *
      (((70331 / 20600 : ℝ) - (2250301 / 659200 : ℝ)) * (14717280778958586239 / 18446744073709551616 : ℝ) / denomMax (2250301 / 659200 : ℝ) (70331 / 20600 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

theorem lower : (3018169731756593 / 18446744073709551616 : ℝ) ≤
    8 * (30123 / 10000000 : ℝ) * ∫ s in (17 / 5 : ℝ)..(70331 / 20600 : ℝ), density s := by
  have he := integral_grid_sum (17 / 5 : ℝ) (70331 / 20600 : ℝ) 32 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [endpoint, alpha, beta])
  norm_num [Finset.sum_range_succ] at he
  linarith only [panel00, panel01, panel02, panel03, panel04, panel05, panel06, panel07, panel08, panel09, panel10, panel11, panel12, panel13, panel14, panel15, panel16, panel17, panel18, panel19, panel20, panel21, panel22, panel23, panel24, panel25, panel26, panel27, panel28, panel29, panel30, panel31, he]

end Wu18938Campaign.M3.Confirmed.TableRow14
