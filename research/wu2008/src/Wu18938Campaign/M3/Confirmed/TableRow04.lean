import Wu18938Campaign.M3.Confirmed.TableBounds

noncomputable section
namespace Wu18938Campaign.M3.Confirmed.TableRow04
open Real Set MeasureTheory QuarterTrim
open WuSource.SrcSixthGain Wu18938Campaign.M3.Confirmed.TableBounds

private theorem panel00 : (2920735165586923 / 18446744073709551616 : ℝ) ≤
    8 * (141585 / 10000000 : ℝ) * ∫ s in (12 / 5 : ℝ)..(769 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (12 / 5 : ℝ)) (b := (769 / 320 : ℝ))
    (l := (12647456407845647263 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (141585 / 10000000 : ℝ))
  have hp : (2920735165586923 / 18446744073709551616 : ℝ) ≤ 8 * (141585 / 10000000 : ℝ) *
      (((769 / 320 : ℝ) - (12 / 5 : ℝ)) * (12647456407845647263 / 18446744073709551616 : ℝ) / denomMax (12 / 5 : ℝ) (769 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel01 : (2920055211267648 / 18446744073709551616 : ℝ) ≤
    8 * (141585 / 10000000 : ℝ) * ∫ s in (769 / 320 : ℝ)..(77 / 32 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (769 / 320 : ℝ)) (b := (77 / 32 : ℝ))
    (l := (12651605449381507943 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (141585 / 10000000 : ℝ))
  have hp : (2920055211267648 / 18446744073709551616 : ℝ) ≤ 8 * (141585 / 10000000 : ℝ) *
      (((77 / 32 : ℝ) - (769 / 320 : ℝ)) * (12651605449381507943 / 18446744073709551616 : ℝ) / denomMax (769 / 320 : ℝ) (77 / 32 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel02 : (2919383688060704 / 18446744073709551616 : ℝ) ≤
    8 * (141585 / 10000000 : ℝ) * ∫ s in (77 / 32 : ℝ)..(771 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (77 / 32 : ℝ)) (b := (771 / 320 : ℝ))
    (l := (12655763458481270509 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (141585 / 10000000 : ℝ))
  have hp : (2919383688060704 / 18446744073709551616 : ℝ) ≤ 8 * (141585 / 10000000 : ℝ) *
      (((771 / 320 : ℝ) - (77 / 32 : ℝ)) * (12655763458481270509 / 18446744073709551616 : ℝ) / denomMax (77 / 32 : ℝ) (771 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel03 : (2918720584721005 / 18446744073709551616 : ℝ) ≤
    8 * (141585 / 10000000 : ℝ) * ∫ s in (771 / 320 : ℝ)..(193 / 80 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (771 / 320 : ℝ)) (b := (193 / 80 : ℝ))
    (l := (12659930464355534216 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (141585 / 10000000 : ℝ))
  have hp : (2918720584721005 / 18446744073709551616 : ℝ) ≤ 8 * (141585 / 10000000 : ℝ) *
      (((193 / 80 : ℝ) - (771 / 320 : ℝ)) * (12659930464355534216 / 18446744073709551616 : ℝ) / denomMax (771 / 320 : ℝ) (193 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel04 : (2918065890154691 / 18446744073709551616 : ℝ) ≤
    8 * (141585 / 10000000 : ℝ) * ∫ s in (193 / 80 : ℝ)..(773 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (193 / 80 : ℝ)) (b := (773 / 320 : ℝ))
    (l := (12664106496342360622 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (141585 / 10000000 : ℝ))
  have hp : (2918065890154691 / 18446744073709551616 : ℝ) ≤ 8 * (141585 / 10000000 : ℝ) *
      (((773 / 320 : ℝ) - (193 / 80 : ℝ)) * (12664106496342360622 / 18446744073709551616 : ℝ) / denomMax (193 / 80 : ℝ) (773 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel05 : (2917419593418657 / 18446744073709551616 : ℝ) ≤
    8 * (141585 / 10000000 : ℝ) * ∫ s in (773 / 320 : ℝ)..(387 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (773 / 320 : ℝ)) (b := (387 / 160 : ℝ))
    (l := (12668291583907972067 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (141585 / 10000000 : ℝ))
  have hp : (2917419593418657 / 18446744073709551616 : ℝ) ≤ 8 * (141585 / 10000000 : ℝ) *
      (((387 / 160 : ℝ) - (773 / 320 : ℝ)) * (12668291583907972067 / 18446744073709551616 : ℝ) / denomMax (773 / 320 : ℝ) (387 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel06 : (2916781683720085 / 18446744073709551616 : ℝ) ≤
    8 * (141585 / 10000000 : ℝ) * ∫ s in (387 / 160 : ℝ)..(155 / 64 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (387 / 160 : ℝ)) (b := (155 / 64 : ℝ))
    (l := (12672485756647454757 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (141585 / 10000000 : ℝ))
  have hp : (2916781683720085 / 18446744073709551616 : ℝ) ≤ 8 * (141585 / 10000000 : ℝ) *
      (((155 / 64 : ℝ) - (387 / 160 : ℝ)) * (12672485756647454757 / 18446744073709551616 : ℝ) / denomMax (387 / 160 : ℝ) (155 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel07 : (2916152150415988 / 18446744073709551616 : ℝ) ≤
    8 * (141585 / 10000000 : ℝ) * ∫ s in (155 / 64 : ℝ)..(97 / 40 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (155 / 64 : ℝ)) (b := (97 / 40 : ℝ))
    (l := (12676689044285466511 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (141585 / 10000000 : ℝ))
  have hp : (2916152150415988 / 18446744073709551616 : ℝ) ≤ 8 * (141585 / 10000000 : ℝ) *
      (((97 / 40 : ℝ) - (155 / 64 : ℝ)) * (12676689044285466511 / 18446744073709551616 : ℝ) / denomMax (155 / 64 : ℝ) (97 / 40 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel08 : (2915530983012760 / 18446744073709551616 : ℝ) ≤
    8 * (141585 / 10000000 : ℝ) * ∫ s in (97 / 40 : ℝ)..(777 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (97 / 40 : ℝ)) (b := (777 / 320 : ℝ))
    (l := (12680901476676949183 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (141585 / 10000000 : ℝ))
  have hp : (2915530983012760 / 18446744073709551616 : ℝ) ≤ 8 * (141585 / 10000000 : ℝ) *
      (((777 / 320 : ℝ) - (97 / 40 : ℝ)) * (12680901476676949183 / 18446744073709551616 : ℝ) / denomMax (97 / 40 : ℝ) (777 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel09 : (2914918171165730 / 18446744073709551616 : ℝ) ≤
    8 * (141585 / 10000000 : ℝ) * ∫ s in (777 / 320 : ℝ)..(389 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (777 / 320 : ℝ)) (b := (389 / 160 : ℝ))
    (l := (12685123083807845815 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (141585 / 10000000 : ℝ))
  have hp : (2914918171165730 / 18446744073709551616 : ℝ) ≤ 8 * (141585 / 10000000 : ℝ) *
      (((389 / 160 : ℝ) - (777 / 320 : ℝ)) * (12685123083807845815 / 18446744073709551616 : ℝ) / denomMax (777 / 320 : ℝ) (389 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel10 : (2914313704678726 / 18446744073709551616 : ℝ) ≤
    8 * (141585 / 10000000 : ℝ) * ∫ s in (389 / 160 : ℝ)..(779 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (389 / 160 : ℝ)) (b := (779 / 320 : ℝ))
    (l := (12689353895795822540 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (141585 / 10000000 : ℝ))
  have hp : (2914313704678726 / 18446744073709551616 : ℝ) ≤ 8 * (141585 / 10000000 : ℝ) *
      (((779 / 320 : ℝ) - (389 / 160 : ℝ)) * (12689353895795822540 / 18446744073709551616 : ℝ) / denomMax (389 / 160 : ℝ) (779 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel11 : (2913717573503644 / 18446744073709551616 : ℝ) ≤
    8 * (141585 / 10000000 : ℝ) * ∫ s in (779 / 320 : ℝ)..(39 / 16 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (779 / 320 : ℝ)) (b := (39 / 16 : ℝ))
    (l := (12693593942890995289 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (141585 / 10000000 : ℝ))
  have hp : (2913717573503644 / 18446744073709551616 : ℝ) ≤ 8 * (141585 / 10000000 : ℝ) *
      (((39 / 16 : ℝ) - (779 / 320 : ℝ)) * (12693593942890995289 / 18446744073709551616 : ℝ) / denomMax (779 / 320 : ℝ) (39 / 16 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel12 : (2913129767740025 / 18446744073709551616 : ℝ) ≤
    8 * (141585 / 10000000 : ℝ) * ∫ s in (39 / 16 : ℝ)..(781 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (39 / 16 : ℝ)) (b := (781 / 320 : ℝ))
    (l := (12697843255476661328 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (141585 / 10000000 : ℝ))
  have hp : (2913129767740025 / 18446744073709551616 : ℝ) ≤ 8 * (141585 / 10000000 : ℝ) *
      (((781 / 320 : ℝ) - (39 / 16 : ℝ)) * (12697843255476661328 / 18446744073709551616 : ℝ) / denomMax (39 / 16 : ℝ) (781 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel13 : (2912550277634635 / 18446744073709551616 : ℝ) ≤
    8 * (141585 / 10000000 : ℝ) * ∫ s in (781 / 320 : ℝ)..(391 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (781 / 320 : ℝ)) (b := (391 / 160 : ℝ))
    (l := (12702101864070035667 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (141585 / 10000000 : ℝ))
  have hp : (2912550277634635 / 18446744073709551616 : ℝ) ≤ 8 * (141585 / 10000000 : ℝ) *
      (((391 / 160 : ℝ) - (781 / 320 : ℝ)) * (12702101864070035667 / 18446744073709551616 : ℝ) / denomMax (781 / 320 : ℝ) (391 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel14 : (2911979093581059 / 18446744073709551616 : ℝ) ≤
    8 * (141585 / 10000000 : ℝ) * ∫ s in (391 / 160 : ℝ)..(783 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (391 / 160 : ℝ)) (b := (783 / 320 : ℝ))
    (l := (12706369799322992375 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (141585 / 10000000 : ℝ))
  have hp : (2911979093581059 / 18446744073709551616 : ℝ) ≤ 8 * (141585 / 10000000 : ℝ) *
      (((783 / 320 : ℝ) - (391 / 160 : ℝ)) * (12706369799322992375 / 18446744073709551616 : ℝ) / denomMax (391 / 160 : ℝ) (783 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel15 : (2911416206119296 / 18446744073709551616 : ℝ) ≤
    8 * (141585 / 10000000 : ℝ) * ∫ s in (783 / 320 : ℝ)..(49 / 20 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (783 / 320 : ℝ)) (b := (49 / 20 : ℝ))
    (l := (12710647092022810846 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (141585 / 10000000 : ℝ))
  have hp : (2911416206119296 / 18446744073709551616 : ℝ) ≤ 8 * (141585 / 10000000 : ℝ) *
      (((49 / 20 : ℝ) - (783 / 320 : ℝ)) * (12710647092022810846 / 18446744073709551616 : ℝ) / denomMax (783 / 320 : ℝ) (49 / 20 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel16 : (2910861605935357 / 18446744073709551616 : ℝ) ≤
    8 * (141585 / 10000000 : ℝ) * ∫ s in (49 / 20 : ℝ)..(157 / 64 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (49 / 20 : ℝ)) (b := (157 / 64 : ℝ))
    (l := (12714933773092927052 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (141585 / 10000000 : ℝ))
  have hp : (2910861605935357 / 18446744073709551616 : ℝ) ≤ 8 * (141585 / 10000000 : ℝ) *
      (((157 / 64 : ℝ) - (49 / 20 : ℝ)) * (12714933773092927052 / 18446744073709551616 : ℝ) / denomMax (49 / 20 : ℝ) (157 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel17 : (2910315283860883 / 18446744073709551616 : ℝ) ≤
    8 * (141585 / 10000000 : ℝ) * ∫ s in (157 / 64 : ℝ)..(393 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (157 / 64 : ℝ)) (b := (393 / 160 : ℝ))
    (l := (12719229873593689815 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (141585 / 10000000 : ℝ))
  have hp : (2910315283860883 / 18446744073709551616 : ℝ) ≤ 8 * (141585 / 10000000 : ℝ) *
      (((393 / 160 : ℝ) - (157 / 64 : ℝ)) * (12719229873593689815 / 18446744073709551616 : ℝ) / denomMax (157 / 64 : ℝ) (393 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel18 : (2909777230872755 / 18446744073709551616 : ℝ) ≤
    8 * (141585 / 10000000 : ℝ) * ∫ s in (393 / 160 : ℝ)..(787 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (393 / 160 : ℝ)) (b := (787 / 320 : ℝ))
    (l := (12723535424723122151 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (141585 / 10000000 : ℝ))
  have hp : (2909777230872755 / 18446744073709551616 : ℝ) ≤ 8 * (141585 / 10000000 : ℝ) *
      (((787 / 320 : ℝ) - (393 / 160 : ℝ)) * (12723535424723122151 / 18446744073709551616 : ℝ) / denomMax (393 / 160 : ℝ) (787 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel19 : (2909247438092715 / 18446744073709551616 : ℝ) ≤
    8 * (141585 / 10000000 : ℝ) * ∫ s in (787 / 320 : ℝ)..(197 / 80 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (787 / 320 : ℝ)) (b := (197 / 80 : ℝ))
    (l := (12727850457817687715 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (141585 / 10000000 : ℝ))
  have hp : (2909247438092715 / 18446744073709551616 : ℝ) ≤ 8 * (141585 / 10000000 : ℝ) *
      (((197 / 80 : ℝ) - (787 / 320 : ℝ)) * (12727850457817687715 / 18446744073709551616 : ℝ) / denomMax (787 / 320 : ℝ) (197 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel20 : (2908725896787003 / 18446744073709551616 : ℝ) ≤
    8 * (141585 / 10000000 : ℝ) * ∫ s in (197 / 80 : ℝ)..(789 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (197 / 80 : ℝ)) (b := (789 / 320 : ℝ))
    (l := (12732175004353062388 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (141585 / 10000000 : ℝ))
  have hp : (2908725896787003 / 18446744073709551616 : ℝ) ≤ 8 * (141585 / 10000000 : ℝ) *
      (((789 / 320 : ℝ) - (197 / 80 : ℝ)) * (12732175004353062388 / 18446744073709551616 : ℝ) / denomMax (197 / 80 : ℝ) (789 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel21 : (2908212598365984 / 18446744073709551616 : ℝ) ≤
    8 * (141585 / 10000000 : ℝ) * ∫ s in (789 / 320 : ℝ)..(79 / 32 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (789 / 320 : ℝ)) (b := (79 / 32 : ℝ))
    (l := (12736509095944911054 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (141585 / 10000000 : ℝ))
  have hp : (2908212598365984 / 18446744073709551616 : ℝ) ≤ 8 * (141585 / 10000000 : ℝ) *
      (((79 / 32 : ℝ) - (789 / 320 : ℝ)) * (12736509095944911054 / 18446744073709551616 : ℝ) / denomMax (789 / 320 : ℝ) (79 / 32 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel22 : (2907707534383795 / 18446744073709551616 : ℝ) ≤
    8 * (141585 / 10000000 : ℝ) * ∫ s in (79 / 32 : ℝ)..(791 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (79 / 32 : ℝ)) (b := (791 / 320 : ℝ))
    (l := (12740852764349669597 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (141585 / 10000000 : ℝ))
  have hp : (2907707534383795 / 18446744073709551616 : ℝ) ≤ 8 * (141585 / 10000000 : ℝ) *
      (((791 / 320 : ℝ) - (79 / 32 : ℝ)) * (12740852764349669597 / 18446744073709551616 : ℝ) / denomMax (79 / 32 : ℝ) (791 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel23 : (2907210696537991 / 18446744073709551616 : ℝ) ≤
    8 * (141585 / 10000000 : ℝ) * ∫ s in (791 / 320 : ℝ)..(99 / 40 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (791 / 320 : ℝ)) (b := (99 / 40 : ℝ))
    (l := (12745206041465332173 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (141585 / 10000000 : ℝ))
  have hp : (2907210696537991 / 18446744073709551616 : ℝ) ≤ 8 * (141585 / 10000000 : ℝ) *
      (((99 / 40 : ℝ) - (791 / 320 : ℝ)) * (12745206041465332173 / 18446744073709551616 : ℝ) / denomMax (791 / 320 : ℝ) (99 / 40 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel24 : (2906722076669202 / 18446744073709551616 : ℝ) ≤
    8 * (141585 / 10000000 : ℝ) * ∫ s in (99 / 40 : ℝ)..(793 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (99 / 40 : ℝ)) (b := (793 / 320 : ℝ))
    (l := (12749568959332243779 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (141585 / 10000000 : ℝ))
  have hp : (2906722076669202 / 18446744073709551616 : ℝ) ≤ 8 * (141585 / 10000000 : ℝ) *
      (((793 / 320 : ℝ) - (99 / 40 : ℝ)) * (12749568959332243779 / 18446744073709551616 : ℝ) / denomMax (99 / 40 : ℝ) (793 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel25 : (2906241666760789 / 18446744073709551616 : ℝ) ≤
    8 * (141585 / 10000000 : ℝ) * ∫ s in (793 / 320 : ℝ)..(397 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (793 / 320 : ℝ)) (b := (397 / 160 : ℝ))
    (l := (12753941550133898186 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (141585 / 10000000 : ℝ))
  have hp : (2906241666760789 / 18446744073709551616 : ℝ) ≤ 8 * (141585 / 10000000 : ℝ) *
      (((397 / 160 : ℝ) - (793 / 320 : ℝ)) * (12753941550133898186 / 18446744073709551616 : ℝ) / denomMax (793 / 320 : ℝ) (397 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel26 : (2905769458938519 / 18446744073709551616 : ℝ) ≤
    8 * (141585 / 10000000 : ℝ) * ∫ s in (397 / 160 : ℝ)..(159 / 64 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (397 / 160 : ℝ)) (b := (159 / 64 : ℝ))
    (l := (12758323846197741253 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (141585 / 10000000 : ℝ))
  have hp : (2905769458938519 / 18446744073709551616 : ℝ) ≤ 8 * (141585 / 10000000 : ℝ) *
      (((159 / 64 : ℝ) - (397 / 160 : ℝ)) * (12758323846197741253 / 18446744073709551616 : ℝ) / denomMax (397 / 160 : ℝ) (159 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel27 : (2905305445470231 / 18446744073709551616 : ℝ) ≤
    8 * (141585 / 10000000 : ℝ) * ∫ s in (159 / 64 : ℝ)..(199 / 80 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (159 / 64 : ℝ)) (b := (199 / 80 : ℝ))
    (l := (12762715879995979682 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (141585 / 10000000 : ℝ))
  have hp : (2905305445470231 / 18446744073709551616 : ℝ) ≤ 8 * (141585 / 10000000 : ℝ) *
      (((199 / 80 : ℝ) - (159 / 64 : ℝ)) * (12762715879995979682 / 18446744073709551616 : ℝ) / denomMax (159 / 64 : ℝ) (199 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel28 : (2904849618765522 / 18446744073709551616 : ℝ) ≤
    8 * (141585 / 10000000 : ℝ) * ∫ s in (199 / 80 : ℝ)..(797 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (199 / 80 : ℝ)) (b := (797 / 320 : ℝ))
    (l := (12767117684146395253 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (141585 / 10000000 : ℝ))
  have hp : (2904849618765522 / 18446744073709551616 : ℝ) ≤ 8 * (141585 / 10000000 : ℝ) *
      (((797 / 320 : ℝ) - (199 / 80 : ℝ)) * (12767117684146395253 / 18446744073709551616 : ℝ) / denomMax (199 / 80 : ℝ) (797 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel29 : (2904401971375429 / 18446744073709551616 : ℝ) ≤
    8 * (141585 / 10000000 : ℝ) * ∫ s in (797 / 320 : ℝ)..(399 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (797 / 320 : ℝ)) (b := (399 / 160 : ℝ))
    (l := (12771529291413164578 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (141585 / 10000000 : ℝ))
  have hp : (2904401971375429 / 18446744073709551616 : ℝ) ≤ 8 * (141585 / 10000000 : ℝ) *
      (((399 / 160 : ℝ) - (797 / 320 : ℝ)) * (12771529291413164578 / 18446744073709551616 : ℝ) / denomMax (797 / 320 : ℝ) (399 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel30 : (2903962495992125 / 18446744073709551616 : ℝ) ≤
    8 * (141585 / 10000000 : ℝ) * ∫ s in (399 / 160 : ℝ)..(799 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (399 / 160 : ℝ)) (b := (799 / 320 : ℝ))
    (l := (12775950734707684423 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (141585 / 10000000 : ℝ))
  have hp : (2903962495992125 / 18446744073709551616 : ℝ) ≤ 8 * (141585 / 10000000 : ℝ) *
      (((799 / 320 : ℝ) - (399 / 160 : ℝ)) * (12775950734707684423 / 18446744073709551616 : ℝ) / denomMax (399 / 160 : ℝ) (799 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel31 : (2903531185448612 / 18446744073709551616 : ℝ) ≤
    8 * (141585 / 10000000 : ℝ) * ∫ s in (799 / 320 : ℝ)..(5 / 2 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (799 / 320 : ℝ)) (b := (5 / 2 : ℝ))
    (l := (12780382047089402639 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (141585 / 10000000 : ℝ))
  have hp : (2903531185448612 / 18446744073709551616 : ℝ) ≤ 8 * (141585 / 10000000 : ℝ) *
      (((5 / 2 : ℝ) - (799 / 320 : ℝ)) * (12780382047089402639 / 18446744073709551616 : ℝ) / denomMax (799 / 320 : ℝ) (5 / 2 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

theorem lower : (93167711949038488 / 18446744073709551616 : ℝ) ≤
    8 * (141585 / 10000000 : ℝ) * ∫ s in (12 / 5 : ℝ)..(5 / 2 : ℝ), density s := by
  have he := integral_grid_sum (12 / 5 : ℝ) (5 / 2 : ℝ) 32 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [endpoint, alpha, beta])
  norm_num [Finset.sum_range_succ] at he
  linarith only [panel00, panel01, panel02, panel03, panel04, panel05, panel06, panel07, panel08, panel09, panel10, panel11, panel12, panel13, panel14, panel15, panel16, panel17, panel18, panel19, panel20, panel21, panel22, panel23, panel24, panel25, panel26, panel27, panel28, panel29, panel30, panel31, he]

end Wu18938Campaign.M3.Confirmed.TableRow04
