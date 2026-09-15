import Wu18938Campaign.M3.Confirmed.TableBounds

noncomputable section
namespace Wu18938Campaign.M3.Confirmed.TableRow02
open Real Set MeasureTheory QuarterTrim
open WuSource.SrcSixthGain Wu18938Campaign.M3.Confirmed.TableBounds

private theorem panel00 : (3657460025720968 / 18446744073709551616 : ℝ) ≤
    8 * (173631 / 10000000 : ℝ) * ∫ s in (11 / 5 : ℝ)..(141 / 64 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (11 / 5 : ℝ)) (b := (141 / 64 : ℝ))
    (l := (12399324535185919907 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (173631 / 10000000 : ℝ))
  have hp : (3657460025720968 / 18446744073709551616 : ℝ) ≤ 8 * (173631 / 10000000 : ℝ) *
      (((141 / 64 : ℝ) - (11 / 5 : ℝ)) * (12399324535185919907 / 18446744073709551616 : ℝ) / denomMax (11 / 5 : ℝ) (141 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel01 : (3655926742361701 / 18446744073709551616 : ℝ) ≤
    8 * (173631 / 10000000 : ℝ) * ∫ s in (141 / 64 : ℝ)..(353 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (141 / 64 : ℝ)) (b := (353 / 160 : ℝ))
    (l := (12402955069205542521 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (173631 / 10000000 : ℝ))
  have hp : (3655926742361701 / 18446744073709551616 : ℝ) ≤ 8 * (173631 / 10000000 : ℝ) *
      (((353 / 160 : ℝ) - (141 / 64 : ℝ)) * (12402955069205542521 / 18446744073709551616 : ℝ) / denomMax (141 / 64 : ℝ) (353 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel02 : (3654405100300712 / 18446744073709551616 : ℝ) ≤
    8 * (173631 / 10000000 : ℝ) * ∫ s in (353 / 160 : ℝ)..(707 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (353 / 160 : ℝ)) (b := (707 / 320 : ℝ))
    (l := (12406592937668924241 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (173631 / 10000000 : ℝ))
  have hp : (3654405100300712 / 18446744073709551616 : ℝ) ≤ 8 * (173631 / 10000000 : ℝ) *
      (((707 / 320 : ℝ) - (353 / 160 : ℝ)) * (12406592937668924241 / 18446744073709551616 : ℝ) / denomMax (353 / 160 : ℝ) (707 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel03 : (3652895072241156 / 18446744073709551616 : ℝ) ≤
    8 * (173631 / 10000000 : ℝ) * ∫ s in (707 / 320 : ℝ)..(177 / 80 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (707 / 320 : ℝ)) (b := (177 / 80 : ℝ))
    (l := (12410238162895176881 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (173631 / 10000000 : ℝ))
  have hp : (3652895072241156 / 18446744073709551616 : ℝ) ≤ 8 * (173631 / 10000000 : ℝ) *
      (((177 / 80 : ℝ) - (707 / 320 : ℝ)) * (12410238162895176881 / 18446744073709551616 : ℝ) / denomMax (707 / 320 : ℝ) (177 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel04 : (3651396631129163 / 18446744073709551616 : ℝ) ≤
    8 * (173631 / 10000000 : ℝ) * ∫ s in (177 / 80 : ℝ)..(709 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (177 / 80 : ℝ)) (b := (709 / 320 : ℝ))
    (l := (12413890767294348844 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (173631 / 10000000 : ℝ))
  have hp : (3651396631129163 / 18446744073709551616 : ℝ) ≤ 8 * (173631 / 10000000 : ℝ) *
      (((709 / 320 : ℝ) - (177 / 80 : ℝ)) * (12413890767294348844 / 18446744073709551616 : ℝ) / denomMax (177 / 80 : ℝ) (709 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel05 : (3649909750152577 / 18446744073709551616 : ℝ) ≤
    8 * (173631 / 10000000 : ℝ) * ∫ s in (709 / 320 : ℝ)..(71 / 32 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (709 / 320 : ℝ)) (b := (71 / 32 : ℝ))
    (l := (12417550773367890191 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (173631 / 10000000 : ℝ))
  have hp : (3649909750152577 / 18446744073709551616 : ℝ) ≤ 8 * (173631 / 10000000 : ℝ) *
      (((71 / 32 : ℝ) - (709 / 320 : ℝ)) * (12417550773367890191 / 18446744073709551616 : ℝ) / denomMax (709 / 320 : ℝ) (71 / 32 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel06 : (3648434402739712 / 18446744073709551616 : ℝ) ≤
    8 * (173631 / 10000000 : ℝ) * ∫ s in (71 / 32 : ℝ)..(711 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (71 / 32 : ℝ)) (b := (711 / 320 : ℝ))
    (l := (12421218203709120561 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (173631 / 10000000 : ℝ))
  have hp : (3648434402739712 / 18446744073709551616 : ℝ) ≤ 8 * (173631 / 10000000 : ℝ) *
      (((711 / 320 : ℝ) - (71 / 32 : ℝ)) * (12421218203709120561 / 18446744073709551616 : ℝ) / denomMax (71 / 32 : ℝ) (711 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel07 : (3646970562558114 / 18446744073709551616 : ℝ) ≤
    8 * (173631 / 10000000 : ℝ) * ∫ s in (711 / 320 : ℝ)..(89 / 40 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (711 / 320 : ℝ)) (b := (89 / 40 : ℝ))
    (l := (12424893081003699987 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (173631 / 10000000 : ℝ))
  have hp : (3646970562558114 / 18446744073709551616 : ℝ) ≤ 8 * (173631 / 10000000 : ℝ) *
      (((89 / 40 : ℝ) - (711 / 320 : ℝ)) * (12424893081003699987 / 18446744073709551616 : ℝ) / denomMax (711 / 320 : ℝ) (89 / 40 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel08 : (3645518203513346 / 18446744073709551616 : ℝ) ≤
    8 * (173631 / 10000000 : ℝ) * ∫ s in (89 / 40 : ℝ)..(713 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (89 / 40 : ℝ)) (b := (713 / 320 : ℝ))
    (l := (12428575428030102618 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (173631 / 10000000 : ℝ))
  have hp : (3645518203513346 / 18446744073709551616 : ℝ) ≤ 8 * (173631 / 10000000 : ℝ) *
      (((713 / 320 : ℝ) - (89 / 40 : ℝ)) * (12428575428030102618 / 18446744073709551616 : ℝ) / denomMax (89 / 40 : ℝ) (713 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel09 : (3644077299747776 / 18446744073709551616 : ℝ) ≤
    8 * (173631 / 10000000 : ℝ) * ∫ s in (713 / 320 : ℝ)..(357 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (713 / 320 : ℝ)) (b := (357 / 160 : ℝ))
    (l := (12432265267660093367 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (173631 / 10000000 : ℝ))
  have hp : (3644077299747776 / 18446744073709551616 : ℝ) ≤ 8 * (173631 / 10000000 : ℝ) *
      (((357 / 160 : ℝ) - (713 / 320 : ℝ)) * (12432265267660093367 / 18446744073709551616 : ℝ) / denomMax (713 / 320 : ℝ) (357 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel10 : (3642647825639386 / 18446744073709551616 : ℝ) ≤
    8 * (173631 / 10000000 : ℝ) * ∫ s in (357 / 160 : ℝ)..(143 / 64 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (357 / 160 : ℝ)) (b := (143 / 64 : ℝ))
    (l := (12435962622859207510 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (173631 / 10000000 : ℝ))
  have hp : (3642647825639386 / 18446744073709551616 : ℝ) ≤ 8 * (173631 / 10000000 : ℝ) *
      (((143 / 64 : ℝ) - (357 / 160 : ℝ)) * (12435962622859207510 / 18446744073709551616 : ℝ) / denomMax (357 / 160 : ℝ) (143 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel11 : (3641229755800591 / 18446744073709551616 : ℝ) ≤
    8 * (173631 / 10000000 : ℝ) * ∫ s in (143 / 64 : ℝ)..(179 / 80 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (143 / 64 : ℝ)) (b := (179 / 80 : ℝ))
    (l := (12439667516687233259 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (173631 / 10000000 : ℝ))
  have hp : (3641229755800591 / 18446744073709551616 : ℝ) ≤ 8 * (173631 / 10000000 : ℝ) *
      (((179 / 80 : ℝ) - (143 / 64 : ℝ)) * (12439667516687233259 / 18446744073709551616 : ℝ) / denomMax (143 / 64 : ℝ) (179 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel12 : (3639823065077068 / 18446744073709551616 : ℝ) ≤
    8 * (173631 / 10000000 : ℝ) * ∫ s in (179 / 80 : ℝ)..(717 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (179 / 80 : ℝ)) (b := (717 / 320 : ℝ))
    (l := (12443379972298697317 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (173631 / 10000000 : ℝ))
  have hp : (3639823065077068 / 18446744073709551616 : ℝ) ≤ 8 * (173631 / 10000000 : ℝ) *
      (((717 / 320 : ℝ) - (179 / 80 : ℝ)) * (12443379972298697317 / 18446744073709551616 : ℝ) / denomMax (179 / 80 : ℝ) (717 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel13 : (3638427728546600 / 18446744073709551616 : ℝ) ≤
    8 * (173631 / 10000000 : ℝ) * ∫ s in (717 / 320 : ℝ)..(359 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (717 / 320 : ℝ)) (b := (359 / 160 : ℝ))
    (l := (12447100012943353463 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (173631 / 10000000 : ℝ))
  have hp : (3638427728546600 / 18446744073709551616 : ℝ) ≤ 8 * (173631 / 10000000 : ℝ) *
      (((359 / 160 : ℝ) - (717 / 320 : ℝ)) * (12447100012943353463 / 18446744073709551616 : ℝ) / denomMax (717 / 320 : ℝ) (359 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel14 : (3637043721517936 / 18446744073709551616 : ℝ) ≤
    8 * (173631 / 10000000 : ℝ) * ∫ s in (359 / 160 : ℝ)..(719 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (359 / 160 : ℝ)) (b := (719 / 320 : ℝ))
    (l := (12450827661966674160 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (173631 / 10000000 : ℝ))
  have hp : (3637043721517936 / 18446744073709551616 : ℝ) ≤ 8 * (173631 / 10000000 : ℝ) *
      (((719 / 320 : ℝ) - (359 / 160 : ℝ)) * (12450827661966674160 / 18446744073709551616 : ℝ) / denomMax (359 / 160 : ℝ) (719 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel15 : (3635671019529656 / 18446744073709551616 : ℝ) ≤
    8 * (173631 / 10000000 : ℝ) * ∫ s in (719 / 320 : ℝ)..(9 / 4 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (719 / 320 : ℝ)) (b := (9 / 4 : ℝ))
    (l := (12454562942810345226 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (173631 / 10000000 : ℝ))
  have hp : (3635671019529656 / 18446744073709551616 : ℝ) ≤ 8 * (173631 / 10000000 : ℝ) *
      (((9 / 4 : ℝ) - (719 / 320 : ℝ)) * (12454562942810345226 / 18446744073709551616 : ℝ) / denomMax (719 / 320 : ℝ) (9 / 4 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel16 : (3634309598349054 / 18446744073709551616 : ℝ) ≤
    8 * (173631 / 10000000 : ℝ) * ∫ s in (9 / 4 : ℝ)..(721 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (9 / 4 : ℝ)) (b := (721 / 320 : ℝ))
    (l := (12458305879012763589 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (173631 / 10000000 : ℝ))
  have hp : (3634309598349054 / 18446744073709551616 : ℝ) ≤ 8 * (173631 / 10000000 : ℝ) *
      (((721 / 320 : ℝ) - (9 / 4 : ℝ)) * (12458305879012763589 / 18446744073709551616 : ℝ) / denomMax (9 / 4 : ℝ) (721 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel17 : (3632959433971033 / 18446744073709551616 : ℝ) ≤
    8 * (173631 / 10000000 : ℝ) * ∫ s in (721 / 320 : ℝ)..(361 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (721 / 320 : ℝ)) (b := (361 / 160 : ℝ))
    (l := (12462056494209538138 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (173631 / 10000000 : ℝ))
  have hp : (3632959433971033 / 18446744073709551616 : ℝ) ≤ 8 * (173631 / 10000000 : ℝ) *
      (((361 / 160 : ℝ) - (721 / 320 : ℝ)) * (12462056494209538138 / 18446744073709551616 : ℝ) / denomMax (721 / 320 : ℝ) (361 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel18 : (3631620502617008 / 18446744073709551616 : ℝ) ≤
    8 * (173631 / 10000000 : ℝ) * ∫ s in (361 / 160 : ℝ)..(723 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (361 / 160 : ℝ)) (b := (723 / 320 : ℝ))
    (l := (12465814812133993705 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (173631 / 10000000 : ℝ))
  have hp : (3631620502617008 / 18446744073709551616 : ℝ) ≤ 8 * (173631 / 10000000 : ℝ) *
      (((723 / 320 : ℝ) - (361 / 160 : ℝ)) * (12465814812133993705 / 18446744073709551616 : ℝ) / denomMax (361 / 160 : ℝ) (723 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel19 : (3630292780733823 / 18446744073709551616 : ℝ) ≤
    8 * (173631 / 10000000 : ℝ) * ∫ s in (723 / 320 : ℝ)..(181 / 80 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (723 / 320 : ℝ)) (b := (181 / 80 : ℝ))
    (l := (12469580856617678195 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (173631 / 10000000 : ℝ))
  have hp : (3630292780733823 / 18446744073709551616 : ℝ) ≤ 8 * (173631 / 10000000 : ℝ) *
      (((181 / 80 : ℝ) - (723 / 320 : ℝ)) * (12469580856617678195 / 18446744073709551616 : ℝ) / denomMax (723 / 320 : ℝ) (181 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel20 : (3628976244992687 / 18446744073709551616 : ℝ) ≤
    8 * (173631 / 10000000 : ℝ) * ∫ s in (181 / 80 : ℝ)..(145 / 64 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (181 / 80 : ℝ)) (b := (145 / 64 : ℝ))
    (l := (12473354651590872883 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (173631 / 10000000 : ℝ))
  have hp : (3628976244992687 / 18446744073709551616 : ℝ) ≤ 8 * (173631 / 10000000 : ℝ) *
      (((145 / 64 : ℝ) - (181 / 80 : ℝ)) * (12473354651590872883 / 18446744073709551616 : ℝ) / denomMax (181 / 80 : ℝ) (145 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel21 : (3627670872288107 / 18446744073709551616 : ℝ) ≤
    8 * (173631 / 10000000 : ℝ) * ∫ s in (145 / 64 : ℝ)..(363 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (145 / 64 : ℝ)) (b := (363 / 160 : ℝ))
    (l := (12477136221083105913 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (173631 / 10000000 : ℝ))
  have hp : (3627670872288107 / 18446744073709551616 : ℝ) ≤ 8 * (173631 / 10000000 : ℝ) *
      (((363 / 160 : ℝ) - (145 / 64 : ℝ)) * (12477136221083105913 / 18446744073709551616 : ℝ) / denomMax (145 / 64 : ℝ) (363 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel22 : (3626376639736847 / 18446744073709551616 : ℝ) ≤
    8 * (173631 / 10000000 : ℝ) * ∫ s in (363 / 160 : ℝ)..(727 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (363 / 160 : ℝ)) (b := (727 / 320 : ℝ))
    (l := (12480925589223669010 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (173631 / 10000000 : ℝ))
  have hp : (3626376639736847 / 18446744073709551616 : ℝ) ≤ 8 * (173631 / 10000000 : ℝ) *
      (((727 / 320 : ℝ) - (363 / 160 : ℝ)) * (12480925589223669010 / 18446744073709551616 : ℝ) / denomMax (363 / 160 : ℝ) (727 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel23 : (3625093524676892 / 18446744073709551616 : ℝ) ≤
    8 * (173631 / 10000000 : ℝ) * ∫ s in (727 / 320 : ℝ)..(91 / 40 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (727 / 320 : ℝ)) (b := (91 / 40 : ℝ))
    (l := (12484722780242137437 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (173631 / 10000000 : ℝ))
  have hp : (3625093524676892 / 18446744073709551616 : ℝ) ≤ 8 * (173631 / 10000000 : ℝ) *
      (((91 / 40 : ℝ) - (727 / 320 : ℝ)) * (12484722780242137437 / 18446744073709551616 : ℝ) / denomMax (727 / 320 : ℝ) (91 / 40 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel24 : (3623821504666421 / 18446744073709551616 : ℝ) ≤
    8 * (173631 / 10000000 : ℝ) * ∫ s in (91 / 40 : ℝ)..(729 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (91 / 40 : ℝ)) (b := (729 / 320 : ℝ))
    (l := (12488527818468893214 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (173631 / 10000000 : ℝ))
  have hp : (3623821504666421 / 18446744073709551616 : ℝ) ≤ 8 * (173631 / 10000000 : ℝ) *
      (((729 / 320 : ℝ) - (91 / 40 : ℝ)) * (12488527818468893214 / 18446744073709551616 : ℝ) / denomMax (91 / 40 : ℝ) (729 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel25 : (3622560557482801 / 18446744073709551616 : ℝ) ≤
    8 * (173631 / 10000000 : ℝ) * ∫ s in (729 / 320 : ℝ)..(73 / 32 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (729 / 320 : ℝ)) (b := (73 / 32 : ℝ))
    (l := (12492340728335651628 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (173631 / 10000000 : ℝ))
  have hp : (3622560557482801 / 18446744073709551616 : ℝ) ≤ 8 * (173631 / 10000000 : ℝ) *
      (((73 / 32 : ℝ) - (729 / 320 : ℝ)) * (12492340728335651628 / 18446744073709551616 : ℝ) / denomMax (729 / 320 : ℝ) (73 / 32 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel26 : (3621310661121581 / 18446744073709551616 : ℝ) ≤
    8 * (173631 / 10000000 : ℝ) * ∫ s in (73 / 32 : ℝ)..(731 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (73 / 32 : ℝ)) (b := (731 / 320 : ℝ))
    (l := (12496161534375991064 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (173631 / 10000000 : ℝ))
  have hp : (3621310661121581 / 18446744073709551616 : ℝ) ≤ 8 * (173631 / 10000000 : ℝ) *
      (((731 / 320 : ℝ) - (73 / 32 : ℝ)) * (12496161534375991064 / 18446744073709551616 : ℝ) / denomMax (73 / 32 : ℝ) (731 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel27 : (3620071793795507 / 18446744073709551616 : ℝ) ≤
    8 * (173631 / 10000000 : ℝ) * ∫ s in (731 / 320 : ℝ)..(183 / 80 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (731 / 320 : ℝ)) (b := (183 / 80 : ℝ))
    (l := (12499990261225886161 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (173631 / 10000000 : ℝ))
  have hp : (3620071793795507 / 18446744073709551616 : ℝ) ≤ 8 * (173631 / 10000000 : ℝ) *
      (((183 / 80 : ℝ) - (731 / 320 : ℝ)) * (12499990261225886161 / 18446744073709551616 : ℝ) / denomMax (731 / 320 : ℝ) (183 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel28 : (3618843933933539 / 18446744073709551616 : ℝ) ≤
    8 * (173631 / 10000000 : ℝ) * ∫ s in (183 / 80 : ℝ)..(733 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (183 / 80 : ℝ)) (b := (733 / 320 : ℝ))
    (l := (12503826933624244343 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (173631 / 10000000 : ℝ))
  have hp : (3618843933933539 / 18446744073709551616 : ℝ) ≤ 8 * (173631 / 10000000 : ℝ) *
      (((733 / 320 : ℝ) - (183 / 80 : ℝ)) * (12503826933624244343 / 18446744073709551616 : ℝ) / denomMax (183 / 80 : ℝ) (733 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel29 : (3617627060179888 / 18446744073709551616 : ℝ) ≤
    8 * (173631 / 10000000 : ℝ) * ∫ s in (733 / 320 : ℝ)..(367 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (733 / 320 : ℝ)) (b := (367 / 160 : ℝ))
    (l := (12507671576413445733 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (173631 / 10000000 : ℝ))
  have hp : (3617627060179888 / 18446744073709551616 : ℝ) ≤ 8 * (173631 / 10000000 : ℝ) *
      (((367 / 160 : ℝ) - (733 / 320 : ℝ)) * (12507671576413445733 / 18446744073709551616 : ℝ) / denomMax (733 / 320 : ℝ) (367 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel30 : (3616421151393062 / 18446744073709551616 : ℝ) ≤
    8 * (173631 / 10000000 : ℝ) * ∫ s in (367 / 160 : ℝ)..(147 / 64 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (367 / 160 : ℝ)) (b := (147 / 64 : ℝ))
    (l := (12511524214539886477 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (173631 / 10000000 : ℝ))
  have hp : (3616421151393062 / 18446744073709551616 : ℝ) ≤ 8 * (173631 / 10000000 : ℝ) *
      (((147 / 64 : ℝ) - (367 / 160 : ℝ)) * (12511524214539886477 / 18446744073709551616 : ℝ) / denomMax (367 / 160 : ℝ) (147 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel31 : (3615226186644914 / 18446744073709551616 : ℝ) ≤
    8 * (173631 / 10000000 : ℝ) * ∫ s in (147 / 64 : ℝ)..(23 / 10 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (147 / 64 : ℝ)) (b := (23 / 10 : ℝ))
    (l := (12515384873054525515 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (173631 / 10000000 : ℝ))
  have hp : (3615226186644914 / 18446744073709551616 : ℝ) ≤ 8 * (173631 / 10000000 : ℝ) *
      (((23 / 10 : ℝ) - (147 / 64 : ℝ)) * (12515384873054525515 / 18446744073709551616 : ℝ) / denomMax (147 / 64 : ℝ) (23 / 10 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

theorem lower : (116335019353159626 / 18446744073709551616 : ℝ) ≤
    8 * (173631 / 10000000 : ℝ) * ∫ s in (11 / 5 : ℝ)..(23 / 10 : ℝ), density s := by
  have he := integral_grid_sum (11 / 5 : ℝ) (23 / 10 : ℝ) 32 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [endpoint, alpha, beta])
  norm_num [Finset.sum_range_succ] at he
  linarith only [panel00, panel01, panel02, panel03, panel04, panel05, panel06, panel07, panel08, panel09, panel10, panel11, panel12, panel13, panel14, panel15, panel16, panel17, panel18, panel19, panel20, panel21, panel22, panel23, panel24, panel25, panel26, panel27, panel28, panel29, panel30, panel31, he]

end Wu18938Campaign.M3.Confirmed.TableRow02
