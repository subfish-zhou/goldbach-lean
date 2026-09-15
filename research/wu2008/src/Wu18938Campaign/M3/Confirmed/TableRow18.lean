import Wu18938Campaign.M3.Confirmed.TableBounds

noncomputable section
namespace Wu18938Campaign.M3.Confirmed.TableRow18
open Real Set MeasureTheory QuarterTrim
open WuSource.SrcSixthGain Wu18938Campaign.M3.Confirmed.TableBounds

private theorem panel00 : (199079681062395 / 18446744073709551616 : ℝ) ≤
    8 * (15336 / 10000000 : ℝ) * ∫ s in (37 / 10 : ℝ)..(237 / 64 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (37 / 10 : ℝ)) (b := (237 / 64 : ℝ))
    (l := (8498528403095797750 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (15336 / 10000000 : ℝ))
  have hp : (199079681062395 / 18446744073709551616 : ℝ) ≤ 8 * (15336 / 10000000 : ℝ) *
      (((237 / 64 : ℝ) - (37 / 10 : ℝ)) * (8498528403095797750 / 18446744073709551616 : ℝ) / denomMax (37 / 10 : ℝ) (237 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel01 : (197400649027859 / 18446744073709551616 : ℝ) ≤
    8 * (15336 / 10000000 : ℝ) * ∫ s in (237 / 64 : ℝ)..(593 / 160 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (237 / 64 : ℝ)) (b := (593 / 160 : ℝ))
    (l := (8424989393872621371 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (15336 / 10000000 : ℝ))
  have hp : (197400649027859 / 18446744073709551616 : ℝ) ≤ 8 * (15336 / 10000000 : ℝ) *
      (((593 / 160 : ℝ) - (237 / 64 : ℝ)) * (8424989393872621371 / 18446744073709551616 : ℝ) / denomMax (237 / 64 : ℝ) (593 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel02 : (195717662518000 / 18446744073709551616 : ℝ) ≤
    8 * (15336 / 10000000 : ℝ) * ∫ s in (593 / 160 : ℝ)..(1187 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (593 / 160 : ℝ)) (b := (1187 / 320 : ℝ))
    (l := (8351298306309917662 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (15336 / 10000000 : ℝ))
  have hp : (195717662518000 / 18446744073709551616 : ℝ) ≤ 8 * (15336 / 10000000 : ℝ) *
      (((1187 / 320 : ℝ) - (593 / 160 : ℝ)) * (8351298306309917662 / 18446744073709551616 : ℝ) / denomMax (593 / 160 : ℝ) (1187 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel03 : (194030694553097 / 18446744073709551616 : ℝ) ≤
    8 * (15336 / 10000000 : ℝ) * ∫ s in (1187 / 320 : ℝ)..(297 / 80 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1187 / 320 : ℝ)) (b := (297 / 80 : ℝ))
    (l := (8277454489941665603 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (15336 / 10000000 : ℝ))
  have hp : (194030694553097 / 18446744073709551616 : ℝ) ≤ 8 * (15336 / 10000000 : ℝ) *
      (((297 / 80 : ℝ) - (1187 / 320 : ℝ)) * (8277454489941665603 / 18446744073709551616 : ℝ) / denomMax (1187 / 320 : ℝ) (297 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel04 : (192339717985537 / 18446744073709551616 : ℝ) ≤
    8 * (15336 / 10000000 : ℝ) * ∫ s in (297 / 80 : ℝ)..(1189 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (297 / 80 : ℝ)) (b := (1189 / 320 : ℝ))
    (l := (8203457290006157197 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (15336 / 10000000 : ℝ))
  have hp : (192339717985537 / 18446744073709551616 : ℝ) ≤ 8 * (15336 / 10000000 : ℝ) *
      (((1189 / 320 : ℝ) - (297 / 80 : ℝ)) * (8203457290006157197 / 18446744073709551616 : ℝ) / denomMax (297 / 80 : ℝ) (1189 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel05 : (190644705498236 / 18446744073709551616 : ℝ) ≤
    8 * (15336 / 10000000 : ℝ) * ∫ s in (1189 / 320 : ℝ)..(119 / 32 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1189 / 320 : ℝ)) (b := (119 / 32 : ℝ))
    (l := (8129306047407262050 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (15336 / 10000000 : ℝ))
  have hp : (190644705498236 / 18446744073709551616 : ℝ) ≤ 8 * (15336 / 10000000 : ℝ) *
      (((119 / 32 : ℝ) - (1189 / 320 : ℝ)) * (8129306047407262050 / 18446744073709551616 : ℝ) / denomMax (1189 / 320 : ℝ) (119 / 32 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel06 : (188945629603031 / 18446744073709551616 : ℝ) ≤
    8 * (15336 / 10000000 : ℝ) * ∫ s in (119 / 32 : ℝ)..(1191 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (119 / 32 : ℝ)) (b := (1191 / 320 : ℝ))
    (l := (8055000098675247002 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (15336 / 10000000 : ℝ))
  have hp : (188945629603031 / 18446744073709551616 : ℝ) ≤ 8 * (15336 / 10000000 : ℝ) *
      (((1191 / 320 : ℝ) - (119 / 32 : ℝ)) * (8055000098675247002 / 18446744073709551616 : ℝ) / denomMax (119 / 32 : ℝ) (1191 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel07 : (187242462639061 / 18446744073709551616 : ℝ) ≤
    8 * (15336 / 10000000 : ℝ) * ∫ s in (1191 / 320 : ℝ)..(149 / 40 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1191 / 320 : ℝ)) (b := (149 / 40 : ℝ))
    (l := (7980538775927144587 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (15336 / 10000000 : ℝ))
  have hp : (187242462639061 / 18446744073709551616 : ℝ) ≤ 8 * (15336 / 10000000 : ℝ) *
      (((149 / 40 : ℝ) - (1191 / 320 : ℝ)) * (7980538775927144587 / 18446744073709551616 : ℝ) / denomMax (1191 / 320 : ℝ) (149 / 40 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel08 : (185535176771130 / 18446744073709551616 : ℝ) ≤
    8 * (15336 / 10000000 : ℝ) * ∫ s in (149 / 40 : ℝ)..(1193 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (149 / 40 : ℝ)) (b := (1193 / 320 : ℝ))
    (l := (7905921406826664009 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (15336 / 10000000 : ℝ))
  have hp : (185535176771130 / 18446744073709551616 : ℝ) ≤ 8 * (15336 / 10000000 : ℝ) *
      (((1193 / 320 : ℝ) - (149 / 40 : ℝ)) * (7905921406826664009 / 18446744073709551616 : ℝ) / denomMax (149 / 40 : ℝ) (1193 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel09 : (183823743988051 / 18446744073709551616 : ℝ) ≤
    8 * (15336 / 10000000 : ℝ) * ∫ s in (1193 / 320 : ℝ)..(597 / 160 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1193 / 320 : ℝ)) (b := (597 / 160 : ℝ))
    (l := (7831147314543638187 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (15336 / 10000000 : ℝ))
  have hp : (183823743988051 / 18446744073709551616 : ℝ) ≤ 8 * (15336 / 10000000 : ℝ) *
      (((597 / 160 : ℝ) - (1193 / 320 : ℝ)) * (7831147314543638187 / 18446744073709551616 : ℝ) / denomMax (1193 / 320 : ℝ) (597 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel10 : (182108136100969 / 18446744073709551616 : ℝ) ≤
    8 * (15336 / 10000000 : ℝ) * ∫ s in (597 / 160 : ℝ)..(239 / 64 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (597 / 160 : ℝ)) (b := (239 / 64 : ℝ))
    (l := (7756215817713000342 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (15336 / 10000000 : ℝ))
  have hp : (182108136100969 / 18446744073709551616 : ℝ) ≤ 8 * (15336 / 10000000 : ℝ) *
      (((239 / 64 : ℝ) - (597 / 160 : ℝ)) * (7756215817713000342 / 18446744073709551616 : ℝ) / denomMax (597 / 160 : ℝ) (239 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel11 : (180388324741671 / 18446744073709551616 : ℝ) ≤
    8 * (15336 / 10000000 : ℝ) * ∫ s in (239 / 64 : ℝ)..(299 / 80 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (239 / 64 : ℝ)) (b := (299 / 80 : ℝ))
    (l := (7681126230393283468 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (15336 / 10000000 : ℝ))
  have hp : (180388324741671 / 18446744073709551616 : ℝ) ≤ 8 * (15336 / 10000000 : ℝ) *
      (((299 / 80 : ℝ) - (239 / 64 : ℝ)) * (7681126230393283468 / 18446744073709551616 : ℝ) / denomMax (239 / 64 : ℝ) (299 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel12 : (178664281360874 / 18446744073709551616 : ℝ) ≤
    8 * (15336 / 10000000 : ℝ) * ∫ s in (299 / 80 : ℝ)..(1197 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (299 / 80 : ℝ)) (b := (1197 / 320 : ℝ))
    (l := (7605877862024635941 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (15336 / 10000000 : ℝ))
  have hp : (178664281360874 / 18446744073709551616 : ℝ) ≤ 8 * (15336 / 10000000 : ℝ) *
      (((1197 / 320 : ℝ) - (299 / 80 : ℝ)) * (7605877862024635941 / 18446744073709551616 : ℝ) / denomMax (299 / 80 : ℝ) (1197 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel13 : (176935977226495 / 18446744073709551616 : ℝ) ≤
    8 * (15336 / 10000000 : ℝ) * ∫ s in (1197 / 320 : ℝ)..(599 / 160 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1197 / 320 : ℝ)) (b := (599 / 160 : ℝ))
    (l := (7530470017386346391 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (15336 / 10000000 : ℝ))
  have hp : (176935977226495 / 18446744073709551616 : ℝ) ≤ 8 * (15336 / 10000000 : ℝ) *
      (((599 / 160 : ℝ) - (1197 / 320 : ℝ)) * (7530470017386346391 / 18446744073709551616 : ℝ) / denomMax (1197 / 320 : ℝ) (599 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel14 : (175203383421901 / 18446744073709551616 : ℝ) ≤
    8 * (15336 / 10000000 : ℝ) * ∫ s in (599 / 160 : ℝ)..(1199 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (599 / 160 : ℝ)) (b := (1199 / 320 : ℝ))
    (l := (7454901996553870847 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (15336 / 10000000 : ℝ))
  have hp : (175203383421901 / 18446744073709551616 : ℝ) ≤ 8 * (15336 / 10000000 : ℝ) *
      (((1199 / 320 : ℝ) - (599 / 160 : ℝ)) * (7454901996553870847 / 18446744073709551616 : ℝ) / denomMax (599 / 160 : ℝ) (1199 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel15 : (173466470844142 / 18446744073709551616 : ℝ) ≤
    8 * (15336 / 10000000 : ℝ) * ∫ s in (1199 / 320 : ℝ)..(15 / 4 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1199 / 320 : ℝ)) (b := (15 / 4 : ℝ))
    (l := (7379173094855355055 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (15336 / 10000000 : ℝ))
  have hp : (173466470844142 / 18446744073709551616 : ℝ) ≤ 8 * (15336 / 10000000 : ℝ) *
      (((15 / 4 : ℝ) - (1199 / 320 : ℝ)) * (7379173094855355055 / 18446744073709551616 : ℝ) / denomMax (1199 / 320 : ℝ) (15 / 4 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel16 : (171725210202163 / 18446744073709551616 : ℝ) ≤
    8 * (15336 / 10000000 : ℝ) * ∫ s in (15 / 4 : ℝ)..(1201 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (15 / 4 : ℝ)) (b := (1201 / 320 : ℝ))
    (l := (7303282602827644752 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (15336 / 10000000 : ℝ))
  have hp : (171725210202163 / 18446744073709551616 : ℝ) ≤ 8 * (15336 / 10000000 : ℝ) *
      (((1201 / 320 : ℝ) - (15 / 4 : ℝ)) * (7303282602827644752 / 18446744073709551616 : ℝ) / denomMax (15 / 4 : ℝ) (1201 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel17 : (169979572014991 / 18446744073709551616 : ℝ) ≤
    8 * (15336 / 10000000 : ℝ) * ∫ s in (1201 / 320 : ℝ)..(601 / 160 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1201 / 320 : ℝ)) (b := (601 / 160 : ℝ))
    (l := (7227229806171776540 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (15336 / 10000000 : ℝ))
  have hp : (169979572014991 / 18446744073709551616 : ℝ) ≤ 8 * (15336 / 10000000 : ℝ) *
      (((601 / 160 : ℝ) - (1201 / 320 : ℝ)) * (7227229806171776540 / 18446744073709551616 : ℝ) / denomMax (1201 / 320 : ℝ) (601 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel18 : (168229526609915 / 18446744073709551616 : ℝ) ≤
    8 * (15336 / 10000000 : ℝ) * ∫ s in (601 / 160 : ℝ)..(1203 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (601 / 160 : ℝ)) (b := (1203 / 320 : ℝ))
    (l := (7151013985707941904 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (15336 / 10000000 : ℝ))
  have hp : (168229526609915 / 18446744073709551616 : ℝ) ≤ 8 * (15336 / 10000000 : ℝ) *
      (((1203 / 320 : ℝ) - (601 / 160 : ℝ)) * (7151013985707941904 / 18446744073709551616 : ℝ) / denomMax (601 / 160 : ℝ) (1203 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel19 : (166475044120627 / 18446744073709551616 : ℝ) ≤
    8 * (15336 / 10000000 : ℝ) * ∫ s in (1203 / 320 : ℝ)..(301 / 80 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1203 / 320 : ℝ)) (b := (301 / 80 : ℝ))
    (l := (7074634417329916764 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (15336 / 10000000 : ℝ))
  have hp : (166475044120627 / 18446744073709551616 : ℝ) ≤ 8 * (15336 / 10000000 : ℝ) *
      (((301 / 80 : ℝ) - (1203 / 320 : ℝ)) * (7074634417329916764 / 18446744073709551616 : ℝ) / denomMax (1203 / 320 : ℝ) (301 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel20 : (164716094485360 / 18446744073709551616 : ℝ) ≤
    8 * (15336 / 10000000 : ℝ) * ∫ s in (301 / 80 : ℝ)..(241 / 64 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (301 / 80 : ℝ)) (b := (241 / 64 : ℝ))
    (l := (6998090371958948852 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (15336 / 10000000 : ℝ))
  have hp : (164716094485360 / 18446744073709551616 : ℝ) ≤ 8 * (15336 / 10000000 : ℝ) *
      (((241 / 64 : ℝ) - (301 / 80 : ℝ)) * (6998090371958948852 / 18446744073709551616 : ℝ) / denomMax (301 / 80 : ℝ) (241 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel21 : (162952647444995 / 18446744073709551616 : ℝ) ≤
    8 * (15336 / 10000000 : ℝ) * ∫ s in (241 / 64 : ℝ)..(603 / 160 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (241 / 64 : ℝ)) (b := (603 / 160 : ℝ))
    (l := (6921381115497095043 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (15336 / 10000000 : ℝ))
  have hp : (162952647444995 / 18446744073709551616 : ℝ) ≤ 8 * (15336 / 10000000 : ℝ) *
      (((603 / 160 : ℝ) - (241 / 64 : ℝ)) * (6921381115497095043 / 18446744073709551616 : ℝ) / denomMax (241 / 64 : ℝ) (603 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel22 : (161184672541147 / 18446744073709551616 : ℝ) ≤
    8 * (15336 / 10000000 : ℝ) * ∫ s in (603 / 160 : ℝ)..(1207 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (603 / 160 : ℝ)) (b := (1207 / 320 : ℝ))
    (l := (6844505908780000657 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (15336 / 10000000 : ℝ))
  have hp : (161184672541147 / 18446744073709551616 : ℝ) ≤ 8 * (15336 / 10000000 : ℝ) *
      (((1207 / 320 : ℝ) - (603 / 160 : ℝ)) * (6844505908780000657 / 18446744073709551616 : ℝ) / denomMax (603 / 160 : ℝ) (1207 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel23 : (159412139114230 / 18446744073709551616 : ℝ) ≤
    8 * (15336 / 10000000 : ℝ) * ∫ s in (1207 / 320 : ℝ)..(151 / 40 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1207 / 320 : ℝ)) (b := (151 / 40 : ℝ))
    (l := (6767464007529112606 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (15336 / 10000000 : ℝ))
  have hp : (159412139114230 / 18446744073709551616 : ℝ) ≤ 8 * (15336 / 10000000 : ℝ) *
      (((151 / 40 : ℝ) - (1207 / 320 : ℝ)) * (6767464007529112606 / 18446744073709551616 : ℝ) / denomMax (1207 / 320 : ℝ) (151 / 40 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel24 : (157635016301507 / 18446744073709551616 : ℝ) ≤
    8 * (15336 / 10000000 : ℝ) * ∫ s in (151 / 40 : ℝ)..(1209 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (151 / 40 : ℝ)) (b := (1209 / 320 : ℝ))
    (l := (6690254662303318109 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (15336 / 10000000 : ℝ))
  have hp : (157635016301507 / 18446744073709551616 : ℝ) ≤ 8 * (15336 / 10000000 : ℝ) *
      (((1209 / 320 : ℝ) - (151 / 40 : ℝ)) * (6690254662303318109 / 18446744073709551616 : ℝ) / denomMax (151 / 40 : ℝ) (1209 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel25 : (155853273035105 / 18446744073709551616 : ℝ) ≤
    8 * (15336 / 10000000 : ℝ) * ∫ s in (1209 / 320 : ℝ)..(121 / 32 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1209 / 320 : ℝ)) (b := (121 / 32 : ℝ))
    (l := (6612877118450000576 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (15336 / 10000000 : ℝ))
  have hp : (155853273035105 / 18446744073709551616 : ℝ) ≤ 8 * (15336 / 10000000 : ℝ) *
      (((121 / 32 : ℝ) - (1209 / 320 : ℝ)) * (6612877118450000576 / 18446744073709551616 : ℝ) / denomMax (1209 / 320 : ℝ) (121 / 32 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel26 : (154066878040017 / 18446744073709551616 : ℝ) ≤
    8 * (15336 / 10000000 : ℝ) * ∫ s in (121 / 32 : ℝ)..(1211 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (121 / 32 : ℝ)) (b := (1211 / 320 : ℝ))
    (l := (6535330616055504099 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (15336 / 10000000 : ℝ))
  have hp : (154066878040017 / 18446744073709551616 : ℝ) ≤ 8 * (15336 / 10000000 : ℝ) *
      (((1211 / 320 : ℝ) - (121 / 32 : ℝ)) * (6535330616055504099 / 18446744073709551616 : ℝ) / denomMax (121 / 32 : ℝ) (1211 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel27 : (152275799832079 / 18446744073709551616 : ℝ) ≤
    8 * (15336 / 10000000 : ℝ) * ∫ s in (1211 / 320 : ℝ)..(303 / 80 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1211 / 320 : ℝ)) (b := (303 / 80 : ℝ))
    (l := (6457614389894997843 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (15336 / 10000000 : ℝ))
  have hp : (152275799832079 / 18446744073709551616 : ℝ) ≤ 8 * (15336 / 10000000 : ℝ) *
      (((303 / 80 : ℝ) - (1211 / 320 : ℝ)) * (6457614389894997843 / 18446744073709551616 : ℝ) / denomMax (1211 / 320 : ℝ) (303 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel28 : (150480006715920 / 18446744073709551616 : ℝ) ≤
    8 * (15336 / 10000000 : ℝ) * ∫ s in (303 / 80 : ℝ)..(1213 / 320 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (303 / 80 : ℝ)) (b := (1213 / 320 : ℝ))
    (l := (6379727669381731496 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (15336 / 10000000 : ℝ))
  have hp : (150480006715920 / 18446744073709551616 : ℝ) ≤ 8 * (15336 / 10000000 : ℝ) *
      (((1213 / 320 : ℝ) - (303 / 80 : ℝ)) * (6379727669381731496 / 18446744073709551616 : ℝ) / denomMax (303 / 80 : ℝ) (1213 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel29 : (148679466782895 / 18446744073709551616 : ℝ) ≤
    8 * (15336 / 10000000 : ℝ) * ∫ s in (1213 / 320 : ℝ)..(607 / 160 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (1213 / 320 : ℝ)) (b := (607 / 160 : ℝ))
    (l := (6301669678515672752 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (15336 / 10000000 : ℝ))
  have hp : (148679466782895 / 18446744073709551616 : ℝ) ≤ 8 * (15336 / 10000000 : ℝ) *
      (((607 / 160 : ℝ) - (1213 / 320 : ℝ)) * (6301669678515672752 / 18446744073709551616 : ℝ) / denomMax (1213 / 320 : ℝ) (607 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel30 : (146874147908985 / 18446744073709551616 : ℝ) ≤
    8 * (15336 / 10000000 : ℝ) * ∫ s in (607 / 160 : ℝ)..(243 / 64 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (607 / 160 : ℝ)) (b := (243 / 64 : ℝ))
    (l := (6223439635831517675 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (15336 / 10000000 : ℝ))
  have hp : (146874147908985 / 18446744073709551616 : ℝ) ≤ 8 * (15336 / 10000000 : ℝ) *
      (((243 / 64 : ℝ) - (607 / 160 : ℝ)) * (6223439635831517675 / 18446744073709551616 : ℝ) / denomMax (607 / 160 : ℝ) (243 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel31 : (145064017752684 / 18446744073709551616 : ℝ) ≤
    8 * (15336 / 10000000 : ℝ) * ∫ s in (243 / 64 : ℝ)..(19 / 5 : ℝ), density s := by
  have h := panel_lower (upper := true) (a := (243 / 64 : ℝ)) (b := (19 / 5 : ℝ))
    (l := (6145036754346064611 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (15336 / 10000000 : ℝ))
  have hp : (145064017752684 / 18446744073709551616 : ℝ) ≤ 8 * (15336 / 10000000 : ℝ) *
      (((19 / 5 : ℝ) - (243 / 64 : ℝ)) * (6145036754346064611 / 18446744073709551616 : ℝ) / denomMax (243 / 64 : ℝ) (19 / 5 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

theorem lower : (5517130210245069 / 18446744073709551616 : ℝ) ≤
    8 * (15336 / 10000000 : ℝ) * ∫ s in (37 / 10 : ℝ)..(19 / 5 : ℝ), density s := by
  have he := integral_grid_sum (37 / 10 : ℝ) (19 / 5 : ℝ) 32 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [endpoint, alpha, beta])
  norm_num [Finset.sum_range_succ] at he
  linarith only [panel00, panel01, panel02, panel03, panel04, panel05, panel06, panel07, panel08, panel09, panel10, panel11, panel12, panel13, panel14, panel15, panel16, panel17, panel18, panel19, panel20, panel21, panel22, panel23, panel24, panel25, panel26, panel27, panel28, panel29, panel30, panel31, he]

end Wu18938Campaign.M3.Confirmed.TableRow18
