import Wu18938Campaign.M3.Confirmed.TableBounds

noncomputable section
namespace Wu18938Campaign.M3.Confirmed.TableRow09
open Real Set MeasureTheory QuarterTrim
open WuSource.SrcSixthGain Wu18938Campaign.M3.Confirmed.TableBounds

private theorem panel00 : (1588843012493976 / 18446744073709551616 : ℝ) ≤
    8 * (77162 / 10000000 : ℝ) * ∫ s in (29 / 10 : ℝ)..(929 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (29 / 10 : ℝ)) (b := (929 / 320 : ℝ))
    (l := (13448981644969993414 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (77162 / 10000000 : ℝ))
  have hp : (1588843012493976 / 18446744073709551616 : ℝ) ≤ 8 * (77162 / 10000000 : ℝ) *
      (((929 / 320 : ℝ) - (29 / 10 : ℝ)) * (13448981644969993414 / 18446744073709551616 : ℝ) / denomMax (29 / 10 : ℝ) (929 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel01 : (1589180937545095 / 18446744073709551616 : ℝ) ≤
    8 * (77162 / 10000000 : ℝ) * ∫ s in (929 / 320 : ℝ)..(93 / 32 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (929 / 320 : ℝ)) (b := (93 / 32 : ℝ))
    (l := (13455045536689212151 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (77162 / 10000000 : ℝ))
  have hp : (1589180937545095 / 18446744073709551616 : ℝ) ≤ 8 * (77162 / 10000000 : ℝ) *
      (((93 / 32 : ℝ) - (929 / 320 : ℝ)) * (13455045536689212151 / 18446744073709551616 : ℝ) / denomMax (929 / 320 : ℝ) (93 / 32 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel02 : (1589523442182404 / 18446744073709551616 : ℝ) ≤
    8 * (77162 / 10000000 : ℝ) * ∫ s in (93 / 32 : ℝ)..(931 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (93 / 32 : ℝ)) (b := (931 / 320 : ℝ))
    (l := (13461125318164337634 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (77162 / 10000000 : ℝ))
  have hp : (1589523442182404 / 18446744073709551616 : ℝ) ≤ 8 * (77162 / 10000000 : ℝ) *
      (((931 / 320 : ℝ) - (93 / 32 : ℝ)) * (13461125318164337634 / 18446744073709551616 : ℝ) / denomMax (93 / 32 : ℝ) (931 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel03 : (1589870532434255 / 18446744073709551616 : ℝ) ≤
    8 * (77162 / 10000000 : ℝ) * ∫ s in (931 / 320 : ℝ)..(233 / 80 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (931 / 320 : ℝ)) (b := (233 / 80 : ℝ))
    (l := (13467221052264837224 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (77162 / 10000000 : ℝ))
  have hp : (1589870532434255 / 18446744073709551616 : ℝ) ≤ 8 * (77162 / 10000000 : ℝ) *
      (((233 / 80 : ℝ) - (931 / 320 : ℝ)) * (13467221052264837224 / 18446744073709551616 : ℝ) / denomMax (931 / 320 : ℝ) (233 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel04 : (1590222214412285 / 18446744073709551616 : ℝ) ≤
    8 * (77162 / 10000000 : ℝ) * ∫ s in (233 / 80 : ℝ)..(933 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (233 / 80 : ℝ)) (b := (933 / 320 : ℝ))
    (l := (13473332802194019767 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (77162 / 10000000 : ℝ))
  have hp : (1590222214412285 / 18446744073709551616 : ℝ) ≤ 8 * (77162 / 10000000 : ℝ) *
      (((933 / 320 : ℝ) - (233 / 80 : ℝ)) * (13473332802194019767 / 18446744073709551616 : ℝ) / denomMax (233 / 80 : ℝ) (933 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel05 : (1590578494311692 / 18446744073709551616 : ℝ) ≤
    8 * (77162 / 10000000 : ℝ) * ∫ s in (933 / 320 : ℝ)..(467 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (933 / 320 : ℝ)) (b := (467 / 160 : ℝ))
    (l := (13479460631491265829 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (77162 / 10000000 : ℝ))
  have hp : (1590578494311692 / 18446744073709551616 : ℝ) ≤ 8 * (77162 / 10000000 : ℝ) *
      (((467 / 160 : ℝ) - (933 / 320 : ℝ)) * (13479460631491265829 / 18446744073709551616 : ℝ) / denomMax (933 / 320 : ℝ) (467 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel06 : (1590939378411510 / 18446744073709551616 : ℝ) ≤
    8 * (77162 / 10000000 : ℝ) * ∫ s in (467 / 160 : ℝ)..(187 / 64 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (467 / 160 : ℝ)) (b := (187 / 64 : ℝ))
    (l := (13485604604034275924 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (77162 / 10000000 : ℝ))
  have hp : (1590939378411510 / 18446744073709551616 : ℝ) ≤ 8 * (77162 / 10000000 : ℝ) *
      (((187 / 64 : ℝ) - (467 / 160 : ℝ)) * (13485604604034275924 / 18446744073709551616 : ℝ) / denomMax (467 / 160 : ℝ) (187 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel07 : (1591304873074900 / 18446744073709551616 : ℝ) ≤
    8 * (77162 / 10000000 : ℝ) * ∫ s in (187 / 64 : ℝ)..(117 / 40 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (187 / 64 : ℝ)) (b := (117 / 40 : ℝ))
    (l := (13491764784041336900 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (77162 / 10000000 : ℝ))
  have hp : (1591304873074900 / 18446744073709551616 : ℝ) ≤ 8 * (77162 / 10000000 : ℝ) *
      (((117 / 40 : ℝ) - (187 / 64 : ℝ)) * (13491764784041336900 / 18446744073709551616 : ℝ) / denomMax (187 / 64 : ℝ) (117 / 40 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel08 : (1591674984749433 / 18446744073709551616 : ℝ) ≤
    8 * (77162 / 10000000 : ℝ) * ∫ s in (117 / 40 : ℝ)..(937 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (117 / 40 : ℝ)) (b := (937 / 320 : ℝ))
    (l := (13497941236073606669 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (77162 / 10000000 : ℝ))
  have hp : (1591674984749433 / 18446744073709551616 : ℝ) ≤ 8 * (77162 / 10000000 : ℝ) *
      (((937 / 320 : ℝ) - (117 / 40 : ℝ)) * (13497941236073606669 / 18446744073709551616 : ℝ) / denomMax (117 / 40 : ℝ) (937 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel09 : (1592049719967383 / 18446744073709551616 : ℝ) ≤
    8 * (77162 / 10000000 : ℝ) * ∫ s in (937 / 320 : ℝ)..(469 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (937 / 320 : ℝ)) (b := (469 / 160 : ℝ))
    (l := (13504134025037417439 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (77162 / 10000000 : ℝ))
  have hp : (1592049719967383 / 18446744073709551616 : ℝ) ≤ 8 * (77162 / 10000000 : ℝ) *
      (((469 / 160 : ℝ) - (937 / 320 : ℝ)) * (13504134025037417439 / 18446744073709551616 : ℝ) / denomMax (937 / 320 : ℝ) (469 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel10 : (1592429085346022 / 18446744073709551616 : ℝ) ≤
    8 * (77162 / 10000000 : ℝ) * ∫ s in (469 / 160 : ℝ)..(939 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (469 / 160 : ℝ)) (b := (939 / 320 : ℝ))
    (l := (13510343216186597632 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (77162 / 10000000 : ℝ))
  have hp : (1592429085346022 / 18446744073709551616 : ℝ) ≤ 8 * (77162 / 10000000 : ℝ) *
      (((939 / 320 : ℝ) - (469 / 160 : ℝ)) * (13510343216186597632 / 18446744073709551616 : ℝ) / denomMax (469 / 160 : ℝ) (939 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel11 : (1592813087587920 / 18446744073709551616 : ℝ) ≤
    8 * (77162 / 10000000 : ℝ) * ∫ s in (939 / 320 : ℝ)..(47 / 16 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (939 / 320 : ℝ)) (b := (47 / 16 : ℝ))
    (l := (13516568875124812669 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (77162 / 10000000 : ℝ))
  have hp : (1592813087587920 / 18446744073709551616 : ℝ) ≤ 8 * (77162 / 10000000 : ℝ) *
      (((47 / 16 : ℝ) - (939 / 320 : ℝ)) * (13516568875124812669 / 18446744073709551616 : ℝ) / denomMax (939 / 320 : ℝ) (47 / 16 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel12 : (1593201733481253 / 18446744073709551616 : ℝ) ≤
    8 * (77162 / 10000000 : ℝ) * ∫ s in (47 / 16 : ℝ)..(941 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (47 / 16 : ℝ)) (b := (941 / 320 : ℝ))
    (l := (13522811067807924796 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (77162 / 10000000 : ℝ))
  have hp : (1593201733481253 / 18446744073709551616 : ℝ) ≤ 8 * (77162 / 10000000 : ℝ) *
      (((941 / 320 : ℝ) - (47 / 16 : ℝ)) * (13522811067807924796 / 18446744073709551616 : ℝ) / denomMax (47 / 16 : ℝ) (941 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel13 : (1593595029900105 / 18446744073709551616 : ℝ) ≤
    8 * (77162 / 10000000 : ℝ) * ∫ s in (941 / 320 : ℝ)..(471 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (941 / 320 : ℝ)) (b := (471 / 160 : ℝ))
    (l := (13529069860546372132 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (77162 / 10000000 : ℝ))
  have hp : (1593595029900105 / 18446744073709551616 : ℝ) ≤ 8 * (77162 / 10000000 : ℝ) *
      (((471 / 160 : ℝ) - (941 / 320 : ℝ)) * (13529069860546372132 / 18446744073709551616 : ℝ) / denomMax (941 / 320 : ℝ) (471 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel14 : (1593992983804784 / 18446744073709551616 : ℝ) ≤
    8 * (77162 / 10000000 : ℝ) * ∫ s in (471 / 160 : ℝ)..(943 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (471 / 160 : ℝ)) (b := (943 / 320 : ℝ))
    (l := (13535345320007567132 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (77162 / 10000000 : ℝ))
  have hp : (1593992983804784 / 18446744073709551616 : ℝ) ≤ 8 * (77162 / 10000000 : ℝ) *
      (((943 / 320 : ℝ) - (471 / 160 : ℝ)) * (13535345320007567132 / 18446744073709551616 : ℝ) / denomMax (471 / 160 : ℝ) (943 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel15 : (1594395602242141 / 18446744073709551616 : ℝ) ≤
    8 * (77162 / 10000000 : ℝ) * ∫ s in (943 / 320 : ℝ)..(59 / 20 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (943 / 320 : ℝ)) (b := (59 / 20 : ℝ))
    (l := (13541637513218314641 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (77162 / 10000000 : ℝ))
  have hp : (1594395602242141 / 18446744073709551616 : ℝ) ≤ 8 * (77162 / 10000000 : ℝ) *
      (((59 / 20 : ℝ) - (943 / 320 : ℝ)) * (13541637513218314641 / 18446744073709551616 : ℝ) / denomMax (943 / 320 : ℝ) (59 / 20 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel16 : (1594802892345885 / 18446744073709551616 : ℝ) ≤
    8 * (77162 / 10000000 : ℝ) * ∫ s in (59 / 20 : ℝ)..(189 / 64 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (59 / 20 : ℝ)) (b := (189 / 64 : ℝ))
    (l := (13547946507567249728 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (77162 / 10000000 : ℝ))
  have hp : (1594802892345885 / 18446744073709551616 : ℝ) ≤ 8 * (77162 / 10000000 : ℝ) *
      (((189 / 64 : ℝ) - (59 / 20 : ℝ)) * (13547946507567249728 / 18446744073709551616 : ℝ) / denomMax (59 / 20 : ℝ) (189 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel17 : (1595214861336914 / 18446744073709551616 : ℝ) ≤
    8 * (77162 / 10000000 : ℝ) * ∫ s in (189 / 64 : ℝ)..(473 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (189 / 64 : ℝ)) (b := (473 / 160 : ℝ))
    (l := (13554272370807295501 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (77162 / 10000000 : ℝ))
  have hp : (1595214861336914 / 18446744073709551616 : ℝ) ≤ 8 * (77162 / 10000000 : ℝ) *
      (((473 / 160 : ℝ) - (189 / 64 : ℝ)) * (13554272370807295501 / 18446744073709551616 : ℝ) / denomMax (189 / 64 : ℝ) (473 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel18 : (1595631516523641 / 18446744073709551616 : ℝ) ≤
    8 * (77162 / 10000000 : ℝ) * ∫ s in (473 / 160 : ℝ)..(947 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (473 / 160 : ℝ)) (b := (947 / 320 : ℝ))
    (l := (13560615171058141078 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (77162 / 10000000 : ℝ))
  have hp : (1595631516523641 / 18446744073709551616 : ℝ) ≤ 8 * (77162 / 10000000 : ℝ) *
      (((947 / 320 : ℝ) - (473 / 160 : ℝ)) * (13560615171058141078 / 18446744073709551616 : ℝ) / denomMax (473 / 160 : ℝ) (947 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel19 : (1596052865302329 / 18446744073709551616 : ℝ) ≤
    8 * (77162 / 10000000 : ℝ) * ∫ s in (947 / 320 : ℝ)..(237 / 80 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (947 / 320 : ℝ)) (b := (237 / 80 : ℝ))
    (l := (13566974976808739922 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (77162 / 10000000 : ℝ))
  have hp : (1596052865302329 / 18446744073709551616 : ℝ) ≤ 8 * (77162 / 10000000 : ℝ) *
      (((237 / 80 : ℝ) - (947 / 320 : ℝ)) * (13566974976808739922 / 18446744073709551616 : ℝ) / denomMax (947 / 320 : ℝ) (237 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel20 : (1596478915157430 / 18446744073709551616 : ℝ) ≤
    8 * (77162 / 10000000 : ℝ) * ∫ s in (237 / 80 : ℝ)..(949 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (237 / 80 : ℝ)) (b := (949 / 320 : ℝ))
    (l := (13573351856919828732 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (77162 / 10000000 : ℝ))
  have hp : (1596478915157430 / 18446744073709551616 : ℝ) ≤ 8 * (77162 / 10000000 : ℝ) *
      (((949 / 320 : ℝ) - (237 / 80 : ℝ)) * (13573351856919828732 / 18446744073709551616 : ℝ) / denomMax (237 / 80 : ℝ) (949 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel21 : (1596909673661928 / 18446744073709551616 : ℝ) ≤
    8 * (77162 / 10000000 : ℝ) * ∫ s in (949 / 320 : ℝ)..(95 / 32 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (949 / 320 : ℝ)) (b := (95 / 32 : ℝ))
    (l := (13579745880626467083 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (77162 / 10000000 : ℝ))
  have hp : (1596909673661928 / 18446744073709551616 : ℝ) ≤ 8 * (77162 / 10000000 : ℝ) *
      (((95 / 32 : ℝ) - (949 / 320 : ℝ)) * (13579745880626467083 / 18446744073709551616 : ℝ) / denomMax (949 / 320 : ℝ) (95 / 32 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel22 : (1597345148477684 / 18446744073709551616 : ℝ) ≤
    8 * (77162 / 10000000 : ℝ) * ∫ s in (95 / 32 : ℝ)..(951 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (95 / 32 : ℝ)) (b := (951 / 320 : ℝ))
    (l := (13586157117540598028 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (77162 / 10000000 : ℝ))
  have hp : (1597345148477684 / 18446744073709551616 : ℝ) ≤ 8 * (77162 / 10000000 : ℝ) *
      (((951 / 320 : ℝ) - (95 / 32 : ℝ)) * (13586157117540598028 / 18446744073709551616 : ℝ) / denomMax (95 / 32 : ℝ) (951 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel23 : (1597785347355787 / 18446744073709551616 : ℝ) ≤
    8 * (77162 / 10000000 : ℝ) * ∫ s in (951 / 320 : ℝ)..(119 / 40 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (951 / 320 : ℝ)) (b := (119 / 40 : ℝ))
    (l := (13592585637653629854 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (77162 / 10000000 : ℝ))
  have hp : (1597785347355787 / 18446744073709551616 : ℝ) ≤ 8 * (77162 / 10000000 : ℝ) *
      (((119 / 40 : ℝ) - (951 / 320 : ℝ)) * (13592585637653629854 / 18446744073709551616 : ℝ) / denomMax (951 / 320 : ℝ) (119 / 40 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel24 : (1598230278136915 / 18446744073709551616 : ℝ) ≤
    8 * (77162 / 10000000 : ℝ) * ∫ s in (119 / 40 : ℝ)..(953 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (119 / 40 : ℝ)) (b := (953 / 320 : ℝ))
    (l := (13599031511339039197 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (77162 / 10000000 : ℝ))
  have hp : (1598230278136915 / 18446744073709551616 : ℝ) ≤ 8 * (77162 / 10000000 : ℝ) *
      (((953 / 320 : ℝ) - (119 / 40 : ℝ)) * (13599031511339039197 / 18446744073709551616 : ℝ) / denomMax (119 / 40 : ℝ) (953 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel25 : (1598679948751690 / 18446744073709551616 : ℝ) ≤
    8 * (77162 / 10000000 : ℝ) * ∫ s in (953 / 320 : ℝ)..(477 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (953 / 320 : ℝ)) (b := (477 / 160 : ℝ))
    (l := (13605494809354995739 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (77162 / 10000000 : ℝ))
  have hp : (1598679948751690 / 18446744073709551616 : ℝ) ≤ 8 * (77162 / 10000000 : ℝ) *
      (((477 / 160 : ℝ) - (953 / 320 : ℝ)) * (13605494809354995739 / 18446744073709551616 : ℝ) / denomMax (953 / 320 : ℝ) (477 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel26 : (1599134367221048 / 18446744073709551616 : ℝ) ≤
    8 * (77162 / 10000000 : ℝ) * ∫ s in (477 / 160 : ℝ)..(191 / 64 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (477 / 160 : ℝ)) (b := (191 / 64 : ℝ))
    (l := (13611975602847008673 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (77162 / 10000000 : ℝ))
  have hp : (1599134367221048 / 18446744073709551616 : ℝ) ≤ 8 * (77162 / 10000000 : ℝ) *
      (((191 / 64 : ℝ) - (477 / 160 : ℝ)) * (13611975602847008673 / 18446744073709551616 : ℝ) / denomMax (477 / 160 : ℝ) (191 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel27 : (1599593541656602 / 18446744073709551616 : ℝ) ≤
    8 * (77162 / 10000000 : ℝ) * ∫ s in (191 / 64 : ℝ)..(239 / 80 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (191 / 64 : ℝ)) (b := (239 / 80 : ℝ))
    (l := (13618473963350595168 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (77162 / 10000000 : ℝ))
  have hp : (1599593541656602 / 18446744073709551616 : ℝ) ≤ 8 * (77162 / 10000000 : ℝ) *
      (((239 / 80 : ℝ) - (191 / 64 : ℝ)) * (13618473963350595168 / 18446744073709551616 : ℝ) / denomMax (191 / 64 : ℝ) (239 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel28 : (1600057480261026 / 18446744073709551616 : ℝ) ≤
    8 * (77162 / 10000000 : ℝ) * ∫ s in (239 / 80 : ℝ)..(957 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (239 / 80 : ℝ)) (b := (957 / 320 : ℝ))
    (l := (13624989962793971042 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (77162 / 10000000 : ℝ))
  have hp : (1600057480261026 / 18446744073709551616 : ℝ) ≤ 8 * (77162 / 10000000 : ℝ) *
      (((957 / 320 : ℝ) - (239 / 80 : ℝ)) * (13624989962793971042 / 18446744073709551616 : ℝ) / denomMax (239 / 80 : ℝ) (957 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel29 : (1600526191328423 / 18446744073709551616 : ℝ) ≤
    8 * (77162 / 10000000 : ℝ) * ∫ s in (957 / 320 : ℝ)..(479 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (957 / 320 : ℝ)) (b := (479 / 160 : ℝ))
    (l := (13631523673500763855 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (77162 / 10000000 : ℝ))
  have hp : (1600526191328423 / 18446744073709551616 : ℝ) ≤ 8 * (77162 / 10000000 : ℝ) *
      (((479 / 160 : ℝ) - (957 / 320 : ℝ)) * (13631523673500763855 / 18446744073709551616 : ℝ) / denomMax (957 / 320 : ℝ) (479 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel30 : (1600999683244717 / 18446744073709551616 : ℝ) ≤
    8 * (77162 / 10000000 : ℝ) * ∫ s in (479 / 160 : ℝ)..(959 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (479 / 160 : ℝ)) (b := (959 / 320 : ℝ))
    (l := (13638075168192748649 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (77162 / 10000000 : ℝ))
  have hp : (1600999683244717 / 18446744073709551616 : ℝ) ≤ 8 * (77162 / 10000000 : ℝ) *
      (((959 / 320 : ℝ) - (479 / 160 : ℝ)) * (13638075168192748649 / 18446744073709551616 : ℝ) / denomMax (479 / 160 : ℝ) (959 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel31 : (1601477964488039 / 18446744073709551616 : ℝ) ≤
    8 * (77162 / 10000000 : ℝ) * ∫ s in (959 / 320 : ℝ)..(3 / 1 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (959 / 320 : ℝ)) (b := (3 / 1 : ℝ))
    (l := (13644644519992606553 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (77162 / 10000000 : ℝ))
  have hp : (1601477964488039 / 18446744073709551616 : ℝ) ≤ 8 * (77162 / 10000000 : ℝ) *
      (((3 / 1 : ℝ) - (959 / 320 : ℝ)) * (13644644519992606553 / 18446744073709551616 : ℝ) / denomMax (959 / 320 : ℝ) (3 / 1 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

theorem lower : (51033535787195216 / 18446744073709551616 : ℝ) ≤
    8 * (77162 / 10000000 : ℝ) * ∫ s in (29 / 10 : ℝ)..(3 / 1 : ℝ), density s := by
  have he := integral_grid_sum (29 / 10 : ℝ) (3 / 1 : ℝ) 32 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [endpoint, alpha, beta])
  norm_num [Finset.sum_range_succ] at he
  linarith only [panel00, panel01, panel02, panel03, panel04, panel05, panel06, panel07, panel08, panel09, panel10, panel11, panel12, panel13, panel14, panel15, panel16, panel17, panel18, panel19, panel20, panel21, panel22, panel23, panel24, panel25, panel26, panel27, panel28, panel29, panel30, panel31, he]

end Wu18938Campaign.M3.Confirmed.TableRow09
