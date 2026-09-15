import Wu18938Campaign.M3.Confirmed.TableBounds

noncomputable section
namespace Wu18938Campaign.M3.Confirmed.TableRow13
open Real Set MeasureTheory QuarterTrim
open WuSource.SrcSixthGain Wu18938Campaign.M3.Confirmed.TableBounds

private theorem panel00 : (813381666523462 / 18446744073709551616 : ℝ) ≤
    8 * (37529 / 10000000 : ℝ) * ∫ s in (33 / 10 : ℝ)..(1057 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (33 / 10 : ℝ)) (b := (1057 / 320 : ℝ))
    (l := (14380042179269284018 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (37529 / 10000000 : ℝ))
  have hp : (813381666523462 / 18446744073709551616 : ℝ) ≤ 8 * (37529 / 10000000 : ℝ) *
      (((1057 / 320 : ℝ) - (33 / 10 : ℝ)) * (14380042179269284018 / 18446744073709551616 : ℝ) / denomMax (33 / 10 : ℝ) (1057 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel01 : (813870811044126 / 18446744073709551616 : ℝ) ≤
    8 * (37529 / 10000000 : ℝ) * ∫ s in (1057 / 320 : ℝ)..(529 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (1057 / 320 : ℝ)) (b := (529 / 160 : ℝ))
    (l := (14388794620150359172 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (37529 / 10000000 : ℝ))
  have hp : (813870811044126 / 18446744073709551616 : ℝ) ≤ 8 * (37529 / 10000000 : ℝ) *
      (((529 / 160 : ℝ) - (1057 / 320 : ℝ)) * (14388794620150359172 / 18446744073709551616 : ℝ) / denomMax (1057 / 320 : ℝ) (529 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel02 : (814362958257824 / 18446744073709551616 : ℝ) ≤
    8 * (37529 / 10000000 : ℝ) * ∫ s in (529 / 160 : ℝ)..(1059 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (529 / 160 : ℝ)) (b := (1059 / 320 : ℝ))
    (l := (14397574722704232676 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (37529 / 10000000 : ℝ))
  have hp : (814362958257824 / 18446744073709551616 : ℝ) ≤ 8 * (37529 / 10000000 : ℝ) *
      (((1059 / 320 : ℝ) - (529 / 160 : ℝ)) * (14397574722704232676 / 18446744073709551616 : ℝ) / denomMax (529 / 160 : ℝ) (1059 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel03 : (814858118220710 / 18446744073709551616 : ℝ) ≤
    8 * (37529 / 10000000 : ℝ) * ∫ s in (1059 / 320 : ℝ)..(53 / 16 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (1059 / 320 : ℝ)) (b := (53 / 16 : ℝ))
    (l := (14406382619272844485 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (37529 / 10000000 : ℝ))
  have hp : (814858118220710 / 18446744073709551616 : ℝ) ≤ 8 * (37529 / 10000000 : ℝ) *
      (((53 / 16 : ℝ) - (1059 / 320 : ℝ)) * (14406382619272844485 / 18446744073709551616 : ℝ) / denomMax (1059 / 320 : ℝ) (53 / 16 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel04 : (815356301069014 / 18446744073709551616 : ℝ) ≤
    8 * (37529 / 10000000 : ℝ) * ∫ s in (53 / 16 : ℝ)..(1061 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (53 / 16 : ℝ)) (b := (1061 / 320 : ℝ))
    (l := (14415218443050011227 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (37529 / 10000000 : ℝ))
  have hp : (815356301069014 / 18446744073709551616 : ℝ) ≤ 8 * (37529 / 10000000 : ℝ) *
      (((1061 / 320 : ℝ) - (53 / 16 : ℝ)) * (14415218443050011227 / 18446744073709551616 : ℝ) / denomMax (53 / 16 : ℝ) (1061 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel05 : (815857401191902 / 18446744073709551616 : ℝ) ≤
    8 * (37529 / 10000000 : ℝ) * ∫ s in (1061 / 320 : ℝ)..(531 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (1061 / 320 : ℝ)) (b := (531 / 160 : ℝ))
    (l := (14424082328088341404 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (37529 / 10000000 : ℝ))
  have hp : (815857401191902 / 18446744073709551616 : ℝ) ≤ 8 * (37529 / 10000000 : ℝ) *
      (((531 / 160 : ℝ) - (1061 / 320 : ℝ)) * (14424082328088341404 / 18446744073709551616 : ℝ) / denomMax (1061 / 320 : ℝ) (531 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel06 : (816360472503267 / 18446744073709551616 : ℝ) ≤
    8 * (37529 / 10000000 : ℝ) * ∫ s in (531 / 160 : ℝ)..(1063 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (531 / 160 : ℝ)) (b := (1063 / 320 : ℝ))
    (l := (14432974409306218518 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (37529 / 10000000 : ℝ))
  have hp : (816360472503267 / 18446744073709551616 : ℝ) ≤ 8 * (37529 / 10000000 : ℝ) *
      (((1063 / 320 : ℝ) - (531 / 160 : ℝ)) * (14432974409306218518 / 18446744073709551616 : ℝ) / denomMax (531 / 160 : ℝ) (1063 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel07 : (816866335178113 / 18446744073709551616 : ℝ) ≤
    8 * (37529 / 10000000 : ℝ) * ∫ s in (1063 / 320 : ℝ)..(133 / 40 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (1063 / 320 : ℝ)) (b := (133 / 40 : ℝ))
    (l := (14441894822494852945 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (37529 / 10000000 : ℝ))
  have hp : (816866335178113 / 18446744073709551616 : ℝ) ≤ 8 * (37529 / 10000000 : ℝ) *
      (((133 / 40 : ℝ) - (1063 / 320 : ℝ)) * (14441894822494852945 / 18446744073709551616 : ℝ) / denomMax (1063 / 320 : ℝ) (133 / 40 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel08 : (817375260267094 / 18446744073709551616 : ℝ) ≤
    8 * (37529 / 10000000 : ℝ) * ∫ s in (133 / 40 : ℝ)..(213 / 64 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (133 / 40 : ℝ)) (b := (213 / 64 : ℝ))
    (l := (14450843704325403321 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (37529 / 10000000 : ℝ))
  have hp : (817375260267094 / 18446744073709551616 : ℝ) ≤ 8 * (37529 / 10000000 : ℝ) *
      (((213 / 64 : ℝ) - (133 / 40 : ℝ)) * (14450843704325403321 / 18446744073709551616 : ℝ) / denomMax (133 / 40 : ℝ) (213 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel09 : (817887258291357 / 18446744073709551616 : ℝ) ≤
    8 * (37529 / 10000000 : ℝ) * ∫ s in (213 / 64 : ℝ)..(533 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (213 / 64 : ℝ)) (b := (533 / 160 : ℝ))
    (l := (14459821192356168261 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (37529 / 10000000 : ℝ))
  have hp : (817887258291357 / 18446744073709551616 : ℝ) ≤ 8 * (37529 / 10000000 : ℝ) *
      (((533 / 160 : ℝ) - (213 / 64 : ℝ)) * (14459821192356168261 / 18446744073709551616 : ℝ) / denomMax (213 / 64 : ℝ) (533 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel10 : (818402339855534 / 18446744073709551616 : ℝ) ≤
    8 * (37529 / 10000000 : ℝ) * ∫ s in (533 / 160 : ℝ)..(1067 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (533 / 160 : ℝ)) (b := (1067 / 320 : ℝ))
    (l := (14468827425039849233 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (37529 / 10000000 : ℝ))
  have hp : (818402339855534 / 18446744073709551616 : ℝ) ≤ 8 * (37529 / 10000000 : ℝ) *
      (((1067 / 320 : ℝ) - (533 / 160 : ℝ)) * (14468827425039849233 / 18446744073709551616 : ℝ) / denomMax (533 / 160 : ℝ) (1067 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel11 : (818920515648358 / 18446744073709551616 : ℝ) ≤
    8 * (37529 / 10000000 : ℝ) * ∫ s in (1067 / 320 : ℝ)..(267 / 80 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (1067 / 320 : ℝ)) (b := (267 / 80 : ℝ))
    (l := (14477862541730885395 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (37529 / 10000000 : ℝ))
  have hp : (818920515648358 / 18446744073709551616 : ℝ) ≤ 8 * (37529 / 10000000 : ℝ) *
      (((267 / 80 : ℝ) - (1067 / 320 : ℝ)) * (14477862541730885395 / 18446744073709551616 : ℝ) / denomMax (1067 / 320 : ℝ) (267 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel12 : (819441796443263 / 18446744073709551616 : ℝ) ≤
    8 * (37529 / 10000000 : ℝ) * ∫ s in (267 / 80 : ℝ)..(1069 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (267 / 80 : ℝ)) (b := (1069 / 320 : ℝ))
    (l := (14486926682692861259 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (37529 / 10000000 : ℝ))
  have hp : (819441796443263 / 18446744073709551616 : ℝ) ≤ 8 * (37529 / 10000000 : ℝ) *
      (((1069 / 320 : ℝ) - (267 / 80 : ℝ)) * (14486926682692861259 / 18446744073709551616 : ℝ) / denomMax (267 / 80 : ℝ) (1069 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel13 : (819966193099013 / 18446744073709551616 : ℝ) ≤
    8 * (37529 / 10000000 : ℝ) * ∫ s in (1069 / 320 : ℝ)..(107 / 32 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (1069 / 320 : ℝ)) (b := (107 / 32 : ℝ))
    (l := (14496019989105988015 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (37529 / 10000000 : ℝ))
  have hp : (819966193099013 / 18446744073709551616 : ℝ) ≤ 8 * (37529 / 10000000 : ℝ) *
      (((107 / 32 : ℝ) - (1069 / 320 : ℝ)) * (14496019989105988015 / 18446744073709551616 : ℝ) / denomMax (1069 / 320 : ℝ) (107 / 32 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel14 : (820493716560318 / 18446744073709551616 : ℝ) ≤
    8 * (37529 / 10000000 : ℝ) * ∫ s in (107 / 32 : ℝ)..(1071 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (107 / 32 : ℝ)) (b := (1071 / 320 : ℝ))
    (l := (14505142603074659382 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (37529 / 10000000 : ℝ))
  have hp : (820493716560318 / 18446744073709551616 : ℝ) ≤ 8 * (37529 / 10000000 : ℝ) *
      (((1071 / 320 : ℝ) - (107 / 32 : ℝ)) * (14505142603074659382 / 18446744073709551616 : ℝ) / denomMax (107 / 32 : ℝ) (1071 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel15 : (821024377858470 / 18446744073709551616 : ℝ) ≤
    8 * (37529 / 10000000 : ℝ) * ∫ s in (1071 / 320 : ℝ)..(67 / 20 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (1071 / 320 : ℝ)) (b := (67 / 20 : ℝ))
    (l := (14514294667635082866 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (37529 / 10000000 : ℝ))
  have hp : (821024377858470 / 18446744073709551616 : ℝ) ≤ 8 * (37529 / 10000000 : ℝ) *
      (((67 / 20 : ℝ) - (1071 / 320 : ℝ)) * (14514294667635082866 / 18446744073709551616 : ℝ) / denomMax (1071 / 320 : ℝ) (67 / 20 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel16 : (821558188111981 / 18446744073709551616 : ℝ) ≤
    8 * (37529 / 10000000 : ℝ) * ∫ s in (67 / 20 : ℝ)..(1073 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (67 / 20 : ℝ)) (b := (1073 / 320 : ℝ))
    (l := (14523476326762987292 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (37529 / 10000000 : ℝ))
  have hp : (821558188111981 / 18446744073709551616 : ℝ) ≤ 8 * (37529 / 10000000 : ℝ) *
      (((1073 / 320 : ℝ) - (67 / 20 : ℝ)) * (14523476326762987292 / 18446744073709551616 : ℝ) / denomMax (67 / 20 : ℝ) (1073 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel17 : (822095158527223 / 18446744073709551616 : ℝ) ≤
    8 * (37529 / 10000000 : ℝ) * ∫ s in (1073 / 320 : ℝ)..(537 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (1073 / 320 : ℝ)) (b := (537 / 160 : ℝ))
    (l := (14532687725381407536 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (37529 / 10000000 : ℝ))
  have hp : (822095158527223 / 18446744073709551616 : ℝ) ≤ 8 * (37529 / 10000000 : ℝ) *
      (((537 / 160 : ℝ) - (1073 / 320 : ℝ)) * (14532687725381407536 / 18446744073709551616 : ℝ) / denomMax (1073 / 320 : ℝ) (537 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel18 : (822635300399085 / 18446744073709551616 : ℝ) ≤
    8 * (37529 / 10000000 : ℝ) * ∫ s in (537 / 160 : ℝ)..(215 / 64 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (537 / 160 : ℝ)) (b := (215 / 64 : ℝ))
    (l := (14541929009368547339 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (37529 / 10000000 : ℝ))
  have hp : (822635300399085 / 18446744073709551616 : ℝ) ≤ 8 * (37529 / 10000000 : ℝ) *
      (((215 / 64 : ℝ) - (537 / 160 : ℝ)) * (14541929009368547339 / 18446744073709551616 : ℝ) / denomMax (537 / 160 : ℝ) (215 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel19 : (823178625111627 / 18446744073709551616 : ℝ) ≤
    8 * (37529 / 10000000 : ℝ) * ∫ s in (215 / 64 : ℝ)..(269 / 80 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (215 / 64 : ℝ)) (b := (269 / 80 : ℝ))
    (l := (14551200325565721137 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (37529 / 10000000 : ℝ))
  have hp : (823178625111627 / 18446744073709551616 : ℝ) ≤ 8 * (37529 / 10000000 : ℝ) *
      (((269 / 80 : ℝ) - (215 / 64 : ℝ)) * (14551200325565721137 / 18446744073709551616 : ℝ) / denomMax (215 / 64 : ℝ) (269 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel20 : (823725144138750 / 18446744073709551616 : ℝ) ≤
    8 * (37529 / 10000000 : ℝ) * ∫ s in (269 / 80 : ℝ)..(1077 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (269 / 80 : ℝ)) (b := (1077 / 320 : ℝ))
    (l := (14560501821785375846 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (37529 / 10000000 : ℝ))
  have hp : (823725144138750 / 18446744073709551616 : ℝ) ≤ 8 * (37529 / 10000000 : ℝ) *
      (((1077 / 320 : ℝ) - (269 / 80 : ℝ)) * (14560501821785375846 / 18446744073709551616 : ℝ) / denomMax (269 / 80 : ℝ) (1077 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel21 : (824274869044863 / 18446744073709551616 : ℝ) ≤
    8 * (37529 / 10000000 : ℝ) * ∫ s in (1077 / 320 : ℝ)..(539 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (1077 / 320 : ℝ)) (b := (539 / 160 : ℝ))
    (l := (14569833646819193538 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (37529 / 10000000 : ℝ))
  have hp : (824274869044863 / 18446744073709551616 : ℝ) ≤ 8 * (37529 / 10000000 : ℝ) *
      (((539 / 160 : ℝ) - (1077 / 320 : ℝ)) * (14569833646819193538 / 18446744073709551616 : ℝ) / denomMax (1077 / 320 : ℝ) (539 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel22 : (824827811485564 / 18446744073709551616 : ℝ) ≤
    8 * (37529 / 10000000 : ℝ) * ∫ s in (539 / 160 : ℝ)..(1079 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (539 / 160 : ℝ)) (b := (1079 / 320 : ℝ))
    (l := (14579195950446275975 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (37529 / 10000000 : ℝ))
  have hp : (824827811485564 / 18446744073709551616 : ℝ) ≤ 8 * (37529 / 10000000 : ℝ) *
      (((1079 / 320 : ℝ) - (539 / 160 : ℝ)) * (14579195950446275975 / 18446744073709551616 : ℝ) / denomMax (539 / 160 : ℝ) (1079 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel23 : (825383983208332 / 18446744073709551616 : ℝ) ≤
    8 * (37529 / 10000000 : ℝ) * ∫ s in (1079 / 320 : ℝ)..(27 / 8 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (1079 / 320 : ℝ)) (b := (27 / 8 : ℝ))
    (l := (14588588883441411976 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (37529 / 10000000 : ℝ))
  have hp : (825383983208332 / 18446744073709551616 : ℝ) ≤ 8 * (37529 / 10000000 : ℝ) *
      (((27 / 8 : ℝ) - (1079 / 320 : ℝ)) * (14588588883441411976 / 18446744073709551616 : ℝ) / denomMax (1079 / 320 : ℝ) (27 / 8 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel24 : (825943396053213 / 18446744073709551616 : ℝ) ≤
    8 * (37529 / 10000000 : ℝ) * ∫ s in (27 / 8 : ℝ)..(1081 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (27 / 8 : ℝ)) (b := (1081 / 320 : ℝ))
    (l := (14598012597583428595 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (37529 / 10000000 : ℝ))
  have hp : (825943396053213 / 18446744073709551616 : ℝ) ≤ 8 * (37529 / 10000000 : ℝ) *
      (((1081 / 320 : ℝ) - (27 / 8 : ℝ)) * (14598012597583428595 / 18446744073709551616 : ℝ) / denomMax (27 / 8 : ℝ) (1081 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel25 : (826506061953525 / 18446744073709551616 : ℝ) ≤
    8 * (37529 / 10000000 : ℝ) * ∫ s in (1081 / 320 : ℝ)..(541 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (1081 / 320 : ℝ)) (b := (541 / 160 : ℝ))
    (l := (14607467245663627119 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (37529 / 10000000 : ℝ))
  have hp : (826506061953525 / 18446744073709551616 : ℝ) ≤ 8 * (37529 / 10000000 : ℝ) *
      (((541 / 160 : ℝ) - (1081 / 320 : ℝ)) * (14607467245663627119 / 18446744073709551616 : ℝ) / denomMax (1081 / 320 : ℝ) (541 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel26 : (827071992936570 / 18446744073709551616 : ℝ) ≤
    8 * (37529 / 10000000 : ℝ) * ∫ s in (541 / 160 : ℝ)..(1083 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (541 / 160 : ℝ)) (b := (1083 / 320 : ℝ))
    (l := (14616952981494304894 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (37529 / 10000000 : ℝ))
  have hp : (827071992936570 / 18446744073709551616 : ℝ) ≤ 8 * (37529 / 10000000 : ℝ) *
      (((1083 / 320 : ℝ) - (541 / 160 : ℝ)) * (14616952981494304894 / 18446744073709551616 : ℝ) / denomMax (541 / 160 : ℝ) (1083 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel27 : (827641201124344 / 18446744073709551616 : ℝ) ≤
    8 * (37529 / 10000000 : ℝ) * ∫ s in (1083 / 320 : ℝ)..(271 / 80 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (1083 / 320 : ℝ)) (b := (271 / 80 : ℝ))
    (l := (14626469959917364011 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (37529 / 10000000 : ℝ))
  have hp : (827641201124344 / 18446744073709551616 : ℝ) ≤ 8 * (37529 / 10000000 : ℝ) *
      (((271 / 80 : ℝ) - (1083 / 320 : ℝ)) * (14626469959917364011 / 18446744073709551616 : ℝ) / denomMax (1083 / 320 : ℝ) (271 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel28 : (828213698734266 / 18446744073709551616 : ℝ) ≤
    8 * (37529 / 10000000 : ℝ) * ∫ s in (271 / 80 : ℝ)..(217 / 64 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (271 / 80 : ℝ)) (b := (217 / 64 : ℝ))
    (l := (14636018336813007889 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (37529 / 10000000 : ℝ))
  have hp : (828213698734266 / 18446744073709551616 : ℝ) ≤ 8 * (37529 / 10000000 : ℝ) *
      (((217 / 64 : ℝ) - (271 / 80 : ℝ)) * (14636018336813007889 / 18446744073709551616 : ℝ) / denomMax (271 / 80 : ℝ) (217 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel29 : (828789498079909 / 18446744073709551616 : ℝ) ≤
    8 * (37529 / 10000000 : ℝ) * ∫ s in (217 / 64 : ℝ)..(543 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (217 / 64 : ℝ)) (b := (543 / 160 : ℝ))
    (l := (14645598269108526814 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (37529 / 10000000 : ℝ))
  have hp : (828789498079909 / 18446744073709551616 : ℝ) ≤ 8 * (37529 / 10000000 : ℝ) *
      (((543 / 160 : ℝ) - (217 / 64 : ℝ)) * (14645598269108526814 / 18446744073709551616 : ℝ) / denomMax (217 / 64 : ℝ) (543 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel30 : (829368611571738 / 18446744073709551616 : ℝ) ≤
    8 * (37529 / 10000000 : ℝ) * ∫ s in (543 / 160 : ℝ)..(1087 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (543 / 160 : ℝ)) (b := (1087 / 320 : ℝ))
    (l := (14655209914787173509 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (37529 / 10000000 : ℝ))
  have hp : (829368611571738 / 18446744073709551616 : ℝ) ≤ 8 * (37529 / 10000000 : ℝ) *
      (((1087 / 320 : ℝ) - (543 / 160 : ℝ)) * (14655209914787173509 / 18446744073709551616 : ℝ) / denomMax (543 / 160 : ℝ) (1087 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel31 : (829951051717857 / 18446744073709551616 : ℝ) ≤
    8 * (37529 / 10000000 : ℝ) * ∫ s in (1087 / 320 : ℝ)..(17 / 5 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (1087 / 320 : ℝ)) (b := (17 / 5 : ℝ))
    (l := (14664853432897129813 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (37529 / 10000000 : ℝ))
  have hp : (829951051717857 / 18446744073709551616 : ℝ) ≤ 8 * (37529 / 10000000 : ℝ) *
      (((17 / 5 : ℝ) - (1087 / 320 : ℝ)) * (14664853432897129813 / 18446744073709551616 : ℝ) / denomMax (1087 / 320 : ℝ) (17 / 5 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

theorem lower : (26285590114210672 / 18446744073709551616 : ℝ) ≤
    8 * (37529 / 10000000 : ℝ) * ∫ s in (33 / 10 : ℝ)..(17 / 5 : ℝ), density s := by
  have he := integral_grid_sum (33 / 10 : ℝ) (17 / 5 : ℝ) 32 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [endpoint, alpha, beta])
  norm_num [Finset.sum_range_succ] at he
  linarith only [panel00, panel01, panel02, panel03, panel04, panel05, panel06, panel07, panel08, panel09, panel10, panel11, panel12, panel13, panel14, panel15, panel16, panel17, panel18, panel19, panel20, panel21, panel22, panel23, panel24, panel25, panel26, panel27, panel28, panel29, panel30, panel31, he]

end Wu18938Campaign.M3.Confirmed.TableRow13
