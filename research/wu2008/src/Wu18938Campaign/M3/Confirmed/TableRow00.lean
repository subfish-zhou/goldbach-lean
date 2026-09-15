import Wu18938Campaign.M3.Confirmed.TableBounds

noncomputable section
namespace Wu18938Campaign.M3.Confirmed.TableRow00
open Real Set MeasureTheory QuarterTrim
open WuSource.SrcSixthGain Wu18938Campaign.M3.Confirmed.TableBounds

private theorem panel00 : (4595951683562688 / 18446744073709551616 : ℝ) ≤
    8 * (211041 / 10000000 : ℝ) * ∫ s in (2 / 1 : ℝ)..(641 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (2 / 1 : ℝ)) (b := (641 / 320 : ℝ))
    (l := (12181269852053927451 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (211041 / 10000000 : ℝ))
  have hp : (4595951683562688 / 18446744073709551616 : ℝ) ≤ 8 * (211041 / 10000000 : ℝ) *
      (((641 / 320 : ℝ) - (2 / 1 : ℝ)) * (12181269852053927451 / 18446744073709551616 : ℝ) / denomMax (2 / 1 : ℝ) (641 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel01 : (4593098589168264 / 18446744073709551616 : ℝ) ≤
    8 * (211041 / 10000000 : ℝ) * ∫ s in (641 / 320 : ℝ)..(321 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (641 / 320 : ℝ)) (b := (321 / 160 : ℝ))
    (l := (12184473573044120662 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (211041 / 10000000 : ℝ))
  have hp : (4593098589168264 / 18446744073709551616 : ℝ) ≤ 8 * (211041 / 10000000 : ℝ) *
      (((321 / 160 : ℝ) - (641 / 320 : ℝ)) * (12184473573044120662 / 18446744073709551616 : ℝ) / denomMax (641 / 320 : ℝ) (321 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel02 : (4590262466155949 / 18446744073709551616 : ℝ) ≤
    8 * (211041 / 10000000 : ℝ) * ∫ s in (321 / 160 : ℝ)..(643 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (321 / 160 : ℝ)) (b := (643 / 320 : ℝ))
    (l := (12187683369921535708 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (211041 / 10000000 : ℝ))
  have hp : (4590262466155949 / 18446744073709551616 : ℝ) ≤ 8 * (211041 / 10000000 : ℝ) *
      (((643 / 320 : ℝ) - (321 / 160 : ℝ)) * (12187683369921535708 / 18446744073709551616 : ℝ) / denomMax (321 / 160 : ℝ) (643 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel03 : (4587443258391512 / 18446744073709551616 : ℝ) ≤
    8 * (211041 / 10000000 : ℝ) * ∫ s in (643 / 320 : ℝ)..(161 / 80 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (643 / 320 : ℝ)) (b := (161 / 80 : ℝ))
    (l := (12190899260035775138 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (211041 / 10000000 : ℝ))
  have hp : (4587443258391512 / 18446744073709551616 : ℝ) ≤ 8 * (211041 / 10000000 : ℝ) *
      (((161 / 80 : ℝ) - (643 / 320 : ℝ)) * (12190899260035775138 / 18446744073709551616 : ℝ) / denomMax (643 / 320 : ℝ) (161 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel04 : (4584640910175712 / 18446744073709551616 : ℝ) ≤
    8 * (211041 / 10000000 : ℝ) * ∫ s in (161 / 80 : ℝ)..(129 / 64 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (161 / 80 : ℝ)) (b := (129 / 64 : ℝ))
    (l := (12194121260802744821 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (211041 / 10000000 : ℝ))
  have hp : (4584640910175712 / 18446744073709551616 : ℝ) ≤ 8 * (211041 / 10000000 : ℝ) *
      (((129 / 64 : ℝ) - (161 / 80 : ℝ)) * (12194121260802744821 / 18446744073709551616 : ℝ) / denomMax (161 / 80 : ℝ) (129 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel05 : (4581855366241336 / 18446744073709551616 : ℝ) ≤
    8 * (211041 / 10000000 : ℝ) * ∫ s in (129 / 64 : ℝ)..(323 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (129 / 64 : ℝ)) (b := (323 / 160 : ℝ))
    (l := (12197349389704971858 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (211041 / 10000000 : ℝ))
  have hp : (4581855366241336 / 18446744073709551616 : ℝ) ≤ 8 * (211041 / 10000000 : ℝ) *
      (((323 / 160 : ℝ) - (129 / 64 : ℝ)) * (12197349389704971858 / 18446744073709551616 : ℝ) / denomMax (129 / 64 : ℝ) (323 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel06 : (4579086571750283 / 18446744073709551616 : ℝ) ≤
    8 * (211041 / 10000000 : ℝ) * ∫ s in (323 / 160 : ℝ)..(647 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (323 / 160 : ℝ)) (b := (647 / 320 : ℝ))
    (l := (12200583664291924326 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (211041 / 10000000 : ℝ))
  have hp : (4579086571750283 / 18446744073709551616 : ℝ) ≤ 8 * (211041 / 10000000 : ℝ) *
      (((647 / 320 : ℝ) - (323 / 160 : ℝ)) * (12200583664291924326 / 18446744073709551616 : ℝ) / denomMax (323 / 160 : ℝ) (647 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel07 : (4576334472290664 / 18446744073709551616 : ℝ) ≤
    8 * (211041 / 10000000 : ℝ) * ∫ s in (647 / 320 : ℝ)..(81 / 40 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (647 / 320 : ℝ)) (b := (81 / 40 : ℝ))
    (l := (12203824102180332882 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (211041 / 10000000 : ℝ))
  have hp : (4576334472290664 / 18446744073709551616 : ℝ) ≤ 8 * (211041 / 10000000 : ℝ) *
      (((81 / 40 : ℝ) - (647 / 320 : ℝ)) * (12203824102180332882 / 18446744073709551616 : ℝ) / denomMax (647 / 320 : ℝ) (81 / 40 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel08 : (4573599013873938 / 18446744073709551616 : ℝ) ≤
    8 * (211041 / 10000000 : ℝ) * ∫ s in (81 / 40 : ℝ)..(649 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (81 / 40 : ℝ)) (b := (649 / 320 : ℝ))
    (l := (12207070721054514214 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (211041 / 10000000 : ℝ))
  have hp : (4573599013873938 / 18446744073709551616 : ℝ) ≤ 8 * (211041 / 10000000 : ℝ) *
      (((649 / 320 : ℝ) - (81 / 40 : ℝ)) * (12207070721054514214 / 18446744073709551616 : ℝ) / denomMax (81 / 40 : ℝ) (649 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel09 : (4570880142932077 / 18446744073709551616 : ℝ) ≤
    8 * (211041 / 10000000 : ℝ) * ∫ s in (649 / 320 : ℝ)..(65 / 32 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (649 / 320 : ℝ)) (b := (65 / 32 : ℝ))
    (l := (12210323538666696378 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (211041 / 10000000 : ℝ))
  have hp : (4570880142932077 / 18446744073709551616 : ℝ) ≤ 8 * (211041 / 10000000 : ℝ) *
      (((65 / 32 : ℝ) - (649 / 320 : ℝ)) * (12210323538666696378 / 18446744073709551616 : ℝ) / denomMax (649 / 320 : ℝ) (65 / 32 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel10 : (4568177806314756 / 18446744073709551616 : ℝ) ≤
    8 * (211041 / 10000000 : ℝ) * ∫ s in (65 / 32 : ℝ)..(651 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (65 / 32 : ℝ)) (b := (651 / 320 : ℝ))
    (l := (12213582572837346014 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (211041 / 10000000 : ℝ))
  have hp : (4568177806314756 / 18446744073709551616 : ℝ) ≤ 8 * (211041 / 10000000 : ℝ) *
      (((651 / 320 : ℝ) - (65 / 32 : ℝ)) * (12213582572837346014 / 18446744073709551616 : ℝ) / denomMax (65 / 32 : ℝ) (651 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel11 : (4565491951286575 / 18446744073709551616 : ℝ) ≤
    8 * (211041 / 10000000 : ℝ) * ∫ s in (651 / 320 : ℝ)..(163 / 80 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (651 / 320 : ℝ)) (b := (163 / 80 : ℝ))
    (l := (12216847841455497459 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (211041 / 10000000 : ℝ))
  have hp : (4565491951286575 / 18446744073709551616 : ℝ) ≤ 8 * (211041 / 10000000 : ℝ) *
      (((163 / 80 : ℝ) - (651 / 320 : ℝ)) * (12216847841455497459 / 18446744073709551616 : ℝ) / denomMax (651 / 320 : ℝ) (163 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel12 : (4562822525524305 / 18446744073709551616 : ℝ) ≤
    8 * (211041 / 10000000 : ℝ) * ∫ s in (163 / 80 : ℝ)..(653 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (163 / 80 : ℝ)) (b := (653 / 320 : ℝ))
    (l := (12220119362479083782 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (211041 / 10000000 : ℝ))
  have hp : (4562822525524305 / 18446744073709551616 : ℝ) ≤ 8 * (211041 / 10000000 : ℝ) *
      (((653 / 320 : ℝ) - (163 / 80 : ℝ)) * (12220119362479083782 / 18446744073709551616 : ℝ) / denomMax (163 / 80 : ℝ) (653 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel13 : (4560169477114166 / 18446744073709551616 : ℝ) ≤
    8 * (211041 / 10000000 : ℝ) * ∫ s in (653 / 320 : ℝ)..(327 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (653 / 320 : ℝ)) (b := (327 / 160 : ℝ))
    (l := (12223397153935269731 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (211041 / 10000000 : ℝ))
  have hp : (4560169477114166 / 18446744073709551616 : ℝ) ≤ 8 * (211041 / 10000000 : ℝ) *
      (((327 / 160 : ℝ) - (653 / 320 : ℝ)) * (12223397153935269731 / 18446744073709551616 : ℝ) / denomMax (653 / 320 : ℝ) (327 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel14 : (4557532754549129 / 18446744073709551616 : ℝ) ≤
    8 * (211041 / 10000000 : ℝ) * ∫ s in (327 / 160 : ℝ)..(131 / 64 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (327 / 160 : ℝ)) (b := (131 / 64 : ℝ))
    (l := (12226681233920786631 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (211041 / 10000000 : ℝ))
  have hp : (4557532754549129 / 18446744073709551616 : ℝ) ≤ 8 * (211041 / 10000000 : ℝ) *
      (((131 / 64 : ℝ) - (327 / 160 : ℝ)) * (12226681233920786631 / 18446744073709551616 : ℝ) / denomMax (327 / 160 : ℝ) (131 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel15 : (4554912306726249 / 18446744073709551616 : ℝ) ≤
    8 * (211041 / 10000000 : ℝ) * ∫ s in (131 / 64 : ℝ)..(41 / 20 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (131 / 64 : ℝ)) (b := (41 / 20 : ℝ))
    (l := (12229971620602269221 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (211041 / 10000000 : ℝ))
  have hp : (4554912306726249 / 18446744073709551616 : ℝ) ≤ 8 * (211041 / 10000000 : ℝ) *
      (((41 / 20 : ℝ) - (131 / 64 : ℝ)) * (12229971620602269221 / 18446744073709551616 : ℝ) / denomMax (131 / 64 : ℝ) (41 / 20 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel16 : (4552308082944017 / 18446744073709551616 : ℝ) ≤
    8 * (211041 / 10000000 : ℝ) * ∫ s in (41 / 20 : ℝ)..(657 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (41 / 20 : ℝ)) (b := (657 / 320 : ℝ))
    (l := (12233268332216594465 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (211041 / 10000000 : ℝ))
  have hp : (4552308082944017 / 18446744073709551616 : ℝ) ≤ 8 * (211041 / 10000000 : ℝ) *
      (((657 / 320 : ℝ) - (41 / 20 : ℝ)) * (12233268332216594465 / 18446744073709551616 : ℝ) / denomMax (41 / 20 : ℝ) (657 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel17 : (4549720032899752 / 18446744073709551616 : ℝ) ≤
    8 * (211041 / 10000000 : ℝ) * ∫ s in (657 / 320 : ℝ)..(329 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (657 / 320 : ℝ)) (b := (329 / 160 : ℝ))
    (l := (12236571387071222334 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (211041 / 10000000 : ℝ))
  have hp : (4549720032899752 / 18446744073709551616 : ℝ) ≤ 8 * (211041 / 10000000 : ℝ) *
      (((329 / 160 : ℝ) - (657 / 320 : ℝ)) * (12236571387071222334 / 18446744073709551616 : ℝ) / denomMax (657 / 320 : ℝ) (329 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel18 : (4547148106687003 / 18446744073709551616 : ℝ) ≤
    8 * (211041 / 10000000 : ℝ) * ∫ s in (329 / 160 : ℝ)..(659 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (329 / 160 : ℝ)) (b := (659 / 320 : ℝ))
    (l := (12239880803544538586 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (211041 / 10000000 : ℝ))
  have hp : (4547148106687003 / 18446744073709551616 : ℝ) ≤ 8 * (211041 / 10000000 : ℝ) *
      (((659 / 320 : ℝ) - (329 / 160 : ℝ)) * (12239880803544538586 / 18446744073709551616 : ℝ) / denomMax (329 / 160 : ℝ) (659 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel19 : (4544592254792990 / 18446744073709551616 : ℝ) ≤
    8 * (211041 / 10000000 : ℝ) * ∫ s in (659 / 320 : ℝ)..(33 / 16 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (659 / 320 : ℝ)) (b := (33 / 16 : ℝ))
    (l := (12243196600086199549 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (211041 / 10000000 : ℝ))
  have hp : (4544592254792990 / 18446744073709551616 : ℝ) ≤ 8 * (211041 / 10000000 : ℝ) *
      (((33 / 16 : ℝ) - (659 / 320 : ℝ)) * (12243196600086199549 / 18446744073709551616 : ℝ) / denomMax (659 / 320 : ℝ) (33 / 16 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel20 : (4542052428096067 / 18446744073709551616 : ℝ) ≤
    8 * (211041 / 10000000 : ℝ) * ∫ s in (33 / 16 : ℝ)..(661 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (33 / 16 : ℝ)) (b := (661 / 320 : ℝ))
    (l := (12246518795217478916 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (211041 / 10000000 : ℝ))
  have hp : (4542052428096067 / 18446744073709551616 : ℝ) ≤ 8 * (211041 / 10000000 : ℝ) *
      (((661 / 320 : ℝ) - (33 / 16 : ℝ)) * (12246518795217478916 / 18446744073709551616 : ℝ) / denomMax (33 / 16 : ℝ) (661 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel21 : (4539528577863206 / 18446744073709551616 : ℝ) ≤
    8 * (211041 / 10000000 : ℝ) * ∫ s in (661 / 320 : ℝ)..(331 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (661 / 320 : ℝ)) (b := (331 / 160 : ℝ))
    (l := (12249847407531616583 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (211041 / 10000000 : ℝ))
  have hp : (4539528577863206 / 18446744073709551616 : ℝ) ≤ 8 * (211041 / 10000000 : ℝ) *
      (((331 / 160 : ℝ) - (661 / 320 : ℝ)) * (12249847407531616583 / 18446744073709551616 : ℝ) / denomMax (661 / 320 : ℝ) (331 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel22 : (4537020655747513 / 18446744073709551616 : ℝ) ≤
    8 * (211041 / 10000000 : ℝ) * ∫ s in (331 / 160 : ℝ)..(663 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (331 / 160 : ℝ)) (b := (663 / 320 : ℝ))
    (l := (12253182455694169529 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (211041 / 10000000 : ℝ))
  have hp : (4537020655747513 / 18446744073709551616 : ℝ) ≤ 8 * (211041 / 10000000 : ℝ) *
      (((663 / 320 : ℝ) - (331 / 160 : ℝ)) * (12253182455694169529 / 18446744073709551616 : ℝ) / denomMax (331 / 160 : ℝ) (663 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel23 : (4534528613785766 / 18446744073709551616 : ℝ) ≤
    8 * (211041 / 10000000 : ℝ) * ∫ s in (663 / 320 : ℝ)..(83 / 40 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (663 / 320 : ℝ)) (b := (83 / 40 : ℝ))
    (l := (12256523958443364754 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (211041 / 10000000 : ℝ))
  have hp : (4534528613785766 / 18446744073709551616 : ℝ) ≤ 8 * (211041 / 10000000 : ℝ) *
      (((83 / 40 : ℝ) - (663 / 320 : ℝ)) * (12256523958443364754 / 18446744073709551616 : ℝ) / denomMax (663 / 320 : ℝ) (83 / 40 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel24 : (4532052404395976 / 18446744073709551616 : ℝ) ≤
    8 * (211041 / 10000000 : ℝ) * ∫ s in (83 / 40 : ℝ)..(133 / 64 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (83 / 40 : ℝ)) (b := (133 / 64 : ℝ))
    (l := (12259871934590454299 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (211041 / 10000000 : ℝ))
  have hp : (4532052404395976 / 18446744073709551616 : ℝ) ≤ 8 * (211041 / 10000000 : ℝ) *
      (((133 / 64 : ℝ) - (83 / 40 : ℝ)) * (12259871934590454299 / 18446744073709551616 : ℝ) / denomMax (83 / 40 : ℝ) (133 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel25 : (4529591980374977 / 18446744073709551616 : ℝ) ≤
    8 * (211041 / 10000000 : ℝ) * ∫ s in (133 / 64 : ℝ)..(333 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (133 / 64 : ℝ)) (b := (333 / 160 : ℝ))
    (l := (12263226403020072346 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (211041 / 10000000 : ℝ))
  have hp : (4529591980374977 / 18446744073709551616 : ℝ) ≤ 8 * (211041 / 10000000 : ℝ) *
      (((333 / 160 : ℝ) - (133 / 64 : ℝ)) * (12263226403020072346 / 18446744073709551616 : ℝ) / denomMax (133 / 64 : ℝ) (333 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel26 : (4527147294896035 / 18446744073709551616 : ℝ) ≤
    8 * (211041 / 10000000 : ℝ) * ∫ s in (333 / 160 : ℝ)..(667 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (333 / 160 : ℝ)) (b := (667 / 320 : ℝ))
    (l := (12266587382690594429 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (211041 / 10000000 : ℝ))
  have hp : (4527147294896035 / 18446744073709551616 : ℝ) ≤ 8 * (211041 / 10000000 : ℝ) *
      (((667 / 320 : ℝ) - (333 / 160 : ℝ)) * (12266587382690594429 / 18446744073709551616 : ℝ) / denomMax (333 / 160 : ℝ) (667 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel27 : (4524718301506487 / 18446744073709551616 : ℝ) ≤
    8 * (211041 / 10000000 : ℝ) * ∫ s in (667 / 320 : ℝ)..(167 / 80 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (667 / 320 : ℝ)) (b := (167 / 80 : ℝ))
    (l := (12269954892634498763 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (211041 / 10000000 : ℝ))
  have hp : (4524718301506487 / 18446744073709551616 : ℝ) ≤ 8 * (211041 / 10000000 : ℝ) *
      (((167 / 80 : ℝ) - (667 / 320 : ℝ)) * (12269954892634498763 / 18446744073709551616 : ℝ) / denomMax (667 / 320 : ℝ) (167 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel28 : (4522304954125397 / 18446744073709551616 : ℝ) ≤
    8 * (211041 / 10000000 : ℝ) * ∫ s in (167 / 80 : ℝ)..(669 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (167 / 80 : ℝ)) (b := (669 / 320 : ℝ))
    (l := (12273328951958729698 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (211041 / 10000000 : ℝ))
  have hp : (4522304954125397 / 18446744073709551616 : ℝ) ≤ 8 * (211041 / 10000000 : ℝ) *
      (((669 / 320 : ℝ) - (167 / 80 : ℝ)) * (12273328951958729698 / 18446744073709551616 : ℝ) / denomMax (167 / 80 : ℝ) (669 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel29 : (4519907207041244 / 18446744073709551616 : ℝ) ≤
    8 * (211041 / 10000000 : ℝ) * ∫ s in (669 / 320 : ℝ)..(67 / 32 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (669 / 320 : ℝ)) (b := (67 / 32 : ℝ))
    (l := (12276709579845063328 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (211041 / 10000000 : ℝ))
  have hp : (4519907207041244 / 18446744073709551616 : ℝ) ≤ 8 * (211041 / 10000000 : ℝ) *
      (((67 / 32 : ℝ) - (669 / 320 : ℝ)) * (12276709579845063328 / 18446744073709551616 : ℝ) / denomMax (669 / 320 : ℝ) (67 / 32 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel30 : (4517525014909626 / 18446744073709551616 : ℝ) ≤
    8 * (211041 / 10000000 : ℝ) * ∫ s in (67 / 32 : ℝ)..(671 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (67 / 32 : ℝ)) (b := (671 / 320 : ℝ))
    (l := (12280096795550475263 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (211041 / 10000000 : ℝ))
  have hp : (4517525014909626 / 18446744073709551616 : ℝ) ≤ 8 * (211041 / 10000000 : ℝ) *
      (((671 / 320 : ℝ) - (67 / 32 : ℝ)) * (12280096795550475263 / 18446744073709551616 : ℝ) / denomMax (67 / 32 : ℝ) (671 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel31 : (4515158332750988 / 18446744073709551616 : ℝ) ≤
    8 * (211041 / 10000000 : ℝ) * ∫ s in (671 / 320 : ℝ)..(21 / 10 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (671 / 320 : ℝ)) (b := (21 / 10 : ℝ))
    (l := (12283490618407510570 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (211041 / 10000000 : ℝ))
  have hp : (4515158332750988 / 18446744073709551616 : ℝ) ≤ 8 * (211041 / 10000000 : ℝ) *
      (((21 / 10 : ℝ) - (671 / 320 : ℝ)) * (12283490618407510570 / 18446744073709551616 : ℝ) / denomMax (671 / 320 : ℝ) (21 / 10 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

theorem lower : (145737563538874647 / 18446744073709551616 : ℝ) ≤
    8 * (211041 / 10000000 : ℝ) * ∫ s in (2 / 1 : ℝ)..(21 / 10 : ℝ), density s := by
  have he := integral_grid_sum (2 / 1 : ℝ) (21 / 10 : ℝ) 32 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [endpoint, alpha, beta])
  norm_num [Finset.sum_range_succ] at he
  linarith only [panel00, panel01, panel02, panel03, panel04, panel05, panel06, panel07, panel08, panel09, panel10, panel11, panel12, panel13, panel14, panel15, panel16, panel17, panel18, panel19, panel20, panel21, panel22, panel23, panel24, panel25, panel26, panel27, panel28, panel29, panel30, panel31, he]

end Wu18938Campaign.M3.Confirmed.TableRow00
