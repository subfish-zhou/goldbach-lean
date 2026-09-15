import Wu18938Campaign.M3.Confirmed.TableBounds

noncomputable section
namespace Wu18938Campaign.M3.Confirmed.TableRow08
open Real Set MeasureTheory QuarterTrim
open WuSource.SrcSixthGain Wu18938Campaign.M3.Confirmed.TableBounds

private theorem panel00 : (1815669426468675 / 18446744073709551616 : ℝ) ≤
    8 * (88648 / 10000000 : ℝ) * ∫ s in (14 / 5 : ℝ)..(897 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (14 / 5 : ℝ)) (b := (897 / 320 : ℝ))
    (l := (13262967369126941130 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (88648 / 10000000 : ℝ))
  have hp : (1815669426468675 / 18446744073709551616 : ℝ) ≤ 8 * (88648 / 10000000 : ℝ) *
      (((897 / 320 : ℝ) - (14 / 5 : ℝ)) * (13262967369126941130 / 18446744073709551616 : ℝ) / denomMax (14 / 5 : ℝ) (897 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel01 : (1815892391628915 / 18446744073709551616 : ℝ) ≤
    8 * (88648 / 10000000 : ℝ) * ∫ s in (897 / 320 : ℝ)..(449 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (897 / 320 : ℝ)) (b := (449 / 160 : ℝ))
    (l := (13268554096394587268 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (88648 / 10000000 : ℝ))
  have hp : (1815892391628915 / 18446744073709551616 : ℝ) ≤ 8 * (88648 / 10000000 : ℝ) *
      (((449 / 160 : ℝ) - (897 / 320 : ℝ)) * (13268554096394587268 / 18446744073709551616 : ℝ) / denomMax (897 / 320 : ℝ) (449 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel02 : (1816120445305527 / 18446744073709551616 : ℝ) ≤
    8 * (88648 / 10000000 : ℝ) * ∫ s in (449 / 160 : ℝ)..(899 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (449 / 160 : ℝ)) (b := (899 / 320 : ℝ))
    (l := (13274154865399653852 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (88648 / 10000000 : ℝ))
  have hp : (1816120445305527 / 18446744073709551616 : ℝ) ≤ 8 * (88648 / 10000000 : ℝ) *
      (((899 / 320 : ℝ) - (449 / 160 : ℝ)) * (13274154865399653852 / 18446744073709551616 : ℝ) / denomMax (449 / 160 : ℝ) (899 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel03 : (1816353591503469 / 18446744073709551616 : ℝ) ≤
    8 * (88648 / 10000000 : ℝ) * ∫ s in (899 / 320 : ℝ)..(45 / 16 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (899 / 320 : ℝ)) (b := (45 / 16 : ℝ))
    (l := (13279769729406849779 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (88648 / 10000000 : ℝ))
  have hp : (1816353591503469 / 18446744073709551616 : ℝ) ≤ 8 * (88648 / 10000000 : ℝ) *
      (((45 / 16 : ℝ) - (899 / 320 : ℝ)) * (13279769729406849779 / 18446744073709551616 : ℝ) / denomMax (899 / 320 : ℝ) (45 / 16 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel04 : (1816591834315522 / 18446744073709551616 : ℝ) ≤
    8 * (88648 / 10000000 : ℝ) * ∫ s in (45 / 16 : ℝ)..(901 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (45 / 16 : ℝ)) (b := (901 / 320 : ℝ))
    (l := (13285398741951927485 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (88648 / 10000000 : ℝ))
  have hp : (1816591834315522 / 18446744073709551616 : ℝ) ≤ 8 * (88648 / 10000000 : ℝ) *
      (((901 / 320 : ℝ) - (45 / 16 : ℝ)) * (13285398741951927485 / 18446744073709551616 : ℝ) / denomMax (45 / 16 : ℝ) (901 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel05 : (1816835177922475 / 18446744073709551616 : ℝ) ≤
    8 * (88648 / 10000000 : ℝ) * ∫ s in (901 / 320 : ℝ)..(451 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (901 / 320 : ℝ)) (b := (451 / 160 : ℝ))
    (l := (13291041956843417375 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (88648 / 10000000 : ℝ))
  have hp : (1816835177922475 / 18446744073709551616 : ℝ) ≤ 8 * (88648 / 10000000 : ℝ) *
      (((451 / 160 : ℝ) - (901 / 320 : ℝ)) * (13291041956843417375 / 18446744073709551616 : ℝ) / denomMax (901 / 320 : ℝ) (451 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel06 : (1817083626593310 / 18446744073709551616 : ℝ) ≤
    8 * (88648 / 10000000 : ℝ) * ∫ s in (451 / 160 : ℝ)..(903 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (451 / 160 : ℝ)) (b := (903 / 320 : ℝ))
    (l := (13296699428164375653 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (88648 / 10000000 : ℝ))
  have hp : (1817083626593310 / 18446744073709551616 : ℝ) ≤ 8 * (88648 / 10000000 : ℝ) *
      (((903 / 320 : ℝ) - (451 / 160 : ℝ)) * (13296699428164375653 / 18446744073709551616 : ℝ) / denomMax (451 / 160 : ℝ) (903 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel07 : (1817337184685391 / 18446744073709551616 : ℝ) ≤
    8 * (88648 / 10000000 : ℝ) * ∫ s in (903 / 320 : ℝ)..(113 / 40 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (903 / 320 : ℝ)) (b := (113 / 40 : ℝ))
    (l := (13302371210274145673 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (88648 / 10000000 : ℝ))
  have hp : (1817337184685391 / 18446744073709551616 : ℝ) ≤ 8 * (88648 / 10000000 : ℝ) *
      (((113 / 40 : ℝ) - (903 / 320 : ℝ)) * (13302371210274145673 / 18446744073709551616 : ℝ) / denomMax (903 / 320 : ℝ) (113 / 40 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel08 : (1817595856644661 / 18446744073709551616 : ℝ) ≤
    8 * (88648 / 10000000 : ℝ) * ∫ s in (113 / 40 : ℝ)..(181 / 64 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (113 / 40 : ℝ)) (b := (181 / 64 : ℝ))
    (l := (13308057357810132924 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (88648 / 10000000 : ℝ))
  have hp : (1817595856644661 / 18446744073709551616 : ℝ) ≤ 8 * (88648 / 10000000 : ℝ) *
      (((181 / 64 : ℝ) - (113 / 40 : ℝ)) * (13308057357810132924 / 18446744073709551616 : ℝ) / denomMax (113 / 40 : ℝ) (181 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel09 : (1817859647005833 / 18446744073709551616 : ℝ) ≤
    8 * (88648 / 10000000 : ℝ) * ∫ s in (181 / 64 : ℝ)..(453 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (181 / 64 : ℝ)) (b := (453 / 160 : ℝ))
    (l := (13313757925689593788 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (88648 / 10000000 : ℝ))
  have hp : (1817859647005833 / 18446744073709551616 : ℝ) ≤ 8 * (88648 / 10000000 : ℝ) *
      (((453 / 160 : ℝ) - (181 / 64 : ℝ)) * (13313757925689593788 / 18446744073709551616 : ℝ) / denomMax (181 / 64 : ℝ) (453 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel10 : (1818128560392602 / 18446744073709551616 : ℝ) ≤
    8 * (88648 / 10000000 : ℝ) * ∫ s in (453 / 160 : ℝ)..(907 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (453 / 160 : ℝ)) (b := (907 / 320 : ℝ))
    (l := (13319472969111438186 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (88648 / 10000000 : ℝ))
  have hp : (1818128560392602 / 18446744073709551616 : ℝ) ≤ 8 * (88648 / 10000000 : ℝ) *
      (((907 / 320 : ℝ) - (453 / 160 : ℝ)) * (13319472969111438186 / 18446744073709551616 : ℝ) / denomMax (453 / 160 : ℝ) (907 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel11 : (1818402601517842 / 18446744073709551616 : ℝ) ≤
    8 * (88648 / 10000000 : ℝ) * ∫ s in (907 / 320 : ℝ)..(227 / 80 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (907 / 320 : ℝ)) (b := (227 / 80 : ℝ))
    (l := (13325202543558046241 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (88648 / 10000000 : ℝ))
  have hp : (1818402601517842 / 18446744073709551616 : ℝ) ≤ 8 * (88648 / 10000000 : ℝ) *
      (((227 / 80 : ℝ) - (907 / 320 : ℝ)) * (13325202543558046241 / 18446744073709551616 : ℝ) / denomMax (907 / 320 : ℝ) (227 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel12 : (1818681775183820 / 18446744073709551616 : ℝ) ≤
    8 * (88648 / 10000000 : ℝ) * ∫ s in (227 / 80 : ℝ)..(909 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (227 / 80 : ℝ)) (b := (909 / 320 : ℝ))
    (l := (13330946704797099089 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (88648 / 10000000 : ℝ))
  have hp : (1818681775183820 / 18446744073709551616 : ℝ) ≤ 8 * (88648 / 10000000 : ℝ) *
      (((909 / 320 : ℝ) - (227 / 80 : ℝ)) * (13330946704797099089 / 18446744073709551616 : ℝ) / denomMax (227 / 80 : ℝ) (909 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel13 : (1818966086282410 / 18446744073709551616 : ℝ) ≤
    8 * (88648 / 10000000 : ℝ) * ∫ s in (909 / 320 : ℝ)..(91 / 32 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (909 / 320 : ℝ)) (b := (91 / 32 : ℝ))
    (l := (13336705508883423957 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (88648 / 10000000 : ℝ))
  have hp : (1818966086282410 / 18446744073709551616 : ℝ) ≤ 8 * (88648 / 10000000 : ℝ) *
      (((91 / 32 : ℝ) - (909 / 320 : ℝ)) * (13336705508883423957 / 18446744073709551616 : ℝ) / denomMax (909 / 320 : ℝ) (91 / 32 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel14 : (1819255539795307 / 18446744073709551616 : ℝ) ≤
    8 * (88648 / 10000000 : ℝ) * ∫ s in (91 / 32 : ℝ)..(911 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (91 / 32 : ℝ)) (b := (911 / 320 : ℝ))
    (l := (13342479012160853658 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (88648 / 10000000 : ℝ))
  have hp : (1819255539795307 / 18446744073709551616 : ℝ) ≤ 8 * (88648 / 10000000 : ℝ) *
      (((911 / 320 : ℝ) - (91 / 32 : ℝ)) * (13342479012160853658 / 18446744073709551616 : ℝ) / denomMax (91 / 32 : ℝ) (911 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel15 : (1819550140794256 / 18446744073709551616 : ℝ) ≤
    8 * (88648 / 10000000 : ℝ) * ∫ s in (911 / 320 : ℝ)..(57 / 20 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (911 / 320 : ℝ)) (b := (57 / 20 : ℝ))
    (l := (13348267271264100612 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (88648 / 10000000 : ℝ))
  have hp : (1819550140794256 / 18446744073709551616 : ℝ) ≤ 8 * (88648 / 10000000 : ℝ) *
      (((57 / 20 : ℝ) - (911 / 320 : ℝ)) * (13348267271264100612 / 18446744073709551616 : ℝ) / denomMax (911 / 320 : ℝ) (57 / 20 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel16 : (1819849894441272 / 18446744073709551616 : ℝ) ≤
    8 * (88648 / 10000000 : ℝ) * ∫ s in (57 / 20 : ℝ)..(913 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (57 / 20 : ℝ)) (b := (913 / 320 : ℝ))
    (l := (13354070343120645547 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (88648 / 10000000 : ℝ))
  have hp : (1819849894441272 / 18446744073709551616 : ℝ) ≤ 8 * (88648 / 10000000 : ℝ) *
      (((913 / 320 : ℝ) - (57 / 20 : ℝ)) * (13354070343120645547 / 18446744073709551616 : ℝ) / denomMax (57 / 20 : ℝ) (913 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel17 : (1820154805988871 / 18446744073709551616 : ℝ) ≤
    8 * (88648 / 10000000 : ℝ) * ∫ s in (913 / 320 : ℝ)..(457 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (913 / 320 : ℝ)) (b := (457 / 160 : ℝ))
    (l := (13359888284952640995 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (88648 / 10000000 : ℝ))
  have hp : (1820154805988871 / 18446744073709551616 : ℝ) ≤ 8 * (88648 / 10000000 : ℝ) *
      (((457 / 160 : ℝ) - (913 / 320 : ℝ)) * (13359888284952640995 / 18446744073709551616 : ℝ) / denomMax (913 / 320 : ℝ) (457 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel18 : (1820464880780307 / 18446744073709551616 : ℝ) ≤
    8 * (88648 / 10000000 : ℝ) * ∫ s in (457 / 160 : ℝ)..(183 / 64 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (457 / 160 : ℝ)) (b := (183 / 64 : ℝ))
    (l := (13365721154278829739 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (88648 / 10000000 : ℝ))
  have hp : (1820464880780307 / 18446744073709551616 : ℝ) ≤ 8 * (88648 / 10000000 : ℝ) *
      (((183 / 64 : ℝ) - (457 / 160 : ℝ)) * (13365721154278829739 / 18446744073709551616 : ℝ) / denomMax (457 / 160 : ℝ) (183 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel19 : (1820780124249810 / 18446744073709551616 : ℝ) ≤
    8 * (88648 / 10000000 : ℝ) * ∫ s in (183 / 64 : ℝ)..(229 / 80 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (183 / 64 : ℝ)) (b := (229 / 80 : ℝ))
    (l := (13371569008916478335 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (88648 / 10000000 : ℝ))
  have hp : (1820780124249810 / 18446744073709551616 : ℝ) ≤ 8 * (88648 / 10000000 : ℝ) *
      (((229 / 80 : ℝ) - (183 / 64 : ℝ)) * (13371569008916478335 / 18446744073709551616 : ℝ) / denomMax (183 / 64 : ℝ) (229 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel20 : (1821100541922824 / 18446744073709551616 : ℝ) ≤
    8 * (88648 / 10000000 : ℝ) * ∫ s in (229 / 80 : ℝ)..(917 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (229 / 80 : ℝ)) (b := (917 / 320 : ℝ))
    (l := (13377431906983325851 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (88648 / 10000000 : ℝ))
  have hp : (1821100541922824 / 18446744073709551616 : ℝ) ≤ 8 * (88648 / 10000000 : ℝ) *
      (((917 / 320 : ℝ) - (229 / 80 : ℝ)) * (13377431906983325851 / 18446744073709551616 : ℝ) / denomMax (229 / 80 : ℝ) (917 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel21 : (1821426139416260 / 18446744073709551616 : ℝ) ≤
    8 * (88648 / 10000000 : ℝ) * ∫ s in (917 / 320 : ℝ)..(459 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (917 / 320 : ℝ)) (b := (459 / 160 : ℝ))
    (l := (13383309906899547969 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (88648 / 10000000 : ℝ))
  have hp : (1821426139416260 / 18446744073709551616 : ℝ) ≤ 8 * (88648 / 10000000 : ℝ) *
      (((459 / 160 : ℝ) - (917 / 320 : ℝ)) * (13383309906899547969 / 18446744073709551616 : ℝ) / denomMax (917 / 320 : ℝ) (459 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel22 : (1821756922438743 / 18446744073709551616 : ℝ) ≤
    8 * (88648 / 10000000 : ℝ) * ∫ s in (459 / 160 : ℝ)..(919 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (459 / 160 : ℝ)) (b := (919 / 320 : ℝ))
    (l := (13389203067389736582 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (88648 / 10000000 : ℝ))
  have hp : (1821756922438743 / 18446744073709551616 : ℝ) ≤ 8 * (88648 / 10000000 : ℝ) *
      (((919 / 320 : ℝ) - (459 / 160 : ℝ)) * (13389203067389736582 / 18446744073709551616 : ℝ) / denomMax (459 / 160 : ℝ) (919 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel23 : (1822092896790867 / 18446744073709551616 : ℝ) ≤
    8 * (88648 / 10000000 : ℝ) * ∫ s in (919 / 320 : ℝ)..(23 / 8 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (919 / 320 : ℝ)) (b := (23 / 8 : ℝ))
    (l := (13395111447484895043 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (88648 / 10000000 : ℝ))
  have hp : (1822092896790867 / 18446744073709551616 : ℝ) ≤ 8 * (88648 / 10000000 : ℝ) *
      (((23 / 8 : ℝ) - (919 / 320 : ℝ)) * (13395111447484895043 / 18446744073709551616 : ℝ) / denomMax (919 / 320 : ℝ) (23 / 8 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel24 : (1822434068365459 / 18446744073709551616 : ℝ) ≤
    8 * (88648 / 10000000 : ℝ) * ∫ s in (23 / 8 : ℝ)..(921 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (23 / 8 : ℝ)) (b := (921 / 320 : ℝ))
    (l := (13401035106524449195 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (88648 / 10000000 : ℝ))
  have hp : (1822434068365459 / 18446744073709551616 : ℝ) ≤ 8 * (88648 / 10000000 : ℝ) *
      (((921 / 320 : ℝ) - (23 / 8 : ℝ)) * (13401035106524449195 / 18446744073709551616 : ℝ) / denomMax (23 / 8 : ℝ) (921 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel25 : (1822780443147835 / 18446744073709551616 : ℝ) ≤
    8 * (88648 / 10000000 : ℝ) * ∫ s in (921 / 320 : ℝ)..(461 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (921 / 320 : ℝ)) (b := (461 / 160 : ℝ))
    (l := (13406974104158274346 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (88648 / 10000000 : ℝ))
  have hp : (1822780443147835 / 18446744073709551616 : ℝ) ≤ 8 * (88648 / 10000000 : ℝ) *
      (((461 / 160 : ℝ) - (921 / 320 : ℝ)) * (13406974104158274346 / 18446744073709551616 : ℝ) / denomMax (921 / 320 : ℝ) (461 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel26 : (1823132027216075 / 18446744073709551616 : ℝ) ≤
    8 * (88648 / 10000000 : ℝ) * ∫ s in (461 / 160 : ℝ)..(923 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (461 / 160 : ℝ)) (b := (923 / 320 : ℝ))
    (l := (13412928500348738321 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (88648 / 10000000 : ℝ))
  have hp : (1823132027216075 / 18446744073709551616 : ℝ) ≤ 8 * (88648 / 10000000 : ℝ) *
      (((923 / 320 : ℝ) - (461 / 160 : ℝ)) * (13412928500348738321 / 18446744073709551616 : ℝ) / denomMax (461 / 160 : ℝ) (923 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel27 : (1823488826741292 / 18446744073709551616 : ℝ) ≤
    8 * (88648 / 10000000 : ℝ) * ∫ s in (923 / 320 : ℝ)..(231 / 80 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (923 / 320 : ℝ)) (b := (231 / 80 : ℝ))
    (l := (13418898355372760753 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (88648 / 10000000 : ℝ))
  have hp : (1823488826741292 / 18446744073709551616 : ℝ) ≤ 8 * (88648 / 10000000 : ℝ) *
      (((231 / 80 : ℝ) - (923 / 320 : ℝ)) * (13418898355372760753 / 18446744073709551616 : ℝ) / denomMax (923 / 320 : ℝ) (231 / 80 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel28 : (1823850847987908 / 18446744073709551616 : ℝ) ≤
    8 * (88648 / 10000000 : ℝ) * ∫ s in (231 / 80 : ℝ)..(185 / 64 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (231 / 80 : ℝ)) (b := (185 / 64 : ℝ))
    (l := (13424883729823888759 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (88648 / 10000000 : ℝ))
  have hp : (1823850847987908 / 18446744073709551616 : ℝ) ≤ 8 * (88648 / 10000000 : ℝ) *
      (((185 / 64 : ℝ) - (231 / 80 : ℝ)) * (13424883729823888759 / 18446744073709551616 : ℝ) / denomMax (231 / 80 : ℝ) (185 / 64 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel29 : (1824218097313938 / 18446744073709551616 : ℝ) ≤
    8 * (88648 / 10000000 : ℝ) * ∫ s in (185 / 64 : ℝ)..(463 / 160 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (185 / 64 : ℝ)) (b := (463 / 160 : ℝ))
    (l := (13430884684614389152 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (88648 / 10000000 : ℝ))
  have hp : (1824218097313938 / 18446744073709551616 : ℝ) ≤ 8 * (88648 / 10000000 : ℝ) *
      (((463 / 160 : ℝ) - (185 / 64 : ℝ)) * (13430884684614389152 / 18446744073709551616 : ℝ) / denomMax (185 / 64 : ℝ) (463 / 160 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel30 : (1824590581171271 / 18446744073709551616 : ℝ) ≤
    8 * (88648 / 10000000 : ℝ) * ∫ s in (463 / 160 : ℝ)..(927 / 320 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (463 / 160 : ℝ)) (b := (927 / 320 : ℝ))
    (l := (13436901280977357351 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (88648 / 10000000 : ℝ))
  have hp : (1824590581171271 / 18446744073709551616 : ℝ) ≤ 8 * (88648 / 10000000 : ℝ) *
      (((927 / 320 : ℝ) - (463 / 160 : ℝ)) * (13436901280977357351 / 18446744073709551616 : ℝ) / denomMax (463 / 160 : ℝ) (927 / 320 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

private theorem panel31 : (1824968306105964 / 18446744073709551616 : ℝ) ≤
    8 * (88648 / 10000000 : ℝ) * ∫ s in (927 / 320 : ℝ)..(29 / 10 : ℝ), density s := by
  have h := panel_lower (upper := false) (a := (927 / 320 : ℝ)) (b := (29 / 10 : ℝ))
    (l := (13442933580468843137 / 18446744073709551616 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [endpoint, alpha, beta])
    (by norm_num [split, alpha, beta]) (by norm_num)
    (by norm_num [ratio, alpha, beta])
    (by norm_num [logLower, ratio, alpha, beta, Finset.sum_range_succ])
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ 8 * (88648 / 10000000 : ℝ))
  have hp : (1824968306105964 / 18446744073709551616 : ℝ) ≤ 8 * (88648 / 10000000 : ℝ) *
      (((29 / 10 : ℝ) - (927 / 320 : ℝ)) * (13442933580468843137 / 18446744073709551616 : ℝ) / denomMax (927 / 320 : ℝ) (29 / 10 : ℝ)) := by
    norm_num [denomMax, denom, vertex, alpha]
  exact hp.trans hm

theorem lower : (58237413290118711 / 18446744073709551616 : ℝ) ≤
    8 * (88648 / 10000000 : ℝ) * ∫ s in (14 / 5 : ℝ)..(29 / 10 : ℝ), density s := by
  have he := integral_grid_sum (14 / 5 : ℝ) (29 / 10 : ℝ) 32 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [endpoint, alpha, beta])
  norm_num [Finset.sum_range_succ] at he
  linarith only [panel00, panel01, panel02, panel03, panel04, panel05, panel06, panel07, panel08, panel09, panel10, panel11, panel12, panel13, panel14, panel15, panel16, panel17, panel18, panel19, panel20, panel21, panel22, panel23, panel24, panel25, panel26, panel27, panel28, panel29, panel30, panel31, he]

end Wu18938Campaign.M3.Confirmed.TableRow08
