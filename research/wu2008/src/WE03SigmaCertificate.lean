import WE03SigmaWeights
import W02AcceptedGain
import W06SigmaV2
import W03Table

noncomputable section
namespace WuTarget.E03Sigma
open NodeExtension ActualNineFeedback
open scoped BigOperators

def amplitudeLower : ℝ := 57153427687978657391 / 77653743750000000000000

theorem amplitudeLower_eq : amplitudeLower = W06.sigmaLower Wu04Bypass.v8 := by
  unfold W06.sigmaLower
  simp_rw [← W02.qV8_cast]
  norm_num [amplitudeLower, Fin.sum_univ_succ, W06.sigmaCoeff, W06.massLower,
    W06.denominatorLower, W02.qV8]

theorem amplitudeLower_pos : 0 < amplitudeLower := by
  norm_num [amplitudeLower]

theorem amplitudeLower_le :
    amplitudeLower ≤ aProfile (nineProfile W04Accepted.enhanced) := by
  rw [amplitudeLower_eq]
  calc
    W06.sigmaLower Wu04Bypass.v8 ≤ W06.sigmaLower W04Accepted.enhanced :=
      Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left
        (W04Accepted.old_le_enhanced k) (W06.sigmaCoeff_pos k).le)
    _ ≤ _ := W06.sigmaLower_le_aProfile W04Accepted.enhanced_nonneg

theorem sum11_eq :
    (∑ i ∈ Finset.Icc 11 29, logTerm i) =
      412486414959560911 / 3166328995398208640 := by
  norm_num [Finset.sum_Icc_succ_top, logTerm]

theorem sum12_eq :
    (∑ i ∈ Finset.Icc 12 29, logTerm i) =
      11740970438014817 / 102139645012845440 := by
  norm_num [Finset.sum_Icc_succ_top, logTerm]

theorem weightLower_eq (j : Fin 21) :
    weightLower j = if j.val < 20 then
      412486414959560911 / 3166328995398208640 else
      11740970438014817 / 102139645012845440 := by
  unfold weightLower sigmaStart
  split_ifs <;> first | exact sum11_eq | exact sum12_eq

def weightedLower : ℝ :=
  1399099504326342791683754933 / 2588934793133759551228748000

theorem weightedLower_eq :
    weightedLower = ∑ j : Fin 21, W03.paidWeights j * weightLower j := by
  simp_rw [weightLower_eq]
  norm_num [weightedLower, Fin.sum_univ_succ, W03.paidWeights]

theorem weightedLower_pos : 0 < weightedLower := by
  norm_num [weightedLower]

def exactGain : ℝ :=
  79963332348802415464324604384925910070813159803 /
    201040479011468223665232194825325000000000000000000

def ordinaryCredit : ℝ := 24859 / 250000000

theorem exactGain_eq : exactGain = amplitudeLower * weightedLower := by
  norm_num [exactGain, amplitudeLower, weightedLower]

theorem ordinaryCredit_pos : 0 < ordinaryCredit := by
  norm_num [ordinaryCredit]

theorem ordinaryCredit_le_exact : ordinaryCredit ≤ exactGain / 4 := by
  norm_num [ordinaryCredit, exactGain]

end WuTarget.E03Sigma
