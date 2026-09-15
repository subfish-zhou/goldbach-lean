import E03SigmaCertificate

noncomputable section
namespace WuTarget.E03Sigma
open NodeExtension ActualNineFeedback DirectFiniteF6
open scoped BigOperators

def rationalNodes : Fin 21 → ℝ :=
  matrixApply W02.rationalMatrix W04Accepted.enhanced

def sigmaNodes (j : Fin 21) : ℝ :=
  aProfile (nineProfile W04Accepted.enhanced) * W02.sigmaWeight j

def rationalGain : ℝ := Gamma rationalNodes 0

def sigmaGain : ℝ := Gamma sigmaNodes 0

theorem rationalNodes_nonneg (j : Fin 21) : 0 ≤ rationalNodes j :=
  matrixApply_nonneg W02.rationalMatrix_nonneg W04Accepted.enhanced_nonneg j

theorem sigmaNodes_nonneg (j : Fin 21) : 0 ≤ sigmaNodes j :=
  mul_nonneg W02Accepted.sigma_nonneg (W02.sigmaWeight_nonneg j)

theorem nodeGain_split : W02Accepted.nodeGain = rationalGain + sigmaGain := by
  simp only [W02Accepted.nodeGain, rationalGain, sigmaGain, W03.Gamma_eq_weights,
    W02Accepted.enhancedNodes, rationalNodes, sigmaNodes, mul_add, Finset.sum_add_distrib]

theorem sigma_net_identity : sigmaGain = W02Accepted.nodeGain - rationalGain := by
  rw [nodeGain_split]
  ring

theorem sigma_integral_identity :
    W02Accepted.nodeGain -
        Gamma (matrixApply W02.rationalMatrix W04Accepted.enhanced) 0 =
      aProfile (nineProfile W04Accepted.enhanced) *
        ∑ j : Fin 21, W03.weight j * W02.sigmaWeight j := by
  change W02Accepted.nodeGain - rationalGain = _
  rw [← sigma_net_identity, sigmaGain, W03.Gamma_eq_weights, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold sigmaNodes
  ring

theorem sigmaNodes_lower (j : Fin 21) :
    amplitudeLower * weightLower j ≤ sigmaNodes j :=
  mul_le_mul amplitudeLower_le (weightLower_le j)
    (weightLower_nonneg j) W02Accepted.sigma_nonneg

theorem exactGain_le_sigmaGain : exactGain ≤ sigmaGain := by
  calc
    exactGain = ∑ j : Fin 21, W03.paidWeights j *
        (amplitudeLower * weightLower j) := by
      rw [exactGain_eq, weightedLower_eq, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ ∑ j : Fin 21, W03.paidWeights j * sigmaNodes j :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left
        (sigmaNodes_lower j) (W03.paidWeights_pos j).le)
    _ ≤ sigmaGain := W03.paid_weights_consumer sigmaNodes_nonneg

theorem exactGain_le_original_difference :
    exactGain ≤ W02Accepted.nodeGain -
      Gamma (matrixApply W02.rationalMatrix W04Accepted.enhanced) 0 := by
  change exactGain ≤ W02Accepted.nodeGain - rationalGain
  rw [← sigma_net_identity]
  exact exactGain_le_sigmaGain

theorem ordinaryCredit_le_original_difference :
    (24859 : ℝ) / 250000000 ≤
      (W02Accepted.nodeGain -
        Gamma (matrixApply W02.rationalMatrix W04Accepted.enhanced) 0) / 4 :=
  ordinaryCredit_le_exact.trans
    (div_le_div_of_nonneg_right exactGain_le_original_difference (by norm_num))

theorem rationalGain_plus_exactGain :
    Gamma (matrixApply W02.rationalMatrix W04Accepted.enhanced) 0 + exactGain ≤
      W02Accepted.nodeGain := by
  change rationalGain + exactGain ≤ _
  rw [nodeGain_split]
  exact add_le_add le_rfl exactGain_le_sigmaGain

theorem rational_weighted_plus_credit :
    (∑ j : Fin 21, W03.paidWeights j *
      matrixApply W02.rationalMatrix W04Accepted.enhanced j) / 4 +
        ordinaryCredit ≤ W02Accepted.nodeGain / 4 := by
  have hb := W03.paid_weights_consumer rationalNodes_nonneg
  have hs := ordinaryCredit_le_original_difference
  change (∑ j : Fin 21, W03.paidWeights j * rationalNodes j) ≤ rationalGain at hb
  change ordinaryCredit ≤ (W02Accepted.nodeGain - rationalGain) / 4 at hs
  change (∑ j : Fin 21, W03.paidWeights j * rationalNodes j) / 4 +
    ordinaryCredit ≤ _
  linarith only [hb, hs]

theorem table_le_rationalNodes (j : Fin 21) :
    (W02.lowerVector j : ℝ) ≤ rationalNodes j := by
  have h : (W02.lowerVector j : ℝ) ≤ (W02.qOutput j : ℝ) := by
    exact_mod_cast W02.output_lower j
  rw [W02.qOutput_cast] at h
  exact h.trans (matrixApply_mono W02.rationalMatrix_nonneg
    W04Accepted.old_le_enhanced j)

theorem table_weighted_plus_credit :
    (∑ j : Fin 21, W03.paidWeights j * (W02.lowerVector j : ℝ)) / 4 +
      (24859 : ℝ) / 250000000 ≤ W02Accepted.nodeGain / 4 := by
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    mul_le_mul_of_nonneg_left (table_le_rationalNodes j) (W03.paidWeights_pos j).le)
  have hs := rational_weighted_plus_credit
  change (∑ j : Fin 21, W03.paidWeights j * rationalNodes j) / 4 +
    ordinaryCredit ≤ W02Accepted.nodeGain / 4 at hs
  change _ / 4 + ordinaryCredit ≤ _
  linarith only [hb, hs]

def rationalPaidCoefficient : ℝ :=
  W11Accepted.paidCoefficient W04Accepted.enhanced +
    (rationalGain - W01.lowGain W04Accepted.enhanced) / 4

theorem paidCoefficient_net_identity :
    W02Accepted.paidCoefficient - rationalPaidCoefficient = sigmaGain / 4 := by
  unfold W02Accepted.paidCoefficient rationalPaidCoefficient
  rw [nodeGain_split]
  ring

theorem paidCoefficient_credit :
    rationalPaidCoefficient + (24859 : ℝ) / 250000000 ≤
      W02Accepted.paidCoefficient := by
  have hs := ordinaryCredit_le_exact.trans
    (div_le_div_of_nonneg_right exactGain_le_sigmaGain (by norm_num : (0 : ℝ) ≤ 4))
  rw [← paidCoefficient_net_identity] at hs
  change (24859 : ℝ) / 250000000 ≤ _ at hs
  linarith only [hs]

end WuTarget.E03Sigma

#print WuTarget.E03Sigma.amplitudeLower
#print WuTarget.E03Sigma.weightedLower
#print WuTarget.E03Sigma.exactGain
#print WuTarget.E03Sigma.ordinaryCredit

set_option pp.fullNames true in
#check WuTarget.E03Sigma.amplitudeLower_le
set_option pp.fullNames true in
#check WuTarget.E03Sigma.weightLower_le
set_option pp.fullNames true in
#check WuTarget.E03Sigma.exactGain_eq
set_option pp.fullNames true in
#check WuTarget.E03Sigma.sigma_integral_identity
set_option pp.fullNames true in
#check WuTarget.E03Sigma.exactGain_le_original_difference
set_option pp.fullNames true in
#check WuTarget.E03Sigma.ordinaryCredit_le_original_difference
set_option pp.fullNames true in
#check WuTarget.E03Sigma.rationalGain_plus_exactGain
set_option pp.fullNames true in
#check WuTarget.E03Sigma.rational_weighted_plus_credit
set_option pp.fullNames true in
#check WuTarget.E03Sigma.table_weighted_plus_credit
set_option pp.fullNames true in
#check WuTarget.E03Sigma.paidCoefficient_net_identity
set_option pp.fullNames true in
#check WuTarget.E03Sigma.paidCoefficient_credit

#print axioms WuTarget.E03Sigma.amplitudeLower_le
#print axioms WuTarget.E03Sigma.weightLower_le
#print axioms WuTarget.E03Sigma.sigma_integral_identity
#print axioms WuTarget.E03Sigma.exactGain_le_original_difference
#print axioms WuTarget.E03Sigma.ordinaryCredit_le_original_difference
#print axioms WuTarget.E03Sigma.rationalGain_plus_exactGain
#print axioms WuTarget.E03Sigma.rational_weighted_plus_credit
#print axioms WuTarget.E03Sigma.table_weighted_plus_credit
#print axioms WuTarget.E03Sigma.paidCoefficient_net_identity
#print axioms WuTarget.E03Sigma.paidCoefficient_credit
