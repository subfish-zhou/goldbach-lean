import E04ContinuousSurplus
import W17AcceptedBudget

noncomputable section
namespace WuTarget.E04Continuous
open Wu2008DoubleSieve ActualNineFeedback NodeExtension W01Continuous

def certifiedAmount : ℝ := 8039587/22000000000000

def netCredit : ℝ :=
  (continuousGain W17Accepted.enhanced-W01.lowGain W17Accepted.enhanced)/4

def replacementCoefficient : ℝ := continuousCoefficient W17Accepted.enhanced

def replacementPaidCoefficient : ℝ := W17Accepted.paidCoefficient+certifiedAmount

theorem enhanced_zero_lower :
    (8039587/500000000 : ℝ) ≤ W17Accepted.enhanced 0 := by
  have h := (W04Accepted.old_le_enhanced 0).trans (W17Accepted.previous_le_enhanced 0)
  norm_num [Wu04Bypass.v8] at h
  exact h

theorem enhanced_surplus_linear :
    W17Accepted.enhanced 0/44000 ≤
      (continuousGain W17Accepted.enhanced-W01.lowGain W17Accepted.enhanced)/4 :=
  surplus_linear W17Accepted.enhanced_nonneg

theorem enhanced_surplus_rational :
    (8039587/22000000000000 : ℝ) ≤
      (continuousGain W17Accepted.enhanced-W01.lowGain W17Accepted.enhanced)/4 := by
  have h := enhanced_surplus_linear
  linarith only [h,enhanced_zero_lower]

theorem certifiedAmount_pos : 0 < certifiedAmount := by norm_num [certifiedAmount]

theorem netCredit_gt_display : (3/10000000 : ℝ) < netCredit := by
  have h := enhanced_surplus_rational
  change _ ≤ netCredit at h
  linarith only [h]

theorem certifiedAmount_le_netCredit : certifiedAmount ≤ netCredit :=
  enhanced_surplus_rational

theorem netCredit_pos : 0 < netCredit :=
  certifiedAmount_pos.trans_le certifiedAmount_le_netCredit

theorem replacement_identity :
    replacementCoefficient = W01.ordinaryCoefficient W17Accepted.enhanced+
      (continuousGain W17Accepted.enhanced-W01.lowGain W17Accepted.enhanced)/4 :=
  continuousCoefficient_eq _

theorem netCredit_identity :
    netCredit = replacementCoefficient-W01.ordinaryCoefficient W17Accepted.enhanced := by
  rw [replacement_identity]
  unfold netCredit
  ring

theorem replacement_gain_strict :
    W01.ordinaryCoefficient W17Accepted.enhanced+(3/10000000 : ℝ) <
      replacementCoefficient := by
  have h := netCredit_gt_display
  rw [netCredit_identity] at h
  linarith only [h]

theorem replacementPaid_net_identity :
    replacementPaidCoefficient-W17Accepted.paidCoefficient = certifiedAmount := by
  unfold replacementPaidCoefficient
  ring

theorem replacementPaid_lt_actual : replacementPaidCoefficient < replacementCoefficient := by
  have hp := W17Accepted.paid_lt_actual
  have hn := certifiedAmount_le_netCredit
  rw [netCredit_identity] at hn
  unfold replacementPaidCoefficient
  linarith only [hp,hn]

theorem enhanced_continuous_Hadm {ε : ℝ} (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1/100 ∧ ∀ δ : ℝ, 0 < δ → δ < d →
      continuousGain W17Accepted.enhanced-ε ≤ truncatedSixthLowerHadmdelta δ := by
  obtain ⟨d0,hd0,_,hx⟩ := W17Accepted.enhanced_actual
  obtain ⟨d,hd,_,hdhi,h⟩ :=
    continuousGain_Hadm_payment W17Accepted.enhanced_nonneg hd0 hx hε
  exact ⟨d,hd,hdhi,h⟩

theorem enhanced_continuous_ordinary_P2 {ε dmax : ℝ}
    (hε : 0 < ε) (hdmax : 0 < dmax) :
    ∃ δ : ℝ, 0 < δ ∧ δ < dmax ∧ δ ≤ 1/100 ∧
      (∀ i : Fin 9, W17Accepted.enhanced i ≤ actualNine δ i) ∧
      (∀ s ∈ Set.Icc (2:ℝ) (41/10),
        hContinuous W17Accepted.enhanced s ≤ wuImprovementLimit false δ s) ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (replacementCoefficient-ε)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨d,hd,_,hx⟩ := W17Accepted.enhanced_actual
  obtain ⟨δ,hδ,hmax,hδd,hdhi,T,hT,h⟩ :=
    continuous_ordinary_P2 W17Accepted.enhanced_nonneg hd hx hε hdmax
  have hnodes := hx δ hδ hδd.le
  exact ⟨δ,hδ,hmax,hdhi,hnodes,
    fun _ hs => hContinuous_le_actual hδ (by linarith) hnodes hs,T,hT,h⟩

theorem replacement_paid_ordinary_P2 {ε dmax : ℝ}
    (hε : 0 < ε) (hdmax : 0 < dmax) :
    ∃ δ : ℝ, 0 < δ ∧ δ < dmax ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (replacementPaidCoefficient-ε)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨δ,hd,hm,hs,_,_,T,hT,hc⟩ := enhanced_continuous_ordinary_P2 hε hdmax
  refine ⟨δ,hd,hm,hs,T,hT,?_⟩
  intro N hN he
  have hM : 0 ≤ U8CanonicalMother.M N :=
    (HighSixPhase6.original_scale_positive (hT.trans hN)).le
  exact (mul_le_mul_of_nonneg_right
    (sub_le_sub_right replacementPaid_lt_actual.le ε) hM).trans (hc N hN he)

theorem replacement_threshold_iff :
    (4491/5000 : ℝ) ≤ replacementPaidCoefficient ↔
      (4491/5000 : ℝ)-certifiedAmount ≤ W17Accepted.paidCoefficient := by
  unfold replacementPaidCoefficient
  constructor <;> intro h <;> linarith only [h]

theorem replacement_refined_target
    (h : (4491/5000 : ℝ)-certifiedAmount ≤ W17Accepted.paidCoefficient) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      RefinedExit.margin/2*U8CanonicalMother.M N ≤
        ((Wu2004MeanValue.refinedGood N (9469/5000)).card : ℝ) ∧
      ∃ p r q : ℕ, p.Prime ∧ (r=1 ∨ r.Prime) ∧ q.Prime ∧
        N=p+r*q ∧ (r : ℝ) ≤ (q : ℝ)^(4469/5000 : ℝ) := by
  apply RefinedExit.from_actual_count (replacement_threshold_iff.mpr h)
  intro ε hε
  obtain ⟨_,_,_,_,T,hT,hc⟩ := replacement_paid_ordinary_P2 hε (by norm_num : (0:ℝ) < 1)
  exact ⟨T,hT,hc⟩

end WuTarget.E04Continuous
