import SrcSixthGainAnalyticHighSlices
import SrcSixthGainAnalyticHighCount

noncomputable section
namespace WuSource.SrcSixthGain.Analytic
open Real Set MeasureTheory QuarterTrim DirectFiniteF6 Wu08G6High
open Wu2008DoubleSieve Wu08TerminalAlignment NodeExtension ActualNineFeedback
open scoped Classical BigOperators

def legalGain (w : Fin 21 → ℝ) : ℝ :=
  8*(∑ j : Fin 21, legalWeight j*w j)+HighConsumer.highGain

theorem high_loss_four (w : Fin 21 → ℝ) :
    highLoss w = 8*(highWeight 0*w 0+highWeight 1*w 1+
      highWeight 2*w 2+highWeight 3*w 3) := by
  rw [high_loss_expansion]
  have hf : (Finset.univ : Finset (Fin 21)).filter (fun j => j.val < 4) =
      {0,1,2,3} := by
    ext j
    fin_cases j <;> decide
  have hs : (∑ j ∈ (Finset.univ : Finset (Fin 21)).filter (fun j => j.val < 4),
      highWeight j*w j) = ∑ j : Fin 21, highWeight j*w j := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j _ hj
    have hn : 4 ≤ j.val := by
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,not_lt] at hj
      exact hj
    rw [later_high_weights_zero j hn,zero_mul]
  rw [← hs,hf]
  simp only [Finset.sum_insert,Finset.sum_singleton,Finset.mem_insert,
    Finset.mem_singleton,Fin.isValue,Fin.reduceEq,or_self,not_false_eq_true]
  ring

theorem legalGain_exact (w : Fin 21 → ℝ) :
    legalGain w = sourceNet w := by
  rw [legalGain,legal_full_weight_identity,sourceNet_exact]

theorem legalGain_original_weights (w : Fin 21 → ℝ) :
    legalGain w =
      8*(∑ j : Fin 21, g6Weight j*w j) -
      8*(highWeight 0*w 0+highWeight 1*w 1+
        highWeight 2*w 2+highWeight 3*w 3)+HighConsumer.highGain := by
  rw [legalGain_exact,sourceNet,high_loss_four]

theorem conservative_le_legalGain {w : Fin 21 → ℝ} (hw : ∀ j, 0 ≤ w j) :
    conservative w ≤ legalGain w := by
  rw [legalGain_exact]
  exact conservative_le_net hw

theorem legalGain_source_lower {delta : ℝ} {w : Fin 21 → ℝ}
    (hd : 0 < delta) (hdhi : delta ≤ 1/10) (hw0 : ∀ j, 0 ≤ w j)
    (hw : ∀ j, w j ≤ wuImprovementLimit false delta (rNode (j.val+1))) :
    legalGain w-HighConsumer.highGain ≤ paperG6 (wuImprovementLimit false delta) := by
  have hs := original_whole_source_lower hd hdhi hw
  have hh := high_nonneg hw0
  rw [legalGain_exact,sourceNet]
  linarith only [hs,hh]

theorem legal_actual_sixth {x : Fin 9 → ℝ} {w : Fin 21 → ℝ} {d0 eps : ℝ}
    (hx0 : ∀ i, 0 ≤ x i) (hw : ∀ j, w j ≤ transferred x j) (hd0 : 0 < d0)
    (hx : ∀ delta : ℝ, 0 < delta → delta ≤ d0 → ∀ i, x i ≤ actualNine delta i)
    (heps : 0 < eps) :
    ∃ d : ℝ, 0 < d ∧ d ≤ d0 ∧ d ≤ 1/100 ∧
      ∀ delta : ℝ, 0 < delta → delta < d →
        ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
          (sixthMain+legalGain w-eps)*U8CanonicalMother.M N ≤ SixthSlotCore.sixth N := by
  obtain ⟨d,hd,hdd0,hdhi,hbound⟩ := WuTarget.W01.actual_sixth hx0 hd0 hx heps
  refine ⟨d,hd,hdd0,hdhi,?_⟩
  intro delta hdelta hdelta'
  obtain ⟨T,hT,hcount⟩ := hbound delta hdelta hdelta'
  refine ⟨T,hT,?_⟩
  intro N hN he
  have hnet := net_le_consumed hw
  rw [← legalGain_exact] at hnet
  exact (mul_le_mul_of_nonneg_right
    (show sixthMain+legalGain w-eps ≤
      truncatedSixthLowerF6lin+WuTarget.W01.lowGain x+HighConsumer.highGain-eps by
      change truncatedSixthLowerF6lin+legalGain w-eps ≤ _
      linarith only [hnet])
    (HighSixPhase6.original_scale_positive (hT.trans hN)).le).trans (hcount N hN he)

theorem legal_sixth_lower {x : Fin 9 → ℝ} {w : Fin 21 → ℝ} {d0 : ℝ}
    (hx0 : ∀ i, 0 ≤ x i) (hw : ∀ j, w j ≤ transferred x j) (hd0 : 0 < d0)
    (hx : ∀ delta : ℝ, 0 < delta → delta ≤ d0 → ∀ i, x i ≤ actualNine delta i) :
    SixthSlotAssembly.SixthLower (legalGain w) := by
  intro eps heps
  obtain ⟨d,hd,_,_,hb⟩ := legal_actual_sixth hx0 hw hd0 hx heps
  obtain ⟨T,hT,hc⟩ := hb (d/2) (half_pos hd) (half_lt_self hd)
  refine ⟨T,hT,?_⟩
  intro N hN he
  simpa only [sixthMain,U8CanonicalMother.M,mul_div_assoc,mul_assoc] using hc N hN he

theorem legal_classical_sixth {x : Fin 9 → ℝ} {w : Fin 21 → ℝ} {d0 eps : ℝ}
    (hx0 : ∀ i, 0 ≤ x i) (hw : ∀ j, w j ≤ transferred x j) (hd0 : 0 < d0)
    (hx : ∀ delta : ℝ, 0 < delta → delta ≤ d0 → ∀ i, x i ≤ actualNine delta i)
    (heps : 0 < eps) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((381/100 : ℝ)+legalGain w-eps)*U8CanonicalMother.M N ≤ SixthSlotCore.sixth N := by
  obtain ⟨d,hd,_,_,hb⟩ := legal_actual_sixth hx0 hw hd0 hx heps
  obtain ⟨T,hT,hc⟩ := hb (d/2) (half_pos hd) (half_lt_self hd)
  refine ⟨T,hT,?_⟩
  intro N hN he
  exact (mul_le_mul_of_nonneg_right
    (by linarith only [WuTarget.E05SixthMajor.actual_sixth_target] :
      (381/100 : ℝ)+legalGain w-eps ≤ sixthMain+legalGain w-eps)
    (HighSixPhase6.original_scale_positive (hT.trans hN)).le).trans (hc N hN he)

theorem legal_ordinary_count {x : Fin 9 → ℝ} {w : Fin 21 → ℝ} {d0 eps dmax : ℝ}
    (hx0 : ∀ i, 0 ≤ x i) (hw : ∀ j, w j ≤ transferred x j) (hd0 : 0 < d0)
    (hx : ∀ delta : ℝ, 0 < delta → delta ≤ d0 → ∀ i, x i ≤ actualNine delta i)
    (heps : 0 < eps) (hdmax : 0 < dmax) :
    ∃ delta : ℝ, 0 < delta ∧ delta < dmax ∧ delta < d0 ∧ delta ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (sourceCoefficient (legalGain w)-eps)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨delta,hd,hdm,hd0',hdhi,T,hT,hcount⟩ :=
    WuTarget.W01.ordinary_P2 hx0 hd0 hx heps hdmax
  refine ⟨delta,hd,hdm,hd0',hdhi,T,hT,?_⟩
  intro N hN he
  have hnet := net_le_consumed hw
  rw [← legalGain_exact] at hnet
  have hc := coefficient_mono hnet
  rw [coefficient_exact] at hc
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_right hc eps)
    (HighSixPhase6.original_scale_positive (hT.trans hN)).le).trans (hcount N hN he)

#print axioms high_loss_four
#print axioms legalGain_original_weights
#print axioms legal_sixth_lower
#print axioms legal_classical_sixth
#print axioms legal_ordinary_count
end WuSource.SrcSixthGain.Analytic
