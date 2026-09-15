import WSrcSingleCount

noncomputable section
namespace WuSource.SrcSingle
open Wu2008DoubleSieve Wu08TerminalAlignment Real Set MeasureTheory Finset
open scoped Interval BigOperators

def secondNodeGain (h22 H12 : ℝ) : ℝ := 8 * (h22 + H12 * log (40 / 39))
def originalThirdLedger (δ : ℝ) : ℝ := fourthSource δ + psiSevenSource δ
def originalSingleLedger (δ : ℝ) : ℝ :=
  secondSource δ + originalThirdLedger δ + fourthSource δ

theorem second_constant_integrable (H12 : ℝ) :
    IntervalIntegrable (fun t : ℝ => H12 / t) volume (78 / 25) (16 / 5) := by
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_const.div continuousOn_id
  intro t ht
  rw [uIcc_of_le (by norm_num : (78 / 25 : ℝ) ≤ 16 / 5)] at ht
  change t ≠ 0
  linarith [ht.1]

theorem second_constant_integral (H12 : ℝ) :
    (∫ t in (78 / 25 : ℝ)..(16 / 5), H12 / t) = H12 * log (40 / 39) := by
  have hderiv : ∀ t ∈ uIcc (78 / 25 : ℝ) (16 / 5),
      HasDerivAt (fun x : ℝ => H12 * log x) (H12 / t) t := by
    intro t ht
    rw [uIcc_of_le (by norm_num : (78 / 25 : ℝ) ≤ 16 / 5)] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    simpa only [div_eq_mul_inv] using (hasDerivAt_log ht0).const_mul H12
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (second_constant_integrable H12)]
  rw [show (40 / 39 : ℝ) = (16 / 5) / (78 / 25) by norm_num,
    log_div (by norm_num : (16 / 5 : ℝ) ≠ 0) (by norm_num : (78 / 25 : ℝ) ≠ 0)]
  ring

theorem second_node_profile {δ H12 : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100)
    (hH : H12 ≤ wuImprovementLimit true δ (sourceNode 12)) :
    ∀ t ∈ Set.Icc (78 / 25 : ℝ) (16 / 5), H12 ≤ wuImprovementLimit true δ t := by
  intro t ht
  apply hH.trans
  apply wuImprovementLimit_upper_antitone hd (by linarith : δ ≤ 1 / 10)
  · exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · norm_num [sourceNode]
  · norm_num [sourceNode]
    exact ht.2

theorem second_node_gain_to_source {δ h22 H12 : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100)
    (hh22 : h22 ≤ wuImprovementLimit false δ (sourceNode 22))
    (hH12 : H12 ≤ wuImprovementLimit true δ (sourceNode 12)) :
    secondNodeGain h22 H12 ≤ secondSource δ := by
  have h22 : h22 ≤ wuImprovementLimit false δ (21 / 5) := by
    norm_num [sourceNode] at hh22 ⊢
    exact hh22
  have h := second_transfer_to_source hd hh h22 (second_constant_integrable H12)
    (second_node_profile hd hh hH12)
  simpa only [secondTransfer, second_constant_integral, secondNodeGain] using h

theorem original_ledger_two_copies (δ : ℝ) :
    originalSingleLedger δ = secondSource δ + 2 * fourthSource δ + psiSevenSource δ := by
  unfold originalSingleLedger originalThirdLedger
  ring

theorem original_node_inputs_to_ledger {δ h22 H12 : ℝ} {H : ℕ → ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100) (hr : δ ≤ sevenRadius)
    (hh22 : h22 ≤ wuImprovementLimit false δ (sourceNode 22))
    (hH12 : H12 ≤ wuImprovementLimit true δ (sourceNode 12))
    (hH0 : ∀ i ∈ Finset.Icc 14 29, 0 ≤ H i)
    (hH : ∀ i ∈ Finset.Icc 14 29, H i ≤ wuImprovementLimit true δ (sourceNode i)) :
    secondNodeGain h22 H12 + 2 * fourthNodeSum H + psiSevenPaid ≤ originalSingleLedger δ := by
  rw [original_ledger_two_copies]
  linarith only [second_node_gain_to_source hd hh hh22 hH12,
    fourth_nodes_to_source hd hh hH0 hH, seven_weighted_forcing_paid hd hr]

theorem original_log_Hh_input_to_count {ρ h22 H12 ε : ℝ} {H : ℕ → ℝ}
    (hρ : 0 < ρ) (hH0 : ∀ i ∈ Finset.Icc 14 29, 0 ≤ H i)
    (hsource : ∀ δ : ℝ, 0 < δ → δ ≤ ρ → δ ≤ 1 / 100 →
      h22 ≤ wuImprovementLimit false δ (sourceNode 22) ∧
      H12 ≤ wuImprovementLimit true δ (sourceNode 12) ∧
      ∀ i ∈ Finset.Icc 14 29, H i ≤ wuImprovementLimit true δ (sourceNode i))
    (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (secondMain - thirdMain - fourthMain +
        secondNodeGain h22 H12 + 2 * fourthNodeSum H - ε) *
          truncatedSixthMassScale N ≤ signedSingleCount N := by
  have hgain : ∀ δ : ℝ, 0 < δ → δ ≤ ρ → δ ≤ 1 / 100 →
      secondNodeGain h22 H12 + 2 * fourthNodeSum H ≤ lowSingleSource δ := by
    intro δ hd hdρ hdhi
    have hs := hsource δ hd hdρ hdhi
    unfold lowSingleSource
    linarith only [second_node_gain_to_source hd hdhi hs.1 hs.2.1,
      fourth_nodes_to_source hd hdhi hH0 hs.2.2]
  simpa only [add_assoc] using low_source_original_classical_count hρ hgain heps

#check @original_node_inputs_to_ledger
#check @original_log_Hh_input_to_count
#print axioms second_node_gain_to_source
#print axioms original_node_inputs_to_ledger
#print axioms original_log_Hh_input_to_count
end WuSource.SrcSingle
