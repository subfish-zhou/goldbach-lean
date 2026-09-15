import LogP2

open Finset Real Wu2008DoubleSieve
open Wu2008DoubleSieve.TruncatedElevenSignedLower
open Wu2008DoubleSieve.TruncatedElevenClassicalCountLower
open Wu2008DoubleSieve.SeventhEighth U8MotherInsertion

namespace SixthSlotCore
noncomputable section

/-- The literal sixth carrier, not a lower bound for it. -/
def sixth (N : ℕ) : ℝ :=
  (truncatedSixthMass N ((N : ℝ)^truncatedSixthLowerAlpha)
    ((N : ℝ)^truncatedSixthLowerBeta) ((N : ℝ)^truncatedSixthLowerSigma)
    ((N : ℝ)^truncatedSixthLowerLambda) : ℝ)

/-- Remove the sixth carrier by an exact identity before any estimates. -/
def remainder (N : ℕ) : ℝ :=
  (truncatedSixthFixedExpression N : ℝ) - sixth N + ((small N).card : ℝ)

def positiveCoefficient : ℝ :=
  24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha)) +
  8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta)) +
  (8*BaseHGain.originalGain+fifthHGain) + fifthPairFlin

/-- This coefficient contains no sixth contribution. -/
def remainderCoefficient (δ : ℝ) : ℝ :=
  FullLogMother.psiCoefficient δ - truncatedSixthLowerF6lin -
    FullSourceLog.GammaLog6 + 8*oldSmallIntegral

theorem positive_without_sixth {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (positiveCoefficient-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
      3*(sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ) +
        (sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerBeta) : ℝ) +
        (fifthPairCount N : ℝ) := by
  have heps : 0 < ε/5 := by positivity
  obtain ⟨T1,hT1,h1⟩ := BaseLowerCounts.actual_count_lower
    BaseLowerCounts.original_exponents.1 BaseLowerCounts.original_exponents.2.1 heps
  obtain ⟨T2,_,h2⟩ := BaseHGain.original_F2_actual_count heps
  obtain ⟨T5,_,h5⟩ := fifthH_actual_improved_lower heps
  refine ⟨max T1 (max T2 T5),by omega,?_⟩
  intro N hN he
  have ha := h1 N (by omega) he
  have hb := h2 N (by omega) he
  have hc := h5 N (by omega) he
  change ((8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta))+
    8*BaseHGain.originalGain)-ε/5)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
    (sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerBeta) : ℝ) at hb
  unfold positiveCoefficient
  ring_nf at ha hb hc ⊢
  linarith only [ha,hb,hc]

/-- Actual signed co-core rebuilt from the three positive producers and all
negative producers. No sixth lower bound, old whole lower bound or count premise. -/
theorem remainder_actual_lower {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (remainderCoefficient δ-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤ remainder N := by
  have heps : 0 < ε/9 := by positivity
  obtain ⟨Tp,_,hp⟩ := positive_without_sixth heps
  obtain ⟨Tu,_,hu⟩ := HighSixLowHJoin.actual_pair_integral_psi_upper hδ hδhi heps
  obtain ⟨T9,hT9,h9⟩ := original_ninth_upper heps
  obtain ⟨Tw,_,hw⟩ := fixed_weighted_switching_epsilon heps
  obtain ⟨Tf,_,hf⟩ := TruncatedFourPhysical.original_sums_upper heps
  obtain ⟨T7,_,h7⟩ := seventh_eighth_physical_classical_upper heps
  obtain ⟨Tl,_,hl⟩ := large_integral_upper heps
  obtain ⟨Tq,_,hq⟩ := FourClassical.physical10_physical11_sum_classical_upper heps
  refine ⟨max Tp (max Tu (max T9 (max Tw (max Tf (max T7 (max Tl Tq)))))),by omega,?_⟩
  intro N hN he
  have hpN := hp N (by omega) he
  have huN := hu N (by omega) he
  have h9N := h9 N (by omega) he
  have hwN := hw N (by omega) he
  have hfN := hf N (by omega) he
  have h7N := (h7 N (by omega) he).1
  have hlN := hl N (by omega) he
  have hqN := hq N (by omega) he
  change _ ≤ _ * (wuSingularSeries N*N/log N^(2 : ℕ)) at huN
  have hz : SeventhEighth.z N = (N : ℝ)^truncatedSixthLowerAlpha := rfl
  have hw' : SeventhEighth.w N = (N : ℝ)^truncatedSixthLowerBeta := rfl
  have hu' : SeventhEighth.u N = (N : ℝ)^truncatedSixthLowerSigma := rfl
  have hv : SeventhEighth.v N = (N : ℝ)^(1/3 : ℝ) := rfl
  rw [hz, hw', hu', hv] at hwN
  rw [physicalT8_card_split, Nat.cast_add] at hwN
  push_cast at hwN
  unfold remainder sixth
  rw [fixed_expression_literal]
  unfold remainderCoefficient FullLogMother.psiCoefficient
  rw [J8_split]
  unfold positiveCoefficient at hpN
  ring_nf at hpN huN h9N hwN hfN h7N hlN hqN ⊢
  linarith only [hpN,huN,h9N,hwN,hfN,h7N,hlN,hqN]

/-- Consume the original finite mother, seven errors and overlap two, while
leaving the sixth slot and small debit literal. -/
theorem ordinary_remainder {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (remainderCoefficient δ-ε)*wuSingularSeries N*N/log N^(2 : ℕ) +
        sixth N - ((small N).card : ℝ) ≤
      4*((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
  obtain ⟨T1,hT1,hmain⟩ := remainder_actual_lower hδ hδhi (half_pos hε)
  obtain ⟨T2,_,herror⟩ := exceptional_power_error_paid (half_pos hε)
  obtain ⟨T3,_,hcutoff⟩ := fixed_cutoff_eventually_admissible
  refine ⟨max T1 (max T2 T3),by omega,?_⟩
  intro N hN he
  have hm := hmain N (by omega) he
  have hp := herror N (by omega)
  have hf := truncatedSixth_fixed_le_count (by omega) he (hcutoff N (by omega))
  unfold remainder at hm
  ring_nf at hm hp ⊢
  linarith only [hm,hp,hf]

end
end SixthSlotCore
