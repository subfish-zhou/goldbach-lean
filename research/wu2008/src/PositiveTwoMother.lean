import PositiveSecondCount
import PositiveCoreP2

namespace PositiveTwoPayment
open Wu2008DoubleSieve Real Finset PositiveCoreResume PositiveSecondPayment
open Wu2008DoubleSieve.TruncatedElevenSignedLower
open Wu2008DoubleSieve.TruncatedElevenClassicalCountLower
open Wu2008DoubleSieve.SeventhEighth U8MotherInsertion
noncomputable section

/-- Two actual positive-count producers at the unchanged original cutoffs.
This internal contract is instantiated below; no conditional endpoint is left unpaid. -/
structure PositiveCounts (g2 g5 : ℝ) : Prop where
  second : ∀ ε : ℝ, 0 < ε →
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta))+8*g2)-ε)*
        wuSingularSeries N*N/log N^(2 : ℕ) ≤
          (sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerBeta) : ℝ)
  fifth : ∀ ε : ℝ, 0 < ε →
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (fifthPairFlin+g5-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        (fifthPairCount N : ℝ)

/-- Both old payments are removed exactly once, before any signed assembly. -/
def increment (g2 g5 : ℝ) : ℝ :=
  8*(g2-BaseHGain.originalGain)+(g5-fifthHGain)

/-- Concrete construction from the newly rebuilt F2 count and the retained full F5 count. -/
theorem two_counts : PositiveCounts secondGain fifthGain := by
  constructor
  · intro ε hε
    exact second_actual_count hε
  · intro ε hε
    exact fifth_count hε

/-- Rebuild positives from their actual individual counts, never add two P2 lower bounds. -/
theorem positive_rebuilt {g2 g5 : ℝ} (counts : PositiveCounts g2 g5) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (SixthSlotCore.positiveCoefficient+increment g2 g5-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        3*(sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ) +
          (sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerBeta) : ℝ) +
          (fifthPairCount N : ℝ) := by
  have hε5 : 0 < ε/5 := by positivity
  obtain ⟨Ta,ha,hA⟩ := BaseLowerCounts.actual_count_lower
    BaseLowerCounts.original_exponents.1 BaseLowerCounts.original_exponents.2.1 hε5
  obtain ⟨Tb,_,hB⟩ := counts.second (ε/5) hε5
  obtain ⟨Tc,_,hC⟩ := counts.fifth (ε/5) hε5
  refine ⟨max Ta (max Tb Tc),by omega,fun N hN he => ?_⟩
  have h1 := hA N (by omega) he
  have h2 := hB N (by omega) he
  have h5 := hC N (by omega) he
  change ((8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta))+
    8*g2)-ε/5)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
    (sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerBeta) : ℝ) at h2
  unfold SixthSlotCore.positiveCoefficient increment
  ring_nf at h1 h2 h5 ⊢
  linarith only [h1,h2,h5]

/-- The actual negative producers are each consumed once, with the original weights. -/
theorem remainder_rebuilt {g2 g5 : ℝ} (counts : PositiveCounts g2 g5) {δ ε : ℝ}
    (hδ : 0 < δ) (hd : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (SixthSlotCore.remainderCoefficient δ+increment g2 g5-ε)*
        wuSingularSeries N*N/log N^(2 : ℕ) ≤ SixthSlotCore.remainder N := by
  have heps : 0 < ε/9 := by positivity
  obtain ⟨Tp,_,hp⟩ := positive_rebuilt counts heps
  obtain ⟨Tu,_,hu⟩ := HighSixLowHJoin.actual_pair_integral_psi_upper hδ hd heps
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
  rw [show SeventhEighth.z N = (N : ℝ)^truncatedSixthLowerAlpha from rfl,
    show SeventhEighth.w N = (N : ℝ)^truncatedSixthLowerBeta from rfl,
    show SeventhEighth.u N = (N : ℝ)^truncatedSixthLowerSigma from rfl,
    show SeventhEighth.v N = (N : ℝ)^(1/3 : ℝ) from rfl] at hwN
  rw [physicalT8_card_split, Nat.cast_add] at hwN
  push_cast at hwN
  unfold SixthSlotCore.remainder SixthSlotCore.sixth
  rw [fixed_expression_literal]
  unfold SixthSlotCore.remainderCoefficient FullLogMother.psiCoefficient
  rw [J8_split]
  unfold SixthSlotCore.positiveCoefficient at hpN
  ring_nf at hpN huN h9N hwN hfN h7N hlN hqN ⊢
  linarith only [hpN,huN,h9N,hwN,hfN,h7N,hlN,hqN]

/-- Original finite mother and power errors, leaving sixth and small debit literal. -/
theorem ordinary_rebuilt {g2 g5 : ℝ} (counts : PositiveCounts g2 g5) {δ ε : ℝ}
    (hδ : 0 < δ) (hd : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (SixthSlotCore.remainderCoefficient δ+increment g2 g5-ε)*
        wuSingularSeries N*N/log N^(2 : ℕ) + SixthSlotCore.sixth N -
        ((small N).card : ℝ) ≤
      4*((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
  obtain ⟨Ta,ha,hA⟩ := remainder_rebuilt counts hδ hd (half_pos hε)
  obtain ⟨Tb,_,hB⟩ := exceptional_power_error_paid (half_pos hε)
  obtain ⟨Tc,_,hC⟩ := fixed_cutoff_eventually_admissible
  refine ⟨max Ta (max Tb Tc),by omega,fun N hN he => ?_⟩
  have h1 := hA N (by omega) he
  have h2 := hB N (by omega)
  have h3 := truncatedSixth_fixed_le_count (by omega) he (hC N (by omega))
  unfold SixthSlotCore.remainder at h1
  ring_nf at h1 h2 ⊢
  linarith only [h1,h2,h3]

end
end PositiveTwoPayment
