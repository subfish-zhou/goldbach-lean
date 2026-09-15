import Wu08FourMotherRelative

noncomputable section
namespace Wu08FourMother
open Wu2008DoubleSieve Real Finset PositiveCoreResume PositiveSecondPayment PositiveTwoPayment
open Wu2008DoubleSieve.TruncatedElevenSignedLower
open Wu2008DoubleSieve.TruncatedElevenClassicalCountLower
open Wu2008DoubleSieve.SeventhEighth U8MotherInsertion
open Wu08FirstPrimeFour.SmallBoundaryRecovery

/-- Literal original Q-count input; constructed by the recovered producer below. -/
def PairUpper (σ : ℝ) : Prop :=
  ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
    (TruncatedFourPhysical.Q10 N : ℝ)+(TruncatedFourPhysical.Q11 N : ℝ) ≤
      (originalIntegral false+originalIntegral true+σ)*U8CanonicalMother.M N

/-- Same signed mother, replacing the old original→physical→classical chain
by the actual original Q upper. Neither old intermediate estimate is subtracted. -/
theorem remainder_rebuilt {δ ε σ : ℝ} (pair : PairUpper σ)
    (hδ : 0 < δ) (hd : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (SixthSlotCore.remainderCoefficient δ+increment secondGain fifthGain+
        restoredDebit-σ-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
      SixthSlotCore.remainder N := by
  have heps : 0 < ε/7 := by positivity
  obtain ⟨Tp,_,hp⟩ := positive_rebuilt two_counts heps
  obtain ⟨Tu,_,hu⟩ := HighSixLowHJoin.actual_pair_integral_psi_upper hδ hd heps
  obtain ⟨T9,hT9,h9⟩ := original_ninth_upper heps
  obtain ⟨Tw,_,hw⟩ := fixed_weighted_switching_epsilon heps
  obtain ⟨T7,_,h7⟩ := seventh_eighth_physical_classical_upper heps
  obtain ⟨Tl,_,hl⟩ := large_integral_upper heps
  obtain ⟨Tq,_,hq⟩ := pair
  refine ⟨max Tp (max Tu (max T9 (max Tw (max T7 (max Tl Tq))))),by omega,?_⟩
  intro N hN he
  have hpN := hp N (by omega) he
  have huN := hu N (by omega) he
  have h9N := h9 N (by omega) he
  have hwN := hw N (by omega) he
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
  unfold TruncatedFourPhysical.Q10 TruncatedFourPhysical.Q11
    TruncatedFourPhysical.T10 TruncatedFourPhysical.T11 fourModulusProduct U8CanonicalMother.M at hqN
  unfold SixthSlotCore.remainder SixthSlotCore.sixth
  rw [fixed_expression_literal]
  unfold SixthSlotCore.remainderCoefficient FullLogMother.psiCoefficient
  rw [J8_split,restoredDebit_exact]
  unfold SixthSlotCore.positiveCoefficient at hpN
  ring_nf at hpN huN h9N hwN h7N hlN hqN ⊢
  linarith only [hpN,huN,h9N,hwN,h7N,hlN,hqN]

/-- Original finite mother and its actual power errors, no old P2 lower bound. -/
theorem ordinary_rebuilt {δ ε σ : ℝ} (pair : PairUpper σ)
    (hδ : 0 < δ) (hd : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (SixthSlotCore.remainderCoefficient δ+increment secondGain fifthGain+
        restoredDebit-σ-ε)*wuSingularSeries N*N/log N^(2 : ℕ)+
        SixthSlotCore.sixth N-((small N).card : ℝ) ≤
      4*((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
  obtain ⟨Ta,ha,hA⟩ := remainder_rebuilt pair hδ hd (half_pos hε)
  obtain ⟨Tb,_,hB⟩ := exceptional_power_error_paid (half_pos hε)
  obtain ⟨Tc,_,hC⟩ := fixed_cutoff_eventually_admissible
  refine ⟨max Ta (max Tb Tc),by omega,fun N hN he => ?_⟩
  have h1 := hA N (by omega) he
  have h2 := hB N (by omega)
  have h3 := truncatedSixth_fixed_le_count (by omega) he (hC N (by omega))
  unfold SixthSlotCore.remainder at h1
  ring_nf at h1 h2 ⊢
  linarith only [h1,h2,h3]

/-- Restored negative coefficients, all actual positive/small/sixth payments once. -/
theorem signed_count {δ ε σ : ℝ} (pair : PairUpper σ)
    (hδ : 0 < δ) (hd : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (FullLogMother.psiCoefficient δ+FeedbackLimit.Cinf-FullSourceLog.GammaLog6+
        increment secondGain fifthGain+restoredDebit+8*U8CanonicalMother.L-
        8*U8CanonicalMother.I-σ-ε)*U8CanonicalMother.M N ≤
      4*((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
  have hε3 : 0 < ε/3 := by positivity
  obtain ⟨Tr,hTr,hr⟩ := ordinary_rebuilt pair hδ hd hε3
  obtain ⟨T6,_,h6⟩ := FeedbackLimit.supplied_sixth (ε/3) hε3
  obtain ⟨Ts,hs⟩ := OriginalU8.Weighted.physicalSmall_original_integral (ε/3) hε3
  refine ⟨max Tr (max T6 Ts),by omega,fun N hN he => ?_⟩
  have hrN := hr N (by omega) he
  have h6N := h6 N (by omega) he
  have hsN := hs N (by omega) he
  have hnorm := U8CanonicalMother.scale_eq_liu (show 0 < N by omega)
  rw [← U8CanonicalMother.small_eq_physicalSmall] at hsN
  have hsM : ((U8MotherInsertion.small N).card : ℝ) ≤
      (8*U8CanonicalMother.I+ε/3)*U8CanonicalMother.M N := by
    rw [hnorm]
    convert hsN using 1
    ring
  unfold SixthSlotCore.remainderCoefficient at hrN
  rw [← U8CanonicalMother.L_eq_oldSmallIntegral] at hrN
  dsimp [U8CanonicalMother.M] at hsM ⊢
  ring_nf at hrN h6N hsM ⊢
  linarith only [hrN,h6N,hsM]

end Wu08FourMother
