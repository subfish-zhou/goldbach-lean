import FullSourceLogGain
import FullAdmissibleCount

namespace Wu2008DoubleSieve.FullLogPositive
open Real
open scoped Classical

/-- Rebuild all four positive terms from their actual producers. F1 has weight three;
F2, F5, F6 have weight one. Their internal deltas need not agree. -/
theorem first_second_fifth_sixth_actual_lower {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha)) +
        8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta)) +
        (8*BaseHGain.originalGain+fifthHGain) + fifthPairFlin +
        truncatedSixthLowerF6lin + FullSourceLog.GammaLog6-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
      3*(sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ) +
        (sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerBeta) : ℝ) +
        (fifthPairCount N : ℝ) +
        (truncatedSixthMass N ((N : ℝ)^truncatedSixthLowerAlpha)
          ((N : ℝ)^truncatedSixthLowerBeta) ((N : ℝ)^truncatedSixthLowerSigma)
          ((N : ℝ)^truncatedSixthLowerLambda) : ℝ) := by
  have heps : 0 < ε/6 := by positivity
  obtain ⟨T1,hT1,h1⟩ := BaseLowerCounts.actual_count_lower
    BaseLowerCounts.original_exponents.1 BaseLowerCounts.original_exponents.2.1 heps
  obtain ⟨T2,_,h2⟩ := BaseHGain.original_F2_actual_count heps
  obtain ⟨T5,_,h5⟩ := fifthH_actual_improved_lower heps
  obtain ⟨T6,_,h6⟩ := FullSourceLog.actual_count_lower heps
  refine ⟨max T1 (max T2 (max T5 T6)),hT1.trans (le_max_left _ _),?_⟩
  intro N hN he
  have hN1 := (le_max_left T1 (max T2 (max T5 T6))).trans hN
  have hN256 := (le_max_right T1 (max T2 (max T5 T6))).trans hN
  have hN2 := (le_max_left T2 (max T5 T6)).trans hN256
  have hN56 := (le_max_right T2 (max T5 T6)).trans hN256
  have hN5 := (le_max_left T5 T6).trans hN56
  have hN6 := (le_max_right T5 T6).trans hN56
  have ha := h1 N hN1 he
  have hb := h2 N hN2 he
  have hc := h5 N hN5 he
  have hd := h6 N hN6 he
  change ((8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta))+
    8*BaseHGain.originalGain)-ε/6)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
    (sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerBeta) : ℝ) at hb
  ring_nf at ha hb hc hd ⊢
  linarith only [ha,hb,hc,hd]

end Wu2008DoubleSieve.FullLogPositive

/-! Fixed-delta reassembly from the actual positive/negative components.
No old classical lower bound is incremented independently by a local gain. -/
namespace Wu2008DoubleSieve.FullLogMother
open Finset Real SingleUpperCounts SingleUpperClassicalLimit
open TruncatedElevenSignedLower SingleUpperHIntegral
open scoped Classical

theorem first_six_actual_lower {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha)) +
        8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta)) + (8*BaseHGain.originalGain+fifthHGain) + fifthPairFlin +
        truncatedSixthLowerF6lin + FullSourceLog.GammaLog6 -
        Gdelta δ (1/3) - Gdelta δ truncatedSixthLowerSigma + gainH34 δ +
        4*firstFunctionalGainPsi δ HighSix.s HighSix.S*HighSix.primeIntegral δ - ε)*
          wuSingularSeries N*N/log N^(2 : ℕ) ≤
      3*(sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ) +
        (sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerBeta) : ℝ) +
        (fifthPairCount N : ℝ) +
        (truncatedSixthMass N ((N : ℝ)^truncatedSixthLowerAlpha)
          ((N : ℝ)^truncatedSixthLowerBeta) ((N : ℝ)^truncatedSixthLowerSigma)
          ((N : ℝ)^truncatedSixthLowerLambda) : ℝ) -
        (U N (1/3) : ℝ) - (U N truncatedSixthLowerSigma : ℝ) := by
  obtain ⟨TP, hTP, hP⟩ := FullLogPositive.first_second_fifth_sixth_actual_lower (half_pos hε)
  obtain ⟨TS, _hTS, hS⟩ :=
    HighSixLowHJoin.actual_pair_integral_psi_upper hδ hδhi (half_pos hε)
  refine ⟨max TP TS, hTP.trans (le_max_left _ _), ?_⟩
  intro N hN he
  have hp := hP N ((le_max_left _ _).trans hN) he
  have hs := hS N ((le_max_right _ _).trans hN) he
  unfold truncatedSixthMassScale at hs
  calc
    _ = (24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha)) +
        8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta)) + (8*BaseHGain.originalGain+fifthHGain) + fifthPairFlin +
        truncatedSixthLowerF6lin + FullSourceLog.GammaLog6 - ε/2)*
          wuSingularSeries N*N/log N^(2 : ℕ) -
        (Gdelta δ (1/3) + Gdelta δ truncatedSixthLowerSigma - gainH34 δ -
        4*firstFunctionalGainPsi δ HighSix.s HighSix.S*HighSix.primeIntegral δ + ε/2)*
          (wuSingularSeries N*N/log N^(2 : ℕ)) := by ring
    _ ≤ _ := by linarith only [hp, hs]


theorem first_six_sub_ninth_actual_lower {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha)) +
        8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta)) + (8*BaseHGain.originalGain+fifthHGain) + fifthPairFlin +
        truncatedSixthLowerF6lin + FullSourceLog.GammaLog6 -
        Gdelta δ (1/3) - Gdelta δ truncatedSixthLowerSigma + gainH34 δ +
        4*firstFunctionalGainPsi δ HighSix.s HighSix.S*HighSix.primeIntegral δ - 8*J9 - ε)*
          wuSingularSeries N*N/log N^(2 : ℕ) ≤
      3*(sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ) +
        (sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerBeta) : ℝ) +
        (fifthPairCount N : ℝ) +
        (truncatedSixthMass N ((N : ℝ)^truncatedSixthLowerAlpha)
          ((N : ℝ)^truncatedSixthLowerBeta) ((N : ℝ)^truncatedSixthLowerSigma)
          ((N : ℝ)^truncatedSixthLowerLambda) : ℝ) -
        (U N (1/3) : ℝ) - (U N truncatedSixthLowerSigma : ℝ) -
        (variableS3Main N ((N : ℝ)^truncatedSixthLowerBeta)
          ((N : ℝ)^truncatedSixthLowerSigma) : ℝ) := by
  obtain ⟨T6, _hT6, h6⟩ := first_six_actual_lower hδ hδhi (half_pos hε)
  obtain ⟨T9, hT9, h9⟩ := original_ninth_upper (half_pos hε)
  refine ⟨max T6 T9, hT9.trans (le_max_right _ _), ?_⟩
  intro N hN he
  have hs := h6 N ((le_max_left _ _).trans hN) he
  have hn := h9 N ((le_max_right _ _).trans hN) he
  calc
    _ = (24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha)) +
        8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta)) + (8*BaseHGain.originalGain+fifthHGain) + fifthPairFlin +
        truncatedSixthLowerF6lin + FullSourceLog.GammaLog6 -
        Gdelta δ (1/3) - Gdelta δ truncatedSixthLowerSigma + gainH34 δ +
        4*firstFunctionalGainPsi δ HighSix.s HighSix.S*HighSix.primeIntegral δ - ε/2)*
          wuSingularSeries N*N/log N^(2 : ℕ) -
        (8*J9 + ε/2)*wuSingularSeries N*N/log N^(2 : ℕ) := by ring
    _ ≤ _ := sub_le_sub hs hn


theorem truncated_fixed_actual_lower {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      let z := (N : ℝ)^truncatedSixthLowerAlpha
      let w := (N : ℝ)^truncatedSixthLowerBeta
      let u := (N : ℝ)^truncatedSixthLowerSigma
      let v := (N : ℝ)^(1/3 : ℝ)
      let V := (N : ℝ)^truncatedSixthLowerLambda
      (24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha)) +
        8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta)) + (8*BaseHGain.originalGain+fifthHGain) + fifthPairFlin +
        truncatedSixthLowerF6lin + FullSourceLog.GammaLog6 -
        Gdelta δ (1/3) - Gdelta δ truncatedSixthLowerSigma + gainH34 δ +
        4*firstFunctionalGainPsi δ HighSix.s HighSix.S*HighSix.primeIntegral δ - 8*J9 - ε)*
          wuSingularSeries N*N/log N^(2 : ℕ) -
        2*(lowerS2 N w u : ℝ) - (lowerS3 N z v : ℝ) -
        ((∑ t ∈ s3DistinctQuadruples N (orderedTriples (primeWindow N z w)),
          sieveCount N (t.1*t.2.1*t.2.2.1*t.2.2.2) N (t.2.1 : ℝ)) : ℤ) -
        ((∑ t ∈ s3Upsilon11Range N z w V,
          sieveCount N (t.1*t.2.1*t.2.2.1*t.2.2.2) N (t.2.1 : ℝ)) : ℤ) ≤
      (truncatedSixthFixedExpression N : ℝ) := by
  obtain ⟨T, hT, h⟩ := first_six_sub_ninth_actual_lower hδ hδhi hε
  refine ⟨T, hT, ?_⟩
  intro N hN he
  dsimp only
  rw [fixed_expression_literal]
  exact sub_le_sub_right (sub_le_sub_right (sub_le_sub_right
    (sub_le_sub_right (h N hN he) _) _) _) _


theorem truncated_fixed_physical_lower {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      let z := (N : ℝ)^truncatedSixthLowerAlpha
      let w := (N : ℝ)^truncatedSixthLowerBeta
      let V := (N : ℝ)^truncatedSixthLowerLambda
      (24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha)) +
        8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta)) + (8*BaseHGain.originalGain+fifthHGain) + fifthPairFlin +
        truncatedSixthLowerF6lin + FullSourceLog.GammaLog6 -
        Gdelta δ (1/3) - Gdelta δ truncatedSixthLowerSigma + gainH34 δ +
        4*firstFunctionalGainPsi δ HighSix.s HighSix.S*HighSix.primeIntegral δ - 8*J9 - ε)*
          wuSingularSeries N*N/log N^(2 : ℕ) -
        2*((SeventhEighth.physicalT7 N).card : ℝ) -
        ((SeventhEighth.physicalT8 N).card : ℝ) -
        ((∑ t ∈ s3DistinctQuadruples N (orderedTriples (primeWindow N z w)),
          sieveCount N (t.1*t.2.1*t.2.2.1*t.2.2.2) N (t.2.1 : ℝ)) : ℤ) -
        ((∑ t ∈ s3Upsilon11Range N z w V,
          sieveCount N (t.1*t.2.1*t.2.2.1*t.2.2.2) N (t.2.1 : ℝ)) : ℤ) ≤
      (truncatedSixthFixedExpression N : ℝ) := by
  obtain ⟨T1, hT1, h1⟩ :=
    truncated_fixed_actual_lower hδ hδhi (half_pos hε)
  obtain ⟨T2, _, h2⟩ :=
    SeventhEighth.fixed_weighted_switching_epsilon (half_pos hε)
  refine ⟨max T1 T2, hT1.trans (le_max_left _ _), ?_⟩
  intro N hN he
  dsimp only
  have ha := h1 N ((le_max_left T1 T2).trans hN) he
  dsimp only at ha
  have hb := h2 N ((le_max_right T1 T2).trans hN) he
  have hz : SeventhEighth.z N = (N : ℝ)^truncatedSixthLowerAlpha := rfl
  have hw : SeventhEighth.w N = (N : ℝ)^truncatedSixthLowerBeta := rfl
  have hu : SeventhEighth.u N = (N : ℝ)^truncatedSixthLowerSigma := rfl
  have hv : SeventhEighth.v N = (N : ℝ)^(1/3 : ℝ) := rfl
  rw [hz, hw, hu, hv] at hb
  push_cast at hb
  ring_nf at ha hb ⊢
  linarith only [ha, hb]


theorem truncated_fixed_all_physical_lower {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha)) +
        8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta)) + (8*BaseHGain.originalGain+fifthHGain) + fifthPairFlin +
        truncatedSixthLowerF6lin + FullSourceLog.GammaLog6 -
        Gdelta δ (1/3) - Gdelta δ truncatedSixthLowerSigma + gainH34 δ +
        4*firstFunctionalGainPsi δ HighSix.s HighSix.S*HighSix.primeIntegral δ - 8*J9 - ε)*
          wuSingularSeries N*N/log N^(2 : ℕ) -
        2*((SeventhEighth.physicalT7 N).card : ℝ) -
        ((SeventhEighth.physicalT8 N).card : ℝ) -
        ((TruncatedFourPhysical.Physical10 N).card : ℝ) -
        ((TruncatedFourPhysical.Physical11 N).card : ℝ) ≤
      (truncatedSixthFixedExpression N : ℝ) := by
  obtain ⟨T1, hT1, h1⟩ :=
    truncated_fixed_physical_lower hδ hδhi (half_pos hε)
  obtain ⟨T2, _, h2⟩ := TruncatedFourPhysical.original_sums_upper (half_pos hε)
  refine ⟨max T1 T2, hT1.trans (le_max_left _ _), ?_⟩
  intro N hN he
  have ha := h1 N ((le_max_left T1 T2).trans hN) he
  have hb := h2 N ((le_max_right T1 T2).trans hN) he
  dsimp only at ha hb
  ring_nf at ha hb ⊢
  linarith only [ha, hb]
end Wu2008DoubleSieve.FullLogMother

namespace Wu2008DoubleSieve.FullLogMother
open Real SingleUpperClassicalLimit SingleUpperHIntegral
open TruncatedElevenClassicalCountLower

/-- Fixed delta: the low H integral and actual U3 local j6 integral are joined. -/
noncomputable def psiCoefficient (δ : ℝ) : ℝ :=
  24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha)) +
    8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta)) + (8*BaseHGain.originalGain+fifthHGain) + fifthPairFlin +
    truncatedSixthLowerF6lin + FullSourceLog.GammaLog6 -
    Gdelta δ (1/3) - Gdelta δ truncatedSixthLowerSigma + gainH34 δ +
    4*firstFunctionalGainPsi δ HighSix.s HighSix.S*HighSix.primeIntegral δ - 8*J9 -
    16*SeventhEighth.J7 - 8*SeventhEighth.J8 -
    8*FourRoughClosedMass.I10 - 8*FourRoughClosedMass.I11
end Wu2008DoubleSieve.FullLogMother

namespace Wu2008DoubleSieve.FullLogCount
open Real SingleUpperHIntegral HighSixDeltaLimit
noncomputable section

/-- The old signed coefficient is identified algebraically, not used as a count lower. -/
theorem fixed_coefficient_identity (δ : ℝ) :
    FullLogMother.psiCoefficient δ = HighSixLowHMother.psiCoefficient δ +
      (8*BaseHGain.originalGain+fifthHGain+(FullSourceLog.GammaLog6-47/481250)) := by
  unfold FullLogMother.psiCoefficient HighSixLowHMother.psiCoefficient
  ring

theorem fixed_same_mother_identity (δ : ℝ) :
    FullLogMother.psiCoefficient δ = HighSixPsiMother.psiCoefficient δ + gainH34 δ +
      (8*BaseHGain.originalGain+fifthHGain+(FullSourceLog.GammaLog6-47/481250)) := by
  rw [fixed_coefficient_identity, ParentPhase9HalfWeightCount.same_mother_identity]
end
end Wu2008DoubleSieve.FullLogCount
