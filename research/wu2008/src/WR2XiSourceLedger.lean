import WR2XiSourceBlock
import Wu08FourMotherCounts

noncomputable section
namespace WuPaper.R2Xi.SourceLedger
open Wu2008DoubleSieve Real Finset
open Wu2008DoubleSieve.TruncatedElevenSignedLower
open Wu2008DoubleSieve.SeventhEighth U8MotherInsertion
open Wu08FirstPrimeFour.SmallBoundaryRecovery

def remainderCoefficient : ℝ := SourceBlock.coefficient-8*J9-
  16*SeventhEighth.J7-8*SeventhEighth.J8+8*oldSmallIntegral-
  originalIntegral false-originalIntegral true

theorem remainder_count {ε σ : ℝ} (pair : Wu08FourMother.PairUpper σ)
    (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (remainderCoefficient-σ-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
      SixthSlotCore.remainder N := by
  have heps : 0 < ε/6 := by positivity
  obtain ⟨Tp,_,hp⟩ := SourceBlock.actual_count heps
  obtain ⟨T9,hT9,h9⟩ := original_ninth_upper heps
  obtain ⟨Tw,_,hw⟩ := fixed_weighted_switching_epsilon heps
  obtain ⟨T7,_,h7⟩ := seventh_eighth_physical_classical_upper heps
  obtain ⟨Tl,_,hl⟩ := large_integral_upper heps
  obtain ⟨Tq,_,hq⟩ := pair
  refine ⟨max Tp (max T9 (max Tw (max T7 (max Tl Tq)))),by omega,?_⟩
  intro N hN he
  have hpN := hp N (by omega) he
  have h9N := h9 N (by omega) he
  have hwN := hw N (by omega) he
  have h7N := (h7 N (by omega) he).1
  have hlN := hl N (by omega) he
  have hqN := hq N (by omega) he
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
  unfold WuSource.SrcSingle.signedSingleCount truncatedSixthMassScale at hpN
  unfold remainderCoefficient
  rw [J8_split]
  ring_nf at hpN h9N hwN h7N hlN hqN ⊢
  linarith only [hpN,h9N,hwN,h7N,hlN,hqN]


end WuPaper.R2Xi.SourceLedger
#print axioms WuPaper.R2Xi.SourceLedger.remainder_count
