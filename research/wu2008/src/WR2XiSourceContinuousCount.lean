import WR2XiSourceCount
import WR2XiSourceSixth

noncomputable section
namespace WuPaper.R2Xi.SourceContinuousCount
open Wu2008DoubleSieve Real Finset SourceLedger
open Wu2008DoubleSieve.SeventhEighth U8MotherInsertion

theorem signed_count {ε σ : ℝ} (pair : Wu08FourMother.PairUpper σ)
    (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (remainderCoefficient+truncatedSixthLowerF6lin+SourceSixth.amount-
        8*U8CanonicalMother.I-σ-ε)*U8CanonicalMother.M N ≤
      4*((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
  have hε3 : 0 < ε/3 := by positivity
  obtain ⟨Tr,hTr,hr⟩ := ordinary_rebuilt pair hε3
  obtain ⟨T6,_,h6⟩ := SourceSixth.supplied_sixth (ε/3) hε3
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
  dsimp [U8CanonicalMother.M] at hsM ⊢
  ring_nf at hrN h6N hsM ⊢
  linarith only [hrN,h6N,hsM]


def coefficient : ℝ := (remainderCoefficient+truncatedSixthLowerF6lin+
  SourceSixth.amount-8*U8CanonicalMother.I)/4

theorem ordinary_count {ε : ℝ} (he : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (coefficient-ε)*U8CanonicalMother.M N ≤
        ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
          ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨T,hT,hc⟩ := signed_count (Wu08FourMother.original_pair_paid (show 0 < 2*ε by positivity))
    (show 0 < 2*ε by positivity)
  refine ⟨T,hT,fun N hN hEven => ?_⟩
  have h := hc N hN hEven
  change _ ≤ 4*((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
    ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) at h
  unfold coefficient
  nlinarith only [h]

end WuPaper.R2Xi.SourceContinuousCount
#print axioms WuPaper.R2Xi.SourceContinuousCount.ordinary_count
