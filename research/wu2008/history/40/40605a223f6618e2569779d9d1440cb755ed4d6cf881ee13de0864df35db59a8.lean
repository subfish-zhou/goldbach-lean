import W12RationalPayment
import Wu08FourMotherTerminal

noncomputable section
open Real Wu2008DoubleSieve

namespace WuTarget.W12

open Wu08TerminalAlignment Wu08FourMother Wu08OriginalFourWeights

def otherNumerator : ℝ :=
  3 * firstMain + secondMain - thirdMain - fourthMain + fifthMain + sixthMain -
    original10 - original11 + 8 * PositiveSecondPayment.secondGain +
    PositiveCoreResume.fifthGain + FeedbackLimit.Cinf +
    4 * Phase20.rawPsi + 4 * Phase18.g18

def paidCoefficient : ℝ := (otherNumerator - rationalUpper)/4

def ceilingCoefficient : ℝ := (otherNumerator - debitCeiling)/4

theorem Qoriginal_exact :
    Qoriginal = (otherNumerator - weightedDebit)/4 := by
  unfold Qoriginal otherNumerator weightedDebit
  ring

theorem paidCoefficient_le_Qoriginal : paidCoefficient ≤ Qoriginal := by
  have h : weightedDebit ≤ rationalUpper := weightedDebit_le_rationalUpper
  rw [Qoriginal_exact]
  unfold paidCoefficient
  linarith only [h]

theorem ceilingCoefficient_lt_paidCoefficient :
    ceilingCoefficient < paidCoefficient := by
  unfold ceilingCoefficient paidCoefficient
  linarith only [rationalUpper_lt_debitCeiling]

theorem ceilingCoefficient_lt_Qoriginal : ceilingCoefficient < Qoriginal :=
  ceilingCoefficient_lt_paidCoefficient.trans_le paidCoefficient_le_Qoriginal

theorem ceilingCoefficient_exact :
    ceilingCoefficient = otherNumerator/4 - 2956239/1000000 := by
  unfold ceilingCoefficient debitCeiling
  ring

theorem remaining_budget_suffices
    (h : (15417756/1000000 : ℝ) ≤ otherNumerator) :
    (4491/5000 : ℝ) < Qoriginal := by
  have hc := ceilingCoefficient_lt_Qoriginal
  rw [ceilingCoefficient_exact] at hc
  linarith only [hc, h]

theorem paid_ordinary_P2_parameters {ζ ξmax : ℝ}
    (hζ : 0 < ζ) (hmax : 0 < ξmax) :
    ∃ ξ : ℝ, 0 < ξ ∧ ξ ≤ min ξmax (1/2) ∧
      ∀ dmax : ℝ, 0 < dmax →
      ∃ δ η ρ ε : ℝ, 0 < δ ∧ δ < dmax ∧ δ ≤ 1/100 ∧
        0 < η ∧ η < 1/8 ∧ 1 < ρ ∧ ρ ≤ 5/4 ∧
        0 < ε ∧ ε < truncatedSixthLowerAlpha ∧ ε < δ ∧
      ∀ A : ℕ, ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        ((TruncatedFourPhysical.Q10 N : ℝ) + (TruncatedFourPhysical.Q11 N : ℝ) ≤
          (Wu08FirstPrimeFour.SmallBoundaryRecovery.originalIntegral false +
            Wu08FirstPrimeFour.SmallBoundaryRecovery.originalIntegral true + ζ/2) *
            U8CanonicalMother.M N + (N : ℝ)/log N^A) ∧
        ((paidCoefficient - ζ) * U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2)
            (Finset.range (N+1))).card : ℝ)) := by
  obtain ⟨ξ, hξ, hξu, hp⟩ := Wu08FourMother.ordinary_P2_parameters hζ hmax
  refine ⟨ξ, hξ, hξu, ?_⟩
  intro dmax hdmax
  obtain ⟨δ, η, ρ, ε, hδ, hδm, hδu, hη, hηu, hρ, hρu, hε, hεa, hεδ, h⟩ :=
    hp dmax hdmax
  refine ⟨δ, η, ρ, ε, hδ, hδm, hδu, hη, hηu, hρ, hρu, hε, hεa, hεδ, ?_⟩
  intro A
  obtain ⟨T, hT, hc⟩ := h A
  refine ⟨T, hT, ?_⟩
  intro N hN he
  have hs : 0 ≤ U8CanonicalMother.M N :=
    (HighSixPhase6.original_scale_positive (hT.trans hN)).le
  exact ⟨(hc N hN he).1,
    (mul_le_mul_of_nonneg_right
      (sub_le_sub_right paidCoefficient_le_Qoriginal ζ) hs).trans (hc N hN he).2⟩

theorem paid_ordinary_P2 (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (paidCoefficient - ζ) * U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2)
            (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨_, _, _, hp⟩ := paid_ordinary_P2_parameters hζ (by norm_num : (0 : ℝ) < 1/2)
  obtain ⟨δ, _, _, _, hδ, _, hd, _, _, _, _, _, _, _, h⟩ :=
    hp (1/100) (by norm_num)
  obtain ⟨T, hT, hN⟩ := h 3
  exact ⟨δ, hδ, hd, T, hT, fun N hn he => (hN N hn he).2⟩

theorem ceiling_ordinary_P2 (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (otherNumerator/4 - 2956239/1000000 - ζ) * U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2)
            (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨δ, hδ, hd, T, hT, h⟩ := paid_ordinary_P2 ζ hζ
  refine ⟨δ, hδ, hd, T, hT, ?_⟩
  intro N hN he
  have hs : 0 ≤ U8CanonicalMother.M N :=
    (HighSixPhase6.original_scale_positive (hT.trans hN)).le
  have hc := ceilingCoefficient_lt_paidCoefficient.le
  rw [ceilingCoefficient_exact] at hc
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_right hc ζ) hs).trans (h N hN he)

end WuTarget.W12
