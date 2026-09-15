import W11JointBound

noncomputable section
open Real Wu2008DoubleSieve

namespace WuTarget.W11
open Wu08TerminalAlignment Wu08FourMother
open PositiveSecondPayment PositiveCoreResume
open Wu08FirstPrimeFour.SmallBoundaryRecovery

/-- Every other actual numerator term, with its original multiplicity. -/
def otherNumerator : ℝ :=
  secondMain + fifthMain + sixthMain - 2 * seventhMain - eighthMain - ninthMain -
    original10 - original11 + 8 * secondGain + fifthGain + FeedbackLimit.Cinf +
    4 * Phase20.rawPsi + 4 * Phase18.g18

theorem original_budget_exact :
    Qoriginal = (3 * firstMain - thirdMain - fourthMain + otherNumerator) / 4 := by
  unfold Qoriginal otherNumerator
  ring

def qPair : ℝ := (3 * firstMain + otherNumerator - pairUpper) / 4

def qCorrelated : ℝ := (correlatedCredit + otherNumerator) / 4

theorem qPair_budget_exact :
    Qoriginal - qPair = (pairUpper - thirdMain - fourthMain) / 4 := by
  rw [original_budget_exact]
  unfold qPair
  ring

/-- The shared correction is spent once; the standalone curvature debit is
    an alternative certificate and is not added to this one. -/
theorem qCorrelated_budget_exact :
    Qoriginal - qCorrelated =
      (AnalyticTotalThreshold.sharedLoss - sharedRecovery) / 4 := by
  rw [original_budget_exact, ← first_exact]
  unfold qCorrelated correlatedCredit AnalyticTotalThreshold.sharedLoss
    thirdMain fourthMain FixedCoefficientUpperEnclosure.a FixedCoefficientUpperEnclosure.s
  ring

theorem qPair_le_original : qPair ≤ Qoriginal := by
  have h := normalized_signed_pair_lower
  rw [original_budget_exact]
  unfold qPair
  linarith only [h]

theorem qCorrelated_le_original : qCorrelated ≤ Qoriginal := by
  have h := sharedRecovery_le
  have he := qCorrelated_budget_exact
  linarith only [h, he]

/-- One call to the original count producer supplies both alternative
    certificates, with the same delta, raw Q10/Q11 bound, and threshold. -/
theorem ordinary_P2_parameters {ζ ξmax : ℝ} (hζ : 0 < ζ) (hmax : 0 < ξmax) :
    ∃ ξ : ℝ, 0 < ξ ∧ ξ ≤ min ξmax (1 / 2) ∧
      ∀ dmax : ℝ, 0 < dmax →
      ∃ δ η ρ ε : ℝ, 0 < δ ∧ δ < dmax ∧ δ ≤ 1 / 100 ∧
        0 < η ∧ η < 1 / 8 ∧ 1 < ρ ∧ ρ ≤ 5 / 4 ∧
        0 < ε ∧ ε < truncatedSixthLowerAlpha ∧ ε < δ ∧
      ∀ A : ℕ, ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        ((TruncatedFourPhysical.Q10 N : ℝ) + (TruncatedFourPhysical.Q11 N : ℝ) ≤
          (originalIntegral false + originalIntegral true + ζ / 2) *
            U8CanonicalMother.M N + (N : ℝ) / log N ^ A) ∧
        ((qPair - ζ) * U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N - p ∧
            ArithmeticFunction.cardFactors (N - p) ≤ 2)
            (Finset.range (N + 1))).card : ℝ)) ∧
        ((qCorrelated - ζ) * U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N - p ∧
            ArithmeticFunction.cardFactors (N - p) ≤ 2)
            (Finset.range (N + 1))).card : ℝ)) := by
  obtain ⟨ξ, hξ, hξu, hp⟩ := Wu08FourMother.ordinary_P2_parameters hζ hmax
  refine ⟨ξ, hξ, hξu, ?_⟩
  intro dmax hdmax
  obtain ⟨δ, η, ρ, ε, hδ, hdmax', hd, hη, hηu, hρ, hρu, hε, hεa, hεδ, hN⟩ :=
    hp dmax hdmax
  refine ⟨δ, η, ρ, ε, hδ, hdmax', hd, hη, hηu, hρ, hρu, hε, hεa, hεδ, ?_⟩
  intro A
  obtain ⟨T, hT, hcount⟩ := hN A
  refine ⟨T, hT, ?_⟩
  intro N hNT heven
  obtain ⟨hraw, hc⟩ := hcount N hNT heven
  have hm : 0 ≤ U8CanonicalMother.M N :=
    (HighSixPhase6.original_scale_positive (hT.trans hNT)).le
  exact ⟨hraw,
    (mul_le_mul_of_nonneg_right (sub_le_sub_right qPair_le_original ζ) hm).trans hc,
    (mul_le_mul_of_nonneg_right (sub_le_sub_right qCorrelated_le_original ζ) hm).trans hc⟩

theorem ordinary_P2 (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        ((qPair - ζ) * U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N - p ∧
            ArithmeticFunction.cardFactors (N - p) ≤ 2)
            (Finset.range (N + 1))).card : ℝ)) ∧
        ((qCorrelated - ζ) * U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N - p ∧
            ArithmeticFunction.cardFactors (N - p) ≤ 2)
            (Finset.range (N + 1))).card : ℝ)) := by
  obtain ⟨_, _, _, hp⟩ := ordinary_P2_parameters hζ (show (0 : ℝ) < 1 / 2 by norm_num)
  obtain ⟨δ, _, _, _, hδ, _, hd, _, _, _, _, _, _, _, h⟩ :=
    hp (1 / 100) (by norm_num)
  obtain ⟨T, hT, hN⟩ := h 3
  exact ⟨δ, hδ, hd, T, hT, fun N hn he => (hN N hn he).2⟩

end WuTarget.W11
