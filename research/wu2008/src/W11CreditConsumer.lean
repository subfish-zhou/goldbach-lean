import W11CreditPayment

noncomputable section
open Real Wu2008DoubleSieve

namespace WuTarget.W11Credit
open Wu08FirstPrimeFour.SmallBoundaryRecovery

/-- The scalar replaces the whole correlated credit, not an additional F1 gain. -/
def qScalar : ℝ := (creditLower + WuTarget.W11.otherNumerator) / 4

theorem scalar_budget_exact :
    WuTarget.W11.qCorrelated - qScalar =
      (WuTarget.W11.correlatedCredit - creditLower) / 4 := by
  unfold WuTarget.W11.qCorrelated qScalar
  ring

theorem qScalar_lt_correlated : qScalar < WuTarget.W11.qCorrelated := by
  have h := creditLower_lt_credit
  have he := scalar_budget_exact
  linarith only [h, he]

theorem qScalar_lt_original : qScalar < Wu08FourMother.Qoriginal :=
  qScalar_lt_correlated.trans_le WuTarget.W11.qCorrelated_le_original

theorem full_budget_exact :
    Wu08FourMother.Qoriginal - qScalar =
      (AnalyticTotalThreshold.sharedLoss - WuTarget.W11.sharedRecovery +
        (WuTarget.W11.correlatedCredit - creditLower)) / 4 := by
  have h1 := WuTarget.W11.qCorrelated_budget_exact
  have h2 := scalar_budget_exact
  linarith only [h1, h2]

theorem remaining_safe_budget :
    4 * (4491 / 5000 : ℝ) - creditLower = 1117791 / 500000 := by
  norm_num [creditLower]

/-- All parameters and the raw Q10/Q11 bound come from one frozen W11 call. -/
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
        ((qScalar - ζ) * U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N - p ∧
            ArithmeticFunction.cardFactors (N - p) ≤ 2)
            (Finset.range (N + 1))).card : ℝ)) := by
  obtain ⟨ξ, hξ, hξu, hp⟩ := WuTarget.W11.ordinary_P2_parameters hζ hmax
  refine ⟨ξ, hξ, hξu, ?_⟩
  intro dmax hdmax
  obtain ⟨δ, η, ρ, ε, hδ, hdmax', hd, hη, hηu, hρ, hρu, hε, hεa, hεδ, hN⟩ :=
    hp dmax hdmax
  refine ⟨δ, η, ρ, ε, hδ, hdmax', hd, hη, hηu, hρ, hρu, hε, hεa, hεδ, ?_⟩
  intro A
  obtain ⟨T, hT, hcount⟩ := hN A
  refine ⟨T, hT, ?_⟩
  intro N hNT heven
  obtain ⟨hraw, _, hc⟩ := hcount N hNT heven
  have hm : 0 ≤ U8CanonicalMother.M N :=
    (HighSixPhase6.original_scale_positive (hT.trans hNT)).le
  exact ⟨hraw,
    (mul_le_mul_of_nonneg_right (sub_le_sub_right qScalar_lt_correlated.le ζ) hm).trans hc⟩

theorem ordinary_P2 (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (qScalar - ζ) * U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N - p ∧
            ArithmeticFunction.cardFactors (N - p) ≤ 2)
            (Finset.range (N + 1))).card : ℝ) := by
  obtain ⟨_, _, _, hp⟩ := ordinary_P2_parameters hζ (show (0 : ℝ) < 1 / 2 by norm_num)
  obtain ⟨δ, _, _, _, hδ, _, hd, _, _, _, _, _, _, _, h⟩ :=
    hp (1 / 100) (by norm_num)
  obtain ⟨T, hT, hN⟩ := h 3
  exact ⟨δ, hδ, hd, T, hT, fun N hn he => (hN N hn he).2⟩

end WuTarget.W11Credit
