import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanActualCountCharacters
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanPrincipalRemainder
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanModernWeightTransfer

namespace MathlibNt.SieveTheory.LiuWeight
open AnalyticNumberTheory.LargeSieve.PanPrincipal
noncomputable section

/-- Exact identity of the two independently constructed actual principal remainders. -/
theorem principalError_eq_liuPanActualPrincipalRaw (N A₁ A₂ q : ℕ) :
    principalError N A₁ A₂ q =
      liuPanActualPrincipalRaw (liuLogarithmicIntegral (2 / Real.log 2))
        N A₁ A₂ q (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) := rfl

/-- The actual same-modulus nonprincipal mass is the only term left unpaid.
The principal remainder has an unconditional uniform logarithmic bound. -/
theorem liuWeight_intervalMaxL_le_nonprincipal_with_paid_principal
    (s : ℝ) (hs : 0 < s) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ q A₁ A₂ : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.sqrt N →
      (A₂ : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) →
      liuMainPanCoprimeIntervalMaxL (liuLogarithmicIntegral (2 / Real.log 2))
        N A₁ A₂ q (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) ≤
        (liuPanActualNonprincipalMass N A₁ A₂ q
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) +
          C * N / Real.log (N : ℝ) ^ s) / q.totient := by
  obtain ⟨C, hC, N₀, h⟩ := principalError_log_saving s hs
  refine ⟨C, hC, N₀, ?_⟩
  intro N hN q A₁ A₂ hq hqN hA
  have hp := h N hN q A₁ A₂ hq hqN hA
  rw [principalError_eq_liuPanActualPrincipalRaw] at hp
  exact (liuWeight_intervalMaxL_le_nonprincipal_add_principal
    (2 / Real.log 2) N (liuSourceZ10 N) (liuSourceY3 N) A₁ A₂ q hq).trans
      (div_le_div_of_nonneg_right (add_le_add le_rfl hp) (Nat.cast_nonneg _))

/-- Actual Pan consumer window, with the normalization fixed before s.
No hypothesis asserting either a PNT estimate or a principal remainder estimate remains. -/
theorem liuPanActualError_le_nonprincipal_with_paid_principal (s : ℝ) (hs : 0 < s) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (B : ℝ) (q : ℕ),
      1 ≤ q → (q : ℝ) ≤ Real.sqrt N →
      liuPanActualError (2 / Real.log 2) N B q ≤
        (liuPanActualNonprincipalMass N (liuPanSourceIntervalLower N B)
          (liuPanSourceIntervalUpper N) q
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) +
          C * N / Real.log (N : ℝ) ^ s) / q.totient := by
  obtain ⟨C, hC, N₀, h⟩ := liuWeight_intervalMaxL_le_nonprincipal_with_paid_principal s hs
  refine ⟨C, hC, N₀, ?_⟩
  intro N hN B q hq hqN
  exact h N hN q _ _ hq hqN
    (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _))

end
end MathlibNt.SieveTheory.LiuWeight