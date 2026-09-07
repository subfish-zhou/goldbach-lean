import MathlibNt.SieveTheory.LiLiuGoldbachG12RoughConnection
import MathlibNt.SieveTheory.LiLiuGoldbachQuadrupleExceptionBudget

open scoped BigOperators
open Finset

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Both exceptional counts on the original cross carrier are paid uniformly
in both upper endpoints. Only the fixed lower prime exponent is used. -/
theorem goldbachG12_exceptions_normalized (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ ε : ℝ, 0 ≤ ε → ∀ b c : ℝ,
      (((∑ v ∈ goldbachG12Labels N ((N : ℝ)^(4/53 : ℝ)) b c,
          goldbachG11RSquareCount (goldbachDifferenceCarrier N ε) v) +
        (∑ v ∈ goldbachG12Labels N ((N : ℝ)^(4/53 : ℝ)) b c,
          goldbachG11NCount (goldbachDifferenceCarrier N ε) N v) : ℤ) : ℝ) ≤
        δ * (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ)^2) := by
  obtain ⟨N₀, hN₀, h⟩ := goldbachQuadruple_exceptions_normalized δ hδ
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN ε hε b c
  have hsub := goldbachG12Labels_subset_goldbachG11Labels N ((N : ℝ)^(4/53 : ℝ)) b c
  have hr :
      (∑ v ∈ goldbachG12Labels N ((N : ℝ)^(4/53 : ℝ)) b c,
        goldbachG11RSquareCount (goldbachDifferenceCarrier N ε) v) ≤
      (∑ v ∈ goldbachG11Labels N ((N : ℝ)^(4/53 : ℝ)) c,
        goldbachG11RSquareCount (goldbachDifferenceCarrier N ε) v) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun v _ _ => Int.natCast_nonneg _)
  have hn :
      (∑ v ∈ goldbachG12Labels N ((N : ℝ)^(4/53 : ℝ)) b c,
        goldbachG11NCount (goldbachDifferenceCarrier N ε) N v) ≤
      (∑ v ∈ goldbachG11Labels N ((N : ℝ)^(4/53 : ℝ)) c,
        goldbachG11NCount (goldbachDifferenceCarrier N ε) N v) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun v _ _ => Int.natCast_nonneg _)
  have hreal :
      (((∑ v ∈ goldbachG12Labels N ((N : ℝ)^(4/53 : ℝ)) b c,
          goldbachG11RSquareCount (goldbachDifferenceCarrier N ε) v) +
        (∑ v ∈ goldbachG12Labels N ((N : ℝ)^(4/53 : ℝ)) b c,
          goldbachG11NCount (goldbachDifferenceCarrier N ε) N v) : ℤ) : ℝ) ≤
      (((∑ v ∈ goldbachG11Labels N ((N : ℝ)^(4/53 : ℝ)) c,
          goldbachG11RSquareCount (goldbachDifferenceCarrier N ε) v) +
        (∑ v ∈ goldbachG11Labels N ((N : ℝ)^(4/53 : ℝ)) c,
          goldbachG11NCount (goldbachDifferenceCarrier N ε) N v) : ℤ) : ℝ) := by
    exact_mod_cast add_le_add hr hn
  exact hreal.trans (h N hN ε hε c)

/-- Original G12 is bounded by its own rough-quotient sum and an arbitrarily
small normalized error. No rough-count or distribution bound is assumed. -/
theorem goldbachWeightG12_le_roughSum_add_normalized (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ ε : ℝ, 0 ≤ ε → ∀ b c : ℝ,
      (goldbachWeightG12 (goldbachDifferenceCarrier N ε) N
        ((N : ℝ)^(4/53 : ℝ)) b c : ℝ) ≤
      ((∑ v ∈ goldbachG12Labels N ((N : ℝ)^(4/53 : ℝ)) b c,
        goldbachG11RoughCount N ε v : ℤ) : ℝ) +
        δ * (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ)^2) := by
  obtain ⟨N₀, hN₀, h⟩ := goldbachG12_exceptions_normalized δ hδ
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN ε hε b c
  have he := h N hN ε hε b c
  have hs := (goldbachWeightG12_roughQuotient_sandwich N ε
    ((N : ℝ)^(4/53 : ℝ)) b c hε).2
  have hsR :
      (goldbachWeightG12 (goldbachDifferenceCarrier N ε) N
        ((N : ℝ)^(4/53 : ℝ)) b c : ℝ) ≤
      ((∑ v ∈ goldbachG12Labels N ((N : ℝ)^(4/53 : ℝ)) b c,
        goldbachG11RoughCount N ε v : ℤ) : ℝ) +
      ((∑ v ∈ goldbachG12Labels N ((N : ℝ)^(4/53 : ℝ)) b c,
        goldbachG11RSquareCount (goldbachDifferenceCarrier N ε) v : ℤ) : ℝ) +
      ((∑ v ∈ goldbachG12Labels N ((N : ℝ)^(4/53 : ℝ)) b c,
        goldbachG11NCount (goldbachDifferenceCarrier N ε) N v : ℤ) : ℝ) := by
    exact_mod_cast hs
  rw [Int.cast_add] at he
  linarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
