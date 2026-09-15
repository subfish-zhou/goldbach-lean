import MathlibNt.Wu2004MeanValue.RefinementParameters
import MathlibNt.Wu2004MeanValue.RefinedSubtraction
import MathlibNt.Wu2004MeanValue.OriginalLargeAsymptotics
import MathlibNt.Wu2004MeanValue.LossIntegral

/-!
# Unconditional loss in refining the actual Chen representation count

The lower count on the right is the frozen actual finite set. No quantitative
lower estimate for that count is assumed here. The small-product parameter
is fixed before either asymptotic threshold.
-/

namespace Wu2004MeanValue

open Filter
open MathlibNt.SieveTheory.SingularSeries
open MathlibNt.SieveTheory.SwitchingPrinciple
noncomputable section

theorem refinedGood_card_lower (a ε : ℝ) (ha : 3 / 2 < a) (ha2 : a < 2)
    (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      (chenGoodRepresentations N).card -
          (8 * Real.log (1 / (a - 1)) + ε) *
            liuSingularSeries N * N / Real.log N ^ 2 ≤
        ((refinedGood N a).card : ℝ) := by
  obtain ⟨η, hη, hηh, E, hE⟩ :=
    exists_fixed_eta_small_product_upper a (ε / 2) ha ha2 (by positivity)
  obtain ⟨L, hL⟩ := originalLargeTripleCount_upper a η (ε / 2)
    ha ha2 hη hηh (by positivity)
  refine ⟨max E L, ?_⟩
  intro N hN hEven
  have hfinite :
      ((chenGoodRepresentations N).card : ℝ) ≤
        (refinedGood N a).card + (originalTripleCount N a η : ℝ) +
          (originalLargeTripleCount N a η : ℝ) := by
    exact_mod_cast chenGood_card_le_refined_add_bad N a η ha ha2
  have hsum :
      (originalTripleCount N a η : ℝ) + (originalLargeTripleCount N a η : ℝ) ≤
        (8 * Real.log (1 / (a - 1)) + ε) *
          liuSingularSeries N * N / Real.log N ^ 2 := by
    calc
      _ ≤ (ε / 2) * liuSingularSeries N * N / Real.log N ^ 2 +
          (8 * (∫ u in (a - 1) / a..(1 / 2 : ℝ), 1 / (u * (1 - u))) + ε / 2) *
            liuSingularSeries N * N / Real.log N ^ 2 :=
        add_le_add (hE N (le_trans (le_max_left _ _) hN) hEven)
          (hL N (le_trans (le_max_right _ _) hN) hEven)
      _ = _ := by rw [loss_integral_eq_log a ha ha2]; ring
  linarith

/-- The explicit unit-corrected source expression, without defining or
importing the independently owned Wu08 counting convention. -/
theorem refinedGood_card_lower_add_unit (a ε : ℝ)
    (ha : 3 / 2 < a) (ha2 : a < 2) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      ((chenGoodRepresentations N).card : ℝ) +
          (if (N - 1).Prime then 1 else 0) -
          (8 * Real.log (1 / (a - 1)) + ε) *
            liuSingularSeries N * N / Real.log N ^ 2 ≤
        ((refinedGood N a).card : ℝ) := by
  obtain ⟨E, hE⟩ := refinedGood_card_lower a (ε / 2) ha ha2 (by positivity)
  refine eventually_atTop.mp ?_
  filter_upwards [eventually_refinement_unit_paid (ε / 2) (by positivity),
    eventually_ge_atTop E] with N hpay hN hEven
  have hu : (if (N - 1).Prime then (1 : ℝ) else 0) ≤ 1 := by
    split_ifs <;> norm_num
  have heq :
      (8 * Real.log (1 / (a - 1)) + ε) *
          liuSingularSeries N * N / Real.log N ^ 2 =
        (8 * Real.log (1 / (a - 1)) + ε / 2) *
          liuSingularSeries N * N / Real.log N ^ 2 +
        (ε / 2) * liuSingularSeries N * N / Real.log N ^ 2 := by ring
  have hlower := hE N hN hEven
  rw [heq]
  linarith

theorem refinedGood_source_parameter_lower (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      (chenGoodRepresentations N).card -
          (8 * Real.log (5000 / 4469) + ε) *
            liuSingularSeries N * N / Real.log N ^ 2 ≤
        ((refinedGood N (9469 / 5000)).card : ℝ) := by
  simpa only [show (1 : ℝ) / (9469 / 5000 - 1) = 5000 / 4469 by norm_num] using
    refinedGood_card_lower (9469 / 5000) ε (by norm_num) (by norm_num) hε

end
end Wu2004MeanValue
