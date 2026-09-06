import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation21AnalyticPayments

/-!
# Conditional uniform level-zero endpoint for Chen equation (21)

Finite character summation and all scalar constant absorption are internal.
The actual termwise contour shift and primitive vertical bound remain explicit.
No unconditional equation-(21) claim is made, and no positive-level dispatcher
is claimed in this module.
-/

noncomputable section
open Classical Complex Finset MeasureTheory Set Filter
open scoped BigOperators ArithmeticFunction Topology
namespace AnalyticNumberTheory.LargeSieve

/-- The genuinely primitive contour input still missing from the current
production stack. It is termwise and conditional on nonvanishing of the
literal equation-(21) line; unlike a terminal hypothesis, it is not a block bound. -/
def Chen1973Lemma6Eq21PrimitiveAlphaToLeftShift
    (x L B k m : ℕ) : Prop :=
  ∀ d ∈ chen1973Lemma6ConductorBlock x L 0,
    ∀ χ : PrimitiveCharacter d,
      ∀ pp ∈ chen1973Lemma6PrimePairShell x B k m,
        (∀ t : ℝ, chen1973Lemma6PrimitiveLValue d
          (chen1973Lemma6Eq21Line x t) χ ≠ 0) →
        chen1973Lemma6ActualPhi x d χ pp *
            χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d) =
          -chen1973Lemma6Eq21VerticalIntegral x d χ pp

/-- Finite character triangle and the exact termwise shift turn the actual
level-zero block into the equation-(21) contour majorant. -/
theorem chen1973Lemma6_eq21_actual_le_contourMajorant
    {x L B k m : ℕ}
    (hline : ∀ d ∈ chen1973Lemma6ConductorBlock x L 0,
      ∀ χ : PrimitiveCharacter d, ∀ t : ℝ,
        chen1973Lemma6PrimitiveLValue d
          (chen1973Lemma6Eq21Line x t) χ ≠ 0)
    (hshift : Chen1973Lemma6Eq21PrimitiveAlphaToLeftShift x L B k m) :
    chen1973Lemma6NmBlockActual x L 0 B k m ≤
      chen1973Lemma6Eq21ContourMajorant x L B k m := by
  unfold chen1973Lemma6NmBlockActual chen1973Lemma6Eq21ContourMajorant
  apply Finset.sum_le_sum
  intro d hd
  apply mul_le_mul_of_nonneg_left
  · calc
      ‖∑ χ : PrimitiveCharacter d,
          star (χ.1 (x : ZMod d)) *
            ∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
              (((Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))⁻¹ : ℝ) : ℂ) *
                chen1973Lemma6ActualPhi x d χ pp *
                  χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d)‖ ≤
          ∑ χ : PrimitiveCharacter d,
            ‖star (χ.1 (x : ZMod d)) *
              ∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
                (((Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))⁻¹ : ℝ) : ℂ) *
                  chen1973Lemma6ActualPhi x d χ pp *
                    χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d)‖ := by
            exact norm_sum_le _ _
      _ ≤ ∑ χ : PrimitiveCharacter d,
          ‖∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
            (((Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))⁻¹ : ℝ) : ℂ) *
              chen1973Lemma6Eq21VerticalIntegral x d χ pp‖ := by
        apply Finset.sum_le_sum
        intro χ hχ
        rw [norm_mul, norm_star]
        have hsum :
            (∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
              (((Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))⁻¹ : ℝ) : ℂ) *
                chen1973Lemma6ActualPhi x d χ pp *
                  χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d)) =
            -(∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
              (((Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))⁻¹ : ℝ) : ℂ) *
                chen1973Lemma6Eq21VerticalIntegral x d χ pp) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro pp hpp
          rw [mul_assoc, hshift d hd χ pp hpp (hline d hd χ), mul_neg]
        rw [hsum, norm_neg]
        exact mul_le_of_le_one_left (norm_nonneg _)
          (DirichletCharacter.norm_le_one χ.1 (x : ZMod d))
  · positivity

/-- For each fixed vertical-estimate constant, one cutoff precedes all source
cell parameters. No smallness assumption on that constant or external Mertens
or scalar-decay payment is required. The two analytic producers remain open. -/
theorem chen1973Lemma6_equation21_levelZero_eventually_of_primitive_inputs
    (Cvert : ℝ) :
    ∃ x₀ : ℕ, ∀ x ≥ x₀, ∀ L B k m l₂ : ℕ,
      Chen1973Lemma6Eq21SourceParameters x L B k m l₂ →
      chen1973Lemma6PrimePairShell x B k m ⊆
        chen1973Lemma6Eq21PrimeRegion x →
      (∀ d ∈ chen1973Lemma6ConductorBlock x L 0,
        ∀ χ : PrimitiveCharacter d, ∀ t : ℝ,
          chen1973Lemma6PrimitiveLValue d
            (chen1973Lemma6Eq21Line x t) χ ≠ 0) →
      Chen1973Lemma6Eq21PrimitiveAlphaToLeftShift x L B k m →
      Chen1973Lemma6Eq21PrimitiveVerticalEstimate Cvert x L B k m →
      chen1973Lemma6NmBlockActual x L 0 B k m ≤
        (x : ℝ) / Real.log x ^ (20 : ℕ) := by
  obtain ⟨x₀, hcutoff⟩ := chen1973Lemma6_eq21_contour_log20_decay_eventually Cvert
  refine ⟨x₀, ?_⟩
  intro x hx L B k m l₂ P hregion hline hshift hvert
  exact (chen1973Lemma6_eq21_actual_le_contourMajorant hline hshift).trans
    (hcutoff x hx L B k m l₂ P hregion hvert)

end AnalyticNumberTheory.LargeSieve