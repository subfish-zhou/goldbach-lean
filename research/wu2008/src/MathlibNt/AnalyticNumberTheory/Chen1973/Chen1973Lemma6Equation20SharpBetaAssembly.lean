import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation20BetaIntegral
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation20UnconditionalFinal

noncomputable section
open Classical Complex Finset MeasureTheory Set
namespace AnalyticNumberTheory.LargeSieve

/-- The original complementary-cell cutoff feeds the new beta integral bound.
The first integral is deliberately retained as an actual integral, not declared small. -/
theorem chen1973Lemma6_equation20_actual_first_and_sharp_beta
    {x L B lastD level k m : ℕ}
    (P : Chen1973Lemma6Eq20ComplementarySourceParameters x L B lastD level k)
    (ε : ℝ) :
    let H := chen1973Lemma6Equation20H x level k ε
    let D := chen1973Lemma6Eq20SourceD L level
    let Q := chen1973Lemma6Eq20SourceQ L level
    chen1973Lemma6NmBlockActual x L level B k m ≤
      12 * (x : ℝ) * Real.log x ^ 2 *
        chen1973Lemma6Eq20CorrectedFirstIntegral x L level B k m H +
      6 * Real.pi * (x : ℝ) ^ ((1 : ℝ) / 2) * Real.log x ^ ((11 : ℝ) / 10) *
        chen1973Lemma6Eq20BetaLinearCoefficient x L level B k H D Q := by
  dsimp only
  have h17 := chen1973Lemma6_equation17_corrected_radial_unconditional
    (x := x) (L := L) (level := level) (B := B) (k := k) (m := m)
    (H := chen1973Lemma6Equation20H x level k ε) P.hx P.hlevel
  unfold chen1973Lemma6Eq17CorrectedRadialFirstIntegral
    chen1973Lemma6Eq17CorrectedRadialSecondIntegral
    chen1973Lemma6Eq17CorrectedRadialKernel at h17
  have hb := chen1973Lemma6_eq20_beta_contribution_budget x L level B k m
    (chen1973Lemma6Equation20H x level k ε)
    (chen1973Lemma6Eq20SourceD L level) (chen1973Lemma6Eq20SourceQ L level)
    P.hx P.hB (chen1973Lemma6Eq20SourceD_pos P) (chen1973Lemma6Eq20SourceQ_ge_two P)
    (chen1973Lemma6_eq20_conductorBlock_subset_source_Ioc P)
  exact h17.trans (add_le_add le_rfl hb)

end AnalyticNumberTheory.LargeSieve