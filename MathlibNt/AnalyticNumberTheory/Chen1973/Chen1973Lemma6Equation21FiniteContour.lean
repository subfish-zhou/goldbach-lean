import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticPolyaVinogradovExplicit
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma2PrimitiveLargeSieve
import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanTypeIIActualTensorMomentExplicit
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLTwistedSmoothedPerron
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation17ContourShift
import MathlibNt.AnalyticNumberTheory.LargeSieve.PrimitiveCharacterElementaryPeriodBound
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLConditionalDerivativeAnalyticContinuation
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLRightHalfPlaneBounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section
open Classical Complex Finset MeasureTheory Set Filter
open scoped BigOperators ArithmeticFunction Topology
namespace AnalyticNumberTheory.LargeSieve

theorem Eq21FiniteContour_rectangle_vertical_identity
    {f : ℂ → ℂ} {β α T : ℝ}
    (hβα : β ≤ α)
    (hT : 0 ≤ T)
    (hf : DifferentiableOn ℂ f {s : ℂ | β ≤ s.re ∧ s.re ≤ α ∧ |s.im| ≤ T}) :
    (∫ t in -T..T, chen1973VerticalSection f α t) -
        (∫ t in -T..T, chen1973VerticalSection f β t) =
      I * chen1973HorizontalSection f β α T := by
  have hrect : DifferentiableOn ℂ f
      (Set.uIcc (((β : ℂ) - T * I).re) (((α : ℂ) + T * I).re) ×ℂ
       Set.uIcc (((β : ℂ) - T * I).im) (((α : ℂ) + T * I).im)) := by
    apply hf.mono
    intro z hz
    have hzre : z.re ∈ Set.uIcc β α := by
      simpa [sub_re, mul_re, mul_zero, zero_mul] using hz.1
    have hzim : z.im ∈ Set.uIcc (-T) T := by
      simpa using hz.2
    rw [Set.uIcc_of_le hβα] at hzre
    rw [Set.uIcc_of_le (by linarith : -T ≤ T)] at hzim
    exact ⟨hzre.1, hzre.2, abs_le.mpr hzim⟩
  have hc := integral_boundary_rect_eq_zero_of_differentiableOn f
    ((β : ℂ) - T * I) ((α : ℂ) + T * I) hrect
  simp only [sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
    sub_zero, add_re, sub_im, mul_im, zero_add, mul_one, add_im,
    smul_eq_mul] at hc
  have hc' :
      ((∫ u in β..α, f (u + (-T) * I)) - ∫ u in β..α, f (u + T * I)) +
        I * (∫ t in -T..T, f (α + t * I)) -
        I * (∫ t in -T..T, f (β + t * I)) = 0 := by
    simpa only [zero_add, add_zero, ofReal_neg, sub_eq_add_neg] using hc
  have hc0 : chen1973HorizontalSection f β α T + I *
      ((∫ t in -T..T, chen1973VerticalSection f α t) -
        ∫ t in -T..T, chen1973VerticalSection f β t) = 0 := by
    unfold chen1973HorizontalSection chen1973VerticalSection
    linear_combination hc'
  have hc1 : I *
      ((∫ t in -T..T, chen1973VerticalSection f α t) -
        ∫ t in -T..T, chen1973VerticalSection f β t) =
      -chen1973HorizontalSection f β α T := by
    linear_combination hc0
  calc
    (∫ t in -T..T, chen1973VerticalSection f α t) -
          (∫ t in -T..T, chen1973VerticalSection f β t) =
        (-I) * (I * ((∫ t in -T..T, chen1973VerticalSection f α t) -
          ∫ t in -T..T, chen1973VerticalSection f β t)) := by
            rw [← mul_assoc, neg_mul, Complex.I_mul_I]
            ring
    _ = (-I) * (-chen1973HorizontalSection f β α T) := by rw [hc1]
    _ = I * chen1973HorizontalSection f β α T := by ring


/-- Every finite vertical section is integrable before Cauchy is applied. -/
theorem Eq21FiniteContour_vertical_intervalIntegrable
    {f : ℂ → ℂ} {β α T v : ℝ} (hT : 0 ≤ T) (hv : v ∈ Icc β α)
    (hf : ContinuousOn f {s : ℂ | β ≤ s.re ∧ s.re ≤ α ∧ |s.im| ≤ T}) :
    IntervalIntegrable (chen1973VerticalSection f v) volume (-T) T := by
  apply ContinuousOn.intervalIntegrable
  apply hf.comp (by fun_prop : ContinuousOn (fun t : ℝ => (v : ℂ) + t * I) (uIcc (-T) T))
  intro t ht
  rw [uIcc_of_le (by linarith : -T ≤ T)] at ht
  simpa using (show β ≤ v ∧ v ≤ α ∧ |t| ≤ T from ⟨hv.1, hv.2, abs_le.mpr ht⟩)


end AnalyticNumberTheory.LargeSieve
