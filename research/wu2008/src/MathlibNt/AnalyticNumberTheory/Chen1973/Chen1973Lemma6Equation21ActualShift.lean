import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation21UniformConditionalFinal
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation17AlphaBridge
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation21ZeroFreeContourBridge

noncomputable section
open Classical Complex Finset MeasureTheory Set
open scoped BigOperators ArithmeticFunction Topology
namespace AnalyticNumberTheory.LargeSieve

/-- The actual weighted source term equals the normalized signed alpha integral. -/
theorem chen1973Lemma6_eq21_actualPhi_mul_eq_alphaTerm
    {x d : ℕ} (χ : PrimitiveCharacter d) (hd : 1 < d) (hx : 3 ≤ x)
    {pp : ℕ × ℕ} (hp₁ : 0 < pp.1) (hp₂ : 0 < pp.2) :
    chen1973Lemma6ActualPhi x d χ pp * χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d) =
      -(((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, chen1973VerticalSection
          (chen1973Lemma6Eq21TermShiftIntegrand x d χ pp)
          (chen1973Lemma6Alpha x) t) := by
  rw [chen1973Lemma6ActualPhi_eq_alphaNegLogDerivIntegral χ hd hx hp₁ hp₂]
  have hfun : (fun t : ℝ => chen1973VerticalSection
      (chen1973Lemma6Eq21TermShiftIntegrand x d χ pp)
      (chen1973Lemma6Alpha x) t) =
      (fun t : ℝ => -χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d) *
        chen1973Lemma6AlphaNegLogDerivIntegrand x d χ pp t) := by
    funext t
    unfold chen1973VerticalSection chen1973Lemma6Eq21TermShiftIntegrand
      chen1973Lemma6Eq21ShiftIntegrand chen1973Lemma6AlphaNegLogDerivIntegrand
    simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast]
    ring
  rw [hfun, integral_const_mul]
  unfold chen1973Lemma6AlphaNegLogDerivIntegral
  ring

/-- Genuine source-term shift from the printed strip and explicit boundary
payments. This does not infer the width bridge or the boundary estimates. -/
theorem chen1973Lemma6_eq21_actualPhi_mul_eq_neg_vertical_of_boundary
    {x L B k m l₂ d : ℕ} {c C : ℝ}
    (P : Chen1973Lemma6Eq21SourceParameters x L B k m l₂)
    (hzero : Chen1973Lemma6Eq21ZeroFreeInput x L c)
    (hbridge : Chen1973Lemma6Eq21ZeroFreeContourBridge x L c)
    (hd : d ∈ chen1973Lemma6ConductorBlock x L 0)
    (χ : PrimitiveCharacter d) {pp : ℕ × ℕ}
    (hp₁ : 0 < pp.1) (hp₂ : 0 < pp.2) (hC : 0 ≤ C)
    (hleft : Integrable (chen1973VerticalSection
      (chen1973Lemma6Eq21TermShiftIntegrand x d χ pp)
        (chen1973Lemma6Eq21Sigma x)))
    (hright : Integrable (chen1973VerticalSection
      (chen1973Lemma6Eq21TermShiftIntegrand x d χ pp) (chen1973Lemma6Alpha x)))
    (hhoriz : ∀ T : ℝ, 0 ≤ T →
      ‖chen1973HorizontalSection
        (chen1973Lemma6Eq21TermShiftIntegrand x d χ pp)
        (chen1973Lemma6Eq21Sigma x) (chen1973Lemma6Alpha x) T‖ ≤ C / (1 + T ^ 2)) :
    chen1973Lemma6ActualPhi x d χ pp * χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d) =
      -chen1973Lemma6Eq21VerticalIntegral x d χ pp := by
  rw [chen1973Lemma6_eq21_actualPhi_mul_eq_alphaTerm χ
    (chen1973Lemma6_eq21_one_lt_conductor hd) P.hx hp₁ hp₂]
  rw [chen1973Lemma6_eq21_term_full_contour_shift
    P hzero hbridge hd χ hp₁ hp₂ hC hleft hright hhoriz]
  rw [chen1973Lemma6_eq21_verticalIntegral_eq_termShift]

/-- Boundary estimates, not a contour-equality or level-zero conclusion. -/
structure Chen1973Lemma6Eq21TermBoundaryPayments
    (x d : ℕ) (χ : PrimitiveCharacter d) (pp : ℕ × ℕ) : Prop where
  left_integrable : Integrable (chen1973VerticalSection
    (chen1973Lemma6Eq21TermShiftIntegrand x d χ pp) (chen1973Lemma6Eq21Sigma x))
  right_integrable : Integrable (chen1973VerticalSection
    (chen1973Lemma6Eq21TermShiftIntegrand x d χ pp) (chen1973Lemma6Alpha x))
  horizontal_decay : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
    ‖chen1973HorizontalSection (chen1973Lemma6Eq21TermShiftIntegrand x d χ pp)
      (chen1973Lemma6Eq21Sigma x) (chen1973Lemma6Alpha x) T‖ ≤ C / (1 + T ^ 2)

/-- The termwise shift is derived, rather than assumed, from the genuine
zero-free strip and its boundary payments. -/
theorem chen1973Lemma6_eq21_primitiveShift_of_boundary
    {x L B k m l₂ : ℕ} {c : ℝ}
    (P : Chen1973Lemma6Eq21SourceParameters x L B k m l₂)
    (hzero : Chen1973Lemma6Eq21ZeroFreeInput x L c)
    (hbridge : Chen1973Lemma6Eq21ZeroFreeContourBridge x L c)
    (hboundary : ∀ d ∈ chen1973Lemma6ConductorBlock x L 0,
      ∀ χ : PrimitiveCharacter d, ∀ pp ∈ chen1973Lemma6PrimePairShell x B k m,
        Chen1973Lemma6Eq21TermBoundaryPayments x d χ pp) :
    Chen1973Lemma6Eq21PrimitiveAlphaToLeftShift x L B k m := by
  intro d hd χ pp hpp _
  obtain ⟨hp₁, hp₂⟩ := chen1973Lemma6PrimePairShell_pos hpp
  obtain ⟨hleft, hright, C, hC, hhoriz⟩ := hboundary d hd χ pp hpp
  exact chen1973Lemma6_eq21_actualPhi_mul_eq_neg_vertical_of_boundary
    P hzero hbridge hd χ hp₁ hp₂ hC hleft hright hhoriz

/-- Uniform actual-cell consequence. The width comparison, boundary estimates,
and vertical estimate remain genuine analytic hypotheses; neither a termwise
shift equality nor the terminal cell bound is assumed. -/
theorem chen1973Lemma6_equation21_levelZero_eventually_of_boundary_inputs
    (Cvert : ℝ) :
    ∃ x₀ : ℕ, ∀ x ≥ x₀, ∀ L B k m l₂ : ℕ, ∀ c : ℝ,
      Chen1973Lemma6Eq21SourceParameters x L B k m l₂ →
      chen1973Lemma6PrimePairShell x B k m ⊆ chen1973Lemma6Eq21PrimeRegion x →
      Chen1973Lemma6Eq21ZeroFreeInput x L c →
      Chen1973Lemma6Eq21ZeroFreeContourBridge x L c →
      (∀ d ∈ chen1973Lemma6ConductorBlock x L 0,
        ∀ χ : PrimitiveCharacter d, ∀ pp ∈ chen1973Lemma6PrimePairShell x B k m,
          Chen1973Lemma6Eq21TermBoundaryPayments x d χ pp) →
      Chen1973Lemma6Eq21PrimitiveVerticalEstimate Cvert x L B k m →
      chen1973Lemma6NmBlockActual x L 0 B k m ≤
        (x : ℝ) / Real.log x ^ (20 : ℕ) := by
  obtain ⟨x₀, hcutoff⟩ :=
    chen1973Lemma6_equation21_levelZero_eventually_of_primitive_inputs Cvert
  refine ⟨x₀, ?_⟩
  intro x hx L B k m l₂ c P hregion hzero hbridge hboundary hvert
  apply hcutoff x hx L B k m l₂ P hregion
  · intro d hd χ t
    exact chen1973Lemma6_eq21_leftLine_nonvanishing hzero hbridge hd χ t
  · exact chen1973Lemma6_eq21_primitiveShift_of_boundary P hzero hbridge hboundary
  · exact hvert

end AnalyticNumberTheory.LargeSieve