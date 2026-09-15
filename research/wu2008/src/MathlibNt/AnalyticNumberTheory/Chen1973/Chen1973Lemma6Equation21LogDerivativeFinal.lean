import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation21UniformVerticalEstimate
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation17CorrectedAssembly

noncomputable section
open MeasureTheory Set Complex Real
open scoped BigOperators Topology
namespace AnalyticNumberTheory.LargeSieve

/-- Integrability on an arbitrary positive line from an actual pointwise bound. -/
theorem chen1973Lemma6_eq21_termVertical_integrable_of_logDerivative_bound
    {x d : ℕ} (hx : 3 ≤ x) (hd : 1 < d) (χ : PrimitiveCharacter d)
    {pp : ℕ × ℕ} (hy : 0 < (x : ℝ) / ((pp.1 : ℝ) * pp.2))
    {σ M : ℝ} (hσ : 0 < σ) (r : ℕ)
    (hderiv : ∀ t : ℝ,
      ‖chen1973PrimitiveLDeriv d ((σ : ℂ) + t * I) χ /
        chen1973Lemma6PrimitiveLValue d ((σ : ℂ) + t * I) χ‖ ≤
        M * (1 + Real.log ((d : ℝ) * (1 + |t|))) ^ r) :
    Integrable (chen1973VerticalSection
      (chen1973Lemma6Eq21TermShiftIntegrand x d χ pp) σ) := by
  let y := (x : ℝ) / ((pp.1 : ℝ) * pp.2)
  let F := fun t : ℝ => chen1973VerticalSection
    (chen1973Lemma6Eq21TermShiftIntegrand x d χ pp) σ t
  let G := fun t : ℝ => ‖chen1973MellinKernel (x : ℝ) ((σ : ℂ) + t * I)‖ *
    (1 + Real.log ((d : ℝ) * (1 + |t|))) ^ r
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd.le
  have hG : Integrable G :=
    (chen1973Lemma6_eq21_weightedKernel_full_integrable_and_bound hx hd1 hσ r).1
  let : NeZero d := ⟨Nat.ne_zero_of_lt hd⟩
  have hχ : χ.1 ≠ 1 := by
    intro h
    have hp := χ.2
    rw [DirichletCharacter.IsPrimitive, h, DirichletCharacter.conductor_one] at hp
    omega
  have hL : Measurable χ.1.LFunction :=
    (DirichletCharacter.differentiable_LFunction hχ).continuous.measurable
  have hLm : Measurable (deriv χ.1.LFunction) := measurable_deriv _
  have hFm : Measurable F := by
    dsimp [F, chen1973VerticalSection, chen1973Lemma6Eq21TermShiftIntegrand,
      chen1973Lemma6Eq21ShiftIntegrand]
    simp only [chen1973PrimitiveLDeriv, chen1973Lemma6PrimitiveLValue, dif_pos hd]
    unfold chen1973MellinKernel
    fun_prop
  apply (hG.const_mul (M * y ^ σ)).mono' hFm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  have hy0 : 0 < y := hy
  have hcpow : ‖(y : ℂ) ^ ((σ : ℂ) + t * I)‖ = y ^ σ := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos hy0 ((σ : ℂ) + t * I)
  dsimp [F, chen1973VerticalSection, chen1973Lemma6Eq21TermShiftIntegrand,
    chen1973Lemma6Eq21ShiftIntegrand]
  change ‖χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d) *
    (((y : ℂ) ^ ((σ : ℂ) + t * I) * chen1973MellinKernel (x : ℝ) ((σ : ℂ) + t * I)) *
    (chen1973PrimitiveLDeriv d ((σ : ℂ) + t * I) χ /
      chen1973Lemma6PrimitiveLValue d ((σ : ℂ) + t * I) χ))‖ ≤ _
  simp only [norm_mul, hcpow]
  calc
    _ ≤ 1 * ((y ^ σ * ‖chen1973MellinKernel (x : ℝ) ((σ : ℂ) + t * I)‖) *
        (M * (1 + Real.log ((d : ℝ) * (1 + |t|))) ^ r)) := by
      apply mul_le_mul (DirichletCharacter.norm_le_one χ.1 _) _ (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left (hderiv t) (by positivity)
    _ = _ := by dsimp [G]; ring

/-- The right-line boundary integrability is unconditional on every source pair. -/
theorem chen1973Lemma6_eq21_alphaTerm_integrable
    {x d : ℕ} (hx : 3 ≤ x) (hd : 1 < d) (χ : PrimitiveCharacter d)
    {pp : ℕ × ℕ} (hy : 0 < (x : ℝ) / ((pp.1 : ℝ) * pp.2)) :
    Integrable (chen1973VerticalSection
      (chen1973Lemma6Eq21TermShiftIntegrand x d χ pp) (chen1973Lemma6Alpha x)) := by
  let : NeZero d := ⟨Nat.ne_zero_of_lt hd⟩
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hα : 0 < chen1973Lemma6Alpha x := by
    unfold chen1973Lemma6Alpha
    positivity
  apply chen1973Lemma6_eq21_termVertical_integrable_of_logDerivative_bound
    (M := 6 * (Real.log (x : ℝ)) ^ 2) hx hd χ hy hα 0
  intro t
  simpa only [pow_zero, mul_one] using
    chen1973Lemma6_alphaLogDerivative_le_six_mul_log_sq χ hd hx t

/-- Source-level terminal with the vertical estimate and both vertical
integrability premises removed. The full-height zero-free strip, the actual
left-line logarithmic-derivative bound, and horizontal decay remain explicit. -/
theorem chen1973Lemma6_equation21_levelZero_eventually_of_logDerivative_and_horizontal
    {M c : ℝ} (hM : 0 ≤ M) (hc : 0 < c) (r : ℕ) :
    ∃ x₀ : ℕ, ∀ x ≥ x₀, ∀ L B k m l₂ : ℕ,
      Chen1973Lemma6Eq21SourceParameters x L B k m l₂ →
      Chen1973Lemma6Eq21ZeroFreeInput x L c →
      (∀ d ∈ chen1973Lemma6ConductorBlock x L 0,
        ∀ χ : PrimitiveCharacter d, ∀ t : ℝ,
          ‖chen1973PrimitiveLDeriv d (chen1973Lemma6Eq21Line x t) χ /
            chen1973Lemma6PrimitiveLValue d (chen1973Lemma6Eq21Line x t) χ‖ ≤
            M * (1 + Real.log ((d : ℝ) * (1 + |t|))) ^ r) →
      (∀ d ∈ chen1973Lemma6ConductorBlock x L 0,
        ∀ χ : PrimitiveCharacter d, ∀ pp ∈ chen1973Lemma6PrimePairShell x B k m,
          ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
            ‖chen1973HorizontalSection (chen1973Lemma6Eq21TermShiftIntegrand x d χ pp)
              (chen1973Lemma6Eq21Sigma x) (chen1973Lemma6Alpha x) T‖ ≤ C / (1 + T ^ 2)) →
      chen1973Lemma6NmBlockActual x L 0 B k m ≤
        (x : ℝ) / Real.log x ^ (20 : ℕ) := by
  obtain ⟨x₁, hfinal⟩ :=
    chen1973Lemma6_equation21_levelZero_eventually_of_source_analytic_inputs 1 c hc
  obtain ⟨x₂, hvertical⟩ :=
    chen1973Lemma6_eq21_primitiveVerticalEstimate_one_eventually_of_logDerivative_bound hM r
  refine ⟨max x₁ x₂, ?_⟩
  intro x hx L B k m l₂ P hzero H hhorizontal
  apply hfinal x ((le_max_left _ _).trans hx) L B k m l₂ P hzero
  · intro d hd χ pp hpp
    have hd1 := chen1973Lemma6_eq21_one_lt_conductor hd
    have hregion := chen1973Lemma6_eq21_actualShell_subset_primeRegion x B k m hpp
    have hy := (chen1973Lemma6_eq21_primeRegion_log_y P.hx hregion).1
    refine ⟨?_, chen1973Lemma6_eq21_alphaTerm_integrable P.hx hd1 χ (zero_lt_one.trans hy),
      hhorizontal d hd χ pp hpp⟩
    exact (chen1973Lemma6_eq21_verticalIntegral_bound_of_logDerivative_bound
      P.hx hd1 χ hy hM r (H d hd χ)).1
  · exact hvertical x ((le_max_right _ _).trans hx) L B k m l₂ P H

end AnalyticNumberTheory.LargeSieve
