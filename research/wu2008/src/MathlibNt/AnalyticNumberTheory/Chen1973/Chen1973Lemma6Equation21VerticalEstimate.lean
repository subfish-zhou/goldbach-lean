import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation21FullKernelBudget
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation21ActualShift
import Mathlib.Analysis.Calculus.FDeriv.Measurable

noncomputable section
open MeasureTheory Set Complex Real
open scoped BigOperators Topology
namespace AnalyticNumberTheory.LargeSieve

/-- An actual primitive vertical integral bound from a pointwise logarithmic-
derivative estimate. Integrability is proved, not supplied or totalized away. -/
theorem chen1973Lemma6_eq21_verticalIntegral_bound_of_logDerivative_bound
    {x d : ℕ} (hx : 3 ≤ x) (hd : 1 < d) (χ : PrimitiveCharacter d)
    {pp : ℕ × ℕ} (hy : 1 < (x : ℝ) / ((pp.1 : ℝ) * pp.2))
    {M : ℝ} (hM : 0 ≤ M) (r : ℕ)
    (hderiv : ∀ t : ℝ,
      ‖chen1973PrimitiveLDeriv d (chen1973Lemma6Eq21Line x t) χ /
        chen1973Lemma6PrimitiveLValue d (chen1973Lemma6Eq21Line x t) χ‖ ≤
        M * (1 + Real.log ((d : ℝ) * (1 + |t|))) ^ r) :
    let a := chen1973PerronScale (x : ℝ)
    let N := chen1973PerronOrder (x : ℝ) + 1
    let D := 1 + Real.log ((d : ℝ) * (1 + a))
    let σ := chen1973Lemma6Eq21Sigma x
    let y := (x : ℝ) / ((pp.1 : ℝ) * pp.2)
    let budget := (σ⁻¹ + Real.log a) * D ^ r +
      ∑ j ∈ Finset.range (r + 1), (Nat.choose r j : ℝ) * D ^ (r - j) *
        ((Nat.factorial j : ℝ) / (N : ℝ) ^ (j + 1))
    Integrable (fun t : ℝ => chen1973VerticalSection
      (chen1973Lemma6Eq21TermShiftIntegrand x d χ pp) σ t) ∧
      ‖((Real.log y)⁻¹ : ℂ) * chen1973Lemma6Eq21VerticalIntegral x d χ pp‖ ≤
        (M / (Real.pi * Real.log y)) * budget * y ^ σ := by
  let a := chen1973PerronScale (x : ℝ)
  let N := chen1973PerronOrder (x : ℝ) + 1
  let D := 1 + Real.log ((d : ℝ) * (1 + a))
  let σ := chen1973Lemma6Eq21Sigma x
  let y := (x : ℝ) / ((pp.1 : ℝ) * pp.2)
  let budget := (σ⁻¹ + Real.log a) * D ^ r +
    ∑ j ∈ Finset.range (r + 1), (Nat.choose r j : ℝ) * D ^ (r - j) *
      ((Nat.factorial j : ℝ) / (N : ℝ) ^ (j + 1))
  let F := fun t : ℝ => chen1973VerticalSection
    (chen1973Lemma6Eq21TermShiftIntegrand x d χ pp) σ t
  let G := fun t : ℝ => ‖chen1973MellinKernel (x : ℝ) ((σ : ℂ) + t * I)‖ *
    (1 + Real.log ((d : ℝ) * (1 + |t|))) ^ r
  change Integrable F ∧ _
  have hy0 : 0 < y := zero_lt_one.trans hy
  have hylog : 0 < Real.log y := Real.log_pos hy
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd.le
  have hσ : 0 < σ := chen1973Lemma6_eq21_sigma_pos hx
  obtain ⟨hG, hGbound⟩ :=
    chen1973Lemma6_eq21_weightedKernel_full_integrable_and_bound hx hd1 hσ r
  change Integrable G at hG
  change (∫ t, G t) ≤ 2 * budget at hGbound
  let : NeZero d := ⟨Nat.ne_zero_of_lt hd⟩
  have hχ : χ.1 ≠ 1 := primitiveCharacter_ne_one hd χ
  have hL : Measurable χ.1.LFunction :=
    (DirichletCharacter.differentiable_LFunction hχ).continuous.measurable
  have hLm : Measurable (deriv χ.1.LFunction) := measurable_deriv _
  have hFm : Measurable F := by
    dsimp [F, chen1973VerticalSection, chen1973Lemma6Eq21TermShiftIntegrand,
      chen1973Lemma6Eq21ShiftIntegrand]
    simp only [chen1973PrimitiveLDeriv, chen1973Lemma6PrimitiveLValue, dif_pos hd]
    unfold chen1973MellinKernel
    fun_prop
  have hpoint : ∀ t, ‖F t‖ ≤ (M * y ^ σ) * G t := by
    intro t
    have hcpow : ‖(y : ℂ) ^ ((σ : ℂ) + t * I)‖ = y ^ σ := by
      simpa using Complex.norm_cpow_eq_rpow_re_of_pos hy0 ((σ : ℂ) + t * I)
    have hD := hderiv t
    change ‖chen1973PrimitiveLDeriv d ((σ : ℂ) + t * I) χ /
      chen1973Lemma6PrimitiveLValue d ((σ : ℂ) + t * I) χ‖ ≤ _ at hD
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
        exact mul_le_mul_of_nonneg_left hD (by positivity)
      _ = _ := by dsimp [G]; ring
  -- The weighted kernel dominates the actual section, proving integrability first.
  have hdom : Integrable (fun t => (M * y ^ σ) * G t) := hG.const_mul _
  have hF : Integrable F := hdom.mono' hFm.aestronglyMeasurable (Filter.Eventually.of_forall hpoint)
  have hint : ‖∫ t, F t‖ ≤ (M * y ^ σ) * (2 * budget) := by
    calc
      _ ≤ ∫ t, ‖F t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t, (M * y ^ σ) * G t :=
        integral_mono_ae hF.norm hdom (Filter.Eventually.of_forall hpoint)
      _ = (M * y ^ σ) * (∫ t, G t) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hGbound (mul_nonneg hM (Real.rpow_nonneg hy0.le _))
  -- Restore the Perron normalization and the factor (log y)⁻¹.
  refine ⟨hF, ?_⟩
  rw [chen1973Lemma6_eq21_verticalIntegral_eq_termShift]
  change ‖((Real.log y)⁻¹ : ℂ) * (((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t, F t)‖ ≤ _
  have hlognorm : ‖((Real.log y)⁻¹ : ℂ)‖ = (Real.log y)⁻¹ := by
    simp [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hylog]
  have hpinorm : ‖(((1 / (2 * Real.pi) : ℝ) : ℂ))‖ = 1 / (2 * Real.pi) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [norm_mul, norm_mul, hlognorm, hpinorm]
  calc
    _ ≤ (Real.log y)⁻¹ * ((1 / (2 * Real.pi)) * ((M * y ^ σ) * (2 * budget))) := by
      gcongr
    _ = _ := by dsimp [budget, a, N, D, σ, y]; ring

end AnalyticNumberTheory.LargeSieve
