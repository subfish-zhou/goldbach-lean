import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation21FullKernelBudget
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation21ZeroFreeContourBridge
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Equation (21): genuine horizontal boundary decay

The sole quantitative analytic input is a pointwise bound for the actual
`L'/L` quotient throughout the closed strip. This file does not prove that
input. The smoothing-order condition is explicit and may be paid eventually
by a caller. Constants may depend on this fixed cell.

Writing `a = PerronScale x`, `N = PerronOrder x + 1`, `σ = Eq21Sigma x`,
`α = Alpha x`, and `y = x/(p₁p₂)`, the proof constructs
`K = 2 * (σ⁻¹ + a^N) * (2*d)^r`, `B = (M*y^α)*K`, and
`C = 2*B*(α-σ)`. The coarse inequality `1 + log z ≤ z` suffices
because no conductor-uniform constant is requested.

Horizontal integrability is proved separately using measurability and the
pointwise majorant on a finite interval. Thus no nonintegrability/zero-integral
convention is used, and no extra zero-free hypothesis is necessary here.
The existing contour deformation still requires its own genuine zero-free
input; this result does not discharge it.
-/

noncomputable section
open MeasureTheory Set Complex Real
open scoped BigOperators Topology
namespace AnalyticNumberTheory.LargeSieve

/-- A deliberately coarse conductor-dependent logarithmic bound. -/
theorem eq21_horizontal_log_bound {d t : ℝ} (hd : 1 ≤ d) (ht : 0 ≤ t) :
    0 ≤ 1 + Real.log (d * (1 + t)) ∧
    1 + Real.log (d * (1 + t)) ≤ 2 * d * max 1 t := by
  have hp : 0 < d * (1 + t) := by positivity
  have hbase : 1 ≤ d * (1 + t) := by nlinarith
  constructor
  · linarith [Real.log_nonneg hbase]
  · have hl := Real.log_le_sub_one_of_pos hp
    have hm1 : 1 ≤ max 1 t := le_max_left _ _
    have hmt : t ≤ max 1 t := le_max_right _ _
    nlinarith

/-- Full true kernel power, reduced to a square tail only after paying the
polynomial weight. The small-height estimate uses the positive real part. -/
theorem eq21_horizontal_weightedKernel_bound
    {x : ℕ} (hx : 3 ≤ x) {σ u d : ℝ} (hσ : 0 < σ) (hu : σ ≤ u)
    (hd : 1 ≤ d) (r : ℕ)
    (horder : r + 1 ≤ chen1973PerronOrder (x : ℝ) + 1) (t : ℝ) :
    ‖chen1973MellinKernel (x : ℝ) ((u : ℂ) + t * I)‖ *
        (1 + Real.log (d * (1 + |t|))) ^ r ≤
      (2 * (σ⁻¹ + chen1973PerronScale (x : ℝ) ^
        (chen1973PerronOrder (x : ℝ) + 1)) * (2 * d) ^ r) / (1 + t ^ 2) := by
  let a := chen1973PerronScale (x : ℝ)
  let N := chen1973PerronOrder (x : ℝ) + 1
  have ha : 0 < a := chen1973Lemma6_eq17_perronScale_pos (by omega)
  have hu0 : 0 < u := hσ.trans_le hu
  have hw := eq21_horizontal_log_bound hd (abs_nonneg t)
  have hkernel_small : ‖chen1973MellinKernel (x : ℝ) ((u : ℂ) + t * I)‖ ≤ σ⁻¹ := by
    have hp := chen1973Lemma6_eq17_one_le_norm_one_add_div ha
      (s := (u : ℂ) + t * I) (by simpa using hu0.le)
    have hpN := one_le_pow₀ (n := N) hp
    have hs : σ ≤ ‖(u : ℂ) + t * I‖ := hu.trans (by
      simpa [abs_of_pos hu0] using Complex.abs_re_le_norm ((u : ℂ) + t * I))
    unfold chen1973MellinKernel
    rw [norm_div, norm_one, norm_mul, norm_pow, ← one_div]
    apply one_div_le_one_div_of_le hσ
    exact hs.trans (le_mul_of_one_le_right (norm_nonneg _) hpN)
  change _ ≤ (2 * (σ⁻¹ + a ^ N) * (2 * d) ^ r) / (1 + t ^ 2)
  have hden : 0 < 1 + t ^ 2 := by positivity
  by_cases ht : |t| ≤ 1
  · have hw' : (1 + Real.log (d * (1 + |t|))) ^ r ≤ (2 * d) ^ r := by
      apply pow_le_pow_left₀ hw.1
      simpa [max_eq_left ht] using hw.2
    have hb := mul_le_mul hkernel_small hw' (pow_nonneg hw.1 r) (inv_nonneg.mpr hσ.le)
    apply hb.trans
    apply (le_div_iff₀ hden).mpr
    have ht2 : t ^ 2 ≤ 1 := by
      have hab := abs_le.mp ht
      nlinarith [hab.1, hab.2]
    have hc : 0 ≤ (2 * d) ^ r := by positivity
    have hi : 0 ≤ σ⁻¹ := by positivity
    have haN : 0 ≤ a ^ N := by positivity
    nlinarith [mul_nonneg haN hc, mul_nonneg hi hc]
  · have ht1 : 1 ≤ |t| := (lt_of_not_ge ht).le
    have ht0 : 0 < |t| := zero_lt_one.trans_le ht1
    have hkernel : ‖chen1973MellinKernel (x : ℝ) ((u : ℂ) + t * I)‖ ≤ a ^ N / |t| ^ (N + 1) := by
      by_cases htpos : 0 ≤ t
      · simpa [a, N, abs_of_nonneg htpos, Nat.add_assoc] using
          chen1973Lemma6_eq21_mellinKernel_tail_bound (σ := u) (x := x) (by omega)
            (by simpa [abs_of_nonneg htpos] using ht0)
      · have heven := chen1973Lemma6_eq21_mellinKernel_norm_neg (x : ℝ) u (-t)
        simpa [a, N, abs_of_neg (lt_of_not_ge htpos), Nat.add_assoc] using
          heven.trans_le (chen1973Lemma6_eq21_mellinKernel_tail_bound
            (σ := u) (x := x) (by omega) (by linarith))
    have hw' : (1 + Real.log (d * (1 + |t|))) ^ r ≤ (2 * d) ^ r * |t| ^ r := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ hw.1
      simpa [max_eq_right ht1] using hw.2
    have hp : |t| ^ (r + 2) ≤ |t| ^ (N + 1) := by
      apply pow_le_pow_right₀ ht1
      dsimp [N]
      omega
    have hcancel : |t| ^ r / |t| ^ (N + 1) ≤ 1 / t ^ 2 := by
      have ht2pos : 0 < t ^ 2 := sq_pos_of_ne_zero (abs_pos.mp ht0)
      apply (div_le_div_iff₀ (pow_pos ht0 _) ht2pos).mpr
      simpa [pow_add, sq_abs] using hp
    have hb := mul_le_mul hkernel hw' (pow_nonneg hw.1 r) (by positivity : 0 ≤ a ^ N / |t| ^ (N + 1))
    calc
      _ ≤ a ^ N / |t| ^ (N + 1) * ((2 * d) ^ r * |t| ^ r) := hb
      _ = (a ^ N * (2 * d) ^ r) * (|t| ^ r / |t| ^ (N + 1)) := by ring
      _ ≤ (a ^ N * (2 * d) ^ r) * (1 / t ^ 2) :=
        mul_le_mul_of_nonneg_left hcancel (by positivity)
      _ ≤ _ := by
        have ht2 : 1 ≤ t ^ 2 := by nlinarith [sq_abs t, sq_nonneg (|t| - 1)]
        have ht2pos : 0 < t ^ 2 := by linarith
        rw [mul_one_div]
        apply (div_le_div_iff₀ ht2pos hden).mpr
        have hc : 0 ≤ (2 * d) ^ r := by positivity
        have hi : 0 ≤ σ⁻¹ := by positivity
        have haN : 0 ≤ a ^ N := by positivity
        nlinarith [mul_nonneg (mul_nonneg hi hc) (sq_nonneg t),
          mul_nonneg (mul_nonneg haN hc) (sub_nonneg.mpr ht2)]

/-- Actual integrand pointwise decay on the whole strip. The character
coefficient is bounded by one, never silently deleted. -/
theorem chen1973Lemma6_eq21_term_pointwise_decay_of_strip_logDerivative
    {x d : ℕ} (hx : 3 ≤ x) (hd : 1 < d) (χ : PrimitiveCharacter d)
    {pp : ℕ × ℕ} (hy : 1 < (x : ℝ) / ((pp.1 : ℝ) * pp.2))
    {M : ℝ} (hM : 0 ≤ M) (r : ℕ)
    (horder : r + 1 ≤ chen1973PerronOrder (x : ℝ) + 1)
    (hderiv : ∀ s : ℂ,
      chen1973Lemma6Eq21Sigma x ≤ s.re ∧ s.re ≤ chen1973Lemma6Alpha x →
      ‖chen1973PrimitiveLDeriv d s χ / chen1973Lemma6PrimitiveLValue d s χ‖ ≤
        M * (1 + Real.log ((d : ℝ) * (1 + |s.im|))) ^ r) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u ∈ Icc (chen1973Lemma6Eq21Sigma x) (chen1973Lemma6Alpha x),
      ∀ t : ℝ, ‖chen1973Lemma6Eq21TermShiftIntegrand x d χ pp ((u : ℂ) + t * I)‖ ≤
        B / (1 + t ^ 2) := by
  let σ := chen1973Lemma6Eq21Sigma x
  let α := chen1973Lemma6Alpha x
  let y := (x : ℝ) / ((pp.1 : ℝ) * pp.2)
  let K := 2 * (σ⁻¹ + chen1973PerronScale (x : ℝ) ^
    (chen1973PerronOrder (x : ℝ) + 1)) * (2 * (d : ℝ)) ^ r
  have hσ : 0 < σ := chen1973Lemma6_eq21_sigma_pos hx
  have hy0 : 0 < y := zero_lt_one.trans hy
  have ha := chen1973Lemma6_eq17_perronScale_pos (x := x) (by omega)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨(M * y ^ α) * K, by positivity, ?_⟩
  intro u hu t
  have hw := eq21_horizontal_log_bound (d := (d : ℝ)) (by exact_mod_cast hd.le) (abs_nonneg t)
  have hD := hderiv ((u : ℂ) + t * I) (by simpa [σ, α] using hu)
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add] at hD
  have hcpow : ‖(y : ℂ) ^ ((u : ℂ) + t * I)‖ ≤ y ^ α := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hy0]
    apply Real.rpow_le_rpow_of_exponent_le hy.le
    simpa [α] using hu.2
  have hker := eq21_horizontal_weightedKernel_bound hx hσ hu.1
    (d := (d : ℝ)) (by exact_mod_cast hd.le) r horder t
  change _ ≤ K / (1 + t ^ 2) at hker
  change ‖χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d) *
    (((y : ℂ) ^ ((u : ℂ) + t * I) * chen1973MellinKernel (x : ℝ) ((u : ℂ) + t * I)) *
      (chen1973PrimitiveLDeriv d ((u : ℂ) + t * I) χ /
        chen1973Lemma6PrimitiveLValue d ((u : ℂ) + t * I) χ))‖ ≤ _
  simp only [norm_mul]
  calc
    _ ≤ 1 * ((y ^ α * ‖chen1973MellinKernel (x : ℝ) ((u : ℂ) + t * I)‖) *
        (M * (1 + Real.log ((d : ℝ) * (1 + |t|))) ^ r)) := by
      apply mul_le_mul (DirichletCharacter.norm_le_one χ.1 _) _ (by positivity) (by positivity)
      exact mul_le_mul (mul_le_mul_of_nonneg_right hcpow (norm_nonneg _)) hD
        (norm_nonneg _) (by positivity)
    _ = (M * y ^ α) * (‖chen1973MellinKernel (x : ℝ) ((u : ℂ) + t * I)‖ *
        (1 + Real.log ((d : ℝ) * (1 + |t|))) ^ r) := by ring
    _ ≤ (M * y ^ α) * (K / (1 + t ^ 2)) :=
      mul_le_mul_of_nonneg_left hker (by positivity)
    _ = _ := by ring

/-- Each actual horizontal section is measurable. This uses the entire
nonprincipal L-function and its measurable derivative, not zero integral
conventions. Nonvanishing is not needed for this measurability fact. -/
theorem chen1973Lemma6_eq21_horizontal_measurable
    {x d : ℕ} (hd : 1 < d) (χ : PrimitiveCharacter d) (pp : ℕ × ℕ) (t : ℝ) :
    Measurable (fun u : ℝ =>
      chen1973Lemma6Eq21TermShiftIntegrand x d χ pp ((u : ℂ) + t * I)) := by
  let : NeZero d := ⟨Nat.ne_zero_of_lt hd⟩
  have hχ : χ.1 ≠ 1 := by
    intro h
    have hp := χ.2
    rw [DirichletCharacter.IsPrimitive, h, DirichletCharacter.conductor_one] at hp
    omega
  have hL : Measurable χ.1.LFunction :=
    (DirichletCharacter.differentiable_LFunction hχ).continuous.measurable
  have hLm : Measurable (deriv χ.1.LFunction) := measurable_deriv _
  dsimp [chen1973Lemma6Eq21TermShiftIntegrand, chen1973Lemma6Eq21ShiftIntegrand]
  simp only [chen1973PrimitiveLDeriv, chen1973Lemma6PrimitiveLValue, dif_pos hd]
  unfold chen1973MellinKernel
  fun_prop

/-- The two genuine horizontal integrals are integrable, and their oriented
bottom-minus-top difference has square decay. The conclusion carries the
factor two for the two edges and their actual length. No horizontal bound or
integrability premise is assumed. -/
theorem chen1973Lemma6_eq21_horizontal_integrable_and_decay_of_strip_logDerivative
    {x d : ℕ} (hx : 3 ≤ x) (hd : 1 < d) (χ : PrimitiveCharacter d)
    {pp : ℕ × ℕ} (hy : 1 < (x : ℝ) / ((pp.1 : ℝ) * pp.2))
    {M : ℝ} (hM : 0 ≤ M) (r : ℕ)
    (horder : r + 1 ≤ chen1973PerronOrder (x : ℝ) + 1)
    (hderiv : ∀ s : ℂ,
      chen1973Lemma6Eq21Sigma x ≤ s.re ∧ s.re ≤ chen1973Lemma6Alpha x →
      ‖chen1973PrimitiveLDeriv d s χ / chen1973Lemma6PrimitiveLValue d s χ‖ ≤
        M * (1 + Real.log ((d : ℝ) * (1 + |s.im|))) ^ r) :
    (∀ t : ℝ, IntervalIntegrable (fun u : ℝ =>
      chen1973Lemma6Eq21TermShiftIntegrand x d χ pp ((u : ℂ) + t * I))
      volume (chen1973Lemma6Eq21Sigma x) (chen1973Lemma6Alpha x)) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
      ‖chen1973HorizontalSection (chen1973Lemma6Eq21TermShiftIntegrand x d χ pp)
        (chen1973Lemma6Eq21Sigma x) (chen1973Lemma6Alpha x) T‖ ≤ C / (1 + T ^ 2) := by
  obtain ⟨B, hB, hpoint⟩ :=
    chen1973Lemma6_eq21_term_pointwise_decay_of_strip_logDerivative hx hd χ hy hM r horder hderiv
  let σ := chen1973Lemma6Eq21Sigma x
  let α := chen1973Lemma6Alpha x
  let F := chen1973Lemma6Eq21TermShiftIntegrand x d χ pp
  have hσα : σ ≤ α := chen1973Lemma6_eq21_sigma_le_alpha hx
  have hint : ∀ t : ℝ, IntervalIntegrable (fun u : ℝ => F ((u : ℂ) + t * I)) volume σ α := by
    intro t
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hσα).mpr
    have hc : IntegrableOn (fun _ : ℝ => B / (1 + t ^ 2)) (Ioc σ α) :=
      continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    apply hc.mono' (chen1973Lemma6_eq21_horizontal_measurable hd χ pp t).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact hpoint u ⟨hu.1.le, hu.2⟩ t
  refine ⟨hint, 2 * B * (α - σ), by positivity, ?_⟩
  intro T _hT
  have hedge : ∀ t : ℝ, ‖∫ u in σ..α, F ((u : ℂ) + t * I)‖ ≤
      (B / (1 + t ^ 2)) * (α - σ) := by
    intro t
    rw [← abs_of_nonneg (sub_nonneg.mpr hσα)]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro u hu
    have hu' : u ∈ Ioc σ α := by simpa [uIoc_of_le hσα] using hu
    exact hpoint u ⟨hu'.1.le, hu'.2⟩ t
  change ‖(∫ u in σ..α, F ((u : ℂ) + (-T) * I)) -
      ∫ u in σ..α, F ((u : ℂ) + T * I)‖ ≤ _
  calc
    _ ≤ ‖∫ u in σ..α, F ((u : ℂ) + (-T) * I)‖ +
        ‖∫ u in σ..α, F ((u : ℂ) + T * I)‖ := norm_sub_le _ _
    _ ≤ (B / (1 + (-T) ^ 2)) * (α - σ) + (B / (1 + T ^ 2)) * (α - σ) :=
      add_le_add (by simpa only [Complex.ofReal_neg] using hedge (-T)) (hedge T)
    _ = _ := by ring

/-- The exact `horizontal_decay` output consumed by the contour bridge. -/
theorem chen1973Lemma6_eq21_horizontal_decay_of_strip_logDerivative
    {x d : ℕ} (hx : 3 ≤ x) (hd : 1 < d) (χ : PrimitiveCharacter d)
    {pp : ℕ × ℕ} (hy : 1 < (x : ℝ) / ((pp.1 : ℝ) * pp.2))
    {M : ℝ} (hM : 0 ≤ M) (r : ℕ)
    (horder : r + 1 ≤ chen1973PerronOrder (x : ℝ) + 1)
    (hderiv : ∀ s : ℂ,
      chen1973Lemma6Eq21Sigma x ≤ s.re ∧ s.re ≤ chen1973Lemma6Alpha x →
      ‖chen1973PrimitiveLDeriv d s χ / chen1973Lemma6PrimitiveLValue d s χ‖ ≤
        M * (1 + Real.log ((d : ℝ) * (1 + |s.im|))) ^ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
      ‖chen1973HorizontalSection (chen1973Lemma6Eq21TermShiftIntegrand x d χ pp)
        (chen1973Lemma6Eq21Sigma x) (chen1973Lemma6Alpha x) T‖ ≤ C / (1 + T ^ 2) :=
  (chen1973Lemma6_eq21_horizontal_integrable_and_decay_of_strip_logDerivative
    hx hd χ hy hM r horder hderiv).2


end AnalyticNumberTheory.LargeSieve
