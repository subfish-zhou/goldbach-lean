/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation17KernelBounds
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma3LFourthMoment
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation17BromwichSum
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLTwistedSmoothedPerron
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
# Chen 1973, Lemma 6, equation (17): alpha-line log-derivative bridge

This module moves the exact finite `ActualPhi` identity from the unconditional
`Re s = 2` Bromwich representation to Chen's line
`Re s = alpha = 1 + 1 / log x`, identifies the von Mangoldt series with
`-L'/L`, and lifts the identity through the finite pair, primitive-character,
and conductor-block sums.  It does not assume an equation-(17) majorization or
any later assembly conclusion.
-/

noncomputable section

open Classical Complex Finset MeasureTheory Set
open scoped BigOperators ArithmeticFunction Topology

namespace AnalyticNumberTheory.LargeSieve

/-- Conductors in a positive-level Chen block are greater than one. -/
theorem chen1973Lemma6ConductorBlock_one_lt
    {x L level d : ℕ} (hlevel : 1 ≤ level)
    (hd : d ∈ chen1973Lemma6ConductorBlock x L level) :
    1 < d := by
  by_cases hzero : level = 0
  · omega
  · simp [chen1973Lemma6ConductorBlock, hzero, chen1973Lemma6DyadicShell] at hd
    omega

private theorem one_lt_of_mem_conductorBlock
    {x L level d : ℕ} (hlevel : 1 ≤ level)
    (hd : d ∈ chen1973Lemma6ConductorBlock x L level) :
    1 < d := by
  exact AnalyticNumberTheory.LargeSieve.chen1973Lemma6ConductorBlock_one_lt hlevel hd

private theorem primitiveCharacter_ne_one_of_one_lt
    {d : ℕ} [NeZero d] (hd : 1 < d) (χ : PrimitiveCharacter d) :
    χ.1 ≠ 1 := by
  exact AnalyticNumberTheory.LargeSieve.chen1973_primitive_ne_one hd χ

private theorem one_lt_alpha {x : ℕ} (hx : 3 ≤ x) :
    1 < chen1973Lemma6Alpha x := by
  unfold chen1973Lemma6Alpha
  have hlog : 0 < Real.log (x : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  linarith [one_div_pos.mpr hlog]

private theorem alpha_le_two {x : ℕ} (hx : 3 ≤ x) :
    chen1973Lemma6Alpha x ≤ 2 := by
  have hlog1 : (1 : ℝ) ≤ Real.log (x : ℝ) :=
    (chen1973Lemma6_eq17_one_le_log_and_order hx).1
  have hlog : 0 < Real.log (x : ℝ) := lt_of_lt_of_le (by norm_num) hlog1
  unfold chen1973Lemma6Alpha
  have hinv : 1 / Real.log (x : ℝ) ≤ 1 := (div_le_one hlog).2 hlog1
  linarith

private theorem one_le_perronScale {x : ℕ} (hx : 3 ≤ x) :
    1 ≤ chen1973PerronScale (x : ℝ) := by
  unfold chen1973PerronScale
  exact Real.one_le_rpow
    (chen1973Lemma6_eq17_one_le_log_and_order hx).1 (by norm_num)

private theorem perronOrder_two_le_succ {x : ℕ} (hx : 3 ≤ x) :
    2 ≤ chen1973PerronOrder (x : ℝ) + 1 := by
  have hord : 1 ≤ chen1973PerronOrder (x : ℝ) :=
    (chen1973Lemma6_eq17_one_le_log_and_order hx).2
  omega

private theorem norm_scaled_mellinKernel_le_inv_one_add_sq
    {x : ℕ} (hx : 3 ≤ x) {X σ t : ℝ} (hX : 0 < X)
    (hσlower : chen1973Lemma6Alpha x ≤ σ) (_hσupper : σ ≤ 2) :
    ‖(X : ℂ) ^ (σ + t * I) * chen1973MellinKernel (x : ℝ) (σ + t * I)‖ ≤
      X ^ σ * chen1973PerronScale (x : ℝ) ^
        (chen1973PerronOrder (x : ℝ) + 1) / σ / (1 + t ^ 2) := by
  let A := chen1973PerronScale (x : ℝ)
  let n := chen1973PerronOrder (x : ℝ)
  let z : ℂ := σ + t * I
  let η : ℂ := (A + σ) + t * I
  have hA : 1 ≤ A := one_le_perronScale hx
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hσpos : 0 < σ := zero_lt_one.trans ((one_lt_alpha hx).trans_le hσlower)
  have hn : 2 ≤ n + 1 := perronOrder_two_le_succ hx
  have hcpow : ‖(X : ℂ) ^ z‖ = X ^ σ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]
    simp [z]
  have hηeq : 1 + z / A = η / A := by
    dsimp [z, η]
    field_simp [hApos.ne']
    ring
  have hzge : σ ≤ ‖z‖ := by
    calc
      σ = |σ| := by rw [abs_of_pos hσpos]
      _ ≤ ‖z‖ := by
        simpa [z] using Complex.abs_re_le_norm z
  have hηsq : ‖η‖ ^ 2 = (A + σ) ^ 2 + t ^ 2 := by
    rw [Complex.sq_norm]
    simp [η, Complex.normSq_apply, pow_two]
  have hηone : 1 ≤ ‖η‖ := by
    have hsq : 1 ≤ ‖η‖ ^ 2 := by
      rw [hηsq]
      nlinarith [sq_nonneg t, hA, hσpos]
    nlinarith [norm_nonneg η, sq_nonneg (‖η‖ - 1)]
  have hηpow : 1 + t ^ 2 ≤ ‖η‖ ^ (n + 1) := by
    calc
      1 + t ^ 2 ≤ ‖η‖ ^ 2 := by
        rw [hηsq]
        nlinarith [sq_nonneg (A + σ - 1), hA, hσpos]
      _ ≤ ‖η‖ ^ (n + 1) := by
        exact pow_le_pow_right₀ hηone hn
  have hknorm :
      ‖chen1973MellinKernel (x : ℝ) z‖ =
        A ^ (n + 1) / (‖z‖ * ‖η‖ ^ (n + 1)) := by
    unfold chen1973MellinKernel
    rw [norm_div, norm_one, norm_mul, norm_pow, hηeq, norm_div, div_pow]
    simp [A, n, abs_of_pos hApos, div_eq_mul_inv,
      mul_left_comm, mul_comm]
  have hstep :
      A ^ (n + 1) / (‖z‖ * ‖η‖ ^ (n + 1)) ≤
        A ^ (n + 1) / (σ * (1 + t ^ 2)) := by
    apply div_le_div_of_nonneg_left (pow_nonneg hApos.le _) (by positivity)
    exact mul_le_mul hzge hηpow (by positivity) (norm_nonneg _)
  calc
    ‖(X : ℂ) ^ z * chen1973MellinKernel (x : ℝ) z‖ =
        X ^ σ * ‖chen1973MellinKernel (x : ℝ) z‖ := by
          rw [norm_mul, hcpow]
    _ = X ^ σ * (A ^ (n + 1) / (‖z‖ * ‖η‖ ^ (n + 1))) := by
          rw [hknorm]
    _ ≤ X ^ σ * (A ^ (n + 1) / (σ * (1 + t ^ 2))) := by
          gcongr
    _ = X ^ σ * A ^ (n + 1) / σ / (1 + t ^ 2) := by
          field_simp [hσpos.ne', show (1 + t ^ 2) ≠ 0 by positivity]

private theorem integrable_scaled_mellinKernel_alpha
    {x : ℕ} (hx : 3 ≤ x) {X : ℝ} (hX : 0 < X) :
    Integrable (fun t : ℝ =>
      (X : ℂ) ^ (chen1973Lemma6Alpha x + t * I) *
        chen1973MellinKernel (x : ℝ) (chen1973Lemma6Alpha x + t * I)) := by
  let C : ℝ := X ^ chen1973Lemma6Alpha x *
      chen1973PerronScale (x : ℝ) ^
        (chen1973PerronOrder (x : ℝ) + 1) / chen1973Lemma6Alpha x
  have hdom : Integrable (fun t : ℝ => C / (1 + t ^ 2)) :=
    integrable_inv_one_add_sq.const_mul C
  have hmeas :
      AEStronglyMeasurable (fun t : ℝ =>
        (X : ℂ) ^ (chen1973Lemma6Alpha x + t * I) *
          chen1973MellinKernel (x : ℝ) (chen1973Lemma6Alpha x + t * I)) := by
    apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · fun_prop (disch := exact Or.inl (by exact_mod_cast hX.ne'))
    · unfold chen1973MellinKernel
      apply Continuous.div continuous_const
      · fun_prop
      · intro t
        apply mul_ne_zero
        · intro hz
          have hzre := congrArg Complex.re hz
          simp at hzre
          linarith [one_lt_alpha hx]
        · apply pow_ne_zero
          intro hz
          have hApos := chen1973Lemma6_eq17_perronScale_pos (by omega : 1 < x)
          have hzre := congrArg Complex.re hz
          simp [div_re] at hzre
          field_simp [hApos.ne'] at hzre
          nlinarith [one_lt_alpha hx, hApos]
  apply Integrable.mono' hdom
  · exact hmeas
  · filter_upwards with t
    simpa [C] using norm_scaled_mellinKernel_le_inv_one_add_sq
      (x := x) hx (X := X) hX
      (σ := chen1973Lemma6Alpha x) le_rfl (alpha_le_two hx) (t := t)

private theorem mellinInv_chen1973MellinKernel_eq_verticalLine
    {x : ℕ} {σ : ℝ} {y : ℝ} (hy : 0 < y) :
    mellinInv σ (chen1973MellinKernel (x : ℝ)) (1 / y) =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, (y : ℂ) ^ (σ + t * I) *
          chen1973MellinKernel (x : ℝ) (σ + t * I)) := by
  rw [mellinInv]
  change (((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ,
      (((1 / y : ℝ) : ℂ) ^ (-(((σ : ℂ) + t * Complex.I))) *
        chen1973MellinKernel (x : ℝ) (((σ : ℂ) + t * Complex.I))))) = _
  congr 2
  ext t
  have hpow :
      (((1 / y : ℝ) : ℂ) ^ (-(((σ : ℂ) + t * Complex.I)))) =
        Complex.cpow (y : ℂ) (((σ : ℂ) + t * Complex.I)) := by
    let w : ℂ := ((σ : ℂ) + t * Complex.I)
    have h1 : (((1 / y : ℝ) : ℂ) ^ (-w)) = (((y : ℂ)⁻¹) ^ (-w)) := by
      congr 1
      simp [one_div]
    rw [show ((σ : ℂ) + t * Complex.I) = w by rfl, h1,
      Complex.inv_cpow_ofReal_nonneg hy.le, Complex.cpow_neg]
    simp
  simpa using congrArg (fun w => w *
    chen1973MellinKernel (x : ℝ) (((σ : ℂ) + t * Complex.I))) hpow

private theorem Chen1973BromwichIdentity_on_alpha
    {x : ℕ} (hx : 3 ≤ x) {y : ℝ} (hy : 0 < y) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, (y : ℂ) ^ (chen1973Lemma6Alpha x + t * I) *
          chen1973MellinKernel (x : ℝ) (chen1973Lemma6Alpha x + t * I)) =
      (chen1973PerronKernelFinite (x : ℝ) y : ℂ) := by
  have hx1 : 1 < (x : ℝ) := by exact_mod_cast (show 1 < x by omega)
  have hvM : Complex.VerticalIntegrable
      (mellin (chen1973GammaDensityPrimitive (x : ℝ)))
      (chen1973Lemma6Alpha x) := by
    rw [Complex.VerticalIntegrable]
    refine (integrable_scaled_mellinKernel_alpha (x := x) hx (X := 1) zero_lt_one).congr ?_
    filter_upwards with t
    rw [mellin_chen1973GammaDensityPrimitive hx1 (by
      simpa using zero_lt_one.trans (one_lt_alpha hx))]
    simp
  have hinv := mellinInv_mellin_eq (chen1973Lemma6Alpha x)
    (chen1973GammaDensityPrimitive (x : ℝ)) (one_div_pos.mpr hy)
    (mellinConvergent_chen1973GammaDensityPrimitive hx1 (by
      simpa using zero_lt_one.trans (one_lt_alpha hx)))
    hvM (continuousAt_chen1973GammaDensityPrimitive (x : ℝ) _ (one_div_pos.mpr hy))
  have hreplace :
      mellinInv (chen1973Lemma6Alpha x)
          (mellin (chen1973GammaDensityPrimitive (x : ℝ))) (1 / y) =
        mellinInv (chen1973Lemma6Alpha x)
          (chen1973MellinKernel (x : ℝ)) (1 / y) := by
    unfold mellinInv
    congr 2
    ext t
    rw [mellin_chen1973GammaDensityPrimitive hx1 (by
      simpa using zero_lt_one.trans (one_lt_alpha hx))]
  rw [hreplace, mellinInv_chen1973MellinKernel_eq_verticalLine hy] at hinv
  rw [hinv, chen1973GammaDensityPrimitive_one_div hy]

private theorem chen1973Lemma6ActualPhi_eq_tsum
    {x d : ℕ} (χ : PrimitiveCharacter d) {pp : ℕ × ℕ}
    (hp₁ : 0 < pp.1) (hp₂ : 0 < pp.2) :
    chen1973Lemma6ActualPhi x d χ pp =
      ∑' n : ℕ,
        (((ArithmeticFunction.vonMangoldt n : ℝ) *
          chen1973PerronKernelFinite (x : ℝ)
            ((x : ℝ) / ((pp.1 : ℝ) * pp.2 * n)) : ℂ) *
          χ.1 (n : ZMod d)) := by
  let f : ℕ → ℂ := fun n =>
    (((ArithmeticFunction.vonMangoldt n : ℝ) *
      chen1973PerronKernelFinite (x : ℝ)
        ((x : ℝ) / ((pp.1 : ℝ) * pp.2 * n)) : ℂ) *
      χ.1 (n : ZMod d))
  have htail : ∀ n : ℕ, n ∉ Finset.range (x + 1) → f n = 0 := by
    intro n hn
    have hxlt : x < n := by
      have : x + 1 ≤ n := by simpa only [Finset.mem_range, not_lt] using hn
      omega
    have hnpos : 0 < n := by omega
    have harg : (x : ℝ) / ((pp.1 : ℝ) * pp.2 * n) ≤ 1 := by
      have hden : 0 < ((pp.1 : ℝ) * pp.2 * n) := by positivity
      rw [div_le_iff₀ hden]
      have hprod : (x : ℝ) ≤ (pp.1 : ℝ) * pp.2 * n := by
        calc
          (x : ℝ) ≤ n := by exact_mod_cast hxlt.le
          _ ≤ (pp.1 : ℝ) * pp.2 * n := by
            have hp : (1 : ℝ) ≤ (pp.1 : ℝ) * pp.2 := by
              nlinarith [show (1 : ℝ) ≤ pp.1 by exact_mod_cast hp₁,
                show (1 : ℝ) ≤ pp.2 by exact_mod_cast hp₂]
            calc
              (n : ℝ) = 1 * n := by ring
              _ ≤ ((pp.1 : ℝ) * pp.2) * n :=
                mul_le_mul_of_nonneg_right hp (by positivity)
              _ = (pp.1 : ℝ) * pp.2 * n := by ring
      simpa using hprod
    simp [f, chen1973PerronKernelFinite_of_le_one harg]
  rw [tsum_eq_sum (s := Finset.range (x + 1)) htail]
  unfold chen1973Lemma6ActualPhi chen1973Lemma5NCarrier f
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro n hn
  by_cases hmem : n ≤ x / (pp.1 * pp.2)
  · simp [hmem]
  · have hnpos : 0 < n := by
      by_contra hzero
      have : n = 0 := Nat.eq_zero_of_not_pos hzero
      subst this
      exact hmem (by positivity)
    have harg : (x : ℝ) / ((pp.1 : ℝ) * pp.2 * n) ≤ 1 := by
      have hden : 0 < ((pp.1 : ℝ) * pp.2 * n) := by positivity
      rw [div_le_iff₀ hden]
      have hquot : x / (pp.1 * pp.2) < n := Nat.lt_of_not_ge hmem
      have hnat : x < n * (pp.1 * pp.2) := by
        exact (Nat.div_lt_iff_lt_mul (Nat.mul_pos hp₁ hp₂)).mp hquot
      have hnat' : x ≤ pp.1 * pp.2 * n := by
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hnat.le
      simpa only [one_mul] using (show (x : ℝ) ≤ (pp.1 : ℝ) * pp.2 * n by
        exact_mod_cast hnat')
    simp [hmem, chen1973PerronKernelFinite_of_le_one harg]

theorem chen1973Lemma6ActualPhi_eq_negLogDerivIntegral_alpha
    {x d : ℕ} [NeZero d] (χ : PrimitiveCharacter d) (_hχ : χ.1 ≠ 1)
    (hx : 3 ≤ x) {pp : ℕ × ℕ} (hp₁ : 0 < pp.1) (hp₂ : 0 < pp.2) :
    chen1973Lemma6ActualPhi x d χ pp =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ,
          (-deriv χ.1.LFunction (chen1973Lemma6Alpha x + t * I) /
              χ.1.LFunction (chen1973Lemma6Alpha x + t * I)) *
            (((x : ℝ) / ((pp.1 : ℝ) * pp.2) : ℂ) ^
              (chen1973Lemma6Alpha x + t * I) *
              chen1973MellinKernel (x : ℝ)
                (chen1973Lemma6Alpha x + t * I))) := by
  let α : ℝ := chen1973Lemma6Alpha x
  let X : ℝ := (x : ℝ) / ((pp.1 : ℝ) * pp.2)
  let kernel : ℝ → ℂ := fun t =>
    (X : ℂ) ^ (α + t * I) * chen1973MellinKernel (x : ℝ) (α + t * I)
  let coeff : ℕ → ℝ := fun n =>
    ‖DirichletCharacter.twistedVonMangoldtCoeff χ.1 n /
      (n : ℂ) ^ ((α : ℝ) : ℂ)‖
  let F : ℕ → ℝ → ℂ := fun n t =>
    DirichletCharacter.twistedVonMangoldtCoeff χ.1 n /
      (n : ℂ) ^ (α + t * I) * kernel t
  have hX : 0 < X := by positivity
  have hα : 1 < α := one_lt_alpha hx
  have hkernel : Integrable kernel := by
    simpa [kernel, α, X] using integrable_scaled_mellinKernel_alpha (x := x) hx hX
  have hcoeff : Summable coeff := by
    have h := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ.1 (by
      simpa only [Complex.ofReal_re] using hα : 1 < (((α : ℝ) : ℂ)).re)
    rw [LSeriesSummable] at h
    convert h.norm using 1
    ext n
    by_cases hn : n = 0
    · simp [coeff, DirichletCharacter.twistedVonMangoldtCoeff, hn, LSeries.term]
    · simp [coeff, DirichletCharacter.twistedVonMangoldtCoeff, hn, LSeries.term, mul_comm]
  have hnorm_eq (n : ℕ) (t : ℝ) :
      ‖DirichletCharacter.twistedVonMangoldtCoeff χ.1 n /
          (n : ℂ) ^ (α + t * I)‖ = coeff n := by
    have hα0 : α ≠ 0 := by linarith [hα]
    by_cases hn : n = 0
    · simp [coeff, DirichletCharacter.twistedVonMangoldtCoeff, hn]
    · unfold coeff
      rw [Complex.norm_div, Complex.norm_div,
        Complex.norm_natCast_cpow_of_re_ne_zero,
        Complex.norm_natCast_cpow_of_re_ne_zero]
      · simp [α]
      · simpa only [Complex.ofReal_re] using hα0
      · simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
          sub_zero, add_zero] using hα0
  have hF_int : ∀ n : ℕ, Integrable (F n) := by
    intro n
    by_cases hn : n = 0
    · simp [F, kernel, DirichletCharacter.twistedVonMangoldtCoeff, hn]
    · have hmeas :
        AEStronglyMeasurable (fun t : ℝ =>
          DirichletCharacter.twistedVonMangoldtCoeff χ.1 n /
            (n : ℂ) ^ (α + t * I)) := by
        apply Continuous.aestronglyMeasurable
        fun_prop (disch := simp [hn])
      have hbd : ∀ t : ℝ,
          ‖DirichletCharacter.twistedVonMangoldtCoeff χ.1 n /
            (n : ℂ) ^ (α + t * I)‖ ≤ coeff n := by
        intro t
        rw [hnorm_eq n t]
      simpa [F] using hkernel.bdd_mul hmeas (ae_of_all _ hbd)
  have hF_sum :
      Summable (fun n : ℕ => ∫ t : ℝ, ‖F n t‖) := by
    have hnorm_integral (n : ℕ) :
        (∫ t : ℝ, ‖F n t‖) = coeff n * ∫ t : ℝ, ‖kernel t‖ := by
      simp_rw [F, norm_mul, hnorm_eq]
      exact integral_const_mul _ _
    simpa only [hnorm_integral] using
      hcoeff.mul_right (∫ t : ℝ, ‖kernel t‖)
  calc
    chen1973Lemma6ActualPhi x d χ pp =
        ∑' n : ℕ,
          (DirichletCharacter.twistedVonMangoldtCoeff χ.1 n) *
            (chen1973PerronKernelFinite (x : ℝ) (X / n) : ℂ) := by
          simpa [X, DirichletCharacter.twistedVonMangoldtCoeff, mul_assoc, mul_left_comm,
            mul_comm, div_eq_mul_inv] using
            chen1973Lemma6ActualPhi_eq_tsum (x := x) (χ := χ) hp₁ hp₂
    _ = (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, ∑' n : ℕ, F n t) := by
          symm
          rw [← MeasureTheory.integral_tsum_of_summable_integral_norm hF_int hF_sum]
          rw [← tsum_mul_left]
          apply tsum_congr
          intro n
          by_cases hn : n = 0
          · simp [F, X, kernel, DirichletCharacter.twistedVonMangoldtCoeff, hn]
          · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
            have hterm :
                (((1 / (2 * Real.pi) : ℝ) : ℂ) *
                  ∫ t : ℝ, F n t) =
                DirichletCharacter.twistedVonMangoldtCoeff χ.1 n *
                  (chen1973PerronKernelFinite (x : ℝ) (X / n) : ℂ) := by
              rw [← MeasureTheory.integral_const_mul]
              rw [← Chen1973BromwichIdentity_on_alpha (x := x) hx
                (div_pos hX (by exact_mod_cast hnpos))]
              rw [← MeasureTheory.integral_const_mul,
                ← MeasureTheory.integral_const_mul]
              apply integral_congr_ae
              filter_upwards with t
              dsimp [F, kernel]
              have hpow :
                  (X : ℂ) ^ (α + t * I) / (n : ℂ) ^ (α + t * I) =
                    ((X / n : ℝ) : ℂ) ^ (α + t * I) := by
                have hmul := @mul_cpow_ofReal_nonneg (a := X / n) (b := (n : ℝ))
                  (r := α + t * I) (div_nonneg hX.le (Nat.cast_nonneg _))
                  (Nat.cast_nonneg _)
                push_cast at hmul
                apply (div_eq_iff (Complex.cpow_ne_zero_iff.mpr (Or.inl (by
                  exact_mod_cast hn)))).2
                simpa [div_mul_cancel₀, hn] using hmul
              rw [show chen1973Lemma6Alpha x = α by rfl]
              rw [← hpow]
              ring
            rw [hterm]
    _ = (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ,
          (-deriv χ.1.LFunction (α + t * I) / χ.1.LFunction (α + t * I)) *
            kernel t) := by
          congr 2
          ext t
          dsimp [F, kernel]
          rw [DirichletCharacter.neg_logDeriv_LFunction_eq_tsum_twistedVonMangoldtCoeff χ.1]
          · rw [tsum_mul_right]
          · simpa [α] using hα
    _ = _ := by simp [α, X, kernel]


/-- The totalized alpha-line `-L'/L` integrand.  On the conductor range
`1 < d`, the totalized values reduce definitionally to the primitive Dirichlet
`L`-function and its derivative. -/
def chen1973Lemma6AlphaNegLogDerivIntegrand
    (x d : ℕ) (χ : PrimitiveCharacter d) (pp : ℕ × ℕ) (t : ℝ) : ℂ :=
  (-chen1973PrimitiveLDeriv d (chen1973Lemma6Alpha x + t * I) χ /
      chen1973Lemma6PrimitiveLValue d (chen1973Lemma6Alpha x + t * I) χ) *
    (((x : ℝ) / ((pp.1 : ℝ) * pp.2) : ℂ) ^
        (chen1973Lemma6Alpha x + t * I) *
      chen1973MellinKernel (x : ℝ) (chen1973Lemma6Alpha x + t * I))

/-- The normalized full alpha-line transform for one primitive character and
one prime pair.  The factor is exactly `1/(2π)` and the logarithmic derivative
has the source sign `-L'/L`. -/
def chen1973Lemma6AlphaNegLogDerivIntegral
    (x d : ℕ) (χ : PrimitiveCharacter d) (pp : ℕ × ℕ) : ℂ :=
  (((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ t : ℝ, chen1973Lemma6AlphaNegLogDerivIntegrand x d χ pp t)

/-- Totalized form of the exact alpha-line bridge, suitable for finite sums. -/
theorem chen1973Lemma6ActualPhi_eq_alphaNegLogDerivIntegral
    {x d : ℕ} (χ : PrimitiveCharacter d) (hd : 1 < d)
    (hx : 3 ≤ x) {pp : ℕ × ℕ} (hp₁ : 0 < pp.1) (hp₂ : 0 < pp.2) :
    chen1973Lemma6ActualPhi x d χ pp =
      chen1973Lemma6AlphaNegLogDerivIntegral x d χ pp := by
  let : NeZero d := ⟨Nat.ne_zero_of_lt hd⟩
  have hχ : χ.1 ≠ 1 := primitiveCharacter_ne_one_of_one_lt hd χ
  simpa [chen1973Lemma6AlphaNegLogDerivIntegral,
    chen1973Lemma6AlphaNegLogDerivIntegrand,
    chen1973PrimitiveLDeriv, chen1973Lemma6PrimitiveLValue, dif_pos hd] using
    chen1973Lemma6ActualPhi_eq_negLogDerivIntegral_alpha χ hχ hx hp₁ hp₂

/-- Finite prime-pair lift of the alpha-line bridge. -/
def chen1973Lemma6AlphaNegLogDerivPrimePairSum
    (x d B k m : ℕ) (χ : PrimitiveCharacter d) : ℂ :=
  ∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
    (Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))⁻¹ *
      chen1973Lemma6AlphaNegLogDerivIntegral x d χ pp *
      χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d)

/-- The actual finite pair sum is exactly its alpha-line `-L'/L` lift. -/
theorem chen1973Lemma6PrimePairSum_eq_alphaNegLogDeriv
    {x d B k m : ℕ} (χ : PrimitiveCharacter d) (hd : 1 < d)
    (hx : 3 ≤ x) :
    (∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
      (Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))⁻¹ *
        chen1973Lemma6ActualPhi x d χ pp *
        χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d)) =
      chen1973Lemma6AlphaNegLogDerivPrimePairSum x d B k m χ := by
  unfold chen1973Lemma6AlphaNegLogDerivPrimePairSum
  apply Finset.sum_congr rfl
  intro pp hpp
  obtain ⟨hp₁, hp₂⟩ := chen1973Lemma6PrimePairShell_pos hpp
  rw [chen1973Lemma6ActualPhi_eq_alphaNegLogDerivIntegral χ hd hx hp₁ hp₂]

/-- The finite primitive-character lift on one conductor. -/
def chen1973Lemma6AlphaNegLogDerivCharacterSum
    (x d B k m : ℕ) : ℂ :=
  ∑ χ : PrimitiveCharacter d,
    star (χ.1 (x : ZMod d)) *
      chen1973Lemma6AlphaNegLogDerivPrimePairSum x d B k m χ

/-- The actual finite primitive-character sum is exactly its alpha-line
`-L'/L` lift. -/
theorem chen1973Lemma6CharacterSum_eq_alphaNegLogDeriv
    {x d B k m : ℕ} (hd : 1 < d) (hx : 3 ≤ x) :
    (∑ χ : PrimitiveCharacter d,
      star (χ.1 (x : ZMod d)) *
        ∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
          (Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))⁻¹ *
            chen1973Lemma6ActualPhi x d χ pp *
            χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d)) =
      chen1973Lemma6AlphaNegLogDerivCharacterSum x d B k m := by
  unfold chen1973Lemma6AlphaNegLogDerivCharacterSum
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [chen1973Lemma6PrimePairSum_eq_alphaNegLogDeriv χ hd hx]

/-- The conductor-block alpha-line expression, with the exact equation-(17)
weight and norm retained. -/
def chen1973Lemma6NmBlockAlphaNegLogDeriv
    (x L level B k m : ℕ) : ℝ :=
  ∑ d ∈ chen1973Lemma6ConductorBlock x L level,
    |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
      (3 : ℝ) ^ d.primeFactors.card / d *
      ‖chen1973Lemma6AlphaNegLogDerivCharacterSum x d B k m‖

/-- Exact conductor-block lift.  The positive level hypothesis is used only to
show that each conductor in the block is greater than one, hence every
primitive character in the block is nonprincipal. -/
theorem chen1973Lemma6NmBlockActual_eq_alphaNegLogDeriv
    {x L level B k m : ℕ} (hlevel : 1 ≤ level) (hx : 3 ≤ x) :
    chen1973Lemma6NmBlockActual x L level B k m =
      chen1973Lemma6NmBlockAlphaNegLogDeriv x L level B k m := by
  unfold chen1973Lemma6NmBlockActual chen1973Lemma6NmBlockAlphaNegLogDeriv
  apply Finset.sum_congr rfl
  intro d hd
  have hd1 : 1 < d := one_lt_of_mem_conductorBlock hlevel hd
  rw [chen1973Lemma6CharacterSum_eq_alphaNegLogDeriv hd1 hx]

end AnalyticNumberTheory.LargeSieve
