/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation17CorrectedKernel
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation19Final
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation19FixedPowerEnvelopes
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation19UniformMoments
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6M2Bound
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

noncomputable section

open Classical Complex Finset MeasureTheory Set
open scoped BigOperators ArithmeticFunction

namespace AnalyticNumberTheory.LargeSieve

/-- The squarefree-conductor loss denoted `I_{l,x}` between (18) and (19). -/
def chen1973Lemma6Equation20Ilx (x level : ℕ) : ℝ :=
  let Q : ℝ := (2 : ℝ) ^ (level : ℝ) * (Real.log x) ^ 100
  Real.exp (6 * Real.log Q / Real.log (Real.log Q))

/-- Chen's displayed complementary-cell cutoff before rounding. -/
def chen1973Lemma6Equation20HReal
    (x level k : ℕ) (ε : ℝ) : ℝ :=
  max
    ((2 : ℝ) ^ (2 * (level : ℝ) - k) *
      (x : ℝ) ^ (-(13 : ℝ) / 30) *
      (Real.log x) ^ 400 * chen1973Lemma6Equation20Ilx x level)
    ((x : ℝ) ^ ((1 : ℝ) / 2 - ε))

/-- The natural cutoff used in the complementary cell. -/
def chen1973Lemma6Equation20H
    (x level k : ℕ) (ε : ℝ) : ℕ :=
  ⌈chen1973Lemma6Equation20HReal x level k ε⌉₊

theorem chen1973Lemma6Equation20H_first_le
    (x level k : ℕ) (ε : ℝ) :
    (2 : ℝ) ^ (2 * (level : ℝ) - k) *
          (x : ℝ) ^ (-(13 : ℝ) / 30) *
          (Real.log x) ^ 400 * chen1973Lemma6Equation20Ilx x level ≤
      chen1973Lemma6Equation20H x level k ε := by
  apply le_trans (le_max_left _ _)
  exact Nat.le_ceil _

theorem chen1973Lemma6Equation20H_second_le
    (x level k : ℕ) (ε : ℝ) :
    (x : ℝ) ^ ((1 : ℝ) / 2 - ε) ≤
      chen1973Lemma6Equation20H x level k ε := by
  apply le_trans (le_max_right _ _)
  exact Nat.le_ceil _

private def eq20CorrectedLinearDecayWeight (v : ℝ) : ℝ :=
  (1 + v) / (1 + |v| ^ ((21 : ℝ) / 10))

private lemma eq20CorrectedLinearDecayWeight_nonneg {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ eq20CorrectedLinearDecayWeight v := by
  unfold eq20CorrectedLinearDecayWeight
  positivity

private lemma eq20CorrectedLinearDecayWeight_continuous :
    Continuous eq20CorrectedLinearDecayWeight := by
  unfold eq20CorrectedLinearDecayWeight
  refine Continuous.div (continuous_const.add continuous_id) ?_ ?_
  · refine continuous_const.add ?_
    exact (Real.continuous_rpow_const (by norm_num : 0 ≤ (21 : ℝ) / 10)).comp continuous_abs
  · intro v
    positivity

private theorem eq20CorrectedLinearDecayWeight_integrable :
    IntegrableOn eq20CorrectedLinearDecayWeight (Ioi (0 : ℝ)) := by
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num), integrableOn_union]
  constructor
  ·
    apply eq20CorrectedLinearDecayWeight_continuous.continuousOn.integrableOn_compact
      isCompact_Icc |>.mono_set
    exact Ioc_subset_Icc_self
  ·
    have hpow : IntegrableOn (fun v : ℝ => 2 * v ^ (-(11 : ℝ) / 10)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).const_mul 2
    apply Integrable.mono' hpow
    ·
      exact eq20CorrectedLinearDecayWeight_continuous.aestronglyMeasurable.restrict
    ·
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      have hv0 : 0 < v := zero_lt_one.trans hv
      have hv1 : 1 ≤ v := hv.le
      have hvq0 : 0 < v ^ ((21 : ℝ) / 10) := Real.rpow_pos_of_pos hv0 _
      have hnum : 1 + v ≤ 2 * v := by linarith
      have hden : v ^ ((21 : ℝ) / 10) ≤ 1 + v ^ ((21 : ℝ) / 10) := by linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (eq20CorrectedLinearDecayWeight_nonneg (show 0 ≤ v by linarith))]
      unfold eq20CorrectedLinearDecayWeight
      rw [abs_of_pos hv0]
      calc
        (1 + v) / (1 + v ^ ((21 : ℝ) / 10)) ≤
            (2 * v) / (v ^ ((21 : ℝ) / 10)) := by
          exact div_le_div₀ (by positivity) hnum hvq0 hden
        _ = 2 * v ^ (-(11 : ℝ) / 10) := by
          calc
            _ = 2 * (v ^ (1 : ℝ) / v ^ ((21 : ℝ) / 10)) := by
              rw [Real.rpow_one, mul_div_assoc]
            _ = _ := by rw [← Real.rpow_sub hv0]; norm_num

private def eq20CorrectedQuadraticDecayWeight (v : ℝ) : ℝ :=
  (1 + v) ^ (2 : ℕ) / (1 + |v| ^ (4 : ℕ))

private lemma eq20CorrectedQuadraticDecayWeight_continuous :
    Continuous eq20CorrectedQuadraticDecayWeight := by
  unfold eq20CorrectedQuadraticDecayWeight
  refine Continuous.div ((continuous_const.add continuous_id).pow 2) ?_ ?_
  · exact continuous_const.add (continuous_abs.pow 4)
  · intro v
    positivity

private theorem eq20CorrectedQuadraticDecayWeight_integrable :
    IntegrableOn eq20CorrectedQuadraticDecayWeight (Ioi (0 : ℝ)) := by
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num), integrableOn_union]
  constructor
  ·
    apply eq20CorrectedQuadraticDecayWeight_continuous.continuousOn.integrableOn_compact
      isCompact_Icc |>.mono_set
    exact Ioc_subset_Icc_self
  ·
    have hpow : IntegrableOn (fun v : ℝ => 4 * v ^ (-2 : ℝ)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) zero_lt_one).const_mul 4
    apply Integrable.mono' hpow
    ·
      exact eq20CorrectedQuadraticDecayWeight_continuous.aestronglyMeasurable.restrict
    ·
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      have hv0 : 0 < v := zero_lt_one.trans hv
      have hv1 : 1 ≤ v := hv.le
      have hnum : (1 + v) ^ (2 : ℕ) ≤ 4 * v ^ (2 : ℕ) := by
        nlinarith [sq_nonneg (v - 1)]
      have hden : (v : ℝ) ^ (4 : ℕ) ≤ 1 + v ^ (4 : ℕ) := by linarith
      rw [Real.norm_eq_abs]
      have hnonneg : 0 ≤ eq20CorrectedQuadraticDecayWeight v := by
        unfold eq20CorrectedQuadraticDecayWeight
        positivity
      rw [abs_of_nonneg hnonneg]
      unfold eq20CorrectedQuadraticDecayWeight
      rw [abs_of_pos hv0]
      calc
        (1 + v) ^ (2 : ℕ) / (1 + v ^ (4 : ℕ)) ≤
            (4 * v ^ (2 : ℕ)) / (v ^ (4 : ℕ)) := by
          exact div_le_div₀ (by positivity) hnum (by positivity) hden
        _ = 4 * v ^ (-2 : ℝ) := by
          rw [mul_div_assoc, ← Real.rpow_natCast v 2, ← Real.rpow_natCast v 4,
            ← Real.rpow_sub hv0]
          norm_num

/-- Corrected-source first half-line integral on the alpha line. -/
def chen1973Lemma6Eq20CorrectedFirstIntegral
    (x L level B k m H : ℕ) : ℝ :=
  ∫ v in Ioi (0 : ℝ),
    chen1973Lemma6A x L level B k m H (chen1973Lemma6Alpha x + v * I) /
      chen1973Lemma6Eq17CorrectedKernel x (chen1973Lemma6Alpha x + v * I)

/-- Corrected-source second half-line integral on the beta line. -/
def chen1973Lemma6Eq20CorrectedSecondIntegral
    (x L level B k m H : ℕ) : ℝ :=
  ∫ v in Ioi (0 : ℝ),
    chen1973Lemma6B x L level B k m H (chen1973Lemma6Beta x + v * I) /
      chen1973Lemma6Eq17CorrectedKernel x (chen1973Lemma6Beta x + v * I)

/-- Corrected-source contour majorization for the complementary cell. -/
def Chen1973Equation20CorrectedContourMajorization
    (x L level B k m H : ℕ) : Prop :=
  chen1973Lemma6NmBlockActual x L level B k m ≤
    2 * (x : ℝ) * Real.log x ^ 2 *
        chen1973Lemma6Eq20CorrectedFirstIntegral x L level B k m H +
      2 * (x : ℝ) ^ ((1 : ℝ) / 2) *
        chen1973Lemma6Eq20CorrectedSecondIntegral x L level B k m H

/-- Explicit scalar envelope for the alpha-line numerator after the fixed pair
moment and the `v`-windowed uniform equation-(14) bound. -/
def chen1973Lemma6Eq20CorrectedFirstPointwiseEnvelope
    (x L level B k m H D Q : ℕ) (v : ℝ) : ℝ :=
  Real.sqrt
      (chen1973Lemma6Eq19PairSecondMoment x L level B k m
        (chen1973Lemma6Alpha x + v * I)) *
    Real.sqrt
      (chen1973Lemma6Eq19I x L level *
        (2 * chen1973Lemma6Eq19SharpConstant *
            ((Q : ℝ) + ((H * H : ℕ) : ℝ) / D) *
            (1 + Real.log (H * H : ℕ)) ^ 4 +
          2 * (Q : ℝ) * chen1973Lemma6Eq19OneSubUniformEnvelope H Q
            (chen1973Lemma6Alpha x) v))

/-- Explicit scalar envelope for the beta-line numerator after the fixed pair
moment and the genuine multiplicative `2,4,4` Hölder reduction. -/
def chen1973Lemma6Eq20CorrectedSecondPointwiseEnvelope
    (x L level B k m H D Q : ℕ) (r v : ℝ) : ℝ :=
  Real.sqrt
      (chen1973Lemma6Eq19PairSecondMoment x L level B k m
        (chen1973Lemma6Beta x + v * I)) *
    Real.sqrt
      (Real.sqrt
          (chen1973Lemma6Eq19I x L level * (Q : ℝ) *
            ((chen1973Lemma6Eq19CircleFourthEnvelopeUniform Q
                (chen1973Lemma6Beta x) v r + 1) / r) ^ 4) *
        Real.sqrt
          (chen1973Lemma6Eq19I x L level *
            (chen1973Lemma6Eq19SharpConstant *
              ((Q : ℝ) + ((H * H : ℕ) : ℝ) / D) *
              (1 + Real.log (H * H : ℕ)) ^ 4)))

theorem chen1973Lemma6_eq20_first_le_pointwiseEnvelope
    (x L level B k m H D Q : ℕ) (v : ℝ)
    (hx : 2 ≤ x) (hH : 0 < H) (hD : 0 < D) (hDQ : D < Q)
    (hcell : chen1973Lemma6ConductorBlock x L level ⊆ Ioc D Q) (hv : 0 ≤ v) :
    chen1973Lemma6A x L level B k m H (chen1973Lemma6Alpha x + v * I) ≤
      chen1973Lemma6Eq20CorrectedFirstPointwiseEnvelope x L level B k m H D Q v := by
  have hα : 1 ≤ chen1973Lemma6Alpha x := by
    unfold chen1973Lemma6Alpha
    have hlog : 0 < Real.log (x : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < x by omega))
    linarith [one_div_pos.mpr hlog]
  have ho := chen1973Lemma6_eq19_oneSub_second_moment_uniform
    x L level H D Q (chen1973Lemma6Alpha x) v hH hD hDQ hα hv hcell v
    (by constructor <;> linarith)
  have hbase := chen1973Lemma6A_le_moment_product x L level B k m H
    (chen1973Lemma6Alpha x + v * I)
  unfold chen1973Lemma6Eq20CorrectedFirstPointwiseEnvelope
  exact hbase.trans (mul_le_mul le_rfl (Real.sqrt_le_sqrt ho)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

theorem chen1973Lemma6_eq20_second_le_pointwiseEnvelope
    (x L level B k m H D Q : ℕ) (r v : ℝ)
    (hD : 0 < D) (hQ : 2 ≤ Q) (hr : 0 < r)
    (hcellIoc : chen1973Lemma6ConductorBlock x L level ⊆ Ioc D Q)
    (hcellIcc : chen1973Lemma6ConductorBlock x L level ⊆ Icc 2 Q)
    (hdom :
      ∀ t ∈ Set.Icc (-v) v,
        Chen1973Lemma3Domain (chen1973Lemma6Beta x + t * I)
          (chen1973Lemma6Beta x) t)
    (hspheres :
      ∀ t ∈ Set.Icc (-v) v, ∀ z ∈ Metric.sphere (chen1973Lemma6Beta x + t * I) r,
        Chen1973Lemma3Domain z z.re z.im)
    (hv : 0 ≤ v) :
    chen1973Lemma6B x L level B k m H (chen1973Lemma6Beta x + v * I) ≤
      chen1973Lemma6Eq20CorrectedSecondPointwiseEnvelope
        x L level B k m H D Q r v := by
  have hL := chen1973Lemma6_eq19_LDeriv_fourth_moment_uniform
    x L level Q (chen1973Lemma6Beta x) v r hQ hv hr hcellIcc hspheres v
    (by constructor <;> linarith)
  have hM := chen1973Lemma6_eq19_mobius_fourth_moment_uniform
    x L level H D Q (chen1973Lemma6Beta x) v hD hcellIoc hdom v
    (by constructor <;> linarith)
  have hbase := chen1973Lemma6B_le_moment_product x L level B k m H
    (chen1973Lemma6Beta x + v * I)
  unfold chen1973Lemma6Eq20CorrectedSecondPointwiseEnvelope
  refine hbase.trans ?_
  gcongr

private theorem eq20_corrected_inv_le_linearDecay
    {x : ℕ} (hx : 3 ≤ x) {σ v : ℝ} (hσ : 0 < σ)
    (horder : 3 ≤ chen1973PerronOrder (x : ℝ) + 1) :
    (chen1973Lemma6Eq17CorrectedKernel x (σ + v * I))⁻¹ ≤
      (2 * Real.log x ^ ((231 : ℝ) / 100) / σ) /
        (1 + |v| ^ ((21 : ℝ) / 10)) := by
  exact chen1973Lemma6_eq17_correctedKernel_inv_le_linearDecay hx hσ horder

private theorem eq20_corrected_inv_le_quadraticDecay
    {x : ℕ} (hx : 3 ≤ x) {σ v : ℝ} (hσ : 0 < σ)
    (horder : 4 ≤ chen1973PerronOrder (x : ℝ) + 1) :
    (chen1973Lemma6Eq17CorrectedKernel x (σ + v * I))⁻¹ ≤
      (2 * Real.log x ^ ((22 : ℝ) / 5) / σ) / (1 + |v| ^ (4 : ℕ)) := by
  have hfac := chen1973Lemma6_eq17_correctedFactor_vertical_inv_le_fourth_power
    hx σ v horder
  have hnorm : σ ≤ ‖((σ : ℂ) + (v : ℂ) * I)‖ := by
    calc
      σ = |((σ : ℂ) + (v : ℂ) * I).re| := by simp [abs_of_pos hσ]
      _ ≤ ‖((σ : ℂ) + (v : ℂ) * I)‖ := Complex.abs_re_le_norm _
  have hcalc :
      ‖((σ : ℂ) + (v : ℂ) * I)‖⁻¹ *
          (1 + (‖((σ : ℂ) + (v : ℂ) * I)‖ /
            chen1973PerronScale (x : ℝ)) ^
              (chen1973PerronOrder (x : ℝ) + 1))⁻¹ ≤
      σ⁻¹ * (2 * Real.log x ^ ((22 : ℝ) / 5) / (1 + |v| ^ (4 : ℕ))) := by
    have hfac0 : 0 ≤
        (1 + (‖((σ : ℂ) + (v : ℂ) * I)‖ /
          chen1973PerronScale (x : ℝ)) ^
            (chen1973PerronOrder (x : ℝ) + 1))⁻¹ := by
      apply inv_nonneg.mpr
      have hscale : 0 < chen1973PerronScale (x : ℝ) :=
        chen1973Lemma6_eq17_perronScale_pos (by omega)
      linarith [pow_nonneg
        (div_nonneg (norm_nonneg ((σ : ℂ) + (v : ℂ) * I)) hscale.le)
        (chen1973PerronOrder (x : ℝ) + 1)]
    exact mul_le_mul (inv_anti₀ hσ hnorm) hfac hfac0 (inv_nonneg.mpr hσ.le)
  simpa [chen1973Lemma6Eq17CorrectedKernel, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    using hcalc

private theorem chen1973Lemma6_eq20_corrected_integrable_of_linear_growth
    {x : ℕ} {σ G : ℝ} (hx : 3 ≤ x) (hσ : 0 < σ)
    (horder : 3 ≤ chen1973PerronOrder (x : ℝ) + 1) (F : ℝ → ℝ)
    (hFcont : ContinuousOn F (Ici 0))
    (hFnonneg : ∀ v ∈ Ioi (0 : ℝ), 0 ≤ F v)
    (hFgrowth : ∀ v ∈ Ioi (0 : ℝ), F v ≤ G * (1 + v)) :
    IntegrableOn (fun v : ℝ =>
      F v / chen1973Lemma6Eq17CorrectedKernel x (σ + v * I)) (Ioi 0) := by
  let C := 2 * Real.log x ^ ((231 : ℝ) / 100) / σ
  have hmajor : IntegrableOn (fun v => C * G * eq20CorrectedLinearDecayWeight v) (Ioi (0 : ℝ)) :=
    eq20CorrectedLinearDecayWeight_integrable.const_mul (C * G)
  apply Integrable.mono' hmajor
  ·
    have hcont :
        ContinuousOn (fun v : ℝ =>
          F v / chen1973Lemma6Eq17CorrectedKernel x (σ + v * I)) (Ioi 0) := by
      apply ContinuousOn.div
      · exact hFcont.mono Ioi_subset_Ici_self
      ·
        unfold chen1973Lemma6Eq17CorrectedKernel
        fun_prop
      ·
        intro v hv
        exact (chen1973Lemma6_eq17_correctedKernel_pos
          (x := x) (v := v) (by omega : 1 < x) hσ).ne'
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  ·
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hkpos := chen1973Lemma6_eq17_correctedKernel_pos
      (x := x) (v := v) (by omega : 1 < x) hσ
    have hinv := eq20_corrected_inv_le_linearDecay (v := v) hx hσ horder
    have hf0 := hFnonneg v hv
    have hfg := hFgrowth v hv
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hf0 hkpos.le), div_eq_mul_inv]
    calc
      F v * (chen1973Lemma6Eq17CorrectedKernel x (σ + v * I))⁻¹ ≤
          (G * (1 + v)) * (C / (1 + |v| ^ ((21 : ℝ) / 10))) := by
        exact mul_le_mul hfg (by simpa [C] using hinv)
          (inv_nonneg.mpr hkpos.le) (hf0.trans hfg)
      _ = C * G * eq20CorrectedLinearDecayWeight v := by
        unfold eq20CorrectedLinearDecayWeight
        ring

private theorem chen1973Lemma6_eq20_corrected_integrable_of_quadratic_growth
    {x : ℕ} {σ G : ℝ} (hx : 3 ≤ x) (hσ : 0 < σ)
    (horder : 4 ≤ chen1973PerronOrder (x : ℝ) + 1) (F : ℝ → ℝ)
    (hFcont : ContinuousOn F (Ici 0))
    (hFnonneg : ∀ v ∈ Ioi (0 : ℝ), 0 ≤ F v)
    (hFgrowth : ∀ v ∈ Ioi (0 : ℝ), F v ≤ G * (1 + v) ^ (2 : ℕ)) :
    IntegrableOn (fun v : ℝ =>
      F v / chen1973Lemma6Eq17CorrectedKernel x (σ + v * I)) (Ioi 0) := by
  let C := 2 * Real.log x ^ ((22 : ℝ) / 5) / σ
  have hmajor :
      IntegrableOn (fun v => C * G * eq20CorrectedQuadraticDecayWeight v) (Ioi (0 : ℝ)) :=
    eq20CorrectedQuadraticDecayWeight_integrable.const_mul (C * G)
  apply Integrable.mono' hmajor
  ·
    have hcont :
        ContinuousOn (fun v : ℝ =>
          F v / chen1973Lemma6Eq17CorrectedKernel x (σ + v * I)) (Ioi 0) := by
      apply ContinuousOn.div
      · exact hFcont.mono Ioi_subset_Ici_self
      ·
        unfold chen1973Lemma6Eq17CorrectedKernel
        fun_prop
      ·
        intro v hv
        exact (chen1973Lemma6_eq17_correctedKernel_pos
          (x := x) (v := v) (by omega : 1 < x) hσ).ne'
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  ·
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hkpos := chen1973Lemma6_eq17_correctedKernel_pos
      (x := x) (v := v) (by omega : 1 < x) hσ
    have hinv := eq20_corrected_inv_le_quadraticDecay (v := v) hx hσ horder
    have hf0 := hFnonneg v hv
    have hfg := hFgrowth v hv
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hf0 hkpos.le), div_eq_mul_inv]
    calc
      F v * (chen1973Lemma6Eq17CorrectedKernel x (σ + v * I))⁻¹ ≤
          (G * (1 + v) ^ (2 : ℕ)) * (C / (1 + |v| ^ (4 : ℕ))) := by
        exact mul_le_mul hfg (by simpa [C] using hinv)
          (inv_nonneg.mpr hkpos.le) (hf0.trans hfg)
      _ = C * G * eq20CorrectedQuadraticDecayWeight v := by
        unfold eq20CorrectedQuadraticDecayWeight
        ring

theorem chen1973Lemma6_equation20_corrected_complementary_cell
    {x L level B D k m Q : ℕ} {ε C₁ C₂ G₁ G₂ r : ℝ}
    (_hcell20 : chen1973Lemma6Eq20Cell x L B D level k)
    (hx : 3 ≤ x) (hD : 0 < D) (hDQ : D < Q) (hQ : 2 ≤ Q) (hr : 0 < r)
    (horder21 : 3 ≤ chen1973PerronOrder (x : ℝ) + 1)
    (horder4 : 4 ≤ chen1973PerronOrder (x : ℝ) + 1)
    (hcellIoc : chen1973Lemma6ConductorBlock x L level ⊆ Ioc D Q)
    (hcellIcc : chen1973Lemma6ConductorBlock x L level ⊆ Icc 2 Q)
    (hcontA : ContinuousOn (fun v : ℝ =>
      chen1973Lemma6A x L level B k m (chen1973Lemma6Equation20H x level k ε)
        (chen1973Lemma6Alpha x + v * I)) (Ici 0))
    (hcontB : ContinuousOn (fun v : ℝ =>
      chen1973Lemma6B x L level B k m (chen1973Lemma6Equation20H x level k ε)
        (chen1973Lemma6Beta x + v * I)) (Ici 0))
    (hdomB : ∀ t : ℝ,
      Chen1973Lemma3Domain (chen1973Lemma6Beta x + t * I)
        (chen1973Lemma6Beta x) t)
    (hspheres : ∀ t : ℝ, ∀ z ∈ Metric.sphere (chen1973Lemma6Beta x + t * I) r,
      Chen1973Lemma3Domain z z.re z.im)
    (hgrowth₁ : ∀ v ∈ Ioi (0 : ℝ),
      chen1973Lemma6Eq20CorrectedFirstPointwiseEnvelope x L level B k m
          (chen1973Lemma6Equation20H x level k ε) D Q v ≤
        G₁ * (1 + v))
    (hgrowth₂ : ∀ v ∈ Ioi (0 : ℝ),
      chen1973Lemma6Eq20CorrectedSecondPointwiseEnvelope x L level B k m
          (chen1973Lemma6Equation20H x level k ε) D Q r v ≤
        G₂ * (1 + v) ^ (2 : ℕ))
    (hpay₁ :
      (2 * Real.log x ^ ((231 : ℝ) / 100) / chen1973Lemma6Alpha x) * G₁ *
          (∫ v in Ioi (0 : ℝ), eq20CorrectedLinearDecayWeight v) ≤
        C₁ / Real.log x ^ 22)
    (hpay₂ :
      (2 * Real.log x ^ ((22 : ℝ) / 5) / chen1973Lemma6Beta x) * G₂ *
          (∫ v in Ioi (0 : ℝ), eq20CorrectedQuadraticDecayWeight v) ≤
        C₂ * (x : ℝ) ^ ((1 : ℝ) / 2) / Real.log x ^ 20)
    (hcontour : Chen1973Equation20CorrectedContourMajorization x L level B k m
      (chen1973Lemma6Equation20H x level k ε)) :
    chen1973Lemma6NmBlockActual x L level B k m ≤
      2 * (C₁ + C₂) * (x : ℝ) / Real.log x ^ 20 := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hα : 1 ≤ chen1973Lemma6Alpha x := by
    unfold chen1973Lemma6Alpha
    linarith [one_div_pos.mpr hlog]
  have hβ : 0 < chen1973Lemma6Beta x := by
    unfold chen1973Lemma6Beta
    linarith [one_div_pos.mpr hlog]
  have hHpos : 0 < chen1973Lemma6Equation20H x level k ε := by
    have hHposR : (0 : ℝ) < (chen1973Lemma6Equation20H x level k ε : ℝ) :=
      (Real.rpow_pos_of_pos hx0 _).trans_le
        (chen1973Lemma6Equation20H_second_le x level k ε)
    exact_mod_cast hHposR
  have hfirstPoint : ∀ v ∈ Ioi (0 : ℝ),
      chen1973Lemma6A x L level B k m (chen1973Lemma6Equation20H x level k ε)
        (chen1973Lemma6Alpha x + v * I) ≤ G₁ * (1 + v) := by
    intro v hv
    exact (chen1973Lemma6_eq20_first_le_pointwiseEnvelope
      x L level B k m (chen1973Lemma6Equation20H x level k ε) D Q v
      (by omega) hHpos hD hDQ hcellIoc (le_of_lt (mem_Ioi.mp hv))).trans
        (hgrowth₁ v hv)
  have hsecondPoint : ∀ v ∈ Ioi (0 : ℝ),
      chen1973Lemma6B x L level B k m (chen1973Lemma6Equation20H x level k ε)
        (chen1973Lemma6Beta x + v * I) ≤ G₂ * (1 + v) ^ (2 : ℕ) := by
    intro v hv
    have hdom :
        ∀ t ∈ Set.Icc (-v) v,
          Chen1973Lemma3Domain (chen1973Lemma6Beta x + t * I)
            (chen1973Lemma6Beta x) t := by
      intro t ht
      exact hdomB t
    have hsphere :
        ∀ t ∈ Set.Icc (-v) v, ∀ z ∈ Metric.sphere (chen1973Lemma6Beta x + t * I) r,
          Chen1973Lemma3Domain z z.re z.im := by
      intro t ht z hz
      exact hspheres t z hz
    exact (chen1973Lemma6_eq20_second_le_pointwiseEnvelope
      x L level B k m (chen1973Lemma6Equation20H x level k ε) D Q r v
      hD hQ hr hcellIoc hcellIcc hdom hsphere (le_of_lt (mem_Ioi.mp hv))).trans
        (hgrowth₂ v hv)
  have hAnonneg : ∀ v ∈ Ioi (0 : ℝ), 0 ≤
      chen1973Lemma6A x L level B k m (chen1973Lemma6Equation20H x level k ε)
        (chen1973Lemma6Alpha x + v * I) := by
    intro v hv
    unfold chen1973Lemma6A
    positivity
  have hBnonneg : ∀ v ∈ Ioi (0 : ℝ), 0 ≤
      chen1973Lemma6B x L level B k m (chen1973Lemma6Equation20H x level k ε)
        (chen1973Lemma6Beta x + v * I) := by
    intro v hv
    unfold chen1973Lemma6B
    positivity
  have hintA := chen1973Lemma6_eq20_corrected_integrable_of_linear_growth
    hx (lt_of_lt_of_le zero_lt_one hα) horder21 _ hcontA hAnonneg hfirstPoint
  have hintB := chen1973Lemma6_eq20_corrected_integrable_of_quadratic_growth
    hx hβ horder4 _ hcontB hBnonneg hsecondPoint
  have hmajorA :
      IntegrableOn (fun v : ℝ =>
        (2 * Real.log x ^ ((231 : ℝ) / 100) / chen1973Lemma6Alpha x) *
          G₁ * eq20CorrectedLinearDecayWeight v) (Ioi (0 : ℝ)) :=
    eq20CorrectedLinearDecayWeight_integrable.const_mul
      ((2 * Real.log x ^ ((231 : ℝ) / 100) / chen1973Lemma6Alpha x) * G₁)
  have hmajorB :
      IntegrableOn (fun v : ℝ =>
        (2 * Real.log x ^ ((22 : ℝ) / 5) / chen1973Lemma6Beta x) *
          G₂ * eq20CorrectedQuadraticDecayWeight v) (Ioi (0 : ℝ)) :=
    eq20CorrectedQuadraticDecayWeight_integrable.const_mul
      ((2 * Real.log x ^ ((22 : ℝ) / 5) / chen1973Lemma6Beta x) * G₂)
  have hfirst :
      chen1973Lemma6Eq20CorrectedFirstIntegral x L level B k m
        (chen1973Lemma6Equation20H x level k ε) ≤ C₁ / Real.log x ^ 22 := by
    unfold chen1973Lemma6Eq20CorrectedFirstIntegral
    calc
      _ ≤ ∫ v in Ioi (0 : ℝ),
          (2 * Real.log x ^ ((231 : ℝ) / 100) / chen1973Lemma6Alpha x) *
            G₁ * eq20CorrectedLinearDecayWeight v := by
        apply integral_mono_ae hintA hmajorA
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
        rw [div_eq_mul_inv]
        have hinv := eq20_corrected_inv_le_linearDecay (v := v)
          hx (lt_of_lt_of_le zero_lt_one hα) horder21
        exact (mul_le_mul (hfirstPoint v hv) (by simpa using hinv)
          (inv_nonneg.mpr (chen1973Lemma6_eq17_correctedKernel_pos
            (x := x) (v := v) (by omega : 1 < x)
            (lt_of_lt_of_le zero_lt_one hα)).le)
          ((hAnonneg v hv).trans (hfirstPoint v hv))).trans_eq (by
            unfold eq20CorrectedLinearDecayWeight
            ring)
      _ = (2 * Real.log x ^ ((231 : ℝ) / 100) / chen1973Lemma6Alpha x) * G₁ *
          (∫ v in Ioi (0 : ℝ), eq20CorrectedLinearDecayWeight v) := by
        rw [MeasureTheory.integral_const_mul]
      _ ≤ _ := hpay₁
  have hsecond :
      chen1973Lemma6Eq20CorrectedSecondIntegral x L level B k m
        (chen1973Lemma6Equation20H x level k ε) ≤
        C₂ * (x : ℝ) ^ ((1 : ℝ) / 2) / Real.log x ^ 20 := by
    unfold chen1973Lemma6Eq20CorrectedSecondIntegral
    calc
      _ ≤ ∫ v in Ioi (0 : ℝ),
          (2 * Real.log x ^ ((22 : ℝ) / 5) / chen1973Lemma6Beta x) *
            G₂ * eq20CorrectedQuadraticDecayWeight v := by
        apply integral_mono_ae hintB hmajorB
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
        rw [div_eq_mul_inv]
        have hinv := eq20_corrected_inv_le_quadraticDecay (v := v) hx hβ horder4
        exact (mul_le_mul (hsecondPoint v hv) (by simpa using hinv)
          (inv_nonneg.mpr (chen1973Lemma6_eq17_correctedKernel_pos
            (x := x) (v := v) (by omega : 1 < x) hβ).le)
          ((hBnonneg v hv).trans (hsecondPoint v hv))).trans_eq (by
            unfold eq20CorrectedQuadraticDecayWeight
            ring)
      _ = (2 * Real.log x ^ ((22 : ℝ) / 5) / chen1973Lemma6Beta x) * G₂ *
          (∫ v in Ioi (0 : ℝ), eq20CorrectedQuadraticDecayWeight v) := by
        rw [MeasureTheory.integral_const_mul]
      _ ≤ _ := hpay₂
  unfold Chen1973Equation20CorrectedContourMajorization at hcontour
  refine hcontour.trans ?_
  calc
    2 * (x : ℝ) * Real.log x ^ 2 *
          chen1973Lemma6Eq20CorrectedFirstIntegral x L level B k m
            (chen1973Lemma6Equation20H x level k ε) +
        2 * (x : ℝ) ^ ((1 : ℝ) / 2) *
          chen1973Lemma6Eq20CorrectedSecondIntegral x L level B k m
            (chen1973Lemma6Equation20H x level k ε) ≤
      2 * (x : ℝ) * Real.log x ^ 2 * (C₁ / Real.log x ^ 22) +
        2 * (x : ℝ) ^ ((1 : ℝ) / 2) *
          (C₂ * (x : ℝ) ^ ((1 : ℝ) / 2) / Real.log x ^ 20) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hfirst (by positivity))
        (mul_le_mul_of_nonneg_left hsecond (by positivity))
    _ = 2 * (C₁ + C₂) * (x : ℝ) / Real.log x ^ 20 := by
      have hxpow :
          (x : ℝ) ^ ((1 : ℝ) / 2) * (x : ℝ) ^ ((1 : ℝ) / 2) = x := by
        rw [← Real.rpow_add hx0]
        norm_num
      have hfirstTerm :
          2 * (x : ℝ) * Real.log x ^ 2 * (C₁ / Real.log x ^ 22) =
            2 * C₁ * (x : ℝ) / Real.log x ^ 20 := by
        field_simp [hlog.ne']
      have hsecondTerm :
          2 * (x : ℝ) ^ ((1 : ℝ) / 2) *
              (C₂ * (x : ℝ) ^ ((1 : ℝ) / 2) / Real.log x ^ 20) =
            2 * C₂ * (x : ℝ) / Real.log x ^ 20 := by
        calc
          _ = 2 * C₂ *
                ((x : ℝ) ^ ((1 : ℝ) / 2) * (x : ℝ) ^ ((1 : ℝ) / 2)) /
              Real.log x ^ 20 := by ring
          _ = _ := by rw [hxpow]
      rw [hfirstTerm, hsecondTerm]
      ring

end AnalyticNumberTheory.LargeSieve
