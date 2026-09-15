import AnalyticNumberTheory.Mertens.PartialSummation
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# An Abelian remainder estimate

This file isolates the dominated-convergence argument used after the
logarithmic change of variables in Mertens' theorem.  A fixed positive cutoff
avoids imposing artificial hypotheses at the origin.
-/

namespace AnalyticNumberTheory.Mertens

open Filter Topology Real Set MeasureTheory

/-- The elementary uniform estimate behind the Abelian remainder argument. -/
theorem mul_exp_neg_mul_le_inv {ε u : ℝ} (hε : 0 < ε) (hu : 0 < u) :
    ε * Real.exp (-(ε * u)) ≤ u⁻¹ := by
  have hmain : (ε * u) * Real.exp (-(ε * u)) ≤ 1 :=
    (Real.mul_exp_neg_le_exp_neg_one (ε * u)).trans
      (Real.exp_le_one_iff.mpr (by norm_num))
  calc
    ε * Real.exp (-(ε * u)) =
        ((ε * u) * Real.exp (-(ε * u))) / u := by field_simp
    _ ≤ 1 / u := (div_le_div_iff_of_pos_right hu).2 hmain
    _ = u⁻¹ := by simp

/-- A reusable Abelian remainder lemma on a half-line with positive cutoff.

The weighted integrability assumption is exactly what is supplied by local
integrability together with an eventual `O(1/u)` estimate: on compact pieces
division by `u` is harmless, while on the tail it gives an integrable
`O(1/u^2)` majorant.
-/
theorem tendsto_mul_integral_exp_remainder_of_integrable_norm_div
    {E : ℝ → ℂ} {a : ℝ} (ha : 0 < a)
    (hE : AEStronglyMeasurable E (volume.restrict (Ioi a)))
    (hdiv : IntegrableOn (fun u : ℝ => ‖E u‖ / u) (Ioi a)) :
    Tendsto
      (fun ε : ℝ =>
        (ε : ℂ) * ∫ u : ℝ in Ioi a,
          E u * (Real.exp (-(ε * u)) : ℂ))
      (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
  let μ := volume.restrict (Ioi a)
  let F : ℝ → ℝ → ℂ := fun ε u =>
    (ε : ℂ) * (E u * (Real.exp (-(ε * u)) : ℂ))
  have hlim : ∀ᵐ u ∂μ, Tendsto (fun ε => F ε u)
      (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
    refine ae_of_all _ fun u => ?_
    have hc : ContinuousAt (fun ε : ℝ => F ε u) 0 := by
      dsimp only [F]
      fun_prop
    have hsub : nhdsWithin (0 : ℝ) (Ioi 0) ≤ 𝓝 0 := inf_le_left
    simpa [F] using hc.tendsto.mono_left hsub
  have hmeas : ∀ᶠ ε in nhdsWithin 0 (Ioi 0),
      AEStronglyMeasurable (F ε) μ := by
    filter_upwards with ε
    exact (hE.mul
      (Complex.continuous_ofReal.comp
        (Real.continuous_exp.comp
          (continuous_const.mul continuous_id).neg)).aestronglyMeasurable).const_mul ε
  have hbound : ∀ᶠ ε in nhdsWithin 0 (Ioi 0),
      ∀ᵐ u ∂μ, ‖F ε u‖ ≤ ‖E u‖ / u := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    simp only [mem_Ioi] at hε hu
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      ε * (‖E u‖ * Real.exp (-(ε * u))) =
          ‖E u‖ * (ε * Real.exp (-(ε * u))) := by ring
      _ ≤ ‖E u‖ * u⁻¹ := mul_le_mul_of_nonneg_left
        (mul_exp_neg_mul_le_inv hε (ha.trans hu)) (norm_nonneg _)
      _ = ‖E u‖ / u := by rw [div_eq_mul_inv]
  have ht := tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (F := F) (f := fun _ => (0 : ℂ))
    (fun u => ‖E u‖ / u) hmeas hbound hdiv hlim
  simpa only [μ, F, integral_zero, integral_const_mul] using ht

/-- Local weighted integrability plus an explicit `C/u` tail bound gives the
global weighted integrability needed by the Abelian remainder lemma. -/
theorem integrableOn_norm_div_of_compact_of_inv_tail
    {E : ℝ → ℂ} {a A C : ℝ} (ha : 0 < a) (haA : a ≤ A)
    (hcompact : IntegrableOn (fun u : ℝ => ‖E u‖ / u) (Ioc a A))
    (hmeas : AEStronglyMeasurable (fun u : ℝ => ‖E u‖ / u)
      (volume.restrict (Ioi A)))
    (htail : ∀ u ∈ Ioi A, ‖E u‖ ≤ C / u) :
    IntegrableOn (fun u : ℝ => ‖E u‖ / u) (Ioi a) := by
  have hA : 0 < A := ha.trans_le haA
  have hpow : IntegrableOn (fun u : ℝ => u ^ (-2 : ℝ)) (Ioi A) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hA
  have hmajor : IntegrableOn (fun u : ℝ => C * u ^ (-2 : ℝ)) (Ioi A) :=
    hpow.const_mul C
  have htailInt : IntegrableOn (fun u : ℝ => ‖E u‖ / u) (Ioi A) := by
    apply Integrable.mono' hmajor hmeas
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := hA.trans hu
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg _) hu0.le)]
    calc
      ‖E u‖ / u ≤ (C / u) / u :=
        div_le_div_of_nonneg_right (htail u hu) hu0.le
      _ = C * u ^ (-2 : ℝ) := by
        rw [show (-2 : ℝ) = (-1 : ℝ) + (-1 : ℝ) by norm_num]
        rw [Real.rpow_add hu0, Real.rpow_neg_one]
        ring
  rw [← Ioc_union_Ioi_eq_Ioi haA]
  exact hcompact.union htailInt

/-- The practical cutoff form: a compact initial piece and an eventual
`C/u` estimate imply that the exponentially damped remainder vanishes in the
Abelian limit `ε → 0+`. -/
theorem tendsto_mul_integral_exp_remainder_of_inv_tail
    {E : ℝ → ℂ} {a A C : ℝ} (ha : 0 < a) (haA : a ≤ A)
    (hE : AEStronglyMeasurable E (volume.restrict (Ioi a)))
    (hcompact : IntegrableOn (fun u : ℝ => ‖E u‖ / u) (Ioc a A))
    (hmeas : AEStronglyMeasurable (fun u : ℝ => ‖E u‖ / u)
      (volume.restrict (Ioi A)))
    (htail : ∀ u ∈ Ioi A, ‖E u‖ ≤ C / u) :
    Tendsto
      (fun ε : ℝ =>
        (ε : ℂ) * ∫ u : ℝ in Ioi a,
          E u * (Real.exp (-(ε * u)) : ℂ))
      (nhdsWithin 0 (Ioi 0)) (𝓝 0) :=
  tendsto_mul_integral_exp_remainder_of_integrable_norm_div ha hE
    (integrableOn_norm_div_of_compact_of_inv_tail ha haA hcompact hmeas htail)

end AnalyticNumberTheory.Mertens
