import MathlibNt.Analysis.LogGridEstimates
import MathlibNt.Analysis.MovingIntervalIntegral
import MathlibNt.SieveTheory.Arithmetic.PrimeReciprocalLogRectangle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! Shared logarithmic-coordinate functions and rectangle integrals.
The grid selection and convergence proofs remain with their source consumers. -/

open MeasureTheory Set
open scoped Interval
namespace MathlibNt.SieveTheory.LiuWeight
noncomputable section
open PrimeReciprocalLogRectangle

/-- The logarithmic density in the two exponent coordinates. -/
def liuLogDensity (x : ℝ × ℝ) : ℝ := 1 / (x.1 * x.2)

/-- Liu's remaining kernel in logarithmic coordinates. -/
def liuLogKernel (x : ℝ × ℝ) : ℝ := 1 / (1 - x.1 - x.2)

/-- The full density occurring in Liu's source integral. -/
def liuLogIntegrand (x : ℝ × ℝ) : ℝ :=
  liuLogKernel x * liuLogDensity x

/-- The same identity as a product-set integral. -/
theorem logarithmicRectangleMass_eq_setIntegral
    {a₀ a₁ b₀ b₁ : ℝ} (ha₀ : 0 < a₀) (ha : a₀ < a₁)
    (hb₀ : 0 < b₀) (hb : b₀ < b₁) :
    logarithmicRectangleMass a₀ a₁ b₀ b₁ =
      ∫ x in Ioc a₀ a₁ ×ˢ Ioc b₀ b₁, liuLogDensity x := by
  have ha₁ : 0 < a₁ := ha₀.trans ha
  have hb₁ : 0 < b₁ := hb₀.trans hb
  change logarithmicRectangleMass a₀ a₁ b₀ b₁ =
    ∫ x in Ioc a₀ a₁ ×ˢ Ioc b₀ b₁, 1 / (x.1 * x.2)
  have hfactor :
      (∫ x in Ioc a₀ a₁ ×ˢ Ioc b₀ b₁, 1 / (x.1 * x.2)) =
        ∫ x in Ioc a₀ a₁ ×ˢ Ioc b₀ b₁, (1 / x.1) * (1 / x.2) := by
    apply MeasureTheory.setIntegral_congr_fun
      (measurableSet_Ioc.prod measurableSet_Ioc)
    intro x hx
    simpa only [one_div] using (mul_inv x.1 x.2)
  rw [hfactor]
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ,
    MeasureTheory.setIntegral_prod_mul
    (fun α : ℝ => 1 / α) (fun β : ℝ => 1 / β)]
  rw [← intervalIntegral.integral_of_le ha.le,
    ← intervalIntegral.integral_of_le hb.le]
  have hia : (∫ α in a₀..a₁, 1 / α) = Real.log (a₁ / a₀) := by
    simpa only [one_div] using integral_inv_of_pos ha₀ ha₁
  have hib : (∫ β in b₀..b₁, 1 / β) = Real.log (b₁ / b₀) := by
    simpa only [one_div] using integral_inv_of_pos hb₀ hb₁
  rw [hia, hib]
  rfl

lemma integrable_indicator_of_integrableOn {f : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)}
    (hs : MeasurableSet s) (hf : IntegrableOn f s) :
    Integrable (s.indicator f) := by
  exact hf.integrable_indicator hs

end
end MathlibNt.SieveTheory.LiuWeight

namespace MathlibNt.SieveTheory.LiuWeight
open MeasureTheory Set

/-- Positive coordinate gaps suffice for density continuity on a rectangle. -/
theorem continuousOn_liuLogDensity_box {a b c d : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ContinuousOn liuLogDensity (Icc a b ×ˢ Icc c d) := by
  unfold liuLogDensity
  apply ContinuousOn.div continuousOn_const
    (continuous_fst.continuousOn.mul continuous_snd.continuousOn)
  intro x hx
  exact mul_ne_zero (ha.trans_le hx.1.1).ne' (hc.trans_le hx.2.1).ne'

/-- An upper-corner gap keeps the remaining denominator away from zero. -/
theorem continuousOn_liuLogKernel_box {a b c d : ℝ} (hgap : b + d < 1) :
    ContinuousOn liuLogKernel (Icc a b ×ˢ Icc c d) := by
  unfold liuLogKernel
  apply ContinuousOn.div continuousOn_const
    ((continuousOn_const.sub continuous_fst.continuousOn).sub continuous_snd.continuousOn)
  intro x hx
  change 1 - x.1 - x.2 ≠ 0
  linarith [hx.1.2, hx.2.2]

/-- Lower coordinate bounds give the exact reciprocal density bound. -/
theorem liuLogDensity_le_of_lower_bounds {a c : ℝ} {x : ℝ × ℝ}
    (ha : 0 < a) (hc : 0 < c) (hx : a ≤ x.1) (hy : c ≤ x.2) :
    liuLogDensity x ≤ 1 / (a * c) := by
  exact one_div_le_one_div_of_le (mul_pos ha hc)
    (mul_le_mul hx hy hc.le (ha.le.trans hx))

end MathlibNt.SieveTheory.LiuWeight
