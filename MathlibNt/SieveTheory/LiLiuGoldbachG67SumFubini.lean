import MathlibNt.SieveTheory.LiLiuGoldbachG67SumDensity
import Mathlib.MeasureTheory.Group.Prod

open Set MeasureTheory
open scoped Interval
noncomputable section
namespace G67SumCoordinate

/-- Compactly supported original integrand, before the measure-preserving shear. -/
def boxKernel (a b c d : ℝ) (φ : ℝ → ℝ) (x : ℝ × ℝ) : ℝ :=
  (Icc a b ×ˢ Icc c d).indicator (fun x => φ (x.1+x.2)/(x.1*x.2)) x

/-- The positive compact rectangle supplies the Fubini integrability hypothesis. -/
theorem boxKernel_integrable {a b c d : ℝ} {φ : ℝ → ℝ}
    (ha : 0 < a) (hc : 0 < c)
    (hφ : ContinuousOn φ (Icc (a+c) (b+d))) :
    Integrable (boxKernel a b c d φ) (volume.prod volume) := by
  apply IntegrableOn.integrable_indicator _ (measurableSet_Icc.prod measurableSet_Icc)
  apply ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  apply ContinuousOn.div
  · exact hφ.comp (continuous_fst.add continuous_snd).continuousOn
      (fun x hx => ⟨add_le_add hx.1.1 hx.2.1, add_le_add hx.1.2 hx.2.2⟩)
  · exact (continuous_fst.mul continuous_snd).continuousOn
  · intro x hx
    exact (mul_pos (ha.trans_le hx.1.1) (hc.trans_le hx.2.1)).ne'

/-- Conversion of a closed interval indicator to its oriented interval integral. -/
theorem integral_closed_indicator {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) :
    (∫ x, (Icc a b).indicator f x) = ∫ x in a..b, f x := by
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hab]

/-- The indicator rectangle has precisely the original iterated integral. -/
theorem integral_boxKernel {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (φ : ℝ → ℝ) :
    (∫ u, ∫ v, boxKernel a b c d φ (u,v)) =
      ∫ u in a..b, ∫ v in c..d, φ (u+v)/(u*v) := by
  have hrow : ∀ u, (∫ v, boxKernel a b c d φ (u,v)) =
      (Icc a b).indicator (fun u => ∫ v in c..d, φ (u+v)/(u*v)) u := by
    intro u
    by_cases hu : u ∈ Icc a b
    · simp only [boxKernel, Set.indicator, mem_prod, hu, true_and, ↓reduceIte]
      simpa only [Set.indicator] using
        integral_closed_indicator hcd (fun v => φ (u+v)/(u*v))
    · simp only [boxKernel, Set.indicator, mem_prod, hu, false_and, ↓reduceIte,
        integral_zero]
  simp_rw [hrow]
  exact integral_closed_indicator hab _

/-- Pointwise moving-domain identity. The outer sum indicator is essential. -/
theorem sheared_boxKernel (a b c d s u : ℝ) (φ : ℝ → ℝ) :
    boxKernel a b c d φ (u,s-u) =
      (Icc (a+c) (b+d)).indicator
        (fun s => (Icc (lower a d s) (upper b c s)).indicator
          (fun u => φ s/(u*(s-u))) u) s := by
  by_cases h : u ∈ Icc a b ∧ s-u ∈ Icc c d
  · have hs : s ∈ Icc (a+c) (b+d) := by
      constructor <;> linarith [h.1.1, h.1.2, h.2.1, h.2.2]
    have hf := fiber_mem.mpr h
    have hp : (u,s-u) ∈ Icc a b ×ˢ Icc c d := h
    simp only [boxKernel, Set.indicator_of_mem hp, Set.indicator_of_mem hs,
      Set.indicator_of_mem hf, add_sub_cancel]
  · have hf : u ∉ Icc (lower a d s) (upper b c s) := by
      simpa only [fiber_mem] using h
    have hp : (u,s-u) ∉ Icc a b ×ˢ Icc c d := h
    rw [boxKernel, Set.indicator_of_notMem hp]
    by_cases hs : s ∈ Icc (a+c) (b+d)
    · rw [Set.indicator_of_mem hs, Set.indicator_of_notMem hf]
    · rw [Set.indicator_of_notMem hs]

/-- Pure sum-coordinate Fubini formula with the fiber still unevaluated. -/
theorem rectangle_sum_fibers {a b c d : ℝ} {φ : ℝ → ℝ}
    (ha : 0 < a) (hc : 0 < c) (hab : a ≤ b) (hcd : c ≤ d)
    (hφ : ContinuousOn φ (Icc (a+c) (b+d))) :
    (∫ u in a..b, ∫ v in c..d, φ (u+v)/(u*v)) =
      ∫ s in (a+c)..(b+d), ∫ u in lower a d s..upper b c s, φ s/(u*(s-u)) := by
  have hi := boxKernel_integrable ha hc hφ
  have hshear : Integrable
      (fun x : ℝ × ℝ => boxKernel a b c d φ (x.1,x.2-x.1)) (volume.prod volume) :=
    ((measurePreserving_prod_sub volume volume).integrable_comp hi.aestronglyMeasurable).mpr hi
  rw [← integral_boxKernel hab hcd φ]
  calc
    _ = ∫ u, ∫ s, boxKernel a b c d φ (u,s-u) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun u =>
        (integral_sub_right_eq_self (fun v => boxKernel a b c d φ (u,v)) u).symm)
    _ = ∫ s, ∫ u, boxKernel a b c d φ (u,s-u) := integral_integral_swap hshear
    _ = ∫ s, (Icc (a+c) (b+d)).indicator
        (fun s => ∫ u in lower a d s..upper b c s, φ s/(u*(s-u))) s := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro s
      simp_rw [sheared_boxKernel]
      by_cases hs : s ∈ Icc (a+c) (b+d)
      · simp only [Set.indicator_of_mem hs]
        exact integral_closed_indicator (fiber_bounds ha hc hab hcd hs).2.1 _
      · simp only [Set.indicator_of_notMem hs, integral_zero]
    _ = _ := integral_closed_indicator (add_le_add hab hcd) _

/-- Exact one-dimensional logarithmic formula; only positivity and continuity are inputs. -/
theorem rectangle_sum_formula {a b c d : ℝ} {φ : ℝ → ℝ}
    (ha : 0 < a) (hc : 0 < c) (hab : a ≤ b) (hcd : c ≤ d)
    (hφ : ContinuousOn φ (Icc (a+c) (b+d))) :
    (∫ u in a..b, ∫ v in c..d, φ (u+v)/(u*v)) =
      ∫ s in (a+c)..(b+d), φ s * weight a b c d s := by
  rw [rectangle_sum_fibers ha hc hab hcd hφ]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le (add_le_add hab hcd)] at hs
  simp_rw [div_eq_mul_one_div (φ s)]
  rw [intervalIntegral.integral_const_mul, fiber_integral ha hc hab hcd hs]

end G67SumCoordinate
