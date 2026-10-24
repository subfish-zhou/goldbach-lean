import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory Set

namespace MathlibNt.Analysis

/-- Integrating a section of a moving half-open interval region retains the
outer indicator, including empty and reversed inner intervals. -/
theorem integral_indicator_moving_Ioc_section
    (s : Set ℝ) (l r : ℝ → ℝ) (f : ℝ × ℝ → ℝ) (u : ℝ) :
    (∫ v, ({x : ℝ × ℝ | x.1 ∈ s ∧ x.2 ∈ Ioc (l x.1) (r x.1)}).indicator
      f (u, v)) = s.indicator (fun u => ∫ v in Ioc (l u) (r u), f (u, v)) u := by
  by_cases hu : u ∈ s
  · rw [indicator_of_mem hu, ← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards with v
    by_cases hv : v ∈ Ioc (l u) (r u)
    · rw [indicator_of_mem (show (u, v) ∈
        {x : ℝ × ℝ | x.1 ∈ s ∧ x.2 ∈ Ioc (l x.1) (r x.1)} from ⟨hu, hv⟩),
        indicator_of_mem hv]
    · rw [indicator_of_notMem (fun h => hv h.2), indicator_of_notMem hv]
  · rw [indicator_of_notMem hu]
    apply integral_eq_zero_of_ae
    filter_upwards with v
    exact indicator_of_notMem (fun h => hu h.1) _

/-- Fubini for an integrable kernel on an actual moving half-open interval
region. No continuity or ordering of the endpoint functions is assumed. -/
theorem setIntegral_moving_Ioc_eq_iterated
    (s : Set ℝ) (l r : ℝ → ℝ) (f : ℝ × ℝ → ℝ)
    (hs : MeasurableSet s)
    (hregion : MeasurableSet {x : ℝ × ℝ | x.1 ∈ s ∧ x.2 ∈ Ioc (l x.1) (r x.1)})
    (hf : IntegrableOn f {x : ℝ × ℝ | x.1 ∈ s ∧ x.2 ∈ Ioc (l x.1) (r x.1)}) :
    (∫ x in {x : ℝ × ℝ | x.1 ∈ s ∧ x.2 ∈ Ioc (l x.1) (r x.1)}, f x) =
      ∫ u in s, ∫ v in Ioc (l u) (r u), f (u, v) := by
  let F := ({x : ℝ × ℝ | x.1 ∈ s ∧ x.2 ∈ Ioc (l x.1) (r x.1)}).indicator f
  have hF : Integrable F := hf.integrable_indicator hregion
  have hFubini : (∫ z, F z) = ∫ u, ∫ v, F (u, v) := by
    rw [Measure.volume_eq_prod ℝ ℝ] at hF ⊢
    exact integral_prod F hF
  rw [← integral_indicator hregion, hFubini, ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards with u
  exact integral_indicator_moving_Ioc_section s l r f u

end MathlibNt.Analysis
