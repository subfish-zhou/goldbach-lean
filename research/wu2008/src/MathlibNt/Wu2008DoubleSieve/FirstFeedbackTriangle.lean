import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The triangular exchanges in Wu (2004), Lemma 6.1

Source: author TeX, lines 2570--2608, especially (6.4) and the scalar
feedback calculation immediately following it. The input function is only
interval integrable; no continuity or gain inequality is assumed.
-/

namespace Wu2008DoubleSieve

open Set MeasureTheory Real
open scoped Interval

theorem firstFeedback_triangle_left_slice {a c d u : ℝ} (hu : u ∈ Icc a (c + d))
    (F : ℝ → ℝ) :
    (∫ x in Icc (a - d) c, (if u ≤ x + d then F x else 0)) =
      ∫ x in (u - d)..c, F x := by
  have heq : (fun x => if u ≤ x + d then F x else 0) = (Ici (u - d)).indicator F := by
    ext x
    simp only [indicator_apply, mem_Ici]
    congr 1
    apply propext
    constructor <;> intro h <;> linarith
  rw [heq, setIntegral_indicator measurableSet_Ici]
  have hs : Icc (a - d) c ∩ Ici (u - d) = Icc (u - d) c := by
    ext x
    simp only [mem_inter_iff, mem_Icc, mem_Ici]
    constructor
    · tauto
    · rintro ⟨hx, hxc⟩
      exact ⟨⟨by linarith [hu.1], hxc⟩, hx⟩
  rw [hs, integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by linarith [hu.2])]

theorem firstFeedback_triangle_right_slice {a c d x : ℝ} (hx : x ∈ Icc (a - d) c)
    (F : ℝ → ℝ) :
    (∫ u in Icc a (c + d), (if u ≤ x + d then F u else 0)) =
      ∫ u in a..(x + d), F u := by
  change (∫ u in Icc a (c + d), (Iic (x + d)).indicator F u) = _
  rw [setIntegral_indicator measurableSet_Iic]
  have hs : Icc a (c + d) ∩ Iic (x + d) = Icc a (x + d) := by
    ext u
    simp only [mem_inter_iff, mem_Icc, mem_Iic]
    constructor
    · tauto
    · rintro ⟨hu, hux⟩
      exact ⟨⟨hu, by linarith [hx.2]⟩, hux⟩
  rw [hs, integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by linarith [hx.1])]

theorem firstFeedback_triangle_mask_integrable {a c d : ℝ} {f : ℝ → ℝ}
    {k : ℝ → ℝ → ℝ} (ha : a ≤ c + d)
    (hf : IntervalIntegrable f volume (a - d) c)
    (hk : ContinuousOn (Function.uncurry k) (Icc a (c + d) ×ˢ Icc (a - d) c)) :
    Integrable (fun p : ℝ × ℝ => if p.1 ≤ p.2 + d then f p.2 * k p.1 p.2 else 0)
      ((volume.restrict (Icc a (c + d))).prod (volume.restrict (Icc (a - d) c))) := by
  have hfi : IntegrableOn f (Icc (a - d) c) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : a - d ≤ c)).mp hf
  have hp := hfi.comp_snd (volume.restrict (Icc a (c + d)))
  rw [Measure.prod_restrict] at hp ⊢
  have hmul := IntegrableOn.mul_continuousOn hp hk (isCompact_Icc.prod isCompact_Icc)
  have hs : MeasurableSet {p : ℝ × ℝ | p.1 ≤ p.2 + d} :=
    isClosed_le continuous_fst (continuous_snd.add continuous_const) |>.measurableSet
  exact hmul.indicator hs

/-- Specialized triangular Fubini, also supplying integrability of both iterated
integrands. Closed endpoints are harmless because the Lebesgue atoms vanish. -/
theorem firstFeedback_triangle {a c d : ℝ} {f : ℝ → ℝ} {k : ℝ → ℝ → ℝ}
    (ha : a ≤ c + d) (hf : IntervalIntegrable f volume (a - d) c)
    (hk : ContinuousOn (Function.uncurry k) (Icc a (c + d) ×ˢ Icc (a - d) c)) :
    IntervalIntegrable (fun u => ∫ x in (u - d)..c, f x * k u x) volume a (c + d) ∧
    IntervalIntegrable (fun x => ∫ u in a..(x + d), f x * k u x) volume (a - d) c ∧
    (∫ u in a..(c + d), ∫ x in (u - d)..c, f x * k u x) =
      ∫ x in (a - d)..c, ∫ u in a..(x + d), f x * k u x := by
  have hmask := firstFeedback_triangle_mask_integrable ha hf hk
  have hl := hmask.integral_prod_left
  have hr := hmask.integral_prod_right
  have hle : a - d ≤ c := by linarith
  have hl' : IntegrableOn (fun u => ∫ x in (u - d)..c, f x * k u x) (Icc a (c + d)) := by
    apply hl.congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    exact firstFeedback_triangle_left_slice hu _
  have hr' : IntegrableOn (fun x => ∫ u in a..(x + d), f x * k u x) (Icc (a - d) c) := by
    apply hr.congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact firstFeedback_triangle_right_slice hx _
  refine ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le ha).mpr hl',
    (intervalIntegrable_iff_integrableOn_Icc_of_le hle).mpr hr', ?_⟩
  rw [intervalIntegral.integral_of_le ha, ← integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hle, ← integral_Icc_eq_integral_Ioc]
  calc
    _ = ∫ u in Icc a (c + d), ∫ x in Icc (a - d) c,
        (if u ≤ x + d then f x * k u x else 0) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro u hu
      exact (firstFeedback_triangle_left_slice hu _).symm
    _ = ∫ x in Icc (a - d) c, ∫ u in Icc a (c + d),
        (if u ≤ x + d then f x * k u x else 0) := integral_integral_swap hmask
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro x hx
      exact firstFeedback_triangle_right_slice hx _



/-- The rectangle kernel used for the scalar feedback exchange is continuous;
the arbitrary input `f` need not be. -/
theorem firstFeedback_log_kernel_continuous :
   ContinuousOn (fun p : ℝ × ℝ => log ((p.2 + 1) / (p.1 - 1)) / p.1)
     (Icc 3 5 ×ˢ Icc 1 3) := by
 apply ContinuousOn.div
 · apply ContinuousOn.log
   · apply ContinuousOn.div
     · exact continuous_snd.continuousOn.add continuousOn_const
     · exact continuous_fst.continuousOn.sub continuousOn_const
     · intro p hp
       linarith [hp.1.1]
   · intro p hp
     exact ne_of_gt (div_pos (by linarith [hp.2.1]) (by linarith [hp.1.1]))
 · exact continuous_fst.continuousOn
 · intro p hp
   linarith [hp.1.1]



end Wu2008DoubleSieve
