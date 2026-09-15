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

theorem firstFeedback_source64 {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 1 3)
   {v : ℝ} (hv : 3 ≤ v) (hv' : v ≤ 5) :
   IntervalIntegrable (fun u => (∫ x in (u - 1)..3, f x) / u) volume (v - 1) 4 ∧
   IntervalIntegrable (fun x => f x * log ((x + 1) / (v - 1))) volume (v - 2) 3 ∧
   (∫ u in (v - 1)..4, (∫ x in (u - 1)..3, f x) / u) =
     ∫ x in (v - 2)..3, f x * log ((x + 1) / (v - 1)) := by
 have hfi : IntervalIntegrable f volume ((v - 1) - 1) 3 := by
   apply hf.mono_set
   rw [uIcc_of_le (by linarith), uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)]
   intro x hx
   exact ⟨by linarith [hx.1], hx.2⟩
 have hk : ContinuousOn (fun p : ℝ × ℝ => p.1⁻¹)
     (Icc (v - 1) (3 + 1) ×ˢ Icc ((v - 1) - 1) 3) := by
   apply continuous_fst.continuousOn.inv₀
   intro p hp
   linarith [hp.1.1]
 have h := firstFeedback_triangle (a := v - 1) (c := 3) (d := 1)
   (k := fun u _ => u⁻¹) (by linarith) hfi hk
 have hsub : v - 1 - 1 = v - 2 := by ring
 simp only [show (3 : ℝ) + 1 = 4 by norm_num, hsub,
   ← div_eq_mul_inv, intervalIntegral.integral_div] at h
 have heval (x : ℝ) (hx : x ∈ Icc (v - 2) 3) :
     (∫ u in (v - 1)..(x + 1), f x / u) = f x * log ((x + 1) / (v - 1)) := by
   simp only [div_eq_mul_inv, intervalIntegral.integral_const_mul]
   rw [integral_inv_of_pos (by linarith) (by linarith [hx.1])]
   simp only [div_eq_mul_inv]
 refine ⟨h.1, h.2.1.congr ?_, h.2.2.trans ?_⟩
 · intro x hx
   apply heval
   rw [uIoc_of_le (by linarith)] at hx
   exact ⟨hx.1.le, hx.2⟩
 · apply intervalIntegral.integral_congr
   rw [uIcc_of_le (by linarith)]
   exact heval

theorem firstFeedback_source64_inner_integrable {f : ℝ → ℝ}
   (hf : IntervalIntegrable f volume 1 3) {u : ℝ} (hu : 2 ≤ u) (hu' : u ≤ 4) :
   IntervalIntegrable f volume (u - 1) 3 := by
  apply hf.mono_set
  rw [uIcc_of_le (by linarith), uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)]
  intro x hx
  exact ⟨by linarith [hx.1], hx.2⟩

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

theorem firstFeedback_scalar_inner_integrable {x : ℝ} (hx : 1 ≤ x) (hx' : x ≤ 3) :
   IntervalIntegrable (fun v => log ((x + 1) / (v - 1)) / v) volume 3 (x + 2) := by
 apply ContinuousOn.intervalIntegrable
 have hm : MapsTo (fun v : ℝ => (v, x)) (uIcc 3 (x + 2)) (Icc 3 5 ×ˢ Icc 1 3) := by
   rw [uIcc_of_le (by linarith)]
   intro v hv
   exact ⟨⟨hv.1, by linarith [hv.2]⟩, hx, hx'⟩
 exact firstFeedback_log_kernel_continuous.comp
   (continuous_id.prodMk continuous_const).continuousOn hm

/-- The second triangular exchange in the proof of Lemma 6.1, with
integrability of both scalar-feedback integrands. -/
theorem firstFeedback_scalar_exchange {f : ℝ → ℝ}
   (hf : IntervalIntegrable f volume 1 3) :
   IntervalIntegrable (fun v =>
     (∫ x in (v - 2)..3, f x * log ((x + 1) / (v - 1))) / v) volume 3 5 ∧
   IntervalIntegrable (fun x =>
     f x * ∫ v in 3..(x + 2), log ((x + 1) / (v - 1)) / v) volume 1 3 ∧
   (∫ v in 3..5, (∫ x in (v - 2)..3, f x * log ((x + 1) / (v - 1))) / v) =
     ∫ x in 1..3, f x * ∫ v in 3..(x + 2), log ((x + 1) / (v - 1)) / v := by
 have h := firstFeedback_triangle (a := 3) (c := 3) (d := 2)
   (k := fun v x => log ((x + 1) / (v - 1)) / v) (by norm_num)
   (by norm_num; exact hf)
   (by convert firstFeedback_log_kernel_continuous using 1 <;> first | rfl | norm_num)
 norm_num only at h
 have hl (v : ℝ) :
     (∫ x in (v - 2)..3, f x * (log ((x + 1) / (v - 1)) / v)) =
       (∫ x in (v - 2)..3, f x * log ((x + 1) / (v - 1))) / v := by
   simp only [← mul_div_assoc, intervalIntegral.integral_div]
 have hr (x : ℝ) :
     (∫ v in (3 : ℝ)..(x + 2), f x * (log ((x + 1) / (v - 1)) / v)) =
       f x * ∫ v in 3..(x + 2), log ((x + 1) / (v - 1)) / v :=
   intervalIntegral.integral_const_mul _ _
 simp_rw [hl, hr] at h
 exact h

end Wu2008DoubleSieve
