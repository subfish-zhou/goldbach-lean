import NodeCross
import Mathlib.MeasureTheory.Integral.Prod

namespace NodeExtension
open Real Set MeasureTheory
open scoped Interval

/-- An interval integral written on its closed interval, including degenerate endpoints. -/
theorem integral_Icc {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) :
    (∫ x in a..b, f x) = ∫ x in Icc a b, f x := by
  rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]

theorem clip_lower {a b c : ℝ} (hc : c ∈ Icc a b) (f : ℝ → ℝ) :
    (∫ x in Icc a b, if c ≤ x then f x else 0) = ∫ x in c..b, f x := by
  rw [integral_Icc hc.2]
  have he : (Ici c) ∩ Icc a b = Icc c b := by
    ext x
    simp only [mem_inter_iff, mem_Ici, mem_Icc]
    constructor
    · rintro ⟨hcx, _, hxb⟩; exact ⟨hcx, hxb⟩
    · rintro ⟨hcx, hxb⟩; exact ⟨hcx, hc.1.trans hcx, hxb⟩
  change (∫ x in Icc a b, (Ici c).indicator f x) = _
  rw [MeasureTheory.integral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici, he]

theorem clip_upper {a b c : ℝ} (hc : c ∈ Icc a b) (f : ℝ → ℝ) :
    (∫ x in Icc a b, if x ≤ c then f x else 0) = ∫ x in a..c, f x := by
  rw [integral_Icc hc.1]
  have he : (Iic c) ∩ Icc a b = Icc a c := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_Icc]
    constructor
    · rintro ⟨hxc, hax, _⟩; exact ⟨hax, hxc⟩
    · rintro ⟨hax, hxc⟩; exact ⟨hxc, hax, hxc.trans hc.2⟩
  change (∫ x in Icc a b, (Iic c).indicator f x) = _
  rw [MeasureTheory.integral_indicator measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic, he]

/-- Genuine Fubini on a closed triangle, with both zero-width edges retained. -/
theorem triangle_swap {a b : ℝ} (hab : a ≤ b) (F : ℝ × ℝ → ℝ)
    (hF : IntegrableOn F (Icc a b ×ˢ Icc a b)) :
    (∫ x in a..b, ∫ t in x..b, F (x, t)) =
      ∫ t in a..b, ∫ x in a..t, F (x, t) := by
  let G : ℝ × ℝ → ℝ := {p | p.1 ≤ p.2}.indicator F
  have hi : Integrable G ((volume.restrict (Icc a b)).prod
      (volume.restrict (Icc a b))) := by
    rw [Measure.prod_restrict]
    exact hF.indicator (measurableSet_le measurable_fst measurable_snd)
  have hf := MeasureTheory.integral_integral_swap (f := fun x t => G (x,t)) hi
  rw [integral_Icc hab, integral_Icc hab]
  calc
    _ = ∫ x in Icc a b, ∫ t in Icc a b, G (x,t) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro x hx
      exact (clip_lower hx (fun t => F (x,t))).symm
    _ = ∫ t in Icc a b, ∫ x in Icc a b, G (x,t) := hf
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro t ht
      exact clip_upper ht (fun x => F (x,t))

theorem reciprocal_continuous {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn (fun x : ℝ => 1 / x) (uIcc a b) := by
  apply continuousOn_const.div continuousOn_id
  rw [uIcc_of_le hab]
  intro x hx
  dsimp
  linarith [hx.1]

theorem triangle_log {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {p : ℝ → ℝ} (hp : IntervalIntegrable p volume a b) :
    (∫ x in a..b, (∫ t in x..b, p t) / x) =
      ∫ t in a..b, p t * log (t / a) := by
  have hq := (reciprocal_continuous ha hab).intervalIntegrable (μ := volume)
  have hip := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hp
  have hiq := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hq
  have hF : IntegrableOn (fun z : ℝ × ℝ => (1 / z.1) * p z.2)
      (Icc a b ×ˢ Icc a b) := by
    change Integrable _ ((volume.prod volume).restrict (Icc a b ×ˢ Icc a b))
    rw [← Measure.prod_restrict]
    exact hiq.mul_prod hip
  calc
    _ = ∫ x in a..b, ∫ t in x..b, (1 / x) * p t := by
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only
      rw [intervalIntegral.integral_const_mul]
      ring
    _ = ∫ t in a..b, ∫ x in a..t, (1 / x) * p t := triangle_swap hab _ hF
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hab] at ht
      dsimp only
      rw [intervalIntegral.integral_mul_const, integral_one_div_of_pos ha
        (lt_of_lt_of_le ha ht.1)]
      ring

theorem tail_div_integrable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {p : ℝ → ℝ} (hp : IntervalIntegrable p volume a b) :
    IntervalIntegrable (fun x => (∫ t in x..b, p t) / x) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div
  · exact intervalIntegral.continuousOn_primitive_interval_left
      ((intervalIntegrable_iff' (by finiteness)).mp hp)
  · exact continuousOn_id
  · rw [uIcc_of_le hab]
    intro x hx
    dsimp
    linarith [hx.1]

theorem shifted_tail {a b : ℝ} (ha : 0 < a + 1) (hab : a ≤ b)
    {p : ℝ → ℝ} (hp : IntervalIntegrable p volume a b) (c : ℝ) :
    IntervalIntegrable (fun x => (c + ∫ t in (x - 1)..b, p t) / x)
      volume (a + 1) (b + 1) ∧
    (∫ x in (a + 1)..(b + 1), (c + ∫ t in (x - 1)..b, p t) / x) =
      c * log ((b + 1) / (a + 1)) +
        ∫ t in a..b, p t * log ((t + 1) / (a + 1)) := by
  have hab' : a + 1 ≤ b + 1 := by linarith
  have hshift : IntervalIntegrable (fun y => p (y - 1)) volume (a + 1) (b + 1) := by
    exact hp.comp_sub_right 1
  have he (x : ℝ) : (∫ y in x..(b + 1), p (y - 1)) = ∫ t in (x - 1)..b, p t := by
    rw [intervalIntegral.integral_comp_sub_right]
    simp
  have hi1 : IntervalIntegrable (fun x : ℝ => c / x) volume (a + 1) (b + 1) := by
    simpa only [mul_one_div] using ((reciprocal_continuous ha hab').intervalIntegrable
      (μ := volume)).const_mul c
  have hi2 := tail_div_integrable ha hab' hshift
  simp_rw [he] at hi2
  constructor
  · simpa only [add_div] using hi1.add hi2
  · have heq : (fun x => (c + ∫ t in (x - 1)..b, p t) / x) =
        (fun x => c / x + (∫ t in (x - 1)..b, p t) / x) := by
      funext x
      exact add_div _ _ _
    rw [heq, intervalIntegral.integral_add hi1 hi2]
    have hc : (∫ x in (a + 1)..(b + 1), c / x) =
        c * log ((b + 1) / (a + 1)) := by
      have hec : (fun x : ℝ => c / x) = (fun x => c * (1 / x)) := by
        funext x
        ring
      rw [hec, intervalIntegral.integral_const_mul,
        integral_one_div_of_pos ha (by linarith)]
    rw [hc]
    apply congrArg (fun z => c * log ((b + 1) / (a + 1)) + z)
    simp_rw [← he]
    rw [triangle_log ha hab' hshift]
    have hs := intervalIntegral.integral_comp_add_right
      (a := a) (b := b) (fun t => p (t - 1) * log (t / (a + 1))) 1
    simpa using hs.symm

theorem triangle_tail_integrable {a b : ℝ} (hab : a ≤ b) (F : ℝ × ℝ → ℝ)
    (hF : IntegrableOn F (Icc a b ×ˢ Icc a b)) :
    IntervalIntegrable (fun x => ∫ t in x..b, F (x,t)) volume a b := by
  let G : ℝ × ℝ → ℝ := {p | p.1 ≤ p.2}.indicator F
  have hi : Integrable G ((volume.restrict (Icc a b)).prod
      (volume.restrict (Icc a b))) := by
    rw [Measure.prod_restrict]
    exact hF.indicator (measurableSet_le measurable_fst measurable_snd)
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
  apply hi.integral_prod_left.congr
  apply ae_restrict_of_forall_mem measurableSet_Icc
  intro x hx
  exact clip_lower hx (fun t => F (x,t))

/-- The second triangular exchange, including its integrability proof. -/
theorem sigma_feedback {p : ℝ → ℝ} (hp : IntervalIntegrable p volume 1 3) :
    IntervalIntegrable (fun v =>
      (∫ t in (v - 2)..3, p t * log ((t + 1) / (v - 1))) / v) volume 3 5 ∧
    (∫ v in (3 : ℝ)..5,
      (∫ t in (v - 2)..3, p t * log ((t + 1) / (v - 1))) / v) =
        ∫ t in (1 : ℝ)..3, p t * sigma 3 (t + 2) (t + 1) := by
  let F : ℝ × ℝ → ℝ := fun z => p (z.2 - 2) *
    (log ((z.2 - 1) / (z.1 - 1)) / z.1)
  have hs : IntervalIntegrable (fun t => p (t - 2)) volume 3 5 := by
    convert hp.comp_sub_right 2 using 1 <;> norm_num
  have hip := (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (3 : ℝ) ≤ 5)).mp hs
  have hbase : IntegrableOn (fun z : ℝ × ℝ => p (z.2 - 2))
      (Icc 3 5 ×ˢ Icc 3 5) := by
    change Integrable _ ((volume.prod volume).restrict (Icc 3 5 ×ˢ Icc 3 5))
    rw [← Measure.prod_restrict]
    exact hip.comp_snd _
  have hc : ContinuousOn (fun z : ℝ × ℝ => log ((z.2 - 1) / (z.1 - 1)) / z.1)
      (Icc 3 5 ×ˢ Icc 3 5) := by
    apply ContinuousOn.div
    · apply ContinuousOn.log
      · exact (continuousOn_snd.sub continuousOn_const).div
          (continuousOn_fst.sub continuousOn_const)
          (fun z hz => by dsimp; linarith [hz.1.1])
      · intro z hz
        exact ne_of_gt (div_pos (by linarith [hz.2.1]) (by linarith [hz.1.1]))
    · exact continuousOn_fst
    · intro z hz
      dsimp
      linarith [hz.1.1]
  have hF : IntegrableOn F (Icc 3 5 ×ˢ Icc 3 5) :=
    hbase.mul_continuousOn hc (isCompact_Icc.prod isCompact_Icc)
  have he (v : ℝ) : (∫ t in v..5, F (v,t)) =
      (∫ t in (v - 2)..3, p t * log ((t + 1) / (v - 1))) / v := by
    have h := intervalIntegral.integral_comp_sub_right (a := v) (b := 5)
      (fun t => p t * log ((t + 1) / (v - 1))) 2
    norm_num only [show (5 : ℝ) - 2 = 3 by norm_num] at h
    rw [← h, ← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [F]
    rw [show t - 2 + 1 = t - 1 by ring]
    ring
  constructor
  · simpa only [he] using triangle_tail_integrable (by norm_num : (3 : ℝ) ≤ 5) F hF
  · simp_rw [← he]
    rw [triangle_swap (by norm_num : (3 : ℝ) ≤ 5) F hF]
    have hs2 := intervalIntegral.integral_comp_add_right (a := 1) (b := 3)
      (fun t => ∫ v in (3 : ℝ)..t, F (v,t)) 2
    norm_num only [show (1 : ℝ) + 2 = 3 by norm_num,
      show (3 : ℝ) + 2 = 5 by norm_num] at hs2
    rw [← hs2]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [F, sigma]
    rw [show t + 2 - 2 = t by ring, show t + 2 - 1 = t + 1 by ring,
      intervalIntegral.integral_const_mul]

end NodeExtension
