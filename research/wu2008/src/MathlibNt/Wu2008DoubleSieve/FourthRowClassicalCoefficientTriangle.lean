import MathlibNt.Wu2008DoubleSieve.Gamma678FeedbackCountLink
import MathlibNt.Wu2008DoubleSieve.FirstFunctionalGainSource
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackTriangle
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackWeightedKernel

namespace Wu2008DoubleSieve
open Set MeasureTheory Real
open scoped Interval

noncomputable def fourthRowClassicalL (x : ℝ) : ℝ :=
  ∫ v in (2 : ℝ)..(x - 1), log (v - 1) / v

noncomputable def fourthRowClassicalJ (x y : ℝ) : ℝ :=
  ∫ u in (1 - 1 / x)..(1 - 1 / y), log (y * u - 1) / (u * (1 - u))

noncomputable def fourthRowClassicalTriangle (A B : ℝ) : ℝ :=
  ∫ t in (1 / A)..(1 / B), ∫ u in t..(1 / B), gamma5MassKernel t u

theorem fourthRowClassical_kernel_continuous {a b : ℝ}
    (ha : 0 < a) (hb : b < 1 / 2) :
    ContinuousOn (Function.uncurry gamma5MassKernel) (Icc a b ×ˢ Icc a b) := by
  apply continuousOn_const.div
    ((continuous_fst.continuousOn.mul continuous_snd.continuousOn).mul
      ((continuousOn_const.sub continuous_fst.continuousOn).sub continuous_snd.continuousOn))
  intro p hp
  exact mul_ne_zero (mul_ne_zero (ne_of_gt (ha.trans_le hp.1.1))
    (ne_of_gt (ha.trans_le hp.2.1))) (ne_of_gt (show 0 < 1 - p.1 - p.2 by linarith [hp.1.2, hp.2.2]))

theorem fourthRowClassical_triangle_fubini {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1 / 2) :
    IntervalIntegrable (fun t => ∫ u in t..b, gamma5MassKernel t u) volume a b ∧
    IntervalIntegrable (fun u => ∫ t in a..u, gamma5MassKernel t u) volume a b ∧
    (∫ t in a..b, ∫ u in t..b, gamma5MassKernel t u) =
      ∫ u in a..b, ∫ t in a..u, gamma5MassKernel t u := by
  have h := firstFeedback_triangle (a := a) (c := b) (d := 0)
    (f := fun _ => 1) (k := gamma5MassKernel) (by simpa using hab)
    (intervalIntegrable_const)
    (by simpa using fourthRowClassical_kernel_continuous ha hb)
  have hs (u t : ℝ) : gamma5MassKernel u t = gamma5MassKernel t u := by
    unfold gamma5MassKernel
    congr 1
    ring
  simpa only [add_zero, sub_zero, one_mul, hs] using h

theorem fourthRowClassical_inner_integrable {a b t l h : ℝ}
    (ha : 0 < a) (hb : b < 1 / 2) (ht : t ∈ Icc a b)
    (hl : l ∈ Icc a b) (hh : h ∈ Icc a b) :
    IntervalIntegrable (gamma5MassKernel t) volume l h := by
  apply ContinuousOn.intervalIntegrable
  apply (fourthRowClassical_kernel_continuous ha hb).comp
    (continuous_const.prodMk continuous_id).continuousOn
  intro u hu
  exact ⟨ht, (uIcc_subset_Icc hl hh) hu⟩

theorem fourthRowClassical_inner_log {a u : ℝ}
    (ha : 0 < a) (hau : a ≤ u) (hu : u < 1 / 2) :
    (∫ t in a..u, gamma5MassKernel t u) =
      (log ((1 - u - a) / a) - log (1 / u - 2)) / (u * (1 - u)) := by
  have hu0 : 0 < u := ha.trans_le hau
  have hc : 0 < 1 - u := by linarith
  have hd : 0 < 1 - u - u := by linarith
  have he : 0 < 1 - u - a := by linarith
  have hpos : 0 < 1 / u - 2 := by
    apply (sub_pos.mpr ((lt_div_iff₀ hu0).mpr (by linarith)))
  calc
    _ = (∫ t in a..u, firstFeedbackWeightedKernel (1 - u) t) / (u * (1 - u)) := by
      rw [← intervalIntegral.integral_div]
      apply intervalIntegral.integral_congr
      intro t ht
      simp only [uIcc_of_le hau, mem_Icc] at ht
      have ht0 : t ≠ 0 := ne_of_gt (ha.trans_le ht.1)
      have hdt : 1 - u - t ≠ 0 := ne_of_gt (by linarith [ht.2])
      dsimp [gamma5MassKernel, firstFeedbackWeightedKernel]
      have hswap : 1 - t - u = 1 - u - t := by ring
      rw [hswap]
      field_simp [ht0, hdt, hu0.ne', hc.ne']
    _ = log (u * (1 - u - a) / (a * (1 - u - u))) / (u * (1 - u)) := by
      rw [firstFeedbackWeightedKernel_integral ha hau (by linarith)]
    _ = _ := by
      congr 1
      rw [← log_div (ne_of_gt (div_pos he ha)) hpos.ne']
      congr 1
      have hd' : 1 - u * 2 ≠ 0 := by linarith
      field_simp [ha.ne', hu0.ne', hd.ne', hd']
      ring

end Wu2008DoubleSieve
