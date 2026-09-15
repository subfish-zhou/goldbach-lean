import MathlibNt.SieveTheory.LinearSieve.JurkatRichert.JurkatRichert1965ChenDelayMonotonicity

/-!
# Exponential coalescence of the actual Jurkat--Richert delay pair

The Dickman renewal identity gives an exponential bound for the weighted gap.
Monotonicity then supplies a common limit with the same rate. This module does
not identify that limit with `1`; that normalization is a separate obligation
in the proof of (5.10). No asymptotic estimate is assumed.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

theorem antitone_delayDifference {A : ℝ} (hA : 0 < A) :
    Antitone (delayDifference A) := by
  have hanti : AntitoneOn (delayDifference A) (Ici 2) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 2)
      (continuous_delayDifference A).continuousOn
    · intro u hu
      rw [interior_Ici, mem_Ioi] at hu
      exact (hasDerivAt_delayDifference A hu).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Ici, mem_Ioi] at hu
      rw [(hasDerivAt_delayDifference A hu).deriv]
      exact div_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (delayDifference_pos hA _).le) (by linarith)
  intro u v huv
  by_cases hu : 2 ≤ u
  · exact hanti hu (hu.trans huv) huv
  · by_cases hv : v ≤ 2
    · rw [delayDifference_initial A hv, delayDifference_initial A (lt_of_not_ge hu).le]
    · have h := hanti (show (2 : ℝ) ∈ Ici 2 by norm_num)
        (show v ∈ Ici 2 from (lt_of_not_ge hv).le) (lt_of_not_ge hv).le
      rw [delayDifference_initial A (lt_of_not_ge hu).le]
      simpa only [delayDifference_initial A le_rfl] using h

/-- The renewal average is bounded by its left endpoint. -/
theorem mul_delayDifference_le_previous {A u : ℝ} (hA : 0 < A) (hu : 2 ≤ u) :
    (u - 1) * delayDifference A u ≤ delayDifference A (u - 1) := by
  rw [delayDifference_renewal A hu]
  calc
    _ ≤ ∫ _t in (u - 1)..u, delayDifference A (u - 1) := by
      apply intervalIntegral.integral_mono_on (by linarith)
        ((continuous_delayDifference A).intervalIntegrable _ _)
        (intervalIntegrable_const)
      intro t ht
      exact antitone_delayDifference hA ht.1
    _ = delayDifference A (u - 1) := by simp

theorem antitoneOn_exp_mul_delayDifference {A : ℝ} (hA : 0 < A) :
    AntitoneOn (fun u => Real.exp u * delayDifference A u) (Ici 2) := by
  have hd (u : ℝ) (hu : 2 < u) :
      HasDerivAt (fun u => Real.exp u * delayDifference A u)
        (Real.exp u * delayDifference A u +
          Real.exp u * (-delayDifference A (u - 1) / (u - 1))) u :=
    (Real.hasDerivAt_exp u).mul (hasDerivAt_delayDifference A hu)
  apply antitoneOn_of_deriv_nonpos (convex_Ici 2)
    (Real.continuous_exp.mul (continuous_delayDifference A)).continuousOn
  · intro u hu
    rw [interior_Ici, mem_Ioi] at hu
    exact (hd u hu).differentiableAt.differentiableWithinAt
  · intro u hu
    rw [interior_Ici, mem_Ioi] at hu
    change deriv (fun u => Real.exp u * delayDifference A u) u ≤ 0
    rw [(hd u hu).deriv]
    have h : delayDifference A u ≤ delayDifference A (u - 1) / (u - 1) :=
      (le_div_iff₀ (show 0 < u - 1 by linarith)).2
      (by simpa [mul_comm] using mul_delayDifference_le_previous hA hu.le)
    have := mul_le_mul_of_nonneg_left h (Real.exp_pos u).le
    rw [neg_div]
    nlinarith

theorem delayDifference_le_exp {A u : ℝ} (hA : 0 < A) :
    delayDifference A u ≤ A * Real.exp 2 * Real.exp (-u) := by
  by_cases hu2 : 2 ≤ u
  · have h := antitoneOn_exp_mul_delayDifference hA
      (show (2 : ℝ) ∈ Ici 2 by norm_num) hu2 hu2
    dsimp only at h
    rw [delayDifference_initial A le_rfl] at h
    have h' := mul_le_mul_of_nonneg_right h (Real.exp_pos (-u)).le
    have heq : Real.exp u * delayDifference A u * Real.exp (-u) =
        delayDifference A u := by
      rw [mul_right_comm, ← Real.exp_add]
      simp
    rw [heq] at h'
    simpa only [mul_comm (Real.exp 2) A] using h'
  · rw [delayDifference_initial A (lt_of_not_ge hu2).le, mul_assoc, ← Real.exp_add]
    exact le_mul_of_one_le_right hA.le
      (Real.one_le_exp_iff.mpr (by linarith))

/-- One constant controls the upper/lower gap on the entire source range. -/
theorem jr1965F_sub_jr1965f_le_exp {u : ℝ} (hu : 1 ≤ u) :
    jr1965F u - jr1965f u ≤
      jr1965DelayConstant * Real.exp 2 * Real.exp (-u) := by
  have hA : 0 < jr1965DelayConstant := by unfold jr1965DelayConstant; positivity
  have hgap : jr1965F u - jr1965f u = delayDifference jr1965DelayConstant u / u := by
    simp [jr1965F, jr1965f, delayFunction, delayDifference, sub_div]
  rw [hgap]
  exact (div_le_self (delayDifference_pos hA u).le hu).trans
    (delayDifference_le_exp hA)

/-- The common limit is constructed from the lower function, not postulated. -/
def jr1965CommonLimit : ℝ := sSup (jr1965f '' Ici 1)

private theorem bddAbove_jr1965f_image : BddAbove (jr1965f '' Ici 1) :=
  ⟨jr1965DelayConstant, by
    rintro _ ⟨u, hu, rfl⟩
    exact jr1965f_le_delayConstant hu⟩

theorem jr1965f_le_commonLimit {u : ℝ} (hu : 1 ≤ u) :
    jr1965f u ≤ jr1965CommonLimit :=
  le_csSup bddAbove_jr1965f_image ⟨u, hu, rfl⟩

theorem commonLimit_le_jr1965F {u : ℝ} (hu : 1 ≤ u) :
    jr1965CommonLimit ≤ jr1965F u := by
  unfold jr1965CommonLimit
  apply csSup_le (s := jr1965f '' Ici 1) ⟨jr1965f 1, 1, by norm_num, rfl⟩
  rintro _ ⟨t, ht, rfl⟩
  change 1 ≤ t at ht
  rcases le_total t u with h | h
  · exact (monotoneOn_jr1965f (by change 0 < t; linarith)
      (by change 0 < u; linarith) h).trans
      (jr1965f_lt_jr1965F (by linarith)).le
  · exact (jr1965f_lt_jr1965F (by linarith : 0 < t)).le.trans
      (antitoneOn_jr1965F (by change 0 < u; linarith)
        (by change 0 < t; linarith) h)

theorem abs_jr1965F_sub_commonLimit_le_exp {u : ℝ} (hu : 1 ≤ u) :
    |jr1965F u - jr1965CommonLimit| ≤
      jr1965DelayConstant * Real.exp 2 * Real.exp (-u) := by
  rw [abs_of_nonneg (sub_nonneg.mpr (commonLimit_le_jr1965F hu))]
  exact (sub_le_sub_left (jr1965f_le_commonLimit hu) _).trans
    (jr1965F_sub_jr1965f_le_exp hu)

theorem abs_jr1965f_sub_commonLimit_le_exp {u : ℝ} (hu : 1 ≤ u) :
    |jr1965f u - jr1965CommonLimit| ≤
      jr1965DelayConstant * Real.exp 2 * Real.exp (-u) := by
  rw [abs_of_nonpos (sub_nonpos.mpr (jr1965f_le_commonLimit hu)), neg_sub]
  exact (sub_le_sub_right (commonLimit_le_jr1965F hu) _).trans
    (jr1965F_sub_jr1965f_le_exp hu)

theorem tendsto_jr1965F_commonLimit :
    Tendsto jr1965F atTop (𝓝 jr1965CommonLimit) := by
  have hbound : Tendsto (fun u : ℝ =>
      jr1965DelayConstant * Real.exp 2 * Real.exp (-u)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul
      (jr1965DelayConstant * Real.exp 2)
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg)) _ hbound
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
  simpa [Real.dist_eq] using abs_jr1965F_sub_commonLimit_le_exp hu

theorem tendsto_jr1965f_commonLimit :
    Tendsto jr1965f atTop (𝓝 jr1965CommonLimit) := by
  have hbound : Tendsto (fun u : ℝ =>
      jr1965DelayConstant * Real.exp 2 * Real.exp (-u)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul
      (jr1965DelayConstant * Real.exp 2)
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg)) _ hbound
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
  simpa [Real.dist_eq] using abs_jr1965f_sub_commonLimit_le_exp hu

end MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
