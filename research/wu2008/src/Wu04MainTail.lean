import Wu04StrongPsiConsumer

namespace Wu04MainTail
open Wu2008DoubleSieve Real Set MeasureTheory LiLiuPrereqBuchstab
open SecondFunctionalFourSevenths SharpLogRecurrence JointLogTotalComparison
noncomputable section

/-- Forced by the already-used 7/4 tangent and the existing universal V bound. -/
def cap : ℝ := 634483/1118040

theorem cap_identity : cap = (8/7+V (7/4))/3 := by
  norm_num [cap,V,upperLog,lowerLog]

theorem cap_bounds : (1:ℝ)/2 ≤ cap ∧ cap < 4/7 := by norm_num [cap]

/-- No new anchor: the previous 7/4 tangent, with its original analytic bound paid by V. -/
theorem tangent {y : ℝ} (hy : 0 < y) :
    log y ≤ (4/7)*y + V (7/4)-1 := by
  have h := log_le_sub_one_of_pos (div_pos hy (by norm_num : (0:ℝ)<7/4))
  rw [log_div hy.ne' (by norm_num)] at h
  have hv := log_le_V (by norm_num : (1:ℝ)≤7/4)
  linarith only [h,hv]

theorem seed {u : ℝ} (hu : 1 ≤ cap*u) (hu3 : u ≤ 3) : buchstab u ≤ cap := by
  have hc : 0 < cap := by norm_num [cap]
  have hu0 : 0 < u := by nlinarith
  by_cases h2 : u ≤ 2
  · rw [buchstab_eq_one_div (by have := cap_bounds.2; nlinarith) h2]
    exact (div_le_iff₀ hu0).2 (by nlinarith only [hu])
  · rw [buchstab_log_segment (le_of_not_ge h2) hu3]
    apply (div_le_iff₀ hu0).2
    have ht := tangent (y:=u-1) (by linarith)
    have hi := cap_identity
    have hb := cap_bounds.2
    nlinarith only [ht,hi,hb,hu3]

theorem step {v : ℝ} (hv : 3 ≤ v)
    (hh : ∀ t : ℝ, 1 ≤ cap*t → t ≤ v → buchstab t ≤ cap)
    {u : ℝ} (hvu : v ≤ u) (hu : u ≤ v+1) : buchstab u ≤ cap := by
  have hcap := cap_bounds.1
  have hcv : 1 ≤ cap*v := by nlinarith
  have hi := intervalIntegral.integral_mono_on (μ:=volume) (show v-1 ≤ u-1 by linarith)
    (continuous_buchstab.intervalIntegrable (v-1) (u-1))
    (intervalIntegrable_const (c:=cap))
    (fun t ht => hh t (by nlinarith [ht.1]) (by linarith [ht.2]))
  rw [intervalIntegral.integral_const] at hi
  simp only [smul_eq_mul] at hi
  have he := buchstab_increment (by linarith : 2 ≤ v) hvu
  have hb := mul_le_mul_of_nonneg_left (hh v hcv le_rfl) (by linarith : 0 ≤ v)
  have hub : u*buchstab u ≤ u*cap := by nlinarith only [hi,he,hb]
  exact (mul_le_mul_iff_right₀ (by linarith : 0<u)).mp hub

theorem tail_prefix (n : ℕ) : ∀ u : ℝ, 1 ≤ cap*u → u ≤ (n:ℝ)+3 → buchstab u ≤ cap := by
  induction n with
  | zero => simpa using fun u hu hu3 => seed (u:=u) hu hu3
  | succ n ih =>
    intro u hu hu'
    by_cases hn : u ≤ (n:ℝ)+3
    · exact ih u hu hn
    · apply step (v:=(n:ℝ)+3) (by linarith [Nat.cast_nonneg (α:=ℝ) n]) ih (le_of_not_ge hn)
      push_cast at hu'
      linarith

/-- A uniform tail bound for the actual DDE solution, not a hypothesized table entry. -/
theorem buchstab_le {u : ℝ} (hu : 1 ≤ cap*u) : buchstab u ≤ cap := by
  obtain ⟨n,hn⟩ := exists_nat_gt u
  exact tail_prefix n u hu (by linarith)

#print axioms buchstab_le
end
end Wu04MainTail
