import MathlibNt.Wu2008DoubleSieve.SecondFunctionalPositiveFinite
import MathlibNt.Wu2008DoubleSieve.ImprovementCrossUpper

namespace Wu2008DoubleSieve.SecondFunctionalLowerPositive
open Set MeasureTheory
open scoped Interval

/-- The actual upper-gain kernel is integrable; no continuity of H is assumed. -/
theorem actual_kernel_integrable {s : ℝ} (hs : 2 ≤ s) (ht : s ≤ 7/2) :
    IntervalIntegrable (fun u => wuImprovementLimit true (1/1000) u / u)
      volume (s-1) (5/2) :=
  wuImprovementLimit_div_intervalIntegrable true (by norm_num) (by norm_num)
    (by linarith) (by linarith) (by norm_num)

/-- Strictness comes from the continuous reciprocal, not from continuity of H. -/
theorem reciprocal_integral_strict {s : ℝ} (hs : 2 ≤ s) (ht : s < 7/2) :
    (7/2-s)*(2/5) < ∫ u in (s-1)..(5/2 : ℝ), 1/u := by
  have hab : s-1 < (5/2 : ℝ) := by linarith
  have hc : ContinuousOn (fun u : ℝ => 1/u) (Icc (s-1) (5/2)) :=
    continuousOn_const.div continuousOn_id (fun u hu => by change u ≠ 0; linarith [hu.1])
  have hi := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    hab (continuousOn_const : ContinuousOn (fun _ : ℝ => (2/5 : ℝ)) _)
    hc (fun u hu => by
      apply (le_div_iff₀ (show 0 < u by linarith [hu.1])).2
      linarith [hu.2])
    ⟨s-1, ⟨le_rfl, hab.le⟩, by
      apply (lt_div_iff₀ (show 0 < s-1 by linarith)).2
      linarith⟩
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
  linarith only [hi]

/-- The original cross inequality transfers the upper seed into a lower gain. -/
theorem h_strict {s : ℝ} (hs : 2 ≤ s) (ht : s < 7/2) :
    (7/2-s)/750 < wuImprovementLimit false (1/1000) s := by
  have hab : s-1 ≤ (5/2 : ℝ) := by linarith
  have hc : ContinuousOn (fun u : ℝ => (1/300 : ℝ)/u) (Icc (s-1) (5/2)) :=
    continuousOn_const.div continuousOn_id (fun u hu => by change u ≠ 0; linarith [hu.1])
  have hi := intervalIntegral.integral_mono_on hab
    (hc.intervalIntegrable_of_Icc hab) (actual_kernel_integrable hs ht.le)
    (fun u hu => div_le_div_of_nonneg_right
      (SecondFunctionalPositiveFinite.H_strict (by linarith [hu.1]) hu.2).le
      (by linarith [hu.1]))
  have he : (∫ u in (s-1)..(5/2 : ℝ), (1/300 : ℝ)/u) =
      (1/300 : ℝ) * ∫ u in (s-1)..(5/2 : ℝ), 1/u := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext u
    ring
  rw [he] at hi
  have hr := reciprocal_integral_strict hs ht
  have hn := wuImprovementLimit_nonneg false (δ := (1/1000 : ℝ)) (s := (7/2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hx := wuImprovementLimit_lower_cross (δ := (1/1000 : ℝ)) (s := s)
    (t := (7/2 : ℝ)) (by norm_num) (by norm_num) hs ht.le (by norm_num)
  norm_num only at hx
  linarith

/-- The right endpoint retains nonnegativity, not an asserted strict gain. -/
theorem h_endpoint_nonneg : 0 ≤ wuImprovementLimit false (1/1000) (7/2) :=
  wuImprovementLimit_nonneg false (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The full rational endpoint margin. -/
theorem h_two_strict : (1/500 : ℝ) < wuImprovementLimit false (1/1000) 2 := by
  have h := h_strict (s := 2) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

/-- A strict uniform value bound, with no uniform finite threshold asserted. -/
theorem h_interval_strict {s : ℝ} (hs : 2 ≤ s) (ht : s ≤ 3) :
    (1/1500 : ℝ) < wuImprovementLimit false (1/1000) s := by
  have h := h_strict hs (by linarith)
  linarith

/-- Consume the exact gap of the original lower improvement. -/
theorem improvement_mem_succ (k : ℕ) {s : ℝ} (hs : 2 ≤ s) (ht : s ≤ 3) :
    (1/1500 : ℝ) ∈ wuEventualImprovements false (k+1) (1/1000) s := by
  have hm := wuImprovementLimit_sub_mem false k (δ := (1/1000 : ℝ)) (s := s)
    (ε := wuImprovementLimit false (1/1000) s - 1/1500)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
    (sub_pos.mpr (h_interval_strict hs ht))
  simpa only [sub_sub_cancel] using hm

/-- Membership for each fixed positive original depth. -/
theorem improvement_mem (k : ℕ) (hk : 1 ≤ k) {s : ℝ} (hs : 2 ≤ s) (ht : s ≤ 3) :
    (1/1500 : ℝ) ∈ wuEventualImprovements false k (1/1000) s := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  exact improvement_mem_succ l hs ht

/-- Literal original finite lower sieve; k and s precede the threshold. -/
theorem finite_source (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : 2 ≤ s) (ht : s ≤ 3) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ),
        wuSourceBox k (1/1000) N i Δ V →
        (wuLowerCoefficient s + 1/1500) *
          boxTheta N ((N : ℝ) ^ (1/2 - (1/1000 : ℝ)))
            (convolutionWuWindows N Δ V) ≤
          wuBoxPhi N (1/1000) (convolutionWuWindows N Δ V) s := by
  obtain ⟨M, hM⟩ := improvement_mem k hk hs ht
  refine ⟨max 4 M, le_max_left _ _, ?_⟩
  intro N hN he i Δ V hbox
  exact hM N ((le_max_right _ _).trans hN) ((le_max_left _ _).trans hN) he i Δ V hbox

end Wu2008DoubleSieve.SecondFunctionalLowerPositive
