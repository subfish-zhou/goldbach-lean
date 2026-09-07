import MathlibNt.SieveTheory.LiLiuPrereqBuchstabBounds

open Set MeasureTheory
open scoped Interval

namespace LiLiuPrereqBuchstab

/-- The actual global Buchstab equation rebased at an arbitrary real anchor. -/
theorem buchstab_weighted_sub_eq_integral {a u : ℝ} (ha : 2 ≤ a) (hu : a ≤ u) :
    u * buchstab u - a * buchstab a = ∫ t in a..u, buchstab (t - 1) := by
  have hc : Continuous (fun t : ℝ => buchstab (t - 1)) :=
    continuous_buchstab.comp (continuous_id.sub continuous_const)
  have he := intervalIntegral.integral_add_adjacent_intervals
    (μ := volume) (hc.intervalIntegrable 2 a) (hc.intervalIntegrable a u)
  have hea := mul_buchstab_eq_integral ha
  have heu := mul_buchstab_eq_integral (ha.trans hu)
  linarith

/-- A proved upper bound on one complete unit interval propagates to the full tail.
No decimal bound or finite starting-interval certificate is assumed to exist here. -/
theorem buchstab_upper_on_tail {a W : ℝ} (ha : 2 ≤ a)
    (hbase : ∀ u ∈ Icc a (a + 1), buchstab u ≤ W) :
    ∀ u : ℝ, a ≤ u → buchstab u ≤ W := by
  have hstage : ∀ n : ℕ, ∀ u : ℝ, a ≤ u → u ≤ a + (n : ℝ) + 1 →
      buchstab u ≤ W := by
    intro n
    induction n with
    | zero =>
      intro u hu hub
      exact hbase u ⟨hu, by simpa using hub⟩
    | succ n ih =>
      intro u hu hub
      by_cases hsmall : u ≤ a + 1
      · exact hbase u ⟨hu, hsmall⟩
      have hlu : a + 1 ≤ u := (lt_of_not_ge hsmall).le
      have hc : Continuous (fun t : ℝ => buchstab (t - 1)) :=
        continuous_buchstab.comp (continuous_id.sub continuous_const)
      have hi := intervalIntegral.integral_mono_on hlu
        (hc.intervalIntegrable (a + 1) u)
        (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => W) volume (a + 1) u)
        (fun t ht => ih (t - 1) (by linarith [ht.1]) (by
          push_cast at hub
          linarith [ht.2]))
      simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
      have he := buchstab_weighted_sub_eq_integral (a := a + 1) (by linarith) hlu
      have hb := hbase (a + 1) ⟨by linarith, le_rfl⟩
      have hp := mul_le_mul_of_nonneg_left hb (show 0 ≤ a + 1 by linarith)
      have hup : 0 < u := by linarith
      apply (mul_le_mul_iff_right₀ hup).mp
      nlinarith
  intro u hu
  obtain ⟨n, hn⟩ := exists_nat_gt (u - a)
  exact hstage n u hu (by linarith)

end LiLiuPrereqBuchstab