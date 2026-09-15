import MathlibNt.Wu2008DoubleSieve.FourSeventhsLog

namespace Wu2008DoubleSieve.SecondFunctionalFourSevenths
open Set Real MeasureTheory LiLiuPrereqBuchstab SecondFunctionalJointTail

/-- The actual history and actual integral DDE give the first logarithmic segment. -/
theorem buchstab_log_segment {u : ℝ} (hu : 2 ≤ u) (hu' : u ≤ 3) :
    buchstab u = (1 + log (u - 1)) / u := by
  have h := buchstab_integral_identity hu
  have he : (∫ v : ℝ in 1..u - 1, buchstab v) = log (u - 1) := by
    calc
      _ = ∫ v : ℝ in 1..u - 1, 1 / v := by
        apply intervalIntegral.integral_congr
        intro v hv
        rw [uIcc_of_le (by linarith : 1 ≤ u - 1)] at hv
        exact buchstab_eq_one_div hv.1 (by linarith [hv.2])
      _ = _ := by rw [integral_one_div_of_pos (by norm_num) (by linarith)]; simp
  rw [he] at h
  apply (eq_div_iff (by linarith : u ≠ 0)).2
  linarith

/-- A uniform seed, proved on an interval rather than checked at points. -/
theorem buchstab_seed {u : ℝ} (hu : (7 / 4 : ℝ) ≤ u) (hu' : u ≤ 3) :
    buchstab u ≤ 4 / 7 := by
  by_cases h2 : u ≤ 2
  · rw [buchstab_eq_one_div (by linarith) h2]
    apply (div_le_iff₀ (by linarith : 0 < u)).2
    linarith
  · rw [buchstab_log_segment (le_of_not_ge h2) hu']
    apply (div_le_iff₀ (by linarith : 0 < u)).2
    have h := log_tangent_four_sevenths (y := u - 1) (by linarith)
    linarith

/-- The true integrated DDE between arbitrary regular endpoints. -/
theorem buchstab_increment {u v : ℝ} (hv : 2 ≤ v) (hvu : v ≤ u) :
    u * buchstab u = v * buchstab v + ∫ t : ℝ in v - 1..u - 1, buchstab t := by
  have h1 := buchstab_integral_identity hv
  have h2 := buchstab_integral_identity (hv.trans hvu)
  have hi := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (continuous_buchstab.intervalIntegrable 1 (v - 1))
    (continuous_buchstab.intervalIntegrable (v - 1) (u - 1))
  linarith

/-- One whole real interval propagates from its actual delay history. -/
theorem buchstab_step {v : ℝ} (hv : 3 ≤ v)
    (hh : ∀ t : ℝ, (7 / 4 : ℝ) ≤ t → t ≤ v → buchstab t ≤ 4 / 7)
    {u : ℝ} (hvu : v ≤ u) (hu : u ≤ v + 1) : buchstab u ≤ 4 / 7 := by
  have hi := intervalIntegral.integral_mono_on (μ := volume) (show v - 1 ≤ u - 1 by linarith)
    (continuous_buchstab.intervalIntegrable (v - 1) (u - 1))
    (intervalIntegrable_const (c := (4 / 7 : ℝ)))
    (fun t ht => hh t (by linarith [ht.1]) (by linarith [ht.2]))
  rw [intervalIntegral.integral_const] at hi
  simp only [smul_eq_mul] at hi
  have he := buchstab_increment (by linarith : 2 ≤ v) hvu
  have hb := hh v (by linarith) le_rfl
  have hvb := mul_le_mul_of_nonneg_left hb (by linarith : 0 ≤ v)
  have hub : u * buchstab u ≤ u * (4 / 7) := by linarith
  exact (mul_le_mul_iff_right₀ (by linarith : 0 < u)).mp hub

/-- Natural induction covers increasingly long real intervals. -/
theorem buchstab_prefix (n : ℕ) :
    ∀ u : ℝ, (7 / 4 : ℝ) ≤ u → u ≤ (n : ℝ) + 3 → buchstab u ≤ 4 / 7 := by
  induction n with
  | zero => simpa using fun u hu hu' => buchstab_seed (u := u) hu hu'
  | succ n ih =>
    intro u hu hu'
    by_cases hn : u ≤ (n : ℝ) + 3
    · exact ih u hu hn
    · apply buchstab_step (v := (n : ℝ) + 3)
        (by linarith [Nat.cast_nonneg (α := ℝ) n]) ih (le_of_not_ge hn)
      push_cast at hu'
      linarith

/-- The fixed rational upper envelope for the actual Buchstab function on the full tail. -/
theorem buchstab_le_four_sevenths {u : ℝ} (hu : (7 / 4 : ℝ) ≤ u) :
    buchstab u ≤ 4 / 7 := by
  obtain ⟨n, hn⟩ := exists_nat_gt u
  exact buchstab_prefix n u hu (by linarith)

end Wu2008DoubleSieve.SecondFunctionalFourSevenths
