import MathlibNt.Wu2008DoubleSieve.FourSeventhsBuchstab

namespace WuSource.SrcBuchstab

open Set Real MeasureTheory LiLiuPrereqBuchstab
open Wu2008DoubleSieve.SecondFunctionalFourSevenths

theorem propagate_step {a v c : ℝ} (ha : 2 ≤ a) (hav : a + 1 ≤ v)
    (hh : ∀ t : ℝ, a ≤ t → t ≤ v → buchstab t ≤ c)
    {u : ℝ} (hvu : v ≤ u) (hu : u ≤ v + 1) : buchstab u ≤ c := by
  have hi := intervalIntegral.integral_mono_on (μ := volume)
    (show v - 1 ≤ u - 1 by linarith)
    (continuous_buchstab.intervalIntegrable (v - 1) (u - 1))
    (intervalIntegrable_const (c := c))
    (fun t ht => hh t (by linarith [ht.1]) (by linarith [ht.2]))
  rw [intervalIntegral.integral_const] at hi
  simp only [smul_eq_mul] at hi
  have he := buchstab_increment (by linarith : 2 ≤ v) hvu
  have hb := mul_le_mul_of_nonneg_left (hh v (by linarith) le_rfl)
    (by linarith : 0 ≤ v)
  exact (mul_le_mul_iff_right₀ (by linarith : 0 < u)).mp (by linarith)

theorem propagate_prefix {a c : ℝ} (ha : 2 ≤ a)
    (seed : ∀ t : ℝ, a ≤ t → t ≤ a + 1 → buchstab t ≤ c) (n : ℕ) :
    ∀ t : ℝ, a ≤ t → t ≤ a + 1 + (n : ℝ) → buchstab t ≤ c := by
  induction n with
  | zero => simpa using seed
  | succ n ih =>
    intro t ht ht'
    by_cases hn : t ≤ a + 1 + (n : ℝ)
    · exact ih t ht hn
    · apply propagate_step ha (le_add_of_nonneg_right (Nat.cast_nonneg n))
        ih (le_of_not_ge hn)
      push_cast at ht'
      linarith

theorem tail_of_unit_window {a c : ℝ} (ha : 2 ≤ a)
    (seed : ∀ t : ℝ, a ≤ t → t ≤ a + 1 → buchstab t ≤ c)
    {t : ℝ} (ht : a ≤ t) : buchstab t ≤ c := by
  obtain ⟨n, hn⟩ := exists_nat_gt t
  exact propagate_prefix ha seed n t ht (by linarith)

theorem fine_tail_of_initial_window
    (seed : ∀ t : ℝ, (17 / 5 : ℝ) ≤ t → t ≤ 22 / 5 →
      buchstab t ≤ 561522 / 1000000)
    {t : ℝ} (ht : (17 / 5 : ℝ) ≤ t) :
    buchstab t ≤ 561522 / 1000000 := by
  apply tail_of_unit_window (a := (17 / 5 : ℝ)) (by norm_num) _ ht
  intro u hu hu'
  exact seed u hu (by linarith)

#print axioms fine_tail_of_initial_window

end WuSource.SrcBuchstab
