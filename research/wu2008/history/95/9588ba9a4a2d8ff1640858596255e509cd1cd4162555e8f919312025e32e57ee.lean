import MathlibNt.Wu2008DoubleSieve.Omega3XReciprocal

/-! # Fixed-power payment on the original reciprocal coefficient mass -/

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology

theorem omega3_repeated_scalar_budget {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ((N : ℝ) / (N : ℝ) ^ η) * (1 + log N) ^ 3 ≤ ε * ((N : ℝ) / log N) := by
  have hlarge : ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ log N :=
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [box_eventually_log_power_budget 4
    (show 0 < 8 / ε by positivity) hη, hlarge, eventually_ge_atTop 1] with N hb hl hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hl0 : 0 < log (N : ℝ) := by linarith
  have hcube : (1 + log (N : ℝ)) ^ 3 ≤ 8 * log N ^ 3 := by
    calc
      _ ≤ (2 * log (N : ℝ)) ^ 3 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 3
      _ = _ := by ring
  calc
    _ ≤ ((N : ℝ) / (N : ℝ) ^ η) * (8 * log N ^ 3) :=
      mul_le_mul_of_nonneg_left hcube (by positivity)
    _ ≤ ((N : ℝ) / ((8 / ε) * log N ^ 4)) * (8 * log N ^ 3) :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left hNr.le (by positivity) hb) (by positivity)
    _ = _ := by field_simp

/-- The coefficient sum is preserved exactly, independently of its support size. -/
theorem omega3_repeated_weighted_floor_le {i N : ℕ}
    (W : Fin i → Finset ℕ) (S : ℕ → Finset (ℕ × ℕ × ℕ))
    {Y : ℝ} (hY : 0 < Y)
    (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (hS : ∀ d ∈ boxConvolutionSupport W, ∀ a ∈ S d,
      a.1 ∈ Icc 1 N ∧ a.2.1 ∈ Icc 1 N ∧ a.2.2 ∈ Icc 1 N)
    (hlow : ∀ d ∈ boxConvolutionSupport W, ∀ a ∈ S d, Y ≤ (a.1 : ℝ)) :
    (∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
      ∑ a ∈ S d, (⌊((N : ℝ) / ((d : ℝ) * a.1 * a.2.1 * a.2.2)) / a.1⌋₊ : ℝ)) ≤
        (((N : ℝ) / Y) * (1 + log N) ^ 3) * boxConvolutionReciprocalMass W := by
  unfold boxConvolutionReciprocalMass
  rw [mul_sum]
  apply sum_le_sum
  intro d hdS
  calc
    _ ≤ (convolutionCoeff W d : ℝ) *
        (((N : ℝ) / ((d : ℝ) * Y)) * (1 + log N) ^ 3) :=
      mul_le_mul_of_nonneg_left
        (omega3_triple_repeated_floor_le N d (S d) (hd d hdS) hY
          (hS d hdS) (hlow d hdS)) (Nat.cast_nonneg _)
    _ = _ := by ring

end Wu2008DoubleSieve
