import Wu18938Campaign.M1.TailBuchstab

namespace Wu18938Campaign.M1

open Finset Wu2008DoubleSieve
open scoped Classical

theorem tail_pair_half_level_le_square {N c d : ℕ} (hN : 0 < N)
    {κ w u : ℝ}
    (ht : (c, d) ∈ truncatedSixthOmitted N ((N : ℝ) ^ κ) w u
      ((N : ℝ) ^ (1 / 2 - 2 * κ))) :
    (N : ℝ) ^ (1 / 2 : ℝ) / ((c : ℝ) * d) ≤ (c : ℝ) ^ 2 := by
  obtain ⟨ht, hprod⟩ := mem_filter.mp ht
  obtain ⟨hc, hd⟩ := mem_product.mp ht
  obtain ⟨hc, _, hzc, _⟩ := mem_primeWindow.mp hc
  have hd := (mem_primeWindow.mp hd).1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hc0 : (0 : ℝ) < c := by exact_mod_cast hc.pos
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.pos
  have hpow :
      (N : ℝ) ^ (1 / 2 - 2 * κ) * ((N : ℝ) ^ κ) ^ 2 =
        (N : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
    congr 1
    norm_num
    ring
  have hsq := pow_le_pow_left₀ (Real.rpow_nonneg hN0.le κ) hzc 2
  apply (div_le_iff₀ (mul_pos hc0 hd0)).mpr
  calc
    (N : ℝ) ^ (1 / 2 : ℝ) =
        (N : ℝ) ^ (1 / 2 - 2 * κ) * ((N : ℝ) ^ κ) ^ 2 := hpow.symm
    _ ≤ ((c : ℝ) * d) * (c : ℝ) ^ 2 :=
      mul_le_mul hprod hsq (sq_nonneg _) (mul_pos hc0 hd0).le
    _ = _ := mul_comm _ _

/-- Only the ordinary half-level lower-sieve substitution is excluded.
No conclusion about other distribution levels or double-sieve gains is made. -/
theorem target_tail_raised_s_lt_two {N c d : ℕ} (hN : 1 < N)
    {δ : ℝ} (hδ : 0 < δ)
    (ht : (c, d) ∈ truncatedSixthOmitted N ((N : ℝ) ^ (100 / 1327 : ℝ))
      ((N : ℝ) ^ (25 / 206 : ℝ)) ((N : ℝ) ^ (1 / 2 - 3 * (100 / 1327 : ℝ)))
      ((N : ℝ) ^ (1 / 2 - 2 * (100 / 1327 : ℝ)))) :
    Real.log ((N : ℝ) ^ (1 / 2 - δ) / ((c : ℝ) * d)) / Real.log c < 2 := by
  have hhalf := tail_pair_half_level_le_square (by omega : 0 < N) ht
  obtain ⟨hpair, _⟩ := mem_filter.mp ht
  obtain ⟨hc, hd⟩ := mem_product.mp hpair
  have hc := (mem_primeWindow.mp hc).1
  have hd := (mem_primeWindow.mp hd).1
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hc1 : (1 : ℝ) < c := by exact_mod_cast hc.one_lt
  have hc0 : (0 : ℝ) < c := by exact_mod_cast hc.pos
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.pos
  have hlevel :
      (N : ℝ) ^ (1 / 2 - δ) / ((c : ℝ) * d) < (c : ℝ) ^ 2 :=
    (div_lt_div_of_pos_right
      (Real.rpow_lt_rpow_of_exponent_lt hN1 (by linarith))
      (mul_pos hc0 hd0)).trans_le hhalf
  have hlog := Real.log_lt_log
    (div_pos (Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < N) _)
      (mul_pos hc0 hd0)) hlevel
  rw [Real.log_pow] at hlog
  exact (div_lt_iff₀ (Real.log_pos hc1)).mpr (by simpa using hlog)

end Wu18938Campaign.M1
