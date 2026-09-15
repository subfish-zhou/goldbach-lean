import MathlibNt.Wu2008DoubleSieve.CanonicalUpperDensity

/-!
# The true source level in the switched upper sieve

The density producer uses real level Q and natural Rosser level floor(Q)+1.
At Z=sqrt(Q) its ratio is exactly two, but log(Q) is not log(N)/2
when delta is fixed.
-/

namespace Wu2008DoubleSieve

open Real Filter
open scoped Topology

theorem omega3_source_sieve_geometry {N : ℕ} {δ : ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    let Q := (N : ℝ) ^ (1 / 2 - δ)
    let Z := sqrt Q
    1 < Q ∧ 1 < Z ∧ Z ≤ Q ∧ Z ≤ N ∧
      1 < ⌊Q⌋₊ + 1 ∧ Z ≤ (⌊Q⌋₊ + 1 : ℕ) ∧
      ⌊Q⌋₊ + 1 ≤ N + 1 ∧ log Q / log Z = 2 := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hα : 0 < 1 / 2 - δ := by linarith
  have hQ : 1 < (N : ℝ) ^ (1 / 2 - δ) := one_lt_rpow hNr hα
  have hQN : (N : ℝ) ^ (1 / 2 - δ) ≤ N := by
    simpa only [rpow_one] using
      rpow_le_rpow_of_exponent_le hNr.le (show 1 / 2 - δ ≤ 1 by linarith)
  have hZ : 1 < sqrt ((N : ℝ) ^ (1 / 2 - δ)) := by
    simpa only [sqrt_one] using sqrt_lt_sqrt zero_le_one hQ
  have hZQ : sqrt ((N : ℝ) ^ (1 / 2 - δ)) ≤ (N : ℝ) ^ (1 / 2 - δ) := by
    simpa only [sqrt_eq_rpow, rpow_one] using
      rpow_le_rpow_of_exponent_le hQ.le (show (1 / 2 : ℝ) ≤ 1 by norm_num)
  have hD : (N : ℝ) ^ (1 / 2 - δ) < (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1 : ℕ) := by
    exact_mod_cast Nat.lt_floor_add_one ((N : ℝ) ^ (1 / 2 - δ))
  have hfloor : ⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ ≤ N :=
    Nat.floor_le_of_le hQN
  refine ⟨hQ, hZ, hZQ, hZQ.trans hQN, ?_, hZQ.trans hD.le, by omega, ?_⟩
  · exact_mod_cast (hQ.trans hD)
  · have hlog : 0 < log ((N : ℝ) ^ (1 / 2 - δ)) := log_pos hQ
    have hzlog : log (sqrt ((N : ℝ) ^ (1 / 2 - δ))) =
        (1 / 2 : ℝ) * log ((N : ℝ) ^ (1 / 2 - δ)) := by
      rw [sqrt_eq_rpow, log_rpow (by positivity)]
    rw [hzlog]
    apply (div_eq_iff (mul_ne_zero (by norm_num) hlog.ne')).mpr
    ring

theorem omega3_source_sqrt_log {N : ℕ} {δ : ℝ} (hN : 0 < N) :
    log (sqrt ((N : ℝ) ^ (1 / 2 - δ))) = (1 / 4 - δ / 2) * log N := by
  rw [sqrt_eq_rpow, log_rpow (by positivity), log_rpow (by positivity)]
  ring

theorem omega3_source_le_sqrt_power {N : ℕ} {δ : ℝ}
    (hN : 0 < N) (hδhi : δ < 1 / 2) :
    (N : ℝ) = (sqrt ((N : ℝ) ^ (1 / 2 - δ))) ^ (2 / (1 / 2 - δ)) := by
  have hα : 1 / 2 - δ ≠ 0 := by linarith
  rw [sqrt_eq_rpow, ← rpow_mul (by positivity), ← rpow_mul (by positivity)]
  rw [show (1 / 2 - δ) * ((1 / 2 : ℝ) * (2 / (1 / 2 - δ))) = 1 by
    calc
      _ = (1 / 2 - δ) / (1 / 2 - δ) := by ring
      _ = 1 := div_self hα]
  rw [rpow_one]

theorem omega3_source_density_factor {N : ℕ} {δ ρ C : ℝ}
    (hN : 2 ≤ N) (hδhi : δ < 1 / 2) :
    ((exp eulerMascheroniConstant + ρ) *
      ((1 + ρ) * (2 * exp (-eulerMascheroniConstant) * C /
        log (sqrt ((N : ℝ) ^ (1 / 2 - δ)))))) =
      ((1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) * (8 / (1 - 2 * δ))) *
        C / log N := by
  have hlog : log (N : ℝ) ≠ 0 := ne_of_gt (log_pos (by exact_mod_cast (show 1 < N by omega)))
  have hden : 1 - 2 * δ ≠ 0 := by linarith
  rw [omega3_source_sqrt_log (by omega), exp_neg]
  rw [show (1 / 4 : ℝ) - δ / 2 = (1 - 2 * δ) / 4 by ring]
  field_simp [hden]
  ring

end Wu2008DoubleSieve
