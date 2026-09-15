import MathlibNt.Wu2008DoubleSieve.NinthMainMass
import MathlibNt.Wu2008DoubleSieve.Omega3XNormalization

/-!
# The coefficient-eight ninth-term upper bound

All density parameters are chosen after the requested error, before N.
The singular series is retained and its fixed positive lower bound pays
absolute errors. This is the actual project ninth term, not the whole
source eleven-term inequality.
-/

namespace Wu2008DoubleSieve

open Real Filter
open scoped Topology

private theorem ninth_density_parameters {ε : ℝ} (hε : 0 < ε) :
    ∃ z : ℝ, 0 < z ∧ z < 1 / 2 ∧
      ((1 + z) * (1 + z * exp (-eulerMascheroniConstant)) *
        (8 / (1 - 2 * z))) * (J9 + z) ≤ 8 * J9 + ε := by
  let f : ℝ → ℝ := fun z => ((1 + z) * (1 + z * exp (-eulerMascheroniConstant)) *
    (8 / (1 - 2 * z))) * (J9 + z)
  have hf : ContinuousAt f 0 := by
    dsimp [f]
    fun_prop (disch := norm_num)
  obtain ⟨d, hd, hfd⟩ := Metric.continuousAt_iff.mp hf ε hε
  let z := min (d / 2) (1 / 20)
  have hz : 0 < z := lt_min (by positivity) (by norm_num)
  have hzd : z < d := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hz20 : z ≤ 1 / 20 := min_le_right _ _
  have hdist : dist z 0 < d := by simpa only [Real.dist_eq, sub_zero, abs_of_pos hz] using hzd
  have h := (abs_lt.mp (show |f z - f 0| < ε by
    simpa only [Real.dist_eq] using hfd hdist)).2
  refine ⟨z, hz, by linarith, ?_⟩
  dsimp [f] at h ⊢
  norm_num at h
  linarith

theorem T9_upper_coefficient_eight {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((T9 N (ninthProfileW N) (ninthProfileU N)).card : ℝ) ≤
        (8 * J9 + ε) * wuSingularSeries N * N / log N ^ (2 : ℕ) := by
  have hc : 0 < wuSingularSeries 1 := wuSingularSeries_pos 1 (by norm_num)
  obtain ⟨z, hz, hzhi, hcoef⟩ := ninth_density_parameters (show 0 < ε / 2 by positivity)
  obtain ⟨T1, hT1, hupper⟩ := T9_upper_source_error_paid hz hzhi hz
    (show 0 < ε * wuSingularSeries 1 / 2 by positivity)
  obtain ⟨T2, _, hmass⟩ := X9_le_J9_add_epsilon hz
  refine ⟨max T1 T2, hT1.trans (le_max_left _ _), ?_⟩
  intro N hN he
  have hN1 := (le_max_left T1 T2).trans hN
  have hN2 := (le_max_right T1 T2).trans hN
  have hNp : 0 < N := by omega
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hC := wuSingularSeries_pos N hNp
  have hClow := wuSingularSeries_le_of_dvd (by norm_num : 0 < (1 : ℕ)) hNp (one_dvd N)
  let K := (1 + z) * (1 + z * exp (-eulerMascheroniConstant)) * (8 / (1 - 2 * z))
  have hK : 0 ≤ K := by
    have hden : 0 < 1 - 2 * z := by linarith
    dsimp [K]
    positivity
  have hm := mul_le_mul_of_nonneg_left (hmass N hN2)
    (show 0 ≤ K * wuSingularSeries N / log N by positivity)
  have hu := hupper N hN1 he
  change _ ≤ K * wuSingularSeries N / log N * X9 N + _ at hu
  have hc2 := mul_le_mul_of_nonneg_right hcoef
    (show 0 ≤ wuSingularSeries N * N / log N ^ (2 : ℕ) by positivity)
  have herr := mul_le_mul_of_nonneg_left hClow
    (show 0 ≤ ε / 2 * N / log N ^ (2 : ℕ) by positivity)
  calc
    _ ≤ K * wuSingularSeries N / log N * ((J9 + z) * N / log N) +
        (ε * wuSingularSeries 1 / 2) * N / log N ^ (2 : ℕ) := by linarith
    _ = (K * (J9 + z)) * (wuSingularSeries N * N / log N ^ (2 : ℕ)) +
        (ε / 2 * N / log N ^ (2 : ℕ)) * wuSingularSeries 1 := by ring
    _ ≤ (8 * J9 + ε / 2) * (wuSingularSeries N * N / log N ^ (2 : ℕ)) +
        (ε / 2 * N / log N ^ (2 : ℕ)) * wuSingularSeries N := add_le_add hc2 herr
    _ = _ := by ring

theorem variableS3Main_upper_F9 {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (variableS3Main N (ninthProfileW N) (ninthProfileU N) : ℝ) ≤
        (8 * J9 + ε) * wuSingularSeries N * N / log N ^ (2 : ℕ) := by
  have hc : 0 < wuSingularSeries 1 := wuSingularSeries_pos 1 (by norm_num)
  obtain ⟨T1, hT1, hT9⟩ := T9_upper_coefficient_eight (show 0 < ε / 2 by positivity)
  obtain ⟨T2, _, hpay⟩ := ninth_power_log_error_budget 0
    (show 0 < 5 / ninthProfileK2 ^ 2 by norm_num [ninthProfileK2])
    (show 0 < ninthProfileK1 by norm_num [ninthProfileK1])
    (show 0 < ε * wuSingularSeries 1 / 2 by positivity)
  refine ⟨max T1 T2, hT1.trans (le_max_left _ _), ?_⟩
  intro N hN he
  have hN1 := (le_max_left T1 T2).trans hN
  have hN2 := (le_max_right T1 T2).trans hN
  have hN512 := hT1.trans hN1
  have hNp : 0 < N := by omega
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hw := (ninth_fixed_cutoffs_ge hN512).1
  have hfinite := variableS3Main_le_T9_add_error (by omega : 4 ≤ N) he
    (by norm_num [ninthProfileK1] : 1 / 14 ≤ ninthProfileK1)
    (by norm_num [ninthProfileK1] : ninthProfileK1 ≤ 1 / 3)
    (by norm_num [ninthProfileK1, ninthProfileK2] : ninthProfileK1 ≤ ninthProfileK2) hw
  change (variableS3Main N (ninthProfileW N) (ninthProfileU N) : ℝ) ≤
    ((T9 N (ninthProfileW N) (ninthProfileU N)).card : ℝ) +
      (5 / ninthProfileK2 ^ 2) * (N : ℝ) ^ (1 - ninthProfileK1) at hfinite
  have heq : (5 / ninthProfileK2 ^ 2) * (N : ℝ) ^ (1 - ninthProfileK1) =
      (5 / ninthProfileK2 ^ 2) * N * log N ^ (0 : ℕ) / (N : ℝ) ^ ninthProfileK1 := by
    rw [rpow_sub (by positivity : (0 : ℝ) < N), rpow_one, pow_zero]
    ring
  rw [heq] at hfinite
  have hp := hpay N hN2
  have ht := hT9 N hN1 he
  have hClow := wuSingularSeries_le_of_dvd (by norm_num : 0 < (1 : ℕ)) hNp (one_dvd N)
  have herr := mul_le_mul_of_nonneg_left hClow
    (show 0 ≤ ε / 2 * N / log N ^ (2 : ℕ) by positivity)
  have hpaid : (ε * wuSingularSeries 1 / 2) * N / log N ^ (2 : ℕ) ≤
      ε / 2 * wuSingularSeries N * N / log N ^ (2 : ℕ) := by
    calc
      _ = (ε / 2 * N / log N ^ (2 : ℕ)) * wuSingularSeries 1 := by ring
      _ ≤ (ε / 2 * N / log N ^ (2 : ℕ)) * wuSingularSeries N := herr
      _ = _ := by ring
  calc
    _ ≤ (8 * J9 + ε / 2) * wuSingularSeries N * N / log N ^ (2 : ℕ) +
        ε / 2 * wuSingularSeries N * N / log N ^ (2 : ℕ) := by linarith
    _ = _ := by ring

end Wu2008DoubleSieve
