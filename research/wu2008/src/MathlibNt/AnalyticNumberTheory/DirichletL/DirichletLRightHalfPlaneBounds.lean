import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.DirichletCharacter.Bounds

open Complex MeasureTheory Set

namespace AnalyticNumberTheory.LargeSieve

/-- Explicit integral-comparison bound for the real zeta majorant. -/
theorem tsum_nat_add_one_rpow_neg_le (σ : ℝ) (hσ : 1 < σ) :
    (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-σ)) ≤ 1 + 1 / (σ - 1) := by
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) :=
    Real.summable_nat_rpow.mpr (by linarith : -σ < -1)
  have hsumm : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-σ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      ((summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-σ)) 1).mpr hbase)
  rw [hsumm.tsum_eq_zero_add]
  simp only [zero_add, Nat.cast_one, Real.one_rpow]
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-σ)) (Ici (1 : ℝ)) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith : -σ ≤ 0)).mono
      (Ici_subset_Ioi.2 zero_lt_one)
  have hanti' : AntitoneOn (fun x : ℝ => x ^ (-σ)) (Ici ((1 : ℕ) : ℝ)) := by
    norm_num
    exact hanti
  have hone : (0 : ℝ) < ((1 : ℕ) : ℝ) := by norm_num
  have htail := AntitoneOn.tsum_comp_add_le_integral (f := fun x : ℝ => x ^ (-σ))
    (1 : ℕ) hanti'
    (integrableOn_Ioi_rpow_of_lt (by linarith : -σ < -1) hone)
    (fun t ht => Real.rpow_nonneg (by
      have ht' := mem_Ioi.mp ht
      norm_num at ht' ⊢
      linarith) _)
  rw [integral_Ioi_rpow_of_lt (by linarith : -σ < -1) hone] at htail
  norm_num at htail
  have hid : -1 / (-σ + 1) = 1 / (σ - 1) := by
    rw [show -σ + 1 = -(σ - 1) by ring, div_neg]
    ring
  rw [hid] at htail
  simpa only [Nat.cast_add, Nat.cast_one, add_comm] using add_le_add_left htail 1

/-- The same majorant indexed from zero; its zero term vanishes. -/
theorem tsum_nat_rpow_neg_le (σ : ℝ) (hσ : 1 < σ) :
    (∑' n : ℕ, (n : ℝ) ^ (-σ)) ≤ 1 + 1 / (σ - 1) := by
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) :=
    Real.summable_nat_rpow.mpr (by linarith : -σ < -1)
  rw [hbase.tsum_eq_zero_add]
  norm_num [Real.zero_rpow (by linarith : -σ ≠ 0)]
  simpa only [Nat.cast_add, Nat.cast_one, one_div] using
    tsum_nat_add_one_rpow_neg_le σ hσ

/-- A Dirichlet L-series in its absolute half-plane is bounded by the elementary
zeta majorant, uniformly in the modulus, character and height. -/
theorem norm_dirichletLSeries_le {q : ℕ} (χ : DirichletCharacter ℂ q)
    (σ t : ℝ) (hσ : 1 < σ) :
    ‖LSeries (fun n : ℕ => χ n) (σ + Complex.I * t)‖ ≤ 1 + 1 / (σ - 1) := by
  have hs : 1 < (σ + Complex.I * t : ℂ).re := by simpa using hσ
  have hsum : Summable (LSeries.term (fun n : ℕ => χ n) (σ + Complex.I * t)) :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs
  have hre : (σ + Complex.I * t : ℂ).re = σ := by simp
  have hterm (n : ℕ) :
      ‖LSeries.term (fun n : ℕ => χ n) (σ + Complex.I * t) n‖ ≤ (n : ℝ) ^ (-σ) := by
    by_cases hn : n = 0
    · simp [LSeries.term, hn, Real.zero_rpow (by linarith : -σ ≠ 0)]
    · rw [LSeries.term, if_neg hn, norm_div,
        norm_natCast_cpow_of_re_ne_zero n (by rw [hre]; linarith), hre,
        Real.rpow_neg (Nat.cast_nonneg n)]
      simpa only [one_div] using
        div_le_div_of_nonneg_right (χ.norm_le_one n)
          (Real.rpow_nonneg (Nat.cast_nonneg n) σ)
  calc
    ‖LSeries (fun n : ℕ => χ n) (σ + Complex.I * t)‖
        ≤ ∑' n, ‖LSeries.term (fun n : ℕ => χ n) (σ + Complex.I * t) n‖ :=
      norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' n : ℕ, (n : ℝ) ^ (-σ) :=
      hsum.norm.tsum_le_tsum hterm
        (Real.summable_nat_rpow.mpr (by linarith : -σ < -1))
    _ ≤ 1 + 1 / (σ - 1) := tsum_nat_rpow_neg_le σ hσ

/-- Explicit uniform right-half-plane bound for the continued L-function. -/
theorem norm_dirichletLFunction_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (σ t : ℝ) (hσ : 1 < σ) :
    ‖χ.LFunction (σ + Complex.I * t)‖ ≤ 1 + 1 / (σ - 1) := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ (by simpa using hσ)]
  exact norm_dirichletLSeries_le χ σ t hσ

end AnalyticNumberTheory.LargeSieve