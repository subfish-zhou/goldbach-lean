import MathlibNt.AnalyticNumberTheory.LargeSieve.DirectConductorWeight

/-! Shared finite coprimality-gate estimates for weighted supports. -/

open Classical Finset
open scoped BigOperators
open AnalyticNumberTheory.LargeSieve

namespace G11FiniteGate

theorem inv_totient_prime_le {p : ℕ} {z : ℝ}
    (hp : p.Prime) (hz : 0 < z) (hzp : z ≤ (p : ℝ)) :
    (p.totient : ℝ)⁻¹ ≤ 2 / z := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one]
  calc
    ((p : ℝ) - 1)⁻¹ ≤ ((p : ℝ) / 2)⁻¹ :=
      inv_anti₀ (by positivity) (by linarith)
    _ = 2 / (p : ℝ) := by field_simp
    _ ≤ 2 / z := div_le_div_of_nonneg_left (by norm_num) hz hzp

/-- Union bound over all distinct prime factors, including those of a composite cofactor. -/
theorem bad_inverseTotientMass_le {N Q m K : ℕ} {z : ℝ}
    (hQ : Q ≤ N) (hm : 0 < m) (hz : 0 < z)
    (hf : ∀ p ∈ m.primeFactors, z ≤ (p : ℝ))
    (hK : m.primeFactors.card ≤ K) :
    (∑ d ∈ Icc 1 Q, if ¬m.Coprime d then (d.totient : ℝ)⁻¹ else 0) ≤
      (2 * K / z) * conductorHarmonicFactor N ^ 2 := by
  calc
    _ ≤ ∑ d ∈ Icc 1 Q,
        ∑ p ∈ m.primeFactors, if p ∣ d then (d.totient : ℝ)⁻¹ else 0 := by
      apply sum_le_sum
      intro d _
      by_cases hbad : ¬m.Coprime d
      · obtain ⟨p, hp, hpm, hpd⟩ := Nat.Prime.not_coprime_iff_dvd.mp hbad
        rw [if_pos hbad]
        have hmem := Nat.mem_primeFactors.mpr ⟨hp, hpm, ne_of_gt hm⟩
        simpa only [if_pos hpd] using
          (single_le_sum (f := fun q => if q ∣ d then (d.totient : ℝ)⁻¹ else 0)
            (fun q (_ : q ∈ m.primeFactors) => by
            split_ifs <;> positivity) hmem :
            (if p ∣ d then (d.totient : ℝ)⁻¹ else 0) ≤ _)
      · rw [if_neg hbad]
        exact sum_nonneg (fun p _ => by split_ifs <;> positivity)
    _ = ∑ p ∈ m.primeFactors, directConductorWeight Q p := by
      rw [sum_comm]
      simp only [directConductorWeight, sum_filter]
    _ ≤ ∑ p ∈ m.primeFactors, conductorHarmonicFactor Q ^ 2 / (p.totient : ℝ) :=
      sum_le_sum (fun p _ => directConductorWeight_le Q p)
    _ ≤ ∑ _p ∈ m.primeFactors, conductorHarmonicFactor Q ^ 2 * (2 / z) := by
      apply sum_le_sum
      intro p hp
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left
        (inv_totient_prime_le (Nat.mem_primeFactors.mp hp).1 hz (hf p hp)) (sq_nonneg _)
    _ = (m.primeFactors.card : ℝ) * (conductorHarmonicFactor Q ^ 2 * (2 / z)) := by
      simp
    _ ≤ (K : ℝ) * (conductorHarmonicFactor Q ^ 2 * (2 / z)) := by
      apply mul_le_mul_of_nonneg_right (by exact_mod_cast hK)
      positivity
    _ = (2 * K / z) * conductorHarmonicFactor Q ^ 2 := by ring
    _ ≤ (2 * K / z) * conductorHarmonicFactor N ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (sq_le_sq₀ (conductorHarmonicFactor_nonneg Q)
        (conductorHarmonicFactor_nonneg N)).mpr (conductorHarmonicFactor_mono hQ)

theorem weightMass_le {N : ℕ} {S : Finset ℕ} {T : ℝ} {w : ℕ → ℝ}
    (hS : S ⊆ Icc 1 N) (hT : 0 ≤ T)
    (hw : ∀ m ∈ S, |w m| ≤ T / (m : ℝ)) :
    ∑ m ∈ S, |w m| ≤ T * conductorHarmonicFactor N := by
  calc
    _ ≤ ∑ m ∈ S, T / (m : ℝ) := sum_le_sum hw
    _ = T * ∑ m ∈ S, (m : ℝ)⁻¹ := by simp [div_eq_mul_inv, mul_sum]
    _ ≤ T * conductorHarmonicFactor N := by
      apply mul_le_mul_of_nonneg_left _ hT
      exact sum_le_sum_of_subset_of_nonneg hS (fun m _ _ => by positivity)

/-- A finite main-term gate budget, not a termwise estimate on AP errors. -/
theorem sum_gate_le_logCube {N Q K : ℕ} {S : Finset ℕ} {z T : ℝ} {w : ℕ → ℝ}
    (hN : 2 ≤ N) (hQ : Q ≤ N) (hz : 0 < z) (hT : 0 ≤ T)
    (hS : S ⊆ Icc 1 N)
    (hf : ∀ m ∈ S, ∀ p ∈ m.primeFactors, z ≤ (p : ℝ))
    (hK : ∀ m ∈ S, m.primeFactors.card ≤ K)
    (hw : ∀ m ∈ S, |w m| ≤ T / (m : ℝ)) :
    (∑ d ∈ Icc 1 Q, |(∑ m ∈ S.filter (fun m => ¬m.Coprime d), w m) /
      (d.totient : ℝ)|) ≤ (2 * K * T / z) * (1 + Real.log (N : ℝ)) ^ 3 := by
  have hlog : 0 ≤ 1 + Real.log (N : ℝ) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast (show 1 ≤ N by omega))
    linarith
  calc
    _ ≤ ∑ d ∈ Icc 1 Q, ∑ m ∈ S,
        (if ¬m.Coprime d then (d.totient : ℝ)⁻¹ else 0) * |w m| := by
      apply sum_le_sum
      intro d _
      calc
        _ = |∑ m ∈ S.filter (fun m => ¬m.Coprime d), w m| * (d.totient : ℝ)⁻¹ := by
          rw [div_eq_mul_inv, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (d.totient : ℝ)⁻¹)]
        _ ≤ (∑ m ∈ S.filter (fun m => ¬m.Coprime d), |w m|) *
            (d.totient : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right (abs_sum_le_sum_abs _ _) (by positivity)
        _ = _ := by
          rw [sum_mul, sum_filter]
          apply sum_congr rfl
          intro m _
          split_ifs <;> ring
    _ = ∑ m ∈ S,
        (∑ d ∈ Icc 1 Q, if ¬m.Coprime d then (d.totient : ℝ)⁻¹ else 0) * |w m| := by
      rw [sum_comm]
      simp only [sum_mul]
    _ ≤ ∑ m ∈ S, ((2 * K / z) * conductorHarmonicFactor N ^ 2) * |w m| := by
      apply sum_le_sum
      intro m hm
      exact mul_le_mul_of_nonneg_right
        (bad_inverseTotientMass_le hQ (mem_Icc.mp (hS hm)).1 hz (hf m hm) (hK m hm))
        (abs_nonneg _)
    _ = ((2 * K / z) * conductorHarmonicFactor N ^ 2) * ∑ m ∈ S, |w m| :=
      (mul_sum _ _ _).symm
    _ ≤ ((2 * K / z) * conductorHarmonicFactor N ^ 2) *
        (T * conductorHarmonicFactor N) :=
      mul_le_mul_of_nonneg_left (weightMass_le hS hT hw) (by positivity)
    _ = (2 * K * T / z) * conductorHarmonicFactor N ^ 3 := by ring
    _ ≤ (2 * K * T / z) * (1 + Real.log (N : ℝ)) ^ 3 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ (conductorHarmonicFactor_nonneg N)
        (conductorHarmonicFactor_le N) 3

end G11FiniteGate
