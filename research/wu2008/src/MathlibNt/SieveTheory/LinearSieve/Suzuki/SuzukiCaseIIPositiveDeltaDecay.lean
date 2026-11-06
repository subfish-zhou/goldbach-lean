import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIIEndpointQuantitative

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

/-- For fixed `A`, a positive power saving in `log D` is eventually absorbed by
any fixed positive relative margin.  The threshold is explicit (an exponential
of a real power), so no uninstantiated "large `D`" hypothesis remains. -/
theorem exists_log_rpow_decay_threshold
    (Δ A σ : ℝ) (_hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) (hA : 0 ≤ A) (hσ : 1 < σ) :
    ∃ D0 : ℝ, 1 < D0 ∧ ∀ D : ℝ, D0 ≤ D →
      A * (Real.log D) ^ (Δ - 1) ≤ (1 - Δ) / (8 * σ) := by
  let β : ℝ := 1 - Δ
  have hβ : 0 < β := sub_pos.mpr hΔ1
  by_cases hAz : A = 0
  · refine ⟨Real.exp 1, ?_, ?_⟩
    · exact Real.one_lt_exp_iff.mpr (by norm_num)
    · intro D hD
      rw [hAz, zero_mul]
      positivity
  · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
    let B : ℝ := (8 * σ * A) / β
    have hσ0 : 0 < σ := lt_trans (by norm_num) hσ
    have hB : 0 < B := by
      dsimp [B]
      positivity
    let T : ℝ := B ^ (1 / β)
    have hT : 0 < T := Real.rpow_pos_of_pos hB _
    have hTpow : T ^ β = B := by
      dsimp [T]
      rw [← Real.rpow_mul (le_of_lt hB)]
      have hexp : (1 / β) * β = 1 := by field_simp
      rw [hexp, Real.rpow_one]
    refine ⟨Real.exp T, ?_, ?_⟩
    · exact Real.one_lt_exp_iff.mpr hT
    · intro D hD
      have hDpos : 0 < D := lt_of_lt_of_le (Real.exp_pos T) hD
      have hlog : T ≤ Real.log D :=
        (Real.le_log_iff_exp_le hDpos).2 hD
      have hlogpos : 0 < Real.log D := lt_of_lt_of_le hT hlog
      have hpow : B ≤ (Real.log D) ^ β := by
        rw [← hTpow]
        exact Real.rpow_le_rpow (le_of_lt hT) hlog (le_of_lt hβ)
      have hden : 0 < (Real.log D) ^ β := Real.rpow_pos_of_pos hlogpos β
      have hmargin : 0 < β / (8 * σ) := by positivity
      have hscaled := mul_le_mul_of_nonneg_left hpow (le_of_lt hmargin)
      have hcancel : (β / (8 * σ)) * B = A := by
        dsimp [B]
        field_simp
      have hquot : A / ((Real.log D) ^ β) ≤ β / (8 * σ) := by
        rw [div_le_iff₀ hden]
        rw [← hcancel]
        exact hscaled
      have hexp : Δ - 1 = -β := by dsimp [β]; ring
      rw [hexp, Real.rpow_neg (le_of_lt hlogpos)]
      simpa [div_eq_mul_inv] using hquot



end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
