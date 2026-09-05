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

/-- Source-legal endpoint form: `A / log D` is factored as the relative
coefficient `A * (log D)^(Δ-1)` times the source scale `(log D)^(-Δ)`. -/
theorem exists_one_div_log_relative_envelope
    (Δ A σ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) (hA : 0 ≤ A) (hσ : 1 < σ) :
    ∃ D0 : ℝ, 1 < D0 ∧ ∀ D : ℝ, D0 ≤ D →
      A / Real.log D ≤
        ((1 - Δ) / (8 * σ)) * (Real.log D) ^ (-Δ) := by
  obtain ⟨D0, hD0, hdec⟩ :=
    exists_log_rpow_decay_threshold Δ A σ hΔ0 hΔ1 hA hσ
  refine ⟨D0, hD0, ?_⟩
  intro D hD
  have hDone : 1 < D := lt_of_lt_of_le hD0 hD
  have hlogpos : 0 < Real.log D := Real.log_pos hDone
  have hfactor :
      A / Real.log D =
        (A * (Real.log D) ^ (Δ - 1)) * (Real.log D) ^ (-Δ) := by
    rw [mul_assoc, ← Real.rpow_add hlogpos]
    have hexp : Δ - 1 + -Δ = -(1 : ℝ) := by ring
    rw [hexp, Real.rpow_neg (le_of_lt hlogpos), Real.rpow_one]
    simp [div_eq_mul_inv]
  rw [hfactor]
  exact mul_le_mul_of_nonneg_right (hdec D hD)
    (Real.rpow_nonneg (le_of_lt hlogpos) (-Δ))

/-- A source-style shrinking relative bracket: the fixed coefficient is
ultimately `O(1 / (σ * log log D))`, with an explicit exponential threshold. -/
theorem exists_log_rpow_decay_loglog_threshold
    (Δ A σ : ℝ) (_hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) (hA : 0 ≤ A) (hσ : 1 < σ) :
    ∃ D0 : ℝ, 1 < D0 ∧ ∀ D : ℝ, D0 ≤ D →
      A * (Real.log D) ^ (Δ - 1) ≤
        (1 - Δ) / (8 * σ * Real.log (Real.log D)) := by
  let β : ℝ := 1 - Δ
  have hβ : 0 < β := sub_pos.mpr hΔ1
  by_cases hAz : A = 0
  · refine ⟨Real.exp 2, Real.one_lt_exp_iff.mpr (by norm_num), ?_⟩
    intro D hD
    rw [hAz, zero_mul]
    have hDpos : 0 < D := lt_of_lt_of_le (Real.exp_pos 2) hD
    have hx : 2 ≤ Real.log D := (Real.le_log_iff_exp_le hDpos).2 hD
    have hloglog : 0 < Real.log (Real.log D) :=
      Real.log_pos (lt_of_lt_of_le (by norm_num) hx)
    positivity
  · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
    have hσ0 : 0 < σ := lt_trans (by norm_num) hσ
    let C : ℝ := (16 * σ * A) / β ^ 2
    have hC : 0 < C := by dsimp [C]; positivity
    let X : ℝ := max 2 (C ^ (2 / β))
    have hX2 : 2 ≤ X := le_max_left _ _
    have hXpos : 0 < X := lt_of_lt_of_le (by norm_num) hX2
    refine ⟨Real.exp X, Real.one_lt_exp_iff.mpr hXpos, ?_⟩
    intro D hD
    have hDpos : 0 < D := lt_of_lt_of_le (Real.exp_pos X) hD
    have hx : X ≤ Real.log D := (Real.le_log_iff_exp_le hDpos).2 hD
    have hx2 : 2 ≤ Real.log D := hX2.trans hx
    have hxpos : 0 < Real.log D := lt_of_lt_of_le (by norm_num) hx2
    have hloglog : 0 < Real.log (Real.log D) :=
      Real.log_pos (lt_of_lt_of_le (by norm_num) hx2)
    let y : ℝ := (Real.log D) ^ (β / 2)
    have hy : 0 < y := Real.rpow_pos_of_pos hxpos _
    have hCroot : C ≤ y := by
      have hroot_le_X : C ^ (2 / β) ≤ X := le_max_right _ _
      have hroot_le_x : C ^ (2 / β) ≤ Real.log D := hroot_le_X.trans hx
      have hrpow := Real.rpow_le_rpow (Real.rpow_nonneg hC.le _) hroot_le_x
        (by positivity : 0 ≤ β / 2)
      have hrootpow : (C ^ (2 / β)) ^ (β / 2) = C := by
        rw [← Real.rpow_mul hC.le]
        have he : (2 / β) * (β / 2) = 1 := by field_simp
        rw [he, Real.rpow_one]
      simpa [y, hrootpow] using hrpow
    have hlog_bound : Real.log (Real.log D) ≤ y / (β / 2) := by
      simpa [y] using Real.log_le_rpow_div (le_of_lt hxpos) (show 0 < β / 2 by positivity)
    have hfirst :
        8 * σ * A * Real.log (Real.log D) ≤
          8 * σ * A * (y / (β / 2)) :=
      mul_le_mul_of_nonneg_left hlog_bound (by positivity)
    have hscale := mul_le_mul_of_nonneg_right hCroot (show 0 ≤ β * y by positivity)
    have hsecond :
        8 * σ * A * (y / (β / 2)) ≤ β * (Real.log D) ^ β := by
      have hy_sq : y * y = (Real.log D) ^ β := by
        dsimp [y]
        rw [← Real.rpow_add hxpos]
        congr 1
        ring
      dsimp [C] at hscale
      calc
        8 * σ * A * (y / (β / 2)) = ((16 * σ * A) / β) * y := by
          field_simp
          ring
        _ = ((16 * σ * A) / β ^ 2) * (β * y) := by field_simp
        _ ≤ y * (β * y) := hscale
        _ = β * (y * y) := by ring
        _ = β * (Real.log D) ^ β := by rw [hy_sq]
    have hcore :
        A * (8 * σ * Real.log (Real.log D)) ≤ β * (Real.log D) ^ β := by
      calc
        A * (8 * σ * Real.log (Real.log D)) =
            8 * σ * A * Real.log (Real.log D) := by ring
        _ ≤ 8 * σ * A * (y / (β / 2)) := hfirst
        _ ≤ β * (Real.log D) ^ β := hsecond
    have hdenpow : 0 < (Real.log D) ^ β := Real.rpow_pos_of_pos hxpos _
    have hdenlog : 0 < 8 * σ * Real.log (Real.log D) := by positivity
    have hquot :
        A / (Real.log D) ^ β ≤ β / (8 * σ * Real.log (Real.log D)) := by
      apply (div_le_iff₀ hdenpow).2
      have haux :
          A ≤ (β * (Real.log D) ^ β) /
            (8 * σ * Real.log (Real.log D)) :=
        (le_div_iff₀ hdenlog).2 hcore
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using haux
    have hexp : Δ - 1 = -β := by dsimp [β]; ring
    rw [hexp, Real.rpow_neg hxpos.le]
    simpa [div_eq_mul_inv] using hquot

end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
