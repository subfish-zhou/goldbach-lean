import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIISourceSigmaDecay

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

lemma source_two_exponent_gap_pos
    {Δ d : ℝ} (hΔ1 : Δ < 1) (hd : 7 / (1 - Δ) < d) :
    0 < (1 - Δ) - 2 / d := by
  have hβ : 0 < 1 - Δ := sub_pos.mpr hΔ1
  have hq : 0 < 7 / (1 - Δ) := by positivity
  have hd0 : 0 < d := hq.trans hd
  have hseven : 7 < d * (1 - Δ) := (div_lt_iff₀ hβ).mp hd
  apply sub_pos.mpr
  apply (div_lt_iff₀ hd0).mpr
  linarith

/-- An explicit threshold absorbing the *quadratic* source-cutoff growth into
`(log D)^(Δ-1)`.  In particular, the coefficient may itself be linear in
`sourceSigma D d`; no `D`-dependent premise remains. -/
theorem exists_sourceSigma_sq_positive_delta_decay_threshold
    (Δ d A : ℝ) (_hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d) (hA : 0 ≤ A) :
    ∃ D0 : ℝ, 1 < D0 ∧ ∀ D : ℝ, D0 ≤ D →
      A * sourceSigma D d * (Real.log D) ^ (Δ - 1) ≤
        (1 - Δ) / (32 * sourceSigma D d) := by
  let β : ℝ := 1 - Δ
  have hβ : 0 < β := sub_pos.mpr hΔ1
  have hq : 0 < 7 / β := by positivity
  have hd0 : 0 < d := hq.trans hd
  let γ : ℝ := β - 2 / d
  have hγ : 0 < γ := by
    dsimp [γ, β]
    exact source_two_exponent_gap_pos hΔ1 hd
  let a : ℝ := γ / 4
  have ha : 0 < a := by dsimp [a]; positivity
  let b : ℝ := γ / 2
  have hb : 0 < b := by dsimp [b]; positivity
  let C : ℝ := max 1 (2048 * A / (β * γ ^ 2))
  have hC1 : 1 ≤ C := le_max_left _ _
  have hCpos : 0 < C := zero_lt_one.trans_le hC1
  let X : ℝ := max 2 (max (Real.log 27) (C ^ (1 / b)))
  have hX2 : 2 ≤ X := le_max_left _ _
  have hXpos : 0 < X := by linarith
  refine ⟨Real.exp X, Real.one_lt_exp_iff.mpr hXpos, ?_⟩
  intro D hD
  have hDpos : 0 < D := (Real.exp_pos X).trans_le hD
  have hx : X ≤ Real.log D := (Real.le_log_iff_exp_le hDpos).2 hD
  let x : ℝ := Real.log D
  have hx2 : 2 ≤ x := hX2.trans hx
  have hxpos : 0 < x := by linarith
  have hlog27X : Real.log 27 ≤ X :=
    (le_max_left (Real.log 27) (C ^ (1 / b))).trans (le_max_right 2 _)
  have hlog27x : Real.log 27 ≤ x := hlog27X.trans hx
  have hlog27D : Real.log (27 * D) = Real.log 27 + x := by
    rw [Real.log_mul (by norm_num : (27 : ℝ) ≠ 0) (ne_of_gt hDpos)]
  have hinner_le : Real.log (27 * D) ≤ 2 * x := by
    rw [hlog27D]
    linarith
  have hinner_pos : 0 < Real.log (27 * D) := by
    rw [hlog27D]
    have : 0 < Real.log (27 : ℝ) := Real.log_pos (by norm_num)
    positivity
  have hlog_inner : Real.log (Real.log (27 * D)) ≤ Real.log (2 * x) :=
    Real.strictMonoOn_log.monotoneOn hinner_pos
      (show 0 < 2 * x by positivity) hinner_le
  have hlog_two_x : Real.log (2 * x) = Real.log 2 + Real.log x := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hxpos)]
  have hlog2_le : Real.log 2 ≤ Real.log x :=
    Real.strictMonoOn_log.monotoneOn (by norm_num) hxpos hx2
  have hll_le_two_log : Real.log (Real.log (27 * D)) ≤ 2 * Real.log x := by
    rw [hlog_two_x] at hlog_inner
    linarith
  have hlogx_bound : Real.log x ≤ x ^ a / a :=
    Real.log_le_rpow_div hxpos.le ha
  have hll_bound : Real.log (Real.log (27 * D)) ≤ (8 / γ) * x ^ a := by
    calc
      Real.log (Real.log (27 * D)) ≤ 2 * Real.log x := hll_le_two_log
      _ ≤ 2 * (x ^ a / a) := mul_le_mul_of_nonneg_left hlogx_bound (by norm_num)
      _ = (8 / γ) * x ^ a := by dsimp [a]; field_simp; ring
  have hllpos : 0 < Real.log (Real.log (27 * D)) := by
    apply Real.log_pos
    rw [hlog27D]
    have hlog27pos : 0 < Real.log (27 : ℝ) := Real.log_pos (by norm_num)
    linarith
  have hboundpos : 0 ≤ (8 / γ) * x ^ a := by positivity
  have hll_sq_bound :
      Real.log (Real.log (27 * D)) ^ 2 ≤ ((8 / γ) * x ^ a) ^ 2 := by
    gcongr
  have hCrootX : C ^ (1 / b) ≤ X :=
    (le_max_right (Real.log 27) (C ^ (1 / b))).trans (le_max_right 2 _)
  have hCrootx : C ^ (1 / b) ≤ x := hCrootX.trans hx
  have hxbC : C ≤ x ^ b := by
    have hr := Real.rpow_le_rpow (Real.rpow_nonneg hCpos.le _) hCrootx hb.le
    have hpow : (C ^ (1 / b)) ^ b = C := by
      rw [← Real.rpow_mul hCpos.le]
      have : (1 / b) * b = 1 := by field_simp
      rw [this, Real.rpow_one]
    rw [hpow] at hr
    exact hr
  have hxpowγ : x ^ (Δ - 1) * (x ^ (1 / d)) ^ 2 = x ^ (-γ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hxpos.le, ← Real.rpow_add hxpos]
    congr 1
    dsimp [γ, β]
    ring
  have hsigpos : 0 < sourceSigma D d := by
    dsimp [sourceSigma]
    exact mul_pos (Real.rpow_pos_of_pos hxpos _) hllpos
  have hdecay : (64 * A / γ ^ 2) * x ^ (-b) ≤ β / 32 := by
    have hcoef : 2048 * A / (β * γ ^ 2) ≤ C := le_max_right _ _
    have hcoefpow : 2048 * A / (β * γ ^ 2) ≤ x ^ b := hcoef.trans hxbC
    have hxb_pos : 0 < x ^ b := Real.rpow_pos_of_pos hxpos _
    rw [Real.rpow_neg hxpos.le]
    change (64 * A / γ ^ 2) / (x ^ b) ≤ β / 32
    rw [div_le_iff₀ hxb_pos]
    have hscaled := mul_le_mul_of_nonneg_right hcoefpow
      (show 0 ≤ β / 32 by positivity)
    calc
      64 * A / γ ^ 2 = (2048 * A / (β * γ ^ 2)) * (β / 32) := by
        field_simp
        ring
      _ ≤ x ^ b * (β / 32) := hscaled
      _ = β / 32 * x ^ b := by ring
  have hproduct :
      (A * sourceSigma D d * x ^ (Δ - 1)) * sourceSigma D d ≤ β / 32 := by
    calc
      (A * sourceSigma D d * x ^ (Δ - 1)) * sourceSigma D d =
          A * x ^ (-γ) * Real.log (Real.log (27 * D)) ^ 2 := by
            dsimp [sourceSigma]
            rw [← hxpowγ]
            ring
      _ ≤ A * x ^ (-γ) * (((8 / γ) * x ^ a) ^ 2) := by
            exact mul_le_mul_of_nonneg_left hll_sq_bound
              (mul_nonneg hA (Real.rpow_nonneg hxpos.le _))
      _ = (64 * A / γ ^ 2) * x ^ (-b) := by
            calc
              A * x ^ (-γ) * (((8 / γ) * x ^ a) ^ 2) =
                  (64 * A / γ ^ 2) * (x ^ (-γ) * (x ^ a * x ^ a)) := by
                    field_simp
                    ring
              _ = (64 * A / γ ^ 2) * x ^ (-γ + (a + a)) := by
                    rw [← Real.rpow_add hxpos, ← Real.rpow_add hxpos]
              _ = (64 * A / γ ^ 2) * x ^ (-b) := by
                    have hexp : -γ + (a + a) = -b := by dsimp [a, b]; ring
                    rw [hexp]
      _ ≤ β / 32 := hdecay
  apply (le_div_iff₀ (show 0 < 32 * sourceSigma D d by positivity)).2
  change (A * sourceSigma D d * x ^ (Δ - 1)) * (32 * sourceSigma D d) ≤ β
  nlinarith [hproduct]

/-- The same explicit threshold also absorbs the `1 / log D` endpoint scale. -/
theorem exists_sourceSigma_sq_one_div_log_decay_threshold
    (Δ d A : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d) (hA : 0 ≤ A) :
    ∃ D0 : ℝ, 1 < D0 ∧ ∀ D : ℝ, D0 ≤ D →
      A * sourceSigma D d / Real.log D ≤
        (1 - Δ) / (32 * sourceSigma D d) := by
  obtain ⟨D0, hD0, hmain⟩ :=
    exists_sourceSigma_sq_positive_delta_decay_threshold Δ d A hΔ0 hΔ1 hd hA
  let D1 : ℝ := max D0 (Real.exp 2)
  have hD1 : 1 < D1 := hD0.trans_le (le_max_left _ _)
  refine ⟨D1, hD1, ?_⟩
  intro D hD
  have hD0D : D0 ≤ D := (le_max_left D0 (Real.exp 2)).trans hD
  have hexpD : Real.exp 2 ≤ D := (le_max_right D0 (Real.exp 2)).trans hD
  have hDpos : 0 < D := (Real.exp_pos 2).trans_le hexpD
  have hxtwo : 2 ≤ Real.log D := (Real.le_log_iff_exp_le hDpos).2 hexpD
  have hxpos : 0 < Real.log D := by linarith
  have hxone : 1 ≤ Real.log D := by linarith
  have hpow_le : (Real.log D) ^ (-(1 : ℝ)) ≤ (Real.log D) ^ (Δ - 1) := by
    apply Real.rpow_le_rpow_of_exponent_le hxone
    linarith
  have hsig_nonneg : 0 ≤ sourceSigma D d := by
    have hsigpos : 0 < sourceSigma D d := by
      dsimp [sourceSigma]
      have hlog27D : Real.log (27 * D) = Real.log 27 + Real.log D := by
        rw [Real.log_mul (by norm_num : (27 : ℝ) ≠ 0) (ne_of_gt hDpos)]
      have hinner_one : 1 < Real.log (27 * D) := by
        rw [hlog27D]
        have hlog27pos : 0 < Real.log (27 : ℝ) := Real.log_pos (by norm_num)
        linarith
      exact mul_pos (Real.rpow_pos_of_pos hxpos _) (Real.log_pos hinner_one)
    exact hsigpos.le
  calc
    A * sourceSigma D d / Real.log D =
        A * sourceSigma D d * (Real.log D) ^ (-(1 : ℝ)) := by
          rw [Real.rpow_neg_one]
          simp [div_eq_mul_inv]
    _ ≤ A * sourceSigma D d * (Real.log D) ^ (Δ - 1) := by
          exact mul_le_mul_of_nonneg_left hpow_le (mul_nonneg hA hsig_nonneg)
    _ ≤ (1 - Δ) / (32 * sourceSigma D d) := hmain D hD0D


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
