import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIIPositiveDeltaDecay

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

/-- Suzuki's source cutoff from Claim 14.5 (p.82):
`σ(D) = (log D)^(1/d) log(log(27D))`. -/
noncomputable def sourceSigma (D d : ℝ) : ℝ :=
  (Real.log D) ^ (1 / d) * Real.log (Real.log (27 * D))

/-- In the source range `0 < Δ < 1`, the hypothesis
`d > 7 / (1 - Δ)` leaves a genuine exponent gap. -/
lemma source_exponent_gap_pos
    {Δ d : ℝ} (hΔ1 : Δ < 1) (hd : 7 / (1 - Δ) < d) :
    0 < (1 - Δ) - 1 / d := by
  have hβ : 0 < 1 - Δ := sub_pos.mpr hΔ1
  have hq : 0 < 7 / (1 - Δ) := by positivity
  have hd0 : 0 < d := hq.trans hd
  have hrecip : 1 / d < (1 - Δ) / 7 := by
    have h := one_div_lt_one_div_of_lt hq hd
    have heq : 1 / (7 / (1 - Δ)) = (1 - Δ) / 7 := by
      field_simp [ne_of_gt hβ]
    rw [heq] at h
    exact h
  linarith

/-- A source-faithful positive-`Δ` endpoint decay theorem.  For every fixed
nonnegative coefficient `A`, the exact source cutoff `sourceSigma D d` is
absorbed eventually.  The threshold is built only from `exp`, `max`, and real
powers; no `D`-dependent inequality is left among the premises. -/
theorem exists_sourceSigma_positive_delta_decay_threshold
    (Δ d A : ℝ) (_hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d) (hA : 0 ≤ A) :
    ∃ D0 : ℝ, 1 < D0 ∧ ∀ D : ℝ, D0 ≤ D →
      A * (Real.log D) ^ (Δ - 1) ≤
        (1 - Δ) / (16 * sourceSigma D d) := by
  let β : ℝ := 1 - Δ
  have hβ : 0 < β := sub_pos.mpr hΔ1
  have hq : 0 < 7 / β := by positivity
  have hd0 : 0 < d := hq.trans hd
  let γ : ℝ := β - 1 / d
  have hγ : 0 < γ := by
    dsimp [γ, β]
    exact source_exponent_gap_pos hΔ1 hd
  let a : ℝ := γ / 2
  have ha : 0 < a := by dsimp [a]; positivity
  let C : ℝ := max 1 (64 * A / (β * γ))
  have hC1 : 1 ≤ C := le_max_left _ _
  have hCpos : 0 < C := zero_lt_one.trans_le hC1
  let X : ℝ := max 2 (max (Real.log 27) (C ^ (1 / a)))
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
    (le_max_left (Real.log 27) (C ^ (1 / a))).trans (le_max_right 2 _)
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
  have hlog2_le : Real.log 2 ≤ Real.log x := by
    exact Real.strictMonoOn_log.monotoneOn (by norm_num) hxpos hx2
  have hll_le_two_log : Real.log (Real.log (27 * D)) ≤ 2 * Real.log x := by
    rw [hlog_two_x] at hlog_inner
    linarith
  have hlogx_bound : Real.log x ≤ x ^ a / a := by
    exact Real.log_le_rpow_div hxpos.le ha
  have hll_bound : Real.log (Real.log (27 * D)) ≤ (4 / γ) * x ^ a := by
    calc
      Real.log (Real.log (27 * D)) ≤ 2 * Real.log x := hll_le_two_log
      _ ≤ 2 * (x ^ a / a) := mul_le_mul_of_nonneg_left hlogx_bound (by norm_num)
      _ = (4 / γ) * x ^ a := by dsimp [a]; field_simp; ring
  have hCrootX : C ^ (1 / a) ≤ X :=
    (le_max_right (Real.log 27) (C ^ (1 / a))).trans (le_max_right 2 _)
  have hCrootx : C ^ (1 / a) ≤ x := hCrootX.trans hx
  have hxaC : C ≤ x ^ a := by
    have hr := Real.rpow_le_rpow (Real.rpow_nonneg hCpos.le _) hCrootx ha.le
    have hpow : (C ^ (1 / a)) ^ a = C := by
      rw [← Real.rpow_mul hCpos.le]
      have : (1 / a) * a = 1 := by field_simp
      rw [this, Real.rpow_one]
    rw [hpow] at hr
    exact hr
  have hxpowγ : x ^ (Δ - 1) * x ^ (1 / d) = x ^ (-γ) := by
    rw [← Real.rpow_add hxpos]
    congr 1
    dsimp [γ, β]
    ring
  have hsigpos : 0 < sourceSigma D d := by
    dsimp [sourceSigma]
    have hfirst : 0 < x ^ (1 / d) := Real.rpow_pos_of_pos hxpos _
    have hllpos : 0 < Real.log (Real.log (27 * D)) := by
      apply Real.log_pos
      rw [hlog27D]
      have hlog27pos : 0 < Real.log (27 : ℝ) := Real.log_pos (by norm_num)
      linarith
    exact mul_pos hfirst hllpos
  have hdecay : (4 * A / γ) * x ^ (-a) ≤ β / 16 := by
    have hcoef : 64 * A / (β * γ) ≤ C := le_max_right _ _
    have hcoefpow : 64 * A / (β * γ) ≤ x ^ a := hcoef.trans hxaC
    have hxa_pos : 0 < x ^ a := Real.rpow_pos_of_pos hxpos _
    rw [Real.rpow_neg hxpos.le]
    change (4 * A / γ) / (x ^ a) ≤ β / 16
    rw [div_le_iff₀ hxa_pos]
    have hscaled := mul_le_mul_of_nonneg_right hcoefpow
      (show 0 ≤ β / 16 by positivity)
    calc
      4 * A / γ = (64 * A / (β * γ)) * (β / 16) := by
        field_simp
        ring
      _ ≤ x ^ a * (β / 16) := hscaled
      _ = β / 16 * x ^ a := by ring
  have hproduct :
      (A * x ^ (Δ - 1)) * sourceSigma D d ≤ β / 16 := by
    calc
      (A * x ^ (Δ - 1)) * sourceSigma D d =
          A * x ^ (-γ) * Real.log (Real.log (27 * D)) := by
            dsimp [sourceSigma]
            change A * x ^ (Δ - 1) *
              (x ^ (1 / d) * Real.log (Real.log (27 * D))) = _
            rw [← hxpowγ]
            ring
      _ ≤ A * x ^ (-γ) * ((4 / γ) * x ^ a) := by
            exact mul_le_mul_of_nonneg_left hll_bound
              (mul_nonneg hA (Real.rpow_nonneg hxpos.le _))
      _ = (4 * A / γ) * x ^ (-a) := by
            calc
              A * x ^ (-γ) * ((4 / γ) * x ^ a) =
                  (4 * A / γ) * (x ^ (-γ) * x ^ a) := by ring
              _ = (4 * A / γ) * x ^ (-γ + a) := by
                    rw [Real.rpow_add hxpos]
              _ = (4 * A / γ) * x ^ (-a) := by
                    have : -γ + a = -a := by dsimp [a]; ring
                    rw [this]
      _ ≤ β / 16 := hdecay
  apply (le_div_iff₀ (show 0 < 16 * sourceSigma D d by positivity)).2
  change (A * x ^ (Δ - 1)) * (16 * sourceSigma D d) ≤ β
  nlinarith [hproduct]


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
