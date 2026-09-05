import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145CaseAHighSScalar

open scoped Classical BigOperators
open Filter Topology Asymptotics

namespace MathlibNt.SieveTheory

open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1600000

/-- Uniform high-coordinate threshold ensuring that the ambient Lemma-14.3
source parameter lies in the decreasing floor-tail regime.  This stronger
ambient form is exactly what the scalar absorption theorem consumes; the
natural-ceiling source is then smaller by `suzukiSourceL_natCeil_rpow_le`. -/
theorem claim145_caseA_highS_sourceLarge_eventually
    {C1 Θ : ℝ} (hC1 : 0 < C1) (hΘ : 0 ≤ Θ) :
    ∀ᶠ K : ℝ in atTop, 2 ≤ K ∧ ∀ (D : ℕ) (s : ℝ),
      2 ≤ D → 2 ≤ s → Real.sqrt K / Real.log K ≤ s →
      Real.log (D : ℝ) ≤ C1 * K ^ Θ →
      Real.exp 1 * suzukiSourceL (D : ℝ) K ≤ s - 2 := by
  let A : ℝ := Θ + 2 + |Real.log C1| + |Real.log (Real.log 2)|
  let B : ℝ := Real.exp 1 * A + 2
  have hA : 0 < A := by
    dsimp [A]
    linarith [abs_nonneg (Real.log C1), abs_nonneg (Real.log (Real.log 2))]
  have hB : 0 < B := by dsimp [B]; positivity
  have hlo :=
    (isLittleO_log_rpow_rpow_atTop 2 (show (0 : ℝ) < 1 / 2 by norm_num)).bound
      (show (0 : ℝ) < 1 / (B + 1) by positivity)
  filter_upwards [eventually_ge_atTop (3 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop 1, hlo] with K hK3 hlogK1 hloK
  have hK1 : 1 < K := by linarith
  have hK0 : 0 < K := by linarith
  have hlogK : 0 < Real.log K := Real.log_pos hK1
  have hsqrt0 : 0 ≤ Real.sqrt K := Real.sqrt_nonneg K
  have hpow0 : 0 ≤ K ^ (1 / 2 : ℝ) := Real.rpow_nonneg hK0.le _
  change |Real.log K ^ (2 : ℝ)| ≤
    1 / (B + 1) * |K ^ (1 / 2 : ℝ)| at hloK
  rw [Real.rpow_two, abs_of_nonneg (sq_nonneg _), abs_of_nonneg hpow0,
    ← Real.sqrt_eq_rpow] at hloK
  have hscaled := mul_le_mul_of_nonneg_left hloK hB.le
  have hfrac : B * (1 / (B + 1)) ≤ 1 := by
    rw [div_eq_mul_inv, ← mul_assoc]
    exact (div_le_one (by positivity : 0 < B + 1)).2 (by linarith)
  have hroot : B * (Real.log K) ^ 2 ≤ Real.sqrt K := by
    calc
      B * (Real.log K) ^ 2 ≤
          (B * (1 / (B + 1))) * Real.sqrt K := by nlinarith
      _ ≤ 1 * Real.sqrt K := mul_le_mul_of_nonneg_right hfrac hsqrt0
      _ = Real.sqrt K := one_mul _
  refine ⟨(show (2 : ℝ) ≤ K by linarith), ?_⟩
  intro D s hD hs hsqrt hsmall
  have hLD := claim145_caseA_highS_sourceL_le_logK
    (D := (D : ℝ)) (K := K) (C1 := C1) (Θ := Θ)
    (by exact_mod_cast hD) hK3 hlogK1 hC1 hΘ hsmall
  have hmain : Real.exp 1 * suzukiSourceL (D : ℝ) K + 2 ≤
      Real.sqrt K / Real.log K := by
    apply (le_div_iff₀ hlogK).2
    have hA0 : 0 ≤ A := hA.le
    have hlogK0 : 0 ≤ Real.log K := hlogK.le
    have hLD' : Real.exp 1 * suzukiSourceL (D : ℝ) K ≤
        Real.exp 1 * A * Real.log K := by
      calc
        Real.exp 1 * suzukiSourceL (D : ℝ) K ≤
            Real.exp 1 * (A * Real.log K) :=
          mul_le_mul_of_nonneg_left hLD (Real.exp_pos 1).le
        _ = Real.exp 1 * A * Real.log K := by ring
    have hleft :
        (Real.exp 1 * suzukiSourceL (D : ℝ) K + 2) * Real.log K ≤
          B * (Real.log K) ^ 2 := by
      dsimp [B]
      nlinarith
    exact hleft.trans hroot
  linarith


end MathlibNt.SieveTheory
