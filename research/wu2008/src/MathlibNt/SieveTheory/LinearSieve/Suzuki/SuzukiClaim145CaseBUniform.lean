import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145SourceBranchInterface
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145CaseBAllS
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped Classical BigOperators
open Filter Finset Topology
open Asymptotics Real

namespace MathlibNt.SieveTheory
open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 3600000

lemma log_two_pos : 0 < log 2 := log_pos (by norm_num)

lemma bound_K (K : ℝ) (hK : 2 ≤ K) : 1 + K / log 2 ≤ K * (1 + 1 / log 2) := by
  have h1 : (1 : ℝ) ≤ K := by linarith
  have h2 : K * (1 + 1 / log 2) = K + K / log 2 := by ring
  rw [h2]
  linarith

lemma log_bound (K : ℝ) (hK : 2 ≤ K) : log (1 + K / log 2) ≤ log K + log (1 + 1 / log 2) := by
  have h_pos1 : 0 < K := by linarith
  have h_pos2 : 0 < 1 + 1 / log 2 := by
    have : 0 < log 2 := log_pos (by norm_num)
    positivity
  have h_le : 1 + K / log 2 ≤ K * (1 + 1 / log 2) := bound_K K hK
  have h_pos3 : 0 < 1 + K / log 2 := by
    have : 0 < log 2 := log_pos (by norm_num)
    positivity
  have h_log_le := log_le_log h_pos3 h_le
  rw [log_mul (ne_of_gt h_pos1) (ne_of_gt h_pos2)] at h_log_le
  exact h_log_le

lemma log_bound_lower (K : ℝ) (hK : 2 ≤ K) : log K - log (log 2) ≤ log (1 + K / log 2) := by
  have h_pos1 : 0 < K := by linarith
  have h_pos2 : 0 < log 2 := log_pos (by norm_num)
  have h_le : K / log 2 ≤ 1 + K / log 2 := by linarith
  have h_pos3 : 0 < K / log 2 := div_pos h_pos1 h_pos2
  have h_log_le := log_le_log h_pos3 h_le
  rw [log_div (ne_of_gt h_pos1) (ne_of_gt h_pos2)] at h_log_le
  exact h_log_le

lemma abs_B_bound (K : ℝ) (hK : 2 ≤ K) :
  let B := -log (log 2) + log (1 + K / log 2)
  |B| ≤ log K + |log (1 + 1 / log 2)| + 2 * |log (log 2)| := by
  intro B
  have h_logK_nonneg : 0 ≤ log K := log_nonneg (by linarith)
  have h_upper : B ≤ log K + |log (1 + 1 / log 2)| + 2 * |log (log 2)| := by
    dsimp [B]
    have h1 := log_bound K hK
    have h2 : log (1 + 1 / log 2) ≤ |log (1 + 1 / log 2)| := le_abs_self _
    have h3 : -log (log 2) ≤ |log (log 2)| := neg_le_abs _
    have h4 : |log (log 2)| ≤ 2 * |log (log 2)| := by linarith [abs_nonneg (log (log 2))]
    linarith
  have h_lower : -(log K + |log (1 + 1 / log 2)| + 2 * |log (log 2)|) ≤ B := by
    dsimp [B]
    have h1 := log_bound_lower K hK
    have h3 : -log (log 2) ≤ |log (log 2)| := neg_le_abs _
    have h4 : log (log 2) ≤ |log (log 2)| := le_abs_self _
    have h5 : 0 ≤ |log (1 + 1 / log 2)| := abs_nonneg _
    linarith
  exact abs_le.mpr ⟨h_lower, h_upper⟩

lemma abs_logQ_bound (K : ℝ) (hK : 2 ≤ K) :
  let Q := log 2 / (1 + K / log 2)
  |log Q| ≤ log K + |log (1 + 1 / log 2)| + 2 * |log (log 2)| := by
  intro Q
  have h_logK_nonneg : 0 ≤ log K := log_nonneg (by linarith)
  have h_pos1 : 0 < log 2 := log_pos (by norm_num)
  have h_pos2 : 0 < 1 + K / log 2 := by positivity
  have h_logQ : log Q = log (log 2) - log (1 + K / log 2) := by
    dsimp [Q]
    rw [log_div (ne_of_gt h_pos1) (ne_of_gt h_pos2)]
  have h_upper : log Q ≤ log K + |log (1 + 1 / log 2)| + 2 * |log (log 2)| := by
    rw [h_logQ]
    have h1 := log_bound_lower K hK
    have h3 : log (log 2) ≤ |log (log 2)| := le_abs_self _
    have h5 : 0 ≤ |log (1 + 1 / log 2)| := abs_nonneg _
    linarith
  have h_lower : -(log K + |log (1 + 1 / log 2)| + 2 * |log (log 2)|) ≤ log Q := by
    rw [h_logQ]
    have h1 := log_bound K hK
    have h2 : log (1 + 1 / log 2) ≤ |log (1 + 1 / log 2)| := le_abs_self _
    have h3 : -log (log 2) ≤ |log (log 2)| := neg_le_abs _
    have h4 : -|log (log 2)| ≤ log (log 2) := neg_abs_le _
    have h5 : 0 ≤ |log (log 2)| := abs_nonneg _
    linarith
  exact abs_le.mpr ⟨h_lower, h_upper⟩

lemma q0_bound (K : ℝ) (hK : 2 ≤ K) (Θ : ℝ) (hΘ : 1 ≤ Θ) (hB : |-log (log 2) + log (1 + K / log 2)| ≤ log K + (|log (1 + 1 / log 2)| + 2 * |log (log 2)|)) (hQ_pos : |log (1 / ((1 / log 2) * (1 + K / log 2)))| ≤ log K + (|log (1 + 1 / log 2)| + 2 * |log (log 2)|)) :
  let C := |log (1 + 1 / log 2)| + 2 * |log (log 2)|
  let C_q0 := max 6 (max (C + 2) (max (C + 9) (exp 1 + 2)))
  let B := -log (log 2) + log (1 + K / log 2)
  let Q := 1 / ((1 / log 2) * (1 + K / log 2))
  let q0 := max 6 (max (|B| + 2) (max (9 + |log Q|) (exp 1 + 2)))
  q0 ≤ Θ * log K + C_q0 := by
  intro C C_q0 B Q q0
  have h_logK_nonneg : 0 ≤ log K := log_nonneg (by linarith)
  have h_logK_le_Θ : log K ≤ Θ * log K := by
    calc log K = 1 * log K := by ring
      _ ≤ Θ * log K := mul_le_mul_of_nonneg_right hΘ h_logK_nonneg
  have h_pos : 0 ≤ Θ * log K := by positivity
  dsimp [q0, C_q0]
  apply max_le
  · linarith [le_max_left 6 (max (C + 2) (max (C + 9) (exp 1 + 2)))]
  · apply max_le
    · have h_max1 : C + 2 ≤ max (C + 2) (max (C + 9) (exp 1 + 2)) := le_max_left _ _
      have h_max2 : max (C + 2) (max (C + 9) (exp 1 + 2)) ≤ max 6 (max (C + 2) (max (C + 9) (exp 1 + 2))) := le_max_right _ _
      have hh1 : |B| + 2 ≤ log K + C + 2 := by linarith
      linarith
    · apply max_le
      · have h_max3 : C + 9 ≤ max (C + 9) (exp 1 + 2) := le_max_left _ _
        have h_max4 : max (C + 9) (exp 1 + 2) ≤ max (C + 2) (max (C + 9) (exp 1 + 2)) := le_max_right _ _
        have h_max5 : max (C + 2) (max (C + 9) (exp 1 + 2)) ≤ max 6 (max (C + 2) (max (C + 9) (exp 1 + 2))) := le_max_right _ _
        have hh2 : 9 + |log Q| ≤ log K + C + 9 := by linarith
        linarith
      · have h_max6 : exp 1 + 2 ≤ max (C + 9) (exp 1 + 2) := le_max_right _ _
        have h_max7 : max (C + 9) (exp 1 + 2) ≤ max (C + 2) (max (C + 9) (exp 1 + 2)) := le_max_right _ _
        have h_max8 : max (C + 2) (max (C + 9) (exp 1 + 2)) ≤ max 6 (max (C + 2) (max (C + 9) (exp 1 + 2))) := le_max_right _ _
        linarith

/-- Claim 14.5 Case B with the analytic constants selected uniformly before the
varying bounding sieve.  The proof's threshold construction uses only the
Section-13 source contract and the scalar parameters; `S` first enters when the
pointwise local-product hypothesis is consumed. -/
theorem claim145_caseB_uniform_in_S
    (H : Section13HatLayers)
    {d Δ Θ : ℝ}
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d) (hTheta : 1 ≤ Θ)
    (hH : Section13HatSourceContract H) :
    ∃ C1min CB : ℝ, 0 < C1min ∧ 0 < CB ∧
      ∀ S : BoundingSieve,
        Claim145CaseBClosed S H d Δ Θ C1min CB := by
  rcases proposition131iiUniformQuantitativeLower_of_source hH with
    ⟨C, M, _hC, hM3, hprop⟩
  have hβ : 0 < 1 - Δ := sub_pos.mpr hΔ1
  have hd7 : 7 < d := by
    have hfrac : 7 ≤ 7 / (1 - Δ) := by
      rw [le_div_iff₀ hβ]
      nlinarith
    exact hfrac.trans_lt hd
  have hd0 : 0 < d := by linarith
  let a : ℝ := 1 / d
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by
    dsimp [a]
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
      (show (1 : ℝ) ≤ d by linarith)
    simpa using h
  have hdom0 := (isLittleO_log_rpow_rpow_atTop 2 ha).bound (show (0 : ℝ) < 1 / 2 by norm_num)
  have hdom : ∀ᶠ x : ℝ in atTop, 2 * (Real.log x) ^ 2 ≤ x ^ a := by
    filter_upwards [hdom0, eventually_ge_atTop (1 : ℝ)] with x hxdom hx1
    have hxpow : 0 ≤ x ^ a := Real.rpow_nonneg (by linarith) _
    rw [Real.rpow_two] at hxdom
    change |(Real.log x) ^ 2| ≤ 1 / 2 * |x ^ a| at hxdom
    rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg hxpow] at hxdom
    nlinarith
  obtain ⟨X, hX⟩ := eventually_atTop.1 hdom
  let r0 : ℝ := (C + 2 + Real.log 2) / (d - 4)
  let C_bound := |Real.log (1 + 1 / Real.log 2)| + 2 * |Real.log (Real.log 2)|
  let C_q0 := max 6 (max (C_bound + 2) (max (C_bound + 9) (Real.exp 1 + 2)))
  let C1min := max (Real.exp (max M (max (Real.exp r0) C_q0))) (max X (max 2 (Real.log 27)))
  have hC1min_pos : 0 < C1min := by
    dsimp [C1min]
    have : 0 < Real.exp (max M (max (Real.exp r0) C_q0)) := Real.exp_pos _
    exact this.trans_le (le_max_left _ _)
  refine ⟨C1min, 1, hC1min_pos, zero_lt_one, ?_⟩
  intro S
  intro C1 K N D s hC1min_C1 hK hlocal hD hs hC1_K_Theta hsigma
  have hDreal : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hD1 : 1 < D := by omega
  have hKpos : 0 < K := by linarith
  have hC145 : 0 ≤ (1 : ℝ) := zero_le_one
  have hDpos : 0 < (D : ℝ) := by linarith
  let D_real : ℝ := D
  let C145 : ℝ := 1
  let x : ℝ := Real.log D_real
  let q : ℝ := Real.log x
  let ell : ℝ := Real.log (Real.log (27 * D_real))
  let σ : ℝ := sourceSigma D_real d
  let L : ℝ := suzukiSourceL D_real K
  let u : ℝ := s / σ
  let b : ℝ := 1 + s ^ d / x

  have h_x_lower : C1min ≤ x := by
    have h_K_pow : 1 ≤ K ^ Θ := by
      have : (1:ℝ) ≤ K := by linarith
      exact Real.one_le_rpow this (by linarith)
    calc C1min ≤ C1min * 1 := by rw [mul_one]
      _ ≤ C1 * 1 := mul_le_mul_of_nonneg_right hC1min_C1 zero_le_one
      _ ≤ C1 * K ^ Θ := mul_le_mul_of_nonneg_left h_K_pow (hC1min_pos.le.trans hC1min_C1)
      _ ≤ x := hC1_K_Theta.le

  have hxX : X ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans h_x_lower)
  have hxrest : max 2 (Real.log 27) ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans h_x_lower)
  have hx2 : 2 ≤ x := (le_max_left 2 _).trans hxrest
  have hx27 : Real.log 27 ≤ x := (le_max_right 2 _).trans hxrest
  have hx : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith

  have hq_lower : max M (max (Real.exp r0) C_q0) ≤ q := by
    have h_exp : Real.exp (max M (max (Real.exp r0) C_q0)) ≤ x := (le_max_left _ _).trans h_x_lower
    exact (Real.le_log_iff_exp_le hx).mpr h_exp

  have hMq : M ≤ q := (le_max_left _ _).trans hq_lower
  have hqM : max M 0 ≤ q := max_le hMq (by linarith [hM3])

  have hlog27D : Real.log (27 * D_real) = Real.log 27 + x := by
    dsimp [x, D_real]
    have : (27:ℝ) ≠ 0 := by norm_num
    have : (D_real:ℝ) ≠ 0 := by positivity
    rw [Real.log_mul (by norm_num) (by positivity)]

  have hinnerLower : x ≤ Real.log (27 * D_real) := by
    rw [hlog27D]
    exact le_add_of_nonneg_left (Real.log_nonneg (by norm_num))

  have hq_ell : q ≤ ell := by
    dsimp [q, ell]
    exact Real.log_le_log hx hinnerLower

  have hq : 0 < q := by
    exact (Real.exp_pos r0).trans_le
      ((le_max_left (Real.exp r0) C_q0).trans
        ((le_max_right M (max (Real.exp r0) C_q0)).trans hq_lower))
  have hr0_q : Real.exp r0 ≤ q := (le_max_left _ _).trans ((le_max_right _ _).trans hq_lower)
  have hr : r0 ≤ Real.log q := (Real.le_log_iff_exp_le hq).mpr hr0_q


  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let B : ℝ := -Real.log (Real.log 2) + Real.log (1 + K / Real.log 2)
  let A : ℝ := (1 / Real.log 2) * (1 + K / Real.log 2)
  let Q : ℝ := 1 / A
  have hQ_pos : 0 < Q := by positivity
  have hApos : 0 < A := by
    dsimp [A]
    positivity
  let q0 : ℝ := max 6 (max (|B| + 2) (max (9 + |Real.log Q|) (Real.exp 1 + 2)))

  have hB_bound : |B| ≤ Real.log K +
      (|Real.log (1 + 1 / Real.log 2)| + 2 * |Real.log (Real.log 2)|) := by
    simpa [B, add_assoc] using abs_B_bound K hK
  have hlogQ_bound : |Real.log Q| ≤ Real.log K +
      (|Real.log (1 + 1 / Real.log 2)| + 2 * |Real.log (Real.log 2)|) := by
    have hdenpos : 0 < 1 + K / Real.log 2 := by positivity
    change |Real.log (1 / ((1 / Real.log 2) *
      (1 + K / Real.log 2)))| ≤ _
    rw [show (1 / ((1 / Real.log 2) * (1 + K / Real.log 2)) : ℝ) =
      Real.log 2 / (1 + K / Real.log 2) by
        field_simp [ne_of_gt hlog2, ne_of_gt hdenpos]]
    simpa [add_assoc] using abs_logQ_bound K hK
  have h_q0_bound : q0 ≤ Θ * Real.log K + C_q0 :=
    q0_bound K hK Θ hTheta hB_bound hlogQ_bound
  have h_Cq0_q : C_q0 ≤ q := (le_max_right (Real.exp r0) C_q0).trans ((le_max_right M (max (Real.exp r0) C_q0)).trans hq_lower)

  have hq_q0 : q0 ≤ q := by
    calc q0 ≤ Θ * Real.log K + C_q0 := h_q0_bound
      _ = Real.log (K ^ Θ) + C_q0 := by rw [Real.log_rpow (by linarith) Θ]
      _ ≤ Real.log (K ^ Θ) + Real.log C1 := by
        have : C_q0 ≤ Real.log C1min := by
          have h_exp : Real.exp C_q0 ≤ C1min := by
            calc Real.exp C_q0 ≤ Real.exp (max M (max (Real.exp r0) C_q0)) := Real.exp_le_exp.mpr ((le_max_right _ _).trans (le_max_right _ _))
              _ ≤ C1min := le_max_left _ _
          exact (Real.le_log_iff_exp_le hC1min_pos).mpr h_exp
        have : C_q0 ≤ Real.log C1 := this.trans (Real.log_le_log hC1min_pos hC1min_C1)
        linarith
      _ = Real.log (C1 * K ^ Θ) := by
        have hC1pos : 0 < C1 := hC1min_pos.trans_le hC1min_C1
        have hKpowpos : 0 < K ^ Θ := Real.rpow_pos_of_pos hKpos Θ
        rw [Real.log_mul (ne_of_gt hC1pos) (ne_of_gt hKpowpos)]
        ring
      _ ≤ Real.log x := by
        have hC1pos : 0 < C1 := hC1min_pos.trans_le hC1min_C1
        have hKpowpos : 0 < K ^ Θ := Real.rpow_pos_of_pos hKpos Θ
        exact Real.log_le_log (mul_pos hC1pos hKpowpos) hC1_K_Theta.le
      _ = q := rfl

  have hq4 : 4 ≤ q := by
    dsimp [q0] at hq_q0
    exact (show (4:ℝ) ≤ 6 by norm_num).trans ((le_max_left 6 _).trans hq_q0)
  have hqB : |B| + 2 ≤ q := (le_max_left _ _).trans ((le_max_right 6 _).trans hq_q0)
  have hqQ : 9 + |Real.log Q| ≤ q := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right 6 _).trans hq_q0))
  have hqe : Real.exp 1 + 2 ≤ q := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right 6 _).trans hq_q0))
  have hMq : M ≤ q := by
    dsimp [q, x]
    exact (le_max_left M 0).trans hqM
  have hr : r0 ≤ Real.log q := by simpa [r0, q, x] using hr
  have hlog27D : Real.log (27 * D_real) = Real.log 27 + x := by
    dsimp [x]
    rw [Real.log_mul (by norm_num : (27 : ℝ) ≠ 0) (ne_of_gt hDpos)]
  have hinnerLower : x ≤ Real.log (27 * D_real) := by
    rw [hlog27D]
    exact le_add_of_nonneg_left (Real.log_nonneg (by norm_num))
  have hinnerUpper : Real.log (27 * D_real) ≤ 2 * x := by
    rw [hlog27D]
    linarith
  have hinnerPos : 0 < Real.log (27 * D_real) := hx.trans_le hinnerLower
  have hellLower : q ≤ ell := by
    dsimp [q, ell]
    exact Real.log_le_log hx hinnerLower
  have hellUpper : ell ≤ 2 * q := by
    have h := Real.log_le_log hinnerPos hinnerUpper
    have hlog2leq : Real.log 2 ≤ q := by
      exact Real.strictMonoOn_log.monotoneOn (by norm_num) hx hx2
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hx)] at h
    dsimp [q] at hlog2leq
    dsimp [ell, q]
    linarith
  have hell : 0 < ell := hq.trans_le hellLower
  have hxa1 : 1 ≤ x ^ a := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1)
      hx1 ha.le
  have hxale : x ^ a ≤ x := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx1 ha1
  have hσdef : σ = x ^ a * ell := by rfl
  have hσLower : x ^ a * q ≤ σ := by
    rw [hσdef]
    exact mul_le_mul_of_nonneg_left hellLower (Real.rpow_nonneg hx.le _)
  have hσUpper : σ ≤ 2 * x * q := by
    rw [hσdef]
    nlinarith [mul_le_mul hxale hellUpper hell.le hx.le]
  have hσ4 : 4 ≤ σ := by
    calc 4 ≤ q := hq4
      _ ≤ x ^ a * q := by nlinarith
      _ ≤ σ := hσLower
  have hσpos : 0 < σ := by linarith
  have hsigma : σ ≤ s := by simpa [σ] using hsigma
  have hs4 : 4 ≤ s := hσ4.trans hsigma
  have hspos : 0 < s := by linarith
  have hu1 : 1 ≤ u := by
    dsimp [u]
    exact (le_div_iff₀ hσpos).2 (by simpa using hsigma)
  have hupos : 0 < u := zero_lt_one.trans_le hu1
  have hsu : s = σ * u := by
    dsimp [u]
    field_simp [ne_of_gt hσpos]
  have hlogu0 : 0 ≤ Real.log u := Real.log_nonneg hu1
  have hlogu_le : Real.log u ≤ u - 1 := Real.log_le_sub_one_of_pos hupos
  have hlogsSplit : Real.log s = Real.log σ + Real.log u := by
    rw [hsu, Real.log_mul (ne_of_gt hσpos) (ne_of_gt hupos)]
  have hLdef : L = q + B := by
    dsimp [L, q, x, B, suzukiSourceL]
    rw [Real.log_div (ne_of_gt hx) (ne_of_gt hlog2)]
    ring
  have hL : 1 ≤ L := by
    rw [hLdef]
    have hnegB : -|B| ≤ B := neg_abs_le B
    linarith
  have hLsq : L ≤ q ^ 2 := by
    rw [hLdef]
    have hBabs : B ≤ |B| := le_abs_self B
    nlinarith [sq_nonneg (q - 2)]
  have hdomx : 2 * q ^ 2 ≤ x ^ a := by
    simpa [q] using hX x hxX
  have habsorbσ : q ^ 2 + 9 * q + |Real.log Q| ≤ σ := by
    have htail : 9 * q + |Real.log Q| ≤ q ^ 2 := by
      have habs : 0 ≤ |Real.log Q| := abs_nonneg _
      nlinarith
    have hxa_le_σ : x ^ a ≤ σ := by
      calc x ^ a ≤ x ^ a * q := by nlinarith [Real.rpow_nonneg hx.le a]
        _ ≤ σ := hσLower
    linarith
  have hsourceσ : Real.exp 1 * L ≤ σ - 2 := by
    have hsigStrong : Real.exp 1 * q ^ 2 + 2 ≤ 2 * q ^ 3 := by
      have hepos := Real.exp_pos 1
      nlinarith [sq_nonneg q, mul_nonneg (sq_nonneg q) (sub_nonneg.mpr hqe)]
    have htwoq3 : 2 * q ^ 3 ≤ σ := by
      have hmul := mul_le_mul_of_nonneg_right hdomx hq.le
      calc
        2 * q ^ 3 = (2 * q ^ 2) * q := by ring
        _ ≤ x ^ a * q := hmul
        _ ≤ σ := hσLower
    nlinarith [mul_le_mul_of_nonneg_left hLsq (Real.exp_pos 1).le]
  have hsource : Real.exp 1 * L ≤ s - 2 := by linarith
  have hlogsσ : Real.log σ ≤ 3 * q := by
    have hboundpos : 0 < 2 * x * q := by positivity
    have h := Real.log_le_log hσpos hσUpper
    rw [Real.log_mul (by positivity : (2 * x : ℝ) ≠ 0) (ne_of_gt hq),
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hx)] at h
    have hlog2le : Real.log 2 ≤ q := by
      exact Real.strictMonoOn_log.monotoneOn (by norm_num) hx hx2
    have hlogqle : Real.log q ≤ q := (Real.log_le_sub_one_of_pos hq).trans (by linarith)
    dsimp [q] at hlog2le
    linarith
  have hloglog3σ : Real.log (Real.log (3 * σ)) ≤ 2 * Real.log q := by
    have h3σ : 0 < 3 * σ := by positivity
    have h6xq : 3 * σ ≤ 6 * x * q := by nlinarith [hσUpper]
    have h6pos : 0 < 6 * x * q := by positivity
    have hlogfirst := Real.log_le_log h3σ h6xq
    rw [Real.log_mul (by positivity : (6 * x : ℝ) ≠ 0) (ne_of_gt hq),
      Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) (ne_of_gt hx)] at hlogfirst
    have hlog6le : Real.log 6 ≤ q := by
      have hq6 : (6 : ℝ) ≤ q := by
        dsimp [q, x]
        exact (le_max_left _ _).trans hq_q0
      exact (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 6)).trans (by linarith)
    have hlogqle : Real.log q ≤ q := (Real.log_le_sub_one_of_pos hq).trans (by linarith)
    have hinner : Real.log (3 * σ) ≤ 3 * q := by
      dsimp [q] at hlog6le
      linarith
    have hinnerpos : 0 < Real.log (3 * σ) := Real.log_pos (by nlinarith [hσ4])
    have h3qpos : 0 < 3 * q := by positivity
    have hsecond := Real.log_le_log hinnerpos hinner
    have hlog3le : Real.log 3 ≤ Real.log q :=
      Real.strictMonoOn_log.monotoneOn (by norm_num) hq (by linarith : (3 : ℝ) ≤ q)
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (ne_of_gt hq)] at hsecond
    linarith
  have hlogL : Real.log L ≤ 2 * Real.log q := by
    have hq2pos : 0 < q ^ 2 := sq_pos_of_pos hq
    have h := Real.log_le_log (by linarith : 0 < L) hLsq
    rw [Real.log_pow] at h
    simpa using h
  have hconst : C + 2 + Real.log 2 ≤ (d - 4) * Real.log q := by
    have hd4 : 0 < d - 4 := by linarith
    have ht := mul_le_mul_of_nonneg_left hr hd4.le
    dsimp [r0] at ht
    field_simp [ne_of_gt hd4] at ht
    linarith
  have habsorb : L + 2 * Real.log s + 3 * q + |Real.log Q| ≤ s := by
    have hbase : L + 2 * Real.log σ + 3 * q + |Real.log Q| ≤ σ := by
      linarith [hLsq, hlogsσ, habsorbσ]
    rw [hlogsSplit]
    have hlogtransport : 2 * Real.log u ≤ 2 * (u - 1) :=
      mul_le_mul_of_nonneg_left hlogu_le (by norm_num)
    have hscale : 2 * (u - 1) ≤ σ * (u - 1) :=
      mul_le_mul_of_nonneg_right (by linarith : (2 : ℝ) ≤ σ)
        (sub_nonneg.mpr hu1)
    have htransport : 2 * Real.log u ≤ s - σ := by
      calc
        2 * Real.log u ≤ 2 * (u - 1) := hlogtransport
        _ ≤ σ * (u - 1) := hscale
        _ = s - σ := by rw [hsu]; ring
    linarith
  have hqσ : q ≤ σ := by
    have hm := mul_le_mul_of_nonneg_right hxa1 hq.le
    have hm' : q ≤ x ^ a * q := by simpa [mul_comm] using hm
    exact hm'.trans hσLower
  have hAlog : 1 ≤ Real.log (3 * σ) := by
    apply (Real.le_log_iff_exp_le (by positivity : 0 < 3 * σ)).2
    calc
      Real.exp 1 ≤ q := by linarith [hqe]
      _ ≤ σ := hqσ
      _ ≤ 3 * σ := by linarith [hσpos]
  have hlog3s_mul : Real.log (3 * s) =
      Real.log (3 * σ) + Real.log u := by
    rw [hsu]
    rw [show 3 * (σ * u) = (3 * σ) * u by ring,
      Real.log_mul (by positivity : (3 * σ : ℝ) ≠ 0) (ne_of_gt hupos)]
  have hlog3s_le : Real.log (3 * s) ≤ u * Real.log (3 * σ) := by
    rw [hlog3s_mul]
    calc
      Real.log (3 * σ) + Real.log u ≤ Real.log (3 * σ) + (u - 1) :=
        by simpa [add_comm] using add_le_add_left hlogu_le (Real.log (3 * σ))
      _ ≤ Real.log (3 * σ) + (u - 1) * Real.log (3 * σ) := by
        have hm := mul_le_mul_of_nonneg_left hAlog (sub_nonneg.mpr hu1)
        simpa using hm
      _ = u * Real.log (3 * σ) := by ring
  have hloglog3s :
      Real.log (Real.log (3 * s)) ≤ 2 * Real.log q + Real.log u := by
    have hleftpos : 0 < Real.log (3 * s) := Real.log_pos (by nlinarith [hs4])
    have hrightpos : 0 < u * Real.log (3 * σ) := mul_pos hupos (lt_of_lt_of_le zero_lt_one hAlog)
    have hh := Real.log_le_log hleftpos hlog3s_le
    rw [Real.log_mul (ne_of_gt hupos)
      (ne_of_gt (lt_of_lt_of_le zero_lt_one hAlog))] at hh
    linarith
  have hσPow : σ ^ d = x * ell ^ d := by
    rw [hσdef, Real.mul_rpow (Real.rpow_nonneg hx.le _) hell.le]
    have hxad : (x ^ a) ^ d = x := by
      rw [← Real.rpow_mul hx.le]
      have : a * d = 1 := by dsimp [a]; field_simp
      rw [this, Real.rpow_one]
    rw [hxad]
  have hsPow : s ^ d = u ^ d * (x * ell ^ d) := by
    rw [hsu, Real.mul_rpow hσpos.le hupos.le, hσPow]
    ring
  have hquot : s ^ d / x = u ^ d * ell ^ d := by
    rw [hsPow]
    field_simp [ne_of_gt hx]
  have hbpos : 0 < b := by
    dsimp [b]
    have : 0 ≤ s ^ d / x := div_nonneg (Real.rpow_nonneg hspos.le _) hx.le
    linarith
  have hblog : d * Real.log q + d * Real.log u ≤ Real.log b := by
    have hqpow : q ^ d ≤ ell ^ d := Real.rpow_le_rpow hq.le hellLower hd0.le
    have hupow : 0 ≤ u ^ d := Real.rpow_nonneg hupos.le _
    have hy_le : u ^ d * q ^ d ≤ b := by
      dsimp [b]
      rw [hquot]
      calc
        u ^ d * q ^ d ≤ u ^ d * ell ^ d :=
          mul_le_mul_of_nonneg_left hqpow hupow
        _ ≤ 1 + u ^ d * ell ^ d := le_add_of_nonneg_left zero_le_one
    have hypos : 0 < u ^ d * q ^ d := mul_pos (Real.rpow_pos_of_pos hupos _)
      (Real.rpow_pos_of_pos hq _)
    have hh := Real.log_le_log hypos hy_le
    rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hupos _))
      (ne_of_gt (Real.rpow_pos_of_pos hq _)),
      Real.log_rpow hupos d, Real.log_rpow hq d] at hh
    linarith
  have hgap : Real.log L + Real.log (Real.log (3 * s)) + C + 2 + Real.log 2 ≤
      Real.log b := by
    have hmid : Real.log L + Real.log (Real.log (3 * s)) + C + 2 + Real.log 2 ≤
        d * Real.log q + d * Real.log u := by
      have hlogu_d : Real.log u ≤ d * Real.log u := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ d) hlogu0
      calc
        Real.log L + Real.log (Real.log (3 * s)) + C + 2 + Real.log 2 =
            (Real.log L + Real.log (Real.log (3 * s))) +
              (C + 2 + Real.log 2) := by ring
        _ ≤ (2 * Real.log q + (2 * Real.log q + Real.log u)) +
              ((d - 4) * Real.log q) :=
          add_le_add (add_le_add hlogL hloglog3s) hconst
        _ = d * Real.log q + Real.log u := by ring
        _ ≤ d * Real.log q + d * Real.log u :=
          add_le_add (le_refl (d * Real.log q)) hlogu_d
    exact hmid.trans hblog
  have hcore := claim145_caseB_scalar_exponent_comparison hx hq hL hs4 hQ_pos rfl
    habsorb hgap
  have hVedge := claim14_5VProduct_lower_of_localProduct
    (S := S) (D := D_real) (K := K) hDreal hlocal
  have hAform : (Real.log D_real / Real.log 2) * (1 + K / Real.log 2) = A * x := by
    dsimp [A, x]
    ring
  rw [hAform] at hVedge
  have hpowDelta : x ^ (-1 : ℝ) ≤ x ^ (-Δ) := by
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hpref : Q / x ^ 3 ≤
      C145 * (claim14_5VProduct S D_real *
        (Real.exp (Real.sqrt K) / x)) * x ^ (-Δ) := by
    have hnonneg : 0 ≤ Q / x ^ 3 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hVedge hnonneg
    have hVpos : 0 < claim14_5VProduct S D_real := by
      unfold claim14_5VProduct
      apply Finset.prod_pos
      intro p hp
      have hpS : p ∈ S.prodPrimes.primeFactors := (Finset.mem_filter.mp hp).1
      have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hpS
      have hpdiv : p ∣ S.prodPrimes := (Nat.mem_primeFactors.mp hpS).2.1
      exact sub_pos.mpr (S.nu_lt_one_of_prime p hpprime hpdiv)
    calc
      Q / x ^ 3 ≤ (claim14_5VProduct S D_real * (A * x)) * (Q / x ^ 3) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
      _ = C145 * (claim14_5VProduct S D_real * (1 / x)) *
          x ^ (-1 : ℝ) := by
            dsimp [Q, C145]
            rw [Real.rpow_neg_one]
            field_simp [ne_of_gt hx, ne_of_gt hApos]
      _ ≤ C145 * (claim14_5VProduct S D_real * (Real.exp (Real.sqrt K) / x)) *
          x ^ (-1 : ℝ) := by
            have hexpK : 1 ≤ Real.exp (Real.sqrt K) :=
              Real.one_le_exp (Real.sqrt_nonneg K)
            gcongr
      _ ≤ C145 * (claim14_5VProduct S D_real * (Real.exp (Real.sqrt K) / x)) *
          x ^ (-Δ) := by gcongr
  have hscalarCore :
      Real.exp (L + (s - 2) * (1 + Real.log L - Real.log (s - 2))) ≤
        C145 * (claim14_5VProduct S D_real * (Real.exp (Real.sqrt K) / x)) *
          x ^ (-Δ) *
          Real.exp (s * Real.log b - s * Real.log s -
            s * Real.log (Real.log (3 * s)) - C * s) := by
    exact hcore.trans (mul_le_mul_of_nonneg_right hpref (Real.exp_pos _).le)
  have hprofile :
      b ^ s * proposition131iiLowerProfile C s =
        Real.exp (s * Real.log b - s * Real.log s -
          s * Real.log (Real.log (3 * s)) - C * s) := by
    unfold proposition131iiLowerProfile
    rw [Real.rpow_def_of_pos hbpos, ← Real.exp_add]
    congr 1
    ring
  have h_cond1 : 0 < σ := hσpos
  have h_cond2 : M ≤ s := hMq.trans (hqσ.trans hsigma)
  have h_cond3 : Real.exp 1 * suzukiSourceL D_real K ≤ s - 2 := hsource
  have h_cond4 : Real.exp (suzukiSourceL D_real K + (s - 2) * (1 + Real.log (suzukiSourceL D_real K) - Real.log (s - 2))) ≤ 1 * (claim14_5VProduct S D_real * (Real.exp (Real.sqrt K) / (Real.log D_real * σ)) * ((1 + s ^ d / Real.log D_real) ^ s * s * proposition131iiLowerProfile C s) * (Real.log D_real) ^ (-Δ)) := by
    rw [← hprofile] at hscalarCore
    have hVnonneg : 0 ≤ claim14_5VProduct S D_real := by
      unfold claim14_5VProduct
      apply Finset.prod_nonneg
      intro p hp
      have hpS : p ∈ S.prodPrimes.primeFactors := (Finset.mem_filter.mp hp).1
      have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hpS
      have hpdiv : p ∣ S.prodPrimes := (Nat.mem_primeFactors.mp hpS).2.1
      exact sub_nonneg.mpr (S.nu_lt_one_of_prime p hpprime hpdiv).le
    have hprofnonneg : 0 ≤ proposition131iiLowerProfile C s := by
      unfold proposition131iiLowerProfile
      exact (Real.exp_pos _).le
    have hbpow : 0 ≤ b ^ s := Real.rpow_nonneg hbpos.le _
    have holdnonneg : 0 ≤
        C145 * (claim14_5VProduct S D_real * (Real.exp (Real.sqrt K) / x)) *
          x ^ (-Δ) * (b ^ s * proposition131iiLowerProfile C s) := by
      positivity
    have hratio : 1 ≤ s / σ := by
      apply (le_div_iff₀ hσpos).2
      simpa using hsigma
    have hlift :
        C145 * (claim14_5VProduct S D_real * (Real.exp (Real.sqrt K) / x)) *
            x ^ (-Δ) * (b ^ s * proposition131iiLowerProfile C s) ≤
          C145 * (claim14_5VProduct S D_real *
            (Real.exp (Real.sqrt K) / (x * σ))) *
            (b ^ s * s * proposition131iiLowerProfile C s) * x ^ (-Δ) := by
      calc
        _ = (C145 * (claim14_5VProduct S D_real * (Real.exp (Real.sqrt K) / x)) *
            x ^ (-Δ) * (b ^ s * proposition131iiLowerProfile C s)) * 1 := by ring
        _ ≤ (C145 * (claim14_5VProduct S D_real * (Real.exp (Real.sqrt K) / x)) *
            x ^ (-Δ) * (b ^ s * proposition131iiLowerProfile C s)) * (s / σ) :=
          mul_le_mul_of_nonneg_left hratio holdnonneg
        _ = _ := by field_simp [ne_of_gt hx, ne_of_gt hσpos]
    have hdesired := hscalarCore.trans hlift
    simpa only [σ, L, b, x, mul_assoc] using hdesired
  exact suzukiLemma14_3_le_claim145Scale_of_scalar_at S H hlocal hD h_cond1 hs h_cond2 hKpos hC145 hprop h_cond3 h_cond4

/-- Compatibility specialization of the uniform-in-`S` Case-B theorem. -/
theorem claim145_caseB_uniform
    (S : BoundingSieve) (H : Section13HatLayers)
    {d Δ Θ : ℝ}
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d) (hTheta : 1 ≤ Θ)
    (hH : Section13HatSourceContract H) :
    ∃ C1min CB : ℝ, 0 < C1min ∧ 0 < CB ∧
      Claim145CaseBClosed S H d Δ Θ C1min CB := by
  obtain ⟨C1min, CB, hC1min, hCB, hall⟩ :=
    claim145_caseB_uniform_in_S H hΔ0 hΔ1 hd hTheta hH
  exact ⟨C1min, CB, hC1min, hCB, hall S⟩


end MathlibNt.SieveTheory
